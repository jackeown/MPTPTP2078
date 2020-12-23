%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H67ZOrMVhk

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:43 EST 2020

% Result     : Theorem 1.10s
% Output     : Refutation 1.10s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 311 expanded)
%              Number of leaves         :   36 ( 103 expanded)
%              Depth                    :   15
%              Number of atoms          : 1274 (4199 expanded)
%              Number of equality atoms :   92 ( 273 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t77_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( ( k2_tops_1 @ A @ B )
              = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
            <=> ( ( k2_tops_1 @ A @ B )
                = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_tops_1])).

thf('0',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v4_pre_topc @ X25 @ X26 )
      | ( ( k2_pre_topc @ X26 @ X25 )
        = X25 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( ( k2_tops_1 @ X32 @ X31 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X32 ) @ ( k2_pre_topc @ X32 @ X31 ) @ ( k1_tops_1 @ X32 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k7_subset_1 @ X19 @ X18 @ X20 )
        = ( k4_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k6_subset_1 @ X16 @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('19',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k7_subset_1 @ X19 @ X18 @ X20 )
        = ( k6_subset_1 @ X18 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('23',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('29',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('30',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('31',plain,(
    ! [X11: $i,X12: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('32',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X9 @ X10 )
        = ( k4_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('33',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k6_subset_1 @ X16 @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('34',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X9 @ X10 )
        = ( k6_subset_1 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X11: $i,X12: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('39',plain,(
    ! [X11: $i,X12: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('40',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('41',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) )
      | ( ( k4_subset_1 @ X14 @ X13 @ X15 )
        = ( k2_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
          = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k6_subset_1 @ sk_B @ X0 ) ) )
        = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k6_subset_1 @ sk_B @ X0 ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['30','43'])).

thf('45',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(t25_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf('46',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_subset_1 @ X21 @ X22 @ ( k3_subset_1 @ X21 @ X22 ) )
        = ( k2_subset_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t25_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('47',plain,(
    ! [X8: $i] :
      ( ( k2_subset_1 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('48',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_subset_1 @ X21 @ X22 @ ( k3_subset_1 @ X21 @ X22 ) )
        = X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('51',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['44','49','50'])).

thf(t6_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('53',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('54',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_tarski @ X5 @ X4 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('55',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X6 @ X7 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X6 @ X7 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('60',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X27 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('61',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) )
      | ( ( k4_subset_1 @ X14 @ X13 @ X15 )
        = ( k2_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('69',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( ( k2_pre_topc @ X34 @ X33 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X34 ) @ X33 @ ( k2_tops_1 @ X34 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('70',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['67','72'])).

thf('74',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['53','58','73'])).

thf('75',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['44','49','50'])).

thf('76',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('78',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X29 @ X30 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('79',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['76','82'])).

thf('84',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('85',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','26','27','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H67ZOrMVhk
% 0.15/0.37  % Computer   : n017.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 18:15:02 EST 2020
% 0.22/0.37  % CPUTime    : 
% 0.22/0.37  % Running portfolio for 600 s
% 0.22/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.22/0.37  % Number of cores: 8
% 0.22/0.37  % Python version: Python 3.6.8
% 0.22/0.38  % Running in FO mode
% 1.10/1.31  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.10/1.31  % Solved by: fo/fo7.sh
% 1.10/1.31  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.10/1.31  % done 817 iterations in 0.825s
% 1.10/1.31  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.10/1.31  % SZS output start Refutation
% 1.10/1.31  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.10/1.31  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.10/1.31  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.10/1.31  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.10/1.31  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.10/1.31  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.10/1.31  thf(sk_B_type, type, sk_B: $i).
% 1.10/1.31  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.10/1.31  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.10/1.31  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.10/1.31  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 1.10/1.31  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.10/1.31  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.10/1.31  thf(sk_A_type, type, sk_A: $i).
% 1.10/1.31  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.10/1.31  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.10/1.31  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.10/1.31  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.10/1.31  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.10/1.31  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.10/1.31  thf(t77_tops_1, conjecture,
% 1.10/1.31    (![A:$i]:
% 1.10/1.31     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.10/1.31       ( ![B:$i]:
% 1.10/1.31         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.10/1.31           ( ( v4_pre_topc @ B @ A ) <=>
% 1.10/1.31             ( ( k2_tops_1 @ A @ B ) =
% 1.10/1.31               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.10/1.31  thf(zf_stmt_0, negated_conjecture,
% 1.10/1.31    (~( ![A:$i]:
% 1.10/1.31        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.10/1.31          ( ![B:$i]:
% 1.10/1.31            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.10/1.31              ( ( v4_pre_topc @ B @ A ) <=>
% 1.10/1.31                ( ( k2_tops_1 @ A @ B ) =
% 1.10/1.31                  ( k7_subset_1 @
% 1.10/1.31                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 1.10/1.31    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 1.10/1.31  thf('0', plain,
% 1.10/1.31      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.10/1.31          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.10/1.31              (k1_tops_1 @ sk_A @ sk_B)))
% 1.10/1.31        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('1', plain,
% 1.10/1.31      (~
% 1.10/1.31       (((k2_tops_1 @ sk_A @ sk_B)
% 1.10/1.31          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.10/1.31             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.10/1.31       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.10/1.31      inference('split', [status(esa)], ['0'])).
% 1.10/1.31  thf('2', plain,
% 1.10/1.31      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.10/1.31          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.10/1.31             (k1_tops_1 @ sk_A @ sk_B)))
% 1.10/1.31        | (v4_pre_topc @ sk_B @ sk_A))),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('3', plain,
% 1.10/1.31      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.10/1.31      inference('split', [status(esa)], ['2'])).
% 1.10/1.31  thf('4', plain,
% 1.10/1.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf(t52_pre_topc, axiom,
% 1.10/1.31    (![A:$i]:
% 1.10/1.31     ( ( l1_pre_topc @ A ) =>
% 1.10/1.31       ( ![B:$i]:
% 1.10/1.31         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.10/1.31           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 1.10/1.31             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 1.10/1.31               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 1.10/1.31  thf('5', plain,
% 1.10/1.31      (![X25 : $i, X26 : $i]:
% 1.10/1.31         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 1.10/1.31          | ~ (v4_pre_topc @ X25 @ X26)
% 1.10/1.31          | ((k2_pre_topc @ X26 @ X25) = (X25))
% 1.10/1.31          | ~ (l1_pre_topc @ X26))),
% 1.10/1.31      inference('cnf', [status(esa)], [t52_pre_topc])).
% 1.10/1.31  thf('6', plain,
% 1.10/1.31      ((~ (l1_pre_topc @ sk_A)
% 1.10/1.31        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 1.10/1.31        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.10/1.31      inference('sup-', [status(thm)], ['4', '5'])).
% 1.10/1.31  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('8', plain,
% 1.10/1.31      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.10/1.31      inference('demod', [status(thm)], ['6', '7'])).
% 1.10/1.31  thf('9', plain,
% 1.10/1.31      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 1.10/1.31         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.10/1.31      inference('sup-', [status(thm)], ['3', '8'])).
% 1.10/1.31  thf('10', plain,
% 1.10/1.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf(l78_tops_1, axiom,
% 1.10/1.31    (![A:$i]:
% 1.10/1.31     ( ( l1_pre_topc @ A ) =>
% 1.10/1.31       ( ![B:$i]:
% 1.10/1.31         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.10/1.31           ( ( k2_tops_1 @ A @ B ) =
% 1.10/1.31             ( k7_subset_1 @
% 1.10/1.31               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 1.10/1.31               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.10/1.31  thf('11', plain,
% 1.10/1.31      (![X31 : $i, X32 : $i]:
% 1.10/1.31         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 1.10/1.31          | ((k2_tops_1 @ X32 @ X31)
% 1.10/1.31              = (k7_subset_1 @ (u1_struct_0 @ X32) @ 
% 1.10/1.31                 (k2_pre_topc @ X32 @ X31) @ (k1_tops_1 @ X32 @ X31)))
% 1.10/1.31          | ~ (l1_pre_topc @ X32))),
% 1.10/1.31      inference('cnf', [status(esa)], [l78_tops_1])).
% 1.10/1.31  thf('12', plain,
% 1.10/1.31      ((~ (l1_pre_topc @ sk_A)
% 1.10/1.31        | ((k2_tops_1 @ sk_A @ sk_B)
% 1.10/1.31            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.10/1.31               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.10/1.31      inference('sup-', [status(thm)], ['10', '11'])).
% 1.10/1.31  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('14', plain,
% 1.10/1.31      (((k2_tops_1 @ sk_A @ sk_B)
% 1.10/1.31         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.10/1.31            (k1_tops_1 @ sk_A @ sk_B)))),
% 1.10/1.31      inference('demod', [status(thm)], ['12', '13'])).
% 1.10/1.31  thf('15', plain,
% 1.10/1.31      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.10/1.31          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.10/1.31             (k1_tops_1 @ sk_A @ sk_B))))
% 1.10/1.31         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.10/1.31      inference('sup+', [status(thm)], ['9', '14'])).
% 1.10/1.31  thf('16', plain,
% 1.10/1.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf(redefinition_k7_subset_1, axiom,
% 1.10/1.31    (![A:$i,B:$i,C:$i]:
% 1.10/1.31     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.10/1.31       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.10/1.31  thf('17', plain,
% 1.10/1.31      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.10/1.31         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 1.10/1.31          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k4_xboole_0 @ X18 @ X20)))),
% 1.10/1.31      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.10/1.31  thf(redefinition_k6_subset_1, axiom,
% 1.10/1.31    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.10/1.31  thf('18', plain,
% 1.10/1.31      (![X16 : $i, X17 : $i]:
% 1.10/1.31         ((k6_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))),
% 1.10/1.31      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.10/1.31  thf('19', plain,
% 1.10/1.31      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.10/1.31         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 1.10/1.31          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k6_subset_1 @ X18 @ X20)))),
% 1.10/1.31      inference('demod', [status(thm)], ['17', '18'])).
% 1.10/1.31  thf('20', plain,
% 1.10/1.31      (![X0 : $i]:
% 1.10/1.31         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.10/1.31           = (k6_subset_1 @ sk_B @ X0))),
% 1.10/1.31      inference('sup-', [status(thm)], ['16', '19'])).
% 1.10/1.31  thf('21', plain,
% 1.10/1.31      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.10/1.31          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.10/1.31         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.10/1.31      inference('demod', [status(thm)], ['15', '20'])).
% 1.10/1.31  thf('22', plain,
% 1.10/1.31      (![X0 : $i]:
% 1.10/1.31         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.10/1.31           = (k6_subset_1 @ sk_B @ X0))),
% 1.10/1.31      inference('sup-', [status(thm)], ['16', '19'])).
% 1.10/1.31  thf('23', plain,
% 1.10/1.31      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.10/1.31          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.10/1.31              (k1_tops_1 @ sk_A @ sk_B))))
% 1.10/1.31         <= (~
% 1.10/1.31             (((k2_tops_1 @ sk_A @ sk_B)
% 1.10/1.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.10/1.31                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.10/1.31      inference('split', [status(esa)], ['0'])).
% 1.10/1.31  thf('24', plain,
% 1.10/1.31      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.10/1.31          != (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.10/1.31         <= (~
% 1.10/1.31             (((k2_tops_1 @ sk_A @ sk_B)
% 1.10/1.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.10/1.31                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.10/1.31      inference('sup-', [status(thm)], ['22', '23'])).
% 1.10/1.31  thf('25', plain,
% 1.10/1.31      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 1.10/1.31         <= (~
% 1.10/1.31             (((k2_tops_1 @ sk_A @ sk_B)
% 1.10/1.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.10/1.31                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 1.10/1.31             ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.10/1.31      inference('sup-', [status(thm)], ['21', '24'])).
% 1.10/1.31  thf('26', plain,
% 1.10/1.31      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.10/1.31          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.10/1.31             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.10/1.31       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.10/1.31      inference('simplify', [status(thm)], ['25'])).
% 1.10/1.31  thf('27', plain,
% 1.10/1.31      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.10/1.31          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.10/1.31             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.10/1.31       ((v4_pre_topc @ sk_B @ sk_A))),
% 1.10/1.31      inference('split', [status(esa)], ['2'])).
% 1.10/1.31  thf('28', plain,
% 1.10/1.31      (![X0 : $i]:
% 1.10/1.31         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.10/1.31           = (k6_subset_1 @ sk_B @ X0))),
% 1.10/1.31      inference('sup-', [status(thm)], ['16', '19'])).
% 1.10/1.31  thf('29', plain,
% 1.10/1.31      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.10/1.31          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.10/1.31             (k1_tops_1 @ sk_A @ sk_B))))
% 1.10/1.31         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.10/1.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.10/1.31                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.10/1.31      inference('split', [status(esa)], ['2'])).
% 1.10/1.31  thf('30', plain,
% 1.10/1.31      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.10/1.31          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.10/1.31         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.10/1.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.10/1.31                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.10/1.31      inference('sup+', [status(thm)], ['28', '29'])).
% 1.10/1.31  thf(dt_k6_subset_1, axiom,
% 1.10/1.31    (![A:$i,B:$i]:
% 1.10/1.31     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.10/1.31  thf('31', plain,
% 1.10/1.31      (![X11 : $i, X12 : $i]:
% 1.10/1.31         (m1_subset_1 @ (k6_subset_1 @ X11 @ X12) @ (k1_zfmisc_1 @ X11))),
% 1.10/1.31      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 1.10/1.31  thf(d5_subset_1, axiom,
% 1.10/1.31    (![A:$i,B:$i]:
% 1.10/1.31     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.10/1.31       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.10/1.31  thf('32', plain,
% 1.10/1.31      (![X9 : $i, X10 : $i]:
% 1.10/1.31         (((k3_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))
% 1.10/1.31          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 1.10/1.31      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.10/1.31  thf('33', plain,
% 1.10/1.31      (![X16 : $i, X17 : $i]:
% 1.10/1.31         ((k6_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))),
% 1.10/1.31      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.10/1.31  thf('34', plain,
% 1.10/1.31      (![X9 : $i, X10 : $i]:
% 1.10/1.31         (((k3_subset_1 @ X9 @ X10) = (k6_subset_1 @ X9 @ X10))
% 1.10/1.31          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 1.10/1.31      inference('demod', [status(thm)], ['32', '33'])).
% 1.10/1.31  thf('35', plain,
% 1.10/1.31      (![X0 : $i, X1 : $i]:
% 1.10/1.31         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 1.10/1.31           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 1.10/1.31      inference('sup-', [status(thm)], ['31', '34'])).
% 1.10/1.31  thf('36', plain,
% 1.10/1.31      (![X11 : $i, X12 : $i]:
% 1.10/1.31         (m1_subset_1 @ (k6_subset_1 @ X11 @ X12) @ (k1_zfmisc_1 @ X11))),
% 1.10/1.31      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 1.10/1.31  thf('37', plain,
% 1.10/1.31      (![X0 : $i, X1 : $i]:
% 1.10/1.31         (m1_subset_1 @ (k3_subset_1 @ X1 @ (k6_subset_1 @ X1 @ X0)) @ 
% 1.10/1.31          (k1_zfmisc_1 @ X1))),
% 1.10/1.31      inference('sup+', [status(thm)], ['35', '36'])).
% 1.10/1.31  thf('38', plain,
% 1.10/1.31      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.10/1.31          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.10/1.31         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.10/1.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.10/1.31                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.10/1.31      inference('sup+', [status(thm)], ['28', '29'])).
% 1.10/1.31  thf('39', plain,
% 1.10/1.31      (![X11 : $i, X12 : $i]:
% 1.10/1.31         (m1_subset_1 @ (k6_subset_1 @ X11 @ X12) @ (k1_zfmisc_1 @ X11))),
% 1.10/1.31      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 1.10/1.31  thf('40', plain,
% 1.10/1.31      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 1.10/1.31         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.10/1.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.10/1.31                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.10/1.31      inference('sup+', [status(thm)], ['38', '39'])).
% 1.10/1.31  thf(redefinition_k4_subset_1, axiom,
% 1.10/1.31    (![A:$i,B:$i,C:$i]:
% 1.10/1.31     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.10/1.31         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.10/1.31       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.10/1.31  thf('41', plain,
% 1.10/1.31      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.10/1.31         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 1.10/1.31          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14))
% 1.10/1.31          | ((k4_subset_1 @ X14 @ X13 @ X15) = (k2_xboole_0 @ X13 @ X15)))),
% 1.10/1.31      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.10/1.31  thf('42', plain,
% 1.10/1.31      ((![X0 : $i]:
% 1.10/1.31          (((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 1.10/1.31             = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0))
% 1.10/1.31           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B))))
% 1.10/1.31         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.10/1.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.10/1.31                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.10/1.31      inference('sup-', [status(thm)], ['40', '41'])).
% 1.10/1.31  thf('43', plain,
% 1.10/1.31      ((![X0 : $i]:
% 1.10/1.31          ((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.10/1.31            (k3_subset_1 @ sk_B @ (k6_subset_1 @ sk_B @ X0)))
% 1.10/1.31            = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.10/1.31               (k3_subset_1 @ sk_B @ (k6_subset_1 @ sk_B @ X0)))))
% 1.10/1.31         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.10/1.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.10/1.31                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.10/1.31      inference('sup-', [status(thm)], ['37', '42'])).
% 1.10/1.31  thf('44', plain,
% 1.10/1.31      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.10/1.31          (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.10/1.31          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.10/1.31             (k3_subset_1 @ sk_B @ 
% 1.10/1.31              (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))))
% 1.10/1.31         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.10/1.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.10/1.31                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.10/1.31      inference('sup+', [status(thm)], ['30', '43'])).
% 1.10/1.31  thf('45', plain,
% 1.10/1.31      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 1.10/1.31         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.10/1.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.10/1.31                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.10/1.31      inference('sup+', [status(thm)], ['38', '39'])).
% 1.10/1.31  thf(t25_subset_1, axiom,
% 1.10/1.31    (![A:$i,B:$i]:
% 1.10/1.31     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.10/1.31       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 1.10/1.31         ( k2_subset_1 @ A ) ) ))).
% 1.10/1.31  thf('46', plain,
% 1.10/1.31      (![X21 : $i, X22 : $i]:
% 1.10/1.31         (((k4_subset_1 @ X21 @ X22 @ (k3_subset_1 @ X21 @ X22))
% 1.10/1.31            = (k2_subset_1 @ X21))
% 1.10/1.31          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 1.10/1.31      inference('cnf', [status(esa)], [t25_subset_1])).
% 1.10/1.31  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.10/1.31  thf('47', plain, (![X8 : $i]: ((k2_subset_1 @ X8) = (X8))),
% 1.10/1.31      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.10/1.31  thf('48', plain,
% 1.10/1.31      (![X21 : $i, X22 : $i]:
% 1.10/1.31         (((k4_subset_1 @ X21 @ X22 @ (k3_subset_1 @ X21 @ X22)) = (X21))
% 1.10/1.31          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 1.10/1.31      inference('demod', [status(thm)], ['46', '47'])).
% 1.10/1.31  thf('49', plain,
% 1.10/1.31      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.10/1.31          (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) = (sk_B)))
% 1.10/1.31         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.10/1.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.10/1.31                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.10/1.31      inference('sup-', [status(thm)], ['45', '48'])).
% 1.10/1.31  thf('50', plain,
% 1.10/1.31      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.10/1.31          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.10/1.31         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.10/1.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.10/1.31                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.10/1.31      inference('sup+', [status(thm)], ['28', '29'])).
% 1.10/1.31  thf('51', plain,
% 1.10/1.31      ((((sk_B)
% 1.10/1.31          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.10/1.31             (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 1.10/1.31         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.10/1.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.10/1.31                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.10/1.31      inference('demod', [status(thm)], ['44', '49', '50'])).
% 1.10/1.31  thf(t6_xboole_1, axiom,
% 1.10/1.31    (![A:$i,B:$i]:
% 1.10/1.31     ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.10/1.31  thf('52', plain,
% 1.10/1.31      (![X2 : $i, X3 : $i]:
% 1.10/1.31         ((k2_xboole_0 @ X2 @ (k2_xboole_0 @ X2 @ X3))
% 1.10/1.31           = (k2_xboole_0 @ X2 @ X3))),
% 1.10/1.31      inference('cnf', [status(esa)], [t6_xboole_1])).
% 1.10/1.31  thf('53', plain,
% 1.10/1.31      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.10/1.31          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.10/1.31             (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 1.10/1.31         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.10/1.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.10/1.31                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.10/1.31      inference('sup+', [status(thm)], ['51', '52'])).
% 1.10/1.31  thf(commutativity_k2_tarski, axiom,
% 1.10/1.31    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.10/1.31  thf('54', plain,
% 1.10/1.31      (![X4 : $i, X5 : $i]: ((k2_tarski @ X5 @ X4) = (k2_tarski @ X4 @ X5))),
% 1.10/1.31      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.10/1.31  thf(l51_zfmisc_1, axiom,
% 1.10/1.31    (![A:$i,B:$i]:
% 1.10/1.31     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.10/1.31  thf('55', plain,
% 1.10/1.31      (![X6 : $i, X7 : $i]:
% 1.10/1.31         ((k3_tarski @ (k2_tarski @ X6 @ X7)) = (k2_xboole_0 @ X6 @ X7))),
% 1.10/1.31      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.10/1.31  thf('56', plain,
% 1.10/1.31      (![X0 : $i, X1 : $i]:
% 1.10/1.31         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 1.10/1.31      inference('sup+', [status(thm)], ['54', '55'])).
% 1.10/1.31  thf('57', plain,
% 1.10/1.31      (![X6 : $i, X7 : $i]:
% 1.10/1.31         ((k3_tarski @ (k2_tarski @ X6 @ X7)) = (k2_xboole_0 @ X6 @ X7))),
% 1.10/1.31      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.10/1.31  thf('58', plain,
% 1.10/1.31      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.10/1.31      inference('sup+', [status(thm)], ['56', '57'])).
% 1.10/1.31  thf('59', plain,
% 1.10/1.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf(dt_k2_tops_1, axiom,
% 1.10/1.31    (![A:$i,B:$i]:
% 1.10/1.31     ( ( ( l1_pre_topc @ A ) & 
% 1.10/1.31         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.10/1.31       ( m1_subset_1 @
% 1.10/1.31         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.10/1.31  thf('60', plain,
% 1.10/1.31      (![X27 : $i, X28 : $i]:
% 1.10/1.31         (~ (l1_pre_topc @ X27)
% 1.10/1.31          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 1.10/1.31          | (m1_subset_1 @ (k2_tops_1 @ X27 @ X28) @ 
% 1.10/1.31             (k1_zfmisc_1 @ (u1_struct_0 @ X27))))),
% 1.10/1.31      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 1.10/1.31  thf('61', plain,
% 1.10/1.31      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.10/1.31         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.10/1.31        | ~ (l1_pre_topc @ sk_A))),
% 1.10/1.31      inference('sup-', [status(thm)], ['59', '60'])).
% 1.10/1.31  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('63', plain,
% 1.10/1.31      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.10/1.31        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.10/1.31      inference('demod', [status(thm)], ['61', '62'])).
% 1.10/1.31  thf('64', plain,
% 1.10/1.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('65', plain,
% 1.10/1.31      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.10/1.31         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 1.10/1.31          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14))
% 1.10/1.31          | ((k4_subset_1 @ X14 @ X13 @ X15) = (k2_xboole_0 @ X13 @ X15)))),
% 1.10/1.31      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.10/1.31  thf('66', plain,
% 1.10/1.31      (![X0 : $i]:
% 1.10/1.31         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.10/1.31            = (k2_xboole_0 @ sk_B @ X0))
% 1.10/1.31          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.10/1.31      inference('sup-', [status(thm)], ['64', '65'])).
% 1.10/1.31  thf('67', plain,
% 1.10/1.31      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.10/1.31         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.10/1.31      inference('sup-', [status(thm)], ['63', '66'])).
% 1.10/1.31  thf('68', plain,
% 1.10/1.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf(t65_tops_1, axiom,
% 1.10/1.31    (![A:$i]:
% 1.10/1.31     ( ( l1_pre_topc @ A ) =>
% 1.10/1.31       ( ![B:$i]:
% 1.10/1.31         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.10/1.31           ( ( k2_pre_topc @ A @ B ) =
% 1.10/1.31             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.10/1.31  thf('69', plain,
% 1.10/1.31      (![X33 : $i, X34 : $i]:
% 1.10/1.31         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 1.10/1.31          | ((k2_pre_topc @ X34 @ X33)
% 1.10/1.31              = (k4_subset_1 @ (u1_struct_0 @ X34) @ X33 @ 
% 1.10/1.31                 (k2_tops_1 @ X34 @ X33)))
% 1.10/1.31          | ~ (l1_pre_topc @ X34))),
% 1.10/1.31      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.10/1.31  thf('70', plain,
% 1.10/1.31      ((~ (l1_pre_topc @ sk_A)
% 1.10/1.31        | ((k2_pre_topc @ sk_A @ sk_B)
% 1.10/1.31            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.10/1.31               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.10/1.31      inference('sup-', [status(thm)], ['68', '69'])).
% 1.10/1.31  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('72', plain,
% 1.10/1.31      (((k2_pre_topc @ sk_A @ sk_B)
% 1.10/1.31         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.10/1.31            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.10/1.31      inference('demod', [status(thm)], ['70', '71'])).
% 1.10/1.31  thf('73', plain,
% 1.10/1.31      (((k2_pre_topc @ sk_A @ sk_B)
% 1.10/1.31         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.10/1.31      inference('sup+', [status(thm)], ['67', '72'])).
% 1.10/1.31  thf('74', plain,
% 1.10/1.31      ((((k2_pre_topc @ sk_A @ sk_B)
% 1.10/1.31          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.10/1.31             (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 1.10/1.31         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.10/1.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.10/1.31                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.10/1.31      inference('demod', [status(thm)], ['53', '58', '73'])).
% 1.10/1.31  thf('75', plain,
% 1.10/1.31      ((((sk_B)
% 1.10/1.31          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.10/1.31             (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 1.10/1.31         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.10/1.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.10/1.31                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.10/1.31      inference('demod', [status(thm)], ['44', '49', '50'])).
% 1.10/1.31  thf('76', plain,
% 1.10/1.31      ((((sk_B) = (k2_pre_topc @ sk_A @ sk_B)))
% 1.10/1.31         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.10/1.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.10/1.31                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.10/1.31      inference('sup+', [status(thm)], ['74', '75'])).
% 1.10/1.31  thf('77', plain,
% 1.10/1.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf(fc1_tops_1, axiom,
% 1.10/1.31    (![A:$i,B:$i]:
% 1.10/1.31     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 1.10/1.31         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.10/1.31       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 1.10/1.31  thf('78', plain,
% 1.10/1.31      (![X29 : $i, X30 : $i]:
% 1.10/1.31         (~ (l1_pre_topc @ X29)
% 1.10/1.31          | ~ (v2_pre_topc @ X29)
% 1.10/1.31          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 1.10/1.31          | (v4_pre_topc @ (k2_pre_topc @ X29 @ X30) @ X29))),
% 1.10/1.31      inference('cnf', [status(esa)], [fc1_tops_1])).
% 1.10/1.31  thf('79', plain,
% 1.10/1.31      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 1.10/1.31        | ~ (v2_pre_topc @ sk_A)
% 1.10/1.31        | ~ (l1_pre_topc @ sk_A))),
% 1.10/1.31      inference('sup-', [status(thm)], ['77', '78'])).
% 1.10/1.31  thf('80', plain, ((v2_pre_topc @ sk_A)),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('82', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 1.10/1.31      inference('demod', [status(thm)], ['79', '80', '81'])).
% 1.10/1.31  thf('83', plain,
% 1.10/1.31      (((v4_pre_topc @ sk_B @ sk_A))
% 1.10/1.31         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.10/1.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.10/1.31                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.10/1.31      inference('sup+', [status(thm)], ['76', '82'])).
% 1.10/1.31  thf('84', plain,
% 1.10/1.31      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.10/1.31      inference('split', [status(esa)], ['0'])).
% 1.10/1.31  thf('85', plain,
% 1.10/1.31      (~
% 1.10/1.31       (((k2_tops_1 @ sk_A @ sk_B)
% 1.10/1.31          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.10/1.31             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.10/1.31       ((v4_pre_topc @ sk_B @ sk_A))),
% 1.10/1.31      inference('sup-', [status(thm)], ['83', '84'])).
% 1.10/1.31  thf('86', plain, ($false),
% 1.10/1.31      inference('sat_resolution*', [status(thm)], ['1', '26', '27', '85'])).
% 1.10/1.31  
% 1.10/1.31  % SZS output end Refutation
% 1.10/1.31  
% 1.10/1.32  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
