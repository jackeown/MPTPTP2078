%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yeZH7rzoC6

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:44 EST 2020

% Result     : Theorem 0.99s
% Output     : Refutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 298 expanded)
%              Number of leaves         :   36 (  99 expanded)
%              Depth                    :   15
%              Number of atoms          : 1226 (4088 expanded)
%              Number of equality atoms :   86 ( 260 expanded)
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

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('32',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('35',plain,(
    ! [X11: $i,X12: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('36',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('37',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) )
      | ( ( k4_subset_1 @ X14 @ X13 @ X15 )
        = ( k2_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
          = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k6_subset_1 @ sk_B @ X0 ) ) )
        = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k6_subset_1 @ sk_B @ X0 ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['30','39'])).

thf('41',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf(t25_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf('42',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_subset_1 @ X21 @ X22 @ ( k3_subset_1 @ X21 @ X22 ) )
        = ( k2_subset_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t25_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('43',plain,(
    ! [X8: $i] :
      ( ( k2_subset_1 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('44',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_subset_1 @ X21 @ X22 @ ( k3_subset_1 @ X21 @ X22 ) )
        = X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('47',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['40','45','46'])).

thf(t6_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('48',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('49',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('50',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_tarski @ X5 @ X4 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('51',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X6 @ X7 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X6 @ X7 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('56',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( ( k2_pre_topc @ X34 @ X33 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X34 ) @ X33 @ ( k2_tops_1 @ X34 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('57',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('68',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['57','58','67'])).

thf('69',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['49','54','68'])).

thf('70',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['40','45','46'])).

thf('71',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('73',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X29 @ X30 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('74',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['71','77'])).

thf('79',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('80',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','26','27','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yeZH7rzoC6
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:59:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.99/1.20  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.99/1.20  % Solved by: fo/fo7.sh
% 0.99/1.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.99/1.20  % done 608 iterations in 0.741s
% 0.99/1.20  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.99/1.20  % SZS output start Refutation
% 0.99/1.20  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.99/1.20  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.99/1.20  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.99/1.20  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.99/1.20  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.99/1.20  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.99/1.20  thf(sk_B_type, type, sk_B: $i).
% 0.99/1.20  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.99/1.20  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.99/1.20  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.99/1.20  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.99/1.20  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.99/1.20  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.99/1.20  thf(sk_A_type, type, sk_A: $i).
% 0.99/1.20  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.99/1.20  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.99/1.20  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.99/1.20  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.99/1.20  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.99/1.20  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.99/1.20  thf(t77_tops_1, conjecture,
% 0.99/1.20    (![A:$i]:
% 0.99/1.20     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.99/1.20       ( ![B:$i]:
% 0.99/1.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.20           ( ( v4_pre_topc @ B @ A ) <=>
% 0.99/1.20             ( ( k2_tops_1 @ A @ B ) =
% 0.99/1.20               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.99/1.20  thf(zf_stmt_0, negated_conjecture,
% 0.99/1.20    (~( ![A:$i]:
% 0.99/1.20        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.99/1.20          ( ![B:$i]:
% 0.99/1.20            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.20              ( ( v4_pre_topc @ B @ A ) <=>
% 0.99/1.20                ( ( k2_tops_1 @ A @ B ) =
% 0.99/1.20                  ( k7_subset_1 @
% 0.99/1.20                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.99/1.20    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.99/1.20  thf('0', plain,
% 0.99/1.20      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.20          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.20              (k1_tops_1 @ sk_A @ sk_B)))
% 0.99/1.20        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('1', plain,
% 0.99/1.20      (~
% 0.99/1.20       (((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.20          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.20             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.99/1.20       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.99/1.20      inference('split', [status(esa)], ['0'])).
% 0.99/1.20  thf('2', plain,
% 0.99/1.20      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.20          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.20             (k1_tops_1 @ sk_A @ sk_B)))
% 0.99/1.20        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('3', plain,
% 0.99/1.20      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.99/1.20      inference('split', [status(esa)], ['2'])).
% 0.99/1.20  thf('4', plain,
% 0.99/1.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf(t52_pre_topc, axiom,
% 0.99/1.20    (![A:$i]:
% 0.99/1.20     ( ( l1_pre_topc @ A ) =>
% 0.99/1.20       ( ![B:$i]:
% 0.99/1.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.20           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.99/1.20             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.99/1.20               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.99/1.20  thf('5', plain,
% 0.99/1.20      (![X25 : $i, X26 : $i]:
% 0.99/1.20         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.99/1.20          | ~ (v4_pre_topc @ X25 @ X26)
% 0.99/1.20          | ((k2_pre_topc @ X26 @ X25) = (X25))
% 0.99/1.20          | ~ (l1_pre_topc @ X26))),
% 0.99/1.20      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.99/1.20  thf('6', plain,
% 0.99/1.20      ((~ (l1_pre_topc @ sk_A)
% 0.99/1.20        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.99/1.20        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.99/1.20      inference('sup-', [status(thm)], ['4', '5'])).
% 0.99/1.20  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('8', plain,
% 0.99/1.20      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.99/1.20      inference('demod', [status(thm)], ['6', '7'])).
% 0.99/1.20  thf('9', plain,
% 0.99/1.20      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.99/1.20         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['3', '8'])).
% 0.99/1.20  thf('10', plain,
% 0.99/1.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf(l78_tops_1, axiom,
% 0.99/1.20    (![A:$i]:
% 0.99/1.20     ( ( l1_pre_topc @ A ) =>
% 0.99/1.20       ( ![B:$i]:
% 0.99/1.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.20           ( ( k2_tops_1 @ A @ B ) =
% 0.99/1.20             ( k7_subset_1 @
% 0.99/1.20               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.99/1.20               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.99/1.20  thf('11', plain,
% 0.99/1.20      (![X31 : $i, X32 : $i]:
% 0.99/1.20         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.99/1.20          | ((k2_tops_1 @ X32 @ X31)
% 0.99/1.20              = (k7_subset_1 @ (u1_struct_0 @ X32) @ 
% 0.99/1.20                 (k2_pre_topc @ X32 @ X31) @ (k1_tops_1 @ X32 @ X31)))
% 0.99/1.20          | ~ (l1_pre_topc @ X32))),
% 0.99/1.20      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.99/1.20  thf('12', plain,
% 0.99/1.20      ((~ (l1_pre_topc @ sk_A)
% 0.99/1.20        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.20            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.99/1.20               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.99/1.20      inference('sup-', [status(thm)], ['10', '11'])).
% 0.99/1.20  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('14', plain,
% 0.99/1.20      (((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.20         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.99/1.20            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.99/1.20      inference('demod', [status(thm)], ['12', '13'])).
% 0.99/1.20  thf('15', plain,
% 0.99/1.20      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.20          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.20             (k1_tops_1 @ sk_A @ sk_B))))
% 0.99/1.20         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.99/1.20      inference('sup+', [status(thm)], ['9', '14'])).
% 0.99/1.20  thf('16', plain,
% 0.99/1.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf(redefinition_k7_subset_1, axiom,
% 0.99/1.20    (![A:$i,B:$i,C:$i]:
% 0.99/1.20     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.99/1.20       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.99/1.20  thf('17', plain,
% 0.99/1.20      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.99/1.20         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.99/1.20          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k4_xboole_0 @ X18 @ X20)))),
% 0.99/1.20      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.99/1.20  thf(redefinition_k6_subset_1, axiom,
% 0.99/1.20    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.99/1.20  thf('18', plain,
% 0.99/1.20      (![X16 : $i, X17 : $i]:
% 0.99/1.20         ((k6_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))),
% 0.99/1.20      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.99/1.20  thf('19', plain,
% 0.99/1.20      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.99/1.20         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.99/1.20          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k6_subset_1 @ X18 @ X20)))),
% 0.99/1.20      inference('demod', [status(thm)], ['17', '18'])).
% 0.99/1.20  thf('20', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.99/1.20           = (k6_subset_1 @ sk_B @ X0))),
% 0.99/1.20      inference('sup-', [status(thm)], ['16', '19'])).
% 0.99/1.20  thf('21', plain,
% 0.99/1.20      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.20          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.99/1.20         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.99/1.20      inference('demod', [status(thm)], ['15', '20'])).
% 0.99/1.20  thf('22', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.99/1.20           = (k6_subset_1 @ sk_B @ X0))),
% 0.99/1.20      inference('sup-', [status(thm)], ['16', '19'])).
% 0.99/1.20  thf('23', plain,
% 0.99/1.20      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.20          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.20              (k1_tops_1 @ sk_A @ sk_B))))
% 0.99/1.20         <= (~
% 0.99/1.20             (((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.20                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.20                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.20      inference('split', [status(esa)], ['0'])).
% 0.99/1.20  thf('24', plain,
% 0.99/1.20      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.20          != (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.99/1.20         <= (~
% 0.99/1.20             (((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.20                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.20                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.20      inference('sup-', [status(thm)], ['22', '23'])).
% 0.99/1.20  thf('25', plain,
% 0.99/1.20      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.99/1.20         <= (~
% 0.99/1.20             (((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.20                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.20                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.99/1.20             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['21', '24'])).
% 0.99/1.20  thf('26', plain,
% 0.99/1.20      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.20          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.20             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.99/1.20       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.99/1.20      inference('simplify', [status(thm)], ['25'])).
% 0.99/1.20  thf('27', plain,
% 0.99/1.20      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.20          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.20             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.99/1.20       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.99/1.20      inference('split', [status(esa)], ['2'])).
% 0.99/1.20  thf('28', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.99/1.20           = (k6_subset_1 @ sk_B @ X0))),
% 0.99/1.20      inference('sup-', [status(thm)], ['16', '19'])).
% 0.99/1.20  thf('29', plain,
% 0.99/1.20      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.20          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.20             (k1_tops_1 @ sk_A @ sk_B))))
% 0.99/1.20         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.20                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.20                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.20      inference('split', [status(esa)], ['2'])).
% 0.99/1.20  thf('30', plain,
% 0.99/1.20      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.20          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.99/1.20         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.20                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.20                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.20      inference('sup+', [status(thm)], ['28', '29'])).
% 0.99/1.20  thf(dt_k6_subset_1, axiom,
% 0.99/1.20    (![A:$i,B:$i]:
% 0.99/1.20     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.99/1.20  thf('31', plain,
% 0.99/1.20      (![X11 : $i, X12 : $i]:
% 0.99/1.20         (m1_subset_1 @ (k6_subset_1 @ X11 @ X12) @ (k1_zfmisc_1 @ X11))),
% 0.99/1.20      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.99/1.20  thf(dt_k3_subset_1, axiom,
% 0.99/1.20    (![A:$i,B:$i]:
% 0.99/1.20     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.99/1.20       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.99/1.20  thf('32', plain,
% 0.99/1.20      (![X9 : $i, X10 : $i]:
% 0.99/1.20         ((m1_subset_1 @ (k3_subset_1 @ X9 @ X10) @ (k1_zfmisc_1 @ X9))
% 0.99/1.20          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.99/1.20      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.99/1.20  thf('33', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]:
% 0.99/1.20         (m1_subset_1 @ (k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)) @ 
% 0.99/1.20          (k1_zfmisc_1 @ X0))),
% 0.99/1.20      inference('sup-', [status(thm)], ['31', '32'])).
% 0.99/1.20  thf('34', plain,
% 0.99/1.20      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.20          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.99/1.20         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.20                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.20                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.20      inference('sup+', [status(thm)], ['28', '29'])).
% 0.99/1.20  thf('35', plain,
% 0.99/1.20      (![X11 : $i, X12 : $i]:
% 0.99/1.20         (m1_subset_1 @ (k6_subset_1 @ X11 @ X12) @ (k1_zfmisc_1 @ X11))),
% 0.99/1.20      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.99/1.20  thf('36', plain,
% 0.99/1.20      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.99/1.20         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.20                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.20                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.20      inference('sup+', [status(thm)], ['34', '35'])).
% 0.99/1.20  thf(redefinition_k4_subset_1, axiom,
% 0.99/1.20    (![A:$i,B:$i,C:$i]:
% 0.99/1.20     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.99/1.20         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.99/1.20       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.99/1.20  thf('37', plain,
% 0.99/1.20      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.99/1.20         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.99/1.20          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14))
% 0.99/1.20          | ((k4_subset_1 @ X14 @ X13 @ X15) = (k2_xboole_0 @ X13 @ X15)))),
% 0.99/1.20      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.99/1.20  thf('38', plain,
% 0.99/1.20      ((![X0 : $i]:
% 0.99/1.20          (((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 0.99/1.20             = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0))
% 0.99/1.20           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B))))
% 0.99/1.20         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.20                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.20                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.20      inference('sup-', [status(thm)], ['36', '37'])).
% 0.99/1.20  thf('39', plain,
% 0.99/1.20      ((![X0 : $i]:
% 0.99/1.20          ((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.99/1.20            (k3_subset_1 @ sk_B @ (k6_subset_1 @ sk_B @ X0)))
% 0.99/1.20            = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.99/1.20               (k3_subset_1 @ sk_B @ (k6_subset_1 @ sk_B @ X0)))))
% 0.99/1.20         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.20                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.20                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.20      inference('sup-', [status(thm)], ['33', '38'])).
% 0.99/1.20  thf('40', plain,
% 0.99/1.20      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.99/1.20          (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.99/1.20          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.99/1.20             (k3_subset_1 @ sk_B @ 
% 0.99/1.20              (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))))
% 0.99/1.20         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.20                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.20                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.20      inference('sup+', [status(thm)], ['30', '39'])).
% 0.99/1.20  thf('41', plain,
% 0.99/1.20      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.99/1.20         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.20                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.20                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.20      inference('sup+', [status(thm)], ['34', '35'])).
% 0.99/1.20  thf(t25_subset_1, axiom,
% 0.99/1.20    (![A:$i,B:$i]:
% 0.99/1.20     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.99/1.20       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.99/1.20         ( k2_subset_1 @ A ) ) ))).
% 0.99/1.20  thf('42', plain,
% 0.99/1.20      (![X21 : $i, X22 : $i]:
% 0.99/1.20         (((k4_subset_1 @ X21 @ X22 @ (k3_subset_1 @ X21 @ X22))
% 0.99/1.20            = (k2_subset_1 @ X21))
% 0.99/1.20          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 0.99/1.20      inference('cnf', [status(esa)], [t25_subset_1])).
% 0.99/1.20  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.99/1.20  thf('43', plain, (![X8 : $i]: ((k2_subset_1 @ X8) = (X8))),
% 0.99/1.20      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.99/1.20  thf('44', plain,
% 0.99/1.20      (![X21 : $i, X22 : $i]:
% 0.99/1.20         (((k4_subset_1 @ X21 @ X22 @ (k3_subset_1 @ X21 @ X22)) = (X21))
% 0.99/1.20          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 0.99/1.20      inference('demod', [status(thm)], ['42', '43'])).
% 0.99/1.20  thf('45', plain,
% 0.99/1.20      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.99/1.20          (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) = (sk_B)))
% 0.99/1.20         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.20                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.20                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.20      inference('sup-', [status(thm)], ['41', '44'])).
% 0.99/1.20  thf('46', plain,
% 0.99/1.20      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.20          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.99/1.20         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.20                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.20                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.20      inference('sup+', [status(thm)], ['28', '29'])).
% 0.99/1.20  thf('47', plain,
% 0.99/1.20      ((((sk_B)
% 0.99/1.20          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.99/1.20             (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 0.99/1.20         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.20                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.20                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.20      inference('demod', [status(thm)], ['40', '45', '46'])).
% 0.99/1.20  thf(t6_xboole_1, axiom,
% 0.99/1.20    (![A:$i,B:$i]:
% 0.99/1.20     ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.99/1.20  thf('48', plain,
% 0.99/1.20      (![X2 : $i, X3 : $i]:
% 0.99/1.20         ((k2_xboole_0 @ X2 @ (k2_xboole_0 @ X2 @ X3))
% 0.99/1.20           = (k2_xboole_0 @ X2 @ X3))),
% 0.99/1.20      inference('cnf', [status(esa)], [t6_xboole_1])).
% 0.99/1.20  thf('49', plain,
% 0.99/1.20      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.99/1.20          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.99/1.20             (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 0.99/1.20         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.20                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.20                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.20      inference('sup+', [status(thm)], ['47', '48'])).
% 0.99/1.20  thf(commutativity_k2_tarski, axiom,
% 0.99/1.20    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.99/1.20  thf('50', plain,
% 0.99/1.20      (![X4 : $i, X5 : $i]: ((k2_tarski @ X5 @ X4) = (k2_tarski @ X4 @ X5))),
% 0.99/1.20      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.99/1.20  thf(l51_zfmisc_1, axiom,
% 0.99/1.20    (![A:$i,B:$i]:
% 0.99/1.20     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.99/1.20  thf('51', plain,
% 0.99/1.20      (![X6 : $i, X7 : $i]:
% 0.99/1.20         ((k3_tarski @ (k2_tarski @ X6 @ X7)) = (k2_xboole_0 @ X6 @ X7))),
% 0.99/1.20      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.99/1.20  thf('52', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]:
% 0.99/1.20         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.99/1.20      inference('sup+', [status(thm)], ['50', '51'])).
% 0.99/1.20  thf('53', plain,
% 0.99/1.20      (![X6 : $i, X7 : $i]:
% 0.99/1.20         ((k3_tarski @ (k2_tarski @ X6 @ X7)) = (k2_xboole_0 @ X6 @ X7))),
% 0.99/1.20      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.99/1.20  thf('54', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.99/1.20      inference('sup+', [status(thm)], ['52', '53'])).
% 0.99/1.20  thf('55', plain,
% 0.99/1.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf(t65_tops_1, axiom,
% 0.99/1.20    (![A:$i]:
% 0.99/1.20     ( ( l1_pre_topc @ A ) =>
% 0.99/1.20       ( ![B:$i]:
% 0.99/1.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.20           ( ( k2_pre_topc @ A @ B ) =
% 0.99/1.20             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.99/1.20  thf('56', plain,
% 0.99/1.20      (![X33 : $i, X34 : $i]:
% 0.99/1.20         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.99/1.20          | ((k2_pre_topc @ X34 @ X33)
% 0.99/1.20              = (k4_subset_1 @ (u1_struct_0 @ X34) @ X33 @ 
% 0.99/1.20                 (k2_tops_1 @ X34 @ X33)))
% 0.99/1.20          | ~ (l1_pre_topc @ X34))),
% 0.99/1.20      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.99/1.20  thf('57', plain,
% 0.99/1.20      ((~ (l1_pre_topc @ sk_A)
% 0.99/1.20        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.99/1.20            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.20               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.99/1.20      inference('sup-', [status(thm)], ['55', '56'])).
% 0.99/1.20  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('59', plain,
% 0.99/1.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf(dt_k2_tops_1, axiom,
% 0.99/1.20    (![A:$i,B:$i]:
% 0.99/1.20     ( ( ( l1_pre_topc @ A ) & 
% 0.99/1.20         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.99/1.20       ( m1_subset_1 @
% 0.99/1.20         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.99/1.20  thf('60', plain,
% 0.99/1.20      (![X27 : $i, X28 : $i]:
% 0.99/1.20         (~ (l1_pre_topc @ X27)
% 0.99/1.20          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.99/1.20          | (m1_subset_1 @ (k2_tops_1 @ X27 @ X28) @ 
% 0.99/1.20             (k1_zfmisc_1 @ (u1_struct_0 @ X27))))),
% 0.99/1.20      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.99/1.20  thf('61', plain,
% 0.99/1.20      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.99/1.20         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.99/1.20        | ~ (l1_pre_topc @ sk_A))),
% 0.99/1.20      inference('sup-', [status(thm)], ['59', '60'])).
% 0.99/1.20  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('63', plain,
% 0.99/1.20      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.99/1.20        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.20      inference('demod', [status(thm)], ['61', '62'])).
% 0.99/1.20  thf('64', plain,
% 0.99/1.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('65', plain,
% 0.99/1.20      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.99/1.20         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.99/1.20          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14))
% 0.99/1.20          | ((k4_subset_1 @ X14 @ X13 @ X15) = (k2_xboole_0 @ X13 @ X15)))),
% 0.99/1.20      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.99/1.20  thf('66', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.99/1.20            = (k2_xboole_0 @ sk_B @ X0))
% 0.99/1.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.99/1.20      inference('sup-', [status(thm)], ['64', '65'])).
% 0.99/1.20  thf('67', plain,
% 0.99/1.20      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.99/1.20         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['63', '66'])).
% 0.99/1.20  thf('68', plain,
% 0.99/1.20      (((k2_pre_topc @ sk_A @ sk_B)
% 0.99/1.20         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.99/1.20      inference('demod', [status(thm)], ['57', '58', '67'])).
% 0.99/1.20  thf('69', plain,
% 0.99/1.20      ((((k2_pre_topc @ sk_A @ sk_B)
% 0.99/1.20          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.99/1.20             (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 0.99/1.20         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.20                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.20                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.20      inference('demod', [status(thm)], ['49', '54', '68'])).
% 0.99/1.20  thf('70', plain,
% 0.99/1.20      ((((sk_B)
% 0.99/1.20          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.99/1.20             (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 0.99/1.20         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.20                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.20                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.20      inference('demod', [status(thm)], ['40', '45', '46'])).
% 0.99/1.20  thf('71', plain,
% 0.99/1.20      ((((sk_B) = (k2_pre_topc @ sk_A @ sk_B)))
% 0.99/1.20         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.20                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.20                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.20      inference('sup+', [status(thm)], ['69', '70'])).
% 0.99/1.20  thf('72', plain,
% 0.99/1.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf(fc1_tops_1, axiom,
% 0.99/1.20    (![A:$i,B:$i]:
% 0.99/1.20     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.99/1.20         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.99/1.20       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.99/1.20  thf('73', plain,
% 0.99/1.20      (![X29 : $i, X30 : $i]:
% 0.99/1.20         (~ (l1_pre_topc @ X29)
% 0.99/1.20          | ~ (v2_pre_topc @ X29)
% 0.99/1.20          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.99/1.20          | (v4_pre_topc @ (k2_pre_topc @ X29 @ X30) @ X29))),
% 0.99/1.20      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.99/1.20  thf('74', plain,
% 0.99/1.20      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.99/1.20        | ~ (v2_pre_topc @ sk_A)
% 0.99/1.20        | ~ (l1_pre_topc @ sk_A))),
% 0.99/1.20      inference('sup-', [status(thm)], ['72', '73'])).
% 0.99/1.20  thf('75', plain, ((v2_pre_topc @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('77', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.99/1.20      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.99/1.20  thf('78', plain,
% 0.99/1.20      (((v4_pre_topc @ sk_B @ sk_A))
% 0.99/1.20         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.20                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.20                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.20      inference('sup+', [status(thm)], ['71', '77'])).
% 0.99/1.20  thf('79', plain,
% 0.99/1.20      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.99/1.20      inference('split', [status(esa)], ['0'])).
% 0.99/1.20  thf('80', plain,
% 0.99/1.20      (~
% 0.99/1.20       (((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.20          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.20             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.99/1.20       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.99/1.20      inference('sup-', [status(thm)], ['78', '79'])).
% 0.99/1.20  thf('81', plain, ($false),
% 0.99/1.20      inference('sat_resolution*', [status(thm)], ['1', '26', '27', '80'])).
% 0.99/1.20  
% 0.99/1.20  % SZS output end Refutation
% 0.99/1.20  
% 0.99/1.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
