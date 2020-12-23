%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2sCeaBZmtx

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:44 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 214 expanded)
%              Number of leaves         :   40 (  76 expanded)
%              Depth                    :   15
%              Number of atoms          : 1201 (2759 expanded)
%              Number of equality atoms :   86 ( 172 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

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
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v4_pre_topc @ X29 @ X30 )
      | ( ( k2_pre_topc @ X30 @ X29 )
        = X29 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
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
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( ( k2_tops_1 @ X36 @ X35 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X36 ) @ ( k2_pre_topc @ X36 @ X35 ) @ ( k1_tops_1 @ X36 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X36 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k7_subset_1 @ X23 @ X22 @ X24 )
        = ( k4_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k6_subset_1 @ X20 @ X21 )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('19',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k7_subset_1 @ X23 @ X22 @ X24 )
        = ( k6_subset_1 @ X22 @ X24 ) ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('32',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('33',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('34',plain,
    ( ( m1_subset_1 @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('36',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) )
      | ( ( k4_subset_1 @ X18 @ X17 @ X19 )
        = ( k2_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
          = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t25_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf('40',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k4_subset_1 @ X25 @ X26 @ ( k3_subset_1 @ X25 @ X26 ) )
        = ( k2_subset_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t25_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('41',plain,(
    ! [X12: $i] :
      ( ( k2_subset_1 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('42',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k4_subset_1 @ X25 @ X26 @ ( k3_subset_1 @ X25 @ X26 ) )
        = X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['38','43'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('45',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('46',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('49',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_tarski @ X9 @ X8 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('50',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X27 @ X28 ) )
      = ( k3_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X27 @ X28 ) )
      = ( k3_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['48','53'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('55',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('56',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('58',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( l1_pre_topc @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X31 @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('59',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) )
      | ( ( k4_subset_1 @ X18 @ X17 @ X19 )
        = ( k2_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('67',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( ( k2_pre_topc @ X38 @ X37 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X38 ) @ X37 @ ( k2_tops_1 @ X38 @ X37 ) ) )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('68',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['65','70'])).

thf('72',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['56','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('74',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X33 @ X34 ) @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('75',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['72','78'])).

thf('80',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('81',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','26','27','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2sCeaBZmtx
% 0.11/0.32  % Computer   : n025.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 12:30:36 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running portfolio for 600 s
% 0.11/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.32  % Number of cores: 8
% 0.11/0.33  % Python version: Python 3.6.8
% 0.11/0.33  % Running in FO mode
% 0.77/0.99  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.77/0.99  % Solved by: fo/fo7.sh
% 0.77/0.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/0.99  % done 941 iterations in 0.553s
% 0.77/0.99  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.77/0.99  % SZS output start Refutation
% 0.77/0.99  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.77/0.99  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.77/0.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.77/0.99  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.77/0.99  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.77/0.99  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.77/0.99  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.77/0.99  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.77/0.99  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.77/0.99  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.77/0.99  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.77/0.99  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.77/0.99  thf(sk_A_type, type, sk_A: $i).
% 0.77/0.99  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.77/0.99  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.77/0.99  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.77/0.99  thf(sk_B_type, type, sk_B: $i).
% 0.77/0.99  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.77/0.99  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.77/0.99  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.77/0.99  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.77/0.99  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.77/0.99  thf(t77_tops_1, conjecture,
% 0.77/0.99    (![A:$i]:
% 0.77/0.99     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.77/0.99       ( ![B:$i]:
% 0.77/0.99         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.99           ( ( v4_pre_topc @ B @ A ) <=>
% 0.77/0.99             ( ( k2_tops_1 @ A @ B ) =
% 0.77/0.99               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.77/0.99  thf(zf_stmt_0, negated_conjecture,
% 0.77/0.99    (~( ![A:$i]:
% 0.77/0.99        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.77/0.99          ( ![B:$i]:
% 0.77/0.99            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.99              ( ( v4_pre_topc @ B @ A ) <=>
% 0.77/0.99                ( ( k2_tops_1 @ A @ B ) =
% 0.77/0.99                  ( k7_subset_1 @
% 0.77/0.99                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.77/0.99    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.77/0.99  thf('0', plain,
% 0.77/0.99      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.77/0.99          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.77/0.99              (k1_tops_1 @ sk_A @ sk_B)))
% 0.77/0.99        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('1', plain,
% 0.77/0.99      (~
% 0.77/0.99       (((k2_tops_1 @ sk_A @ sk_B)
% 0.77/0.99          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.77/0.99             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.77/0.99       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.77/0.99      inference('split', [status(esa)], ['0'])).
% 0.77/0.99  thf('2', plain,
% 0.77/0.99      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.77/0.99          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.77/0.99             (k1_tops_1 @ sk_A @ sk_B)))
% 0.77/0.99        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('3', plain,
% 0.77/0.99      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.77/0.99      inference('split', [status(esa)], ['2'])).
% 0.77/0.99  thf('4', plain,
% 0.77/0.99      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf(t52_pre_topc, axiom,
% 0.77/0.99    (![A:$i]:
% 0.77/0.99     ( ( l1_pre_topc @ A ) =>
% 0.77/0.99       ( ![B:$i]:
% 0.77/0.99         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.99           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.77/0.99             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.77/0.99               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.77/0.99  thf('5', plain,
% 0.77/0.99      (![X29 : $i, X30 : $i]:
% 0.77/0.99         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.77/0.99          | ~ (v4_pre_topc @ X29 @ X30)
% 0.77/0.99          | ((k2_pre_topc @ X30 @ X29) = (X29))
% 0.77/0.99          | ~ (l1_pre_topc @ X30))),
% 0.77/0.99      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.77/0.99  thf('6', plain,
% 0.77/0.99      ((~ (l1_pre_topc @ sk_A)
% 0.77/0.99        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.77/0.99        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.77/0.99      inference('sup-', [status(thm)], ['4', '5'])).
% 0.77/0.99  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('8', plain,
% 0.77/0.99      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.77/0.99      inference('demod', [status(thm)], ['6', '7'])).
% 0.77/0.99  thf('9', plain,
% 0.77/0.99      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.77/0.99         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.77/0.99      inference('sup-', [status(thm)], ['3', '8'])).
% 0.77/0.99  thf('10', plain,
% 0.77/0.99      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf(l78_tops_1, axiom,
% 0.77/0.99    (![A:$i]:
% 0.77/0.99     ( ( l1_pre_topc @ A ) =>
% 0.77/0.99       ( ![B:$i]:
% 0.77/0.99         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.99           ( ( k2_tops_1 @ A @ B ) =
% 0.77/0.99             ( k7_subset_1 @
% 0.77/0.99               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.77/0.99               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.77/0.99  thf('11', plain,
% 0.77/0.99      (![X35 : $i, X36 : $i]:
% 0.77/0.99         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.77/0.99          | ((k2_tops_1 @ X36 @ X35)
% 0.77/0.99              = (k7_subset_1 @ (u1_struct_0 @ X36) @ 
% 0.77/0.99                 (k2_pre_topc @ X36 @ X35) @ (k1_tops_1 @ X36 @ X35)))
% 0.77/0.99          | ~ (l1_pre_topc @ X36))),
% 0.77/0.99      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.77/0.99  thf('12', plain,
% 0.77/0.99      ((~ (l1_pre_topc @ sk_A)
% 0.77/0.99        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.77/0.99            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.99               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.77/0.99      inference('sup-', [status(thm)], ['10', '11'])).
% 0.77/0.99  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('14', plain,
% 0.77/0.99      (((k2_tops_1 @ sk_A @ sk_B)
% 0.77/0.99         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.77/0.99            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.77/0.99      inference('demod', [status(thm)], ['12', '13'])).
% 0.77/0.99  thf('15', plain,
% 0.77/0.99      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.77/0.99          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.77/0.99             (k1_tops_1 @ sk_A @ sk_B))))
% 0.77/0.99         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.77/0.99      inference('sup+', [status(thm)], ['9', '14'])).
% 0.77/0.99  thf('16', plain,
% 0.77/0.99      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf(redefinition_k7_subset_1, axiom,
% 0.77/0.99    (![A:$i,B:$i,C:$i]:
% 0.77/0.99     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.77/0.99       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.77/0.99  thf('17', plain,
% 0.77/0.99      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.77/0.99         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 0.77/0.99          | ((k7_subset_1 @ X23 @ X22 @ X24) = (k4_xboole_0 @ X22 @ X24)))),
% 0.77/0.99      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.77/0.99  thf(redefinition_k6_subset_1, axiom,
% 0.77/0.99    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.77/0.99  thf('18', plain,
% 0.77/0.99      (![X20 : $i, X21 : $i]:
% 0.77/0.99         ((k6_subset_1 @ X20 @ X21) = (k4_xboole_0 @ X20 @ X21))),
% 0.77/0.99      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.77/0.99  thf('19', plain,
% 0.77/0.99      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.77/0.99         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 0.77/0.99          | ((k7_subset_1 @ X23 @ X22 @ X24) = (k6_subset_1 @ X22 @ X24)))),
% 0.77/0.99      inference('demod', [status(thm)], ['17', '18'])).
% 0.77/0.99  thf('20', plain,
% 0.77/0.99      (![X0 : $i]:
% 0.77/0.99         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.77/0.99           = (k6_subset_1 @ sk_B @ X0))),
% 0.77/0.99      inference('sup-', [status(thm)], ['16', '19'])).
% 0.77/0.99  thf('21', plain,
% 0.77/0.99      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.77/0.99          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.77/0.99         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.77/0.99      inference('demod', [status(thm)], ['15', '20'])).
% 0.77/0.99  thf('22', plain,
% 0.77/0.99      (![X0 : $i]:
% 0.77/0.99         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.77/0.99           = (k6_subset_1 @ sk_B @ X0))),
% 0.77/0.99      inference('sup-', [status(thm)], ['16', '19'])).
% 0.77/0.99  thf('23', plain,
% 0.77/0.99      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.77/0.99          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.77/0.99              (k1_tops_1 @ sk_A @ sk_B))))
% 0.77/0.99         <= (~
% 0.77/0.99             (((k2_tops_1 @ sk_A @ sk_B)
% 0.77/0.99                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.77/0.99                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.77/0.99      inference('split', [status(esa)], ['0'])).
% 0.77/0.99  thf('24', plain,
% 0.77/0.99      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.77/0.99          != (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.77/0.99         <= (~
% 0.77/0.99             (((k2_tops_1 @ sk_A @ sk_B)
% 0.77/0.99                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.77/0.99                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.77/0.99      inference('sup-', [status(thm)], ['22', '23'])).
% 0.77/0.99  thf('25', plain,
% 0.77/0.99      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.77/0.99         <= (~
% 0.77/0.99             (((k2_tops_1 @ sk_A @ sk_B)
% 0.77/0.99                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.77/0.99                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.77/0.99             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.77/0.99      inference('sup-', [status(thm)], ['21', '24'])).
% 0.77/0.99  thf('26', plain,
% 0.77/0.99      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.77/0.99          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.77/0.99             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.77/0.99       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.77/0.99      inference('simplify', [status(thm)], ['25'])).
% 0.77/0.99  thf('27', plain,
% 0.77/0.99      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.77/0.99          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.77/0.99             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.77/0.99       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.77/0.99      inference('split', [status(esa)], ['2'])).
% 0.77/0.99  thf('28', plain,
% 0.77/0.99      (![X0 : $i]:
% 0.77/0.99         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.77/0.99           = (k6_subset_1 @ sk_B @ X0))),
% 0.77/0.99      inference('sup-', [status(thm)], ['16', '19'])).
% 0.77/0.99  thf('29', plain,
% 0.77/0.99      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.77/0.99          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.77/0.99             (k1_tops_1 @ sk_A @ sk_B))))
% 0.77/0.99         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.77/0.99                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.77/0.99                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.77/0.99      inference('split', [status(esa)], ['2'])).
% 0.77/0.99  thf('30', plain,
% 0.77/0.99      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.77/0.99          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.77/0.99         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.77/0.99                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.77/0.99                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.77/0.99      inference('sup+', [status(thm)], ['28', '29'])).
% 0.77/0.99  thf(dt_k6_subset_1, axiom,
% 0.77/0.99    (![A:$i,B:$i]:
% 0.77/0.99     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.77/0.99  thf('31', plain,
% 0.77/0.99      (![X15 : $i, X16 : $i]:
% 0.77/0.99         (m1_subset_1 @ (k6_subset_1 @ X15 @ X16) @ (k1_zfmisc_1 @ X15))),
% 0.77/0.99      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.77/0.99  thf('32', plain,
% 0.77/0.99      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.77/0.99         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.77/0.99                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.77/0.99                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.77/0.99      inference('sup+', [status(thm)], ['30', '31'])).
% 0.77/0.99  thf(dt_k3_subset_1, axiom,
% 0.77/0.99    (![A:$i,B:$i]:
% 0.77/0.99     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.77/0.99       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.77/0.99  thf('33', plain,
% 0.77/0.99      (![X13 : $i, X14 : $i]:
% 0.77/0.99         ((m1_subset_1 @ (k3_subset_1 @ X13 @ X14) @ (k1_zfmisc_1 @ X13))
% 0.77/0.99          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.77/0.99      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.77/0.99  thf('34', plain,
% 0.77/0.99      (((m1_subset_1 @ (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.77/0.99         (k1_zfmisc_1 @ sk_B)))
% 0.77/0.99         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.77/0.99                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.77/0.99                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.77/0.99      inference('sup-', [status(thm)], ['32', '33'])).
% 0.77/0.99  thf('35', plain,
% 0.77/0.99      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.77/0.99         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.77/0.99                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.77/0.99                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.77/0.99      inference('sup+', [status(thm)], ['30', '31'])).
% 0.77/0.99  thf(redefinition_k4_subset_1, axiom,
% 0.77/0.99    (![A:$i,B:$i,C:$i]:
% 0.77/0.99     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.77/0.99         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.77/0.99       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.77/0.99  thf('36', plain,
% 0.77/0.99      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.77/0.99         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.77/0.99          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18))
% 0.77/0.99          | ((k4_subset_1 @ X18 @ X17 @ X19) = (k2_xboole_0 @ X17 @ X19)))),
% 0.77/0.99      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.77/0.99  thf('37', plain,
% 0.77/0.99      ((![X0 : $i]:
% 0.77/0.99          (((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 0.77/0.99             = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0))
% 0.77/0.99           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B))))
% 0.77/0.99         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.77/0.99                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.77/0.99                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.77/0.99      inference('sup-', [status(thm)], ['35', '36'])).
% 0.77/0.99  thf('38', plain,
% 0.77/0.99      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.77/0.99          (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.77/0.99          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.77/0.99             (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 0.77/0.99         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.77/0.99                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.77/0.99                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.77/0.99      inference('sup-', [status(thm)], ['34', '37'])).
% 0.77/0.99  thf('39', plain,
% 0.77/0.99      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.77/0.99         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.77/0.99                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.77/0.99                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.77/0.99      inference('sup+', [status(thm)], ['30', '31'])).
% 0.77/0.99  thf(t25_subset_1, axiom,
% 0.77/0.99    (![A:$i,B:$i]:
% 0.77/0.99     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.77/0.99       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.77/0.99         ( k2_subset_1 @ A ) ) ))).
% 0.77/0.99  thf('40', plain,
% 0.77/0.99      (![X25 : $i, X26 : $i]:
% 0.77/0.99         (((k4_subset_1 @ X25 @ X26 @ (k3_subset_1 @ X25 @ X26))
% 0.77/0.99            = (k2_subset_1 @ X25))
% 0.77/0.99          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 0.77/0.99      inference('cnf', [status(esa)], [t25_subset_1])).
% 0.77/0.99  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.77/0.99  thf('41', plain, (![X12 : $i]: ((k2_subset_1 @ X12) = (X12))),
% 0.77/0.99      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.77/0.99  thf('42', plain,
% 0.77/0.99      (![X25 : $i, X26 : $i]:
% 0.77/0.99         (((k4_subset_1 @ X25 @ X26 @ (k3_subset_1 @ X25 @ X26)) = (X25))
% 0.77/0.99          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 0.77/0.99      inference('demod', [status(thm)], ['40', '41'])).
% 0.77/0.99  thf('43', plain,
% 0.77/0.99      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.77/0.99          (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) = (sk_B)))
% 0.77/0.99         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.77/0.99                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.77/0.99                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.77/0.99      inference('sup-', [status(thm)], ['39', '42'])).
% 0.77/0.99  thf('44', plain,
% 0.77/0.99      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.77/0.99          (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) = (sk_B)))
% 0.77/0.99         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.77/0.99                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.77/0.99                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.77/0.99      inference('sup+', [status(thm)], ['38', '43'])).
% 0.77/0.99  thf(t7_xboole_1, axiom,
% 0.77/0.99    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.77/0.99  thf('45', plain,
% 0.77/0.99      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.77/0.99      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.77/0.99  thf(t28_xboole_1, axiom,
% 0.77/0.99    (![A:$i,B:$i]:
% 0.77/0.99     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.77/0.99  thf('46', plain,
% 0.77/0.99      (![X4 : $i, X5 : $i]:
% 0.77/0.99         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.77/0.99      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.77/0.99  thf('47', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.77/0.99      inference('sup-', [status(thm)], ['45', '46'])).
% 0.77/0.99  thf('48', plain,
% 0.77/0.99      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.77/0.99          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.77/0.99         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.77/0.99                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.77/0.99                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.77/0.99      inference('sup+', [status(thm)], ['44', '47'])).
% 0.77/0.99  thf(commutativity_k2_tarski, axiom,
% 0.77/0.99    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.77/0.99  thf('49', plain,
% 0.77/0.99      (![X8 : $i, X9 : $i]: ((k2_tarski @ X9 @ X8) = (k2_tarski @ X8 @ X9))),
% 0.77/0.99      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.77/0.99  thf(t12_setfam_1, axiom,
% 0.77/0.99    (![A:$i,B:$i]:
% 0.77/0.99     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.77/0.99  thf('50', plain,
% 0.77/0.99      (![X27 : $i, X28 : $i]:
% 0.77/0.99         ((k1_setfam_1 @ (k2_tarski @ X27 @ X28)) = (k3_xboole_0 @ X27 @ X28))),
% 0.77/0.99      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.77/0.99  thf('51', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.77/0.99      inference('sup+', [status(thm)], ['49', '50'])).
% 0.77/0.99  thf('52', plain,
% 0.77/0.99      (![X27 : $i, X28 : $i]:
% 0.77/0.99         ((k1_setfam_1 @ (k2_tarski @ X27 @ X28)) = (k3_xboole_0 @ X27 @ X28))),
% 0.77/0.99      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.77/0.99  thf('53', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.77/0.99      inference('sup+', [status(thm)], ['51', '52'])).
% 0.77/0.99  thf('54', plain,
% 0.77/0.99      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.77/0.99          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.77/0.99         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.77/0.99                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.77/0.99                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.77/0.99      inference('demod', [status(thm)], ['48', '53'])).
% 0.77/0.99  thf(t22_xboole_1, axiom,
% 0.77/0.99    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.77/0.99  thf('55', plain,
% 0.77/0.99      (![X2 : $i, X3 : $i]:
% 0.77/0.99         ((k2_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)) = (X2))),
% 0.77/0.99      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.77/0.99  thf('56', plain,
% 0.77/0.99      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.77/0.99         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.77/0.99                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.77/0.99                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.77/0.99      inference('sup+', [status(thm)], ['54', '55'])).
% 0.77/0.99  thf('57', plain,
% 0.77/0.99      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf(dt_k2_tops_1, axiom,
% 0.77/0.99    (![A:$i,B:$i]:
% 0.77/0.99     ( ( ( l1_pre_topc @ A ) & 
% 0.77/0.99         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.77/0.99       ( m1_subset_1 @
% 0.77/0.99         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.77/0.99  thf('58', plain,
% 0.77/0.99      (![X31 : $i, X32 : $i]:
% 0.77/0.99         (~ (l1_pre_topc @ X31)
% 0.77/0.99          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.77/0.99          | (m1_subset_1 @ (k2_tops_1 @ X31 @ X32) @ 
% 0.77/0.99             (k1_zfmisc_1 @ (u1_struct_0 @ X31))))),
% 0.77/0.99      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.77/0.99  thf('59', plain,
% 0.77/0.99      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.77/0.99         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.77/0.99        | ~ (l1_pre_topc @ sk_A))),
% 0.77/0.99      inference('sup-', [status(thm)], ['57', '58'])).
% 0.77/0.99  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('61', plain,
% 0.77/0.99      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.77/0.99        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.99      inference('demod', [status(thm)], ['59', '60'])).
% 0.77/0.99  thf('62', plain,
% 0.77/0.99      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('63', plain,
% 0.77/0.99      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.77/0.99         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.77/0.99          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18))
% 0.77/0.99          | ((k4_subset_1 @ X18 @ X17 @ X19) = (k2_xboole_0 @ X17 @ X19)))),
% 0.77/0.99      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.77/0.99  thf('64', plain,
% 0.77/0.99      (![X0 : $i]:
% 0.77/0.99         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.77/0.99            = (k2_xboole_0 @ sk_B @ X0))
% 0.77/0.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.77/0.99      inference('sup-', [status(thm)], ['62', '63'])).
% 0.77/0.99  thf('65', plain,
% 0.77/0.99      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.77/0.99         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.77/0.99      inference('sup-', [status(thm)], ['61', '64'])).
% 0.77/0.99  thf('66', plain,
% 0.77/0.99      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf(t65_tops_1, axiom,
% 0.77/0.99    (![A:$i]:
% 0.77/0.99     ( ( l1_pre_topc @ A ) =>
% 0.77/0.99       ( ![B:$i]:
% 0.77/0.99         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.99           ( ( k2_pre_topc @ A @ B ) =
% 0.77/0.99             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.77/0.99  thf('67', plain,
% 0.77/0.99      (![X37 : $i, X38 : $i]:
% 0.77/0.99         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.77/0.99          | ((k2_pre_topc @ X38 @ X37)
% 0.77/0.99              = (k4_subset_1 @ (u1_struct_0 @ X38) @ X37 @ 
% 0.77/0.99                 (k2_tops_1 @ X38 @ X37)))
% 0.77/0.99          | ~ (l1_pre_topc @ X38))),
% 0.77/0.99      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.77/0.99  thf('68', plain,
% 0.77/0.99      ((~ (l1_pre_topc @ sk_A)
% 0.77/0.99        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.77/0.99            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.77/0.99               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.77/0.99      inference('sup-', [status(thm)], ['66', '67'])).
% 0.77/0.99  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('70', plain,
% 0.77/0.99      (((k2_pre_topc @ sk_A @ sk_B)
% 0.77/0.99         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.77/0.99            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.77/0.99      inference('demod', [status(thm)], ['68', '69'])).
% 0.77/0.99  thf('71', plain,
% 0.77/0.99      (((k2_pre_topc @ sk_A @ sk_B)
% 0.77/0.99         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.77/0.99      inference('sup+', [status(thm)], ['65', '70'])).
% 0.77/0.99  thf('72', plain,
% 0.77/0.99      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.77/0.99         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.77/0.99                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.77/0.99                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.77/0.99      inference('sup+', [status(thm)], ['56', '71'])).
% 0.77/0.99  thf('73', plain,
% 0.77/0.99      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf(fc1_tops_1, axiom,
% 0.77/0.99    (![A:$i,B:$i]:
% 0.77/0.99     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.77/0.99         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.77/0.99       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.77/0.99  thf('74', plain,
% 0.77/0.99      (![X33 : $i, X34 : $i]:
% 0.77/0.99         (~ (l1_pre_topc @ X33)
% 0.77/0.99          | ~ (v2_pre_topc @ X33)
% 0.77/0.99          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.77/0.99          | (v4_pre_topc @ (k2_pre_topc @ X33 @ X34) @ X33))),
% 0.77/0.99      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.77/0.99  thf('75', plain,
% 0.77/0.99      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.77/0.99        | ~ (v2_pre_topc @ sk_A)
% 0.77/0.99        | ~ (l1_pre_topc @ sk_A))),
% 0.77/0.99      inference('sup-', [status(thm)], ['73', '74'])).
% 0.77/0.99  thf('76', plain, ((v2_pre_topc @ sk_A)),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('78', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.77/0.99      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.77/0.99  thf('79', plain,
% 0.77/0.99      (((v4_pre_topc @ sk_B @ sk_A))
% 0.77/0.99         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.77/0.99                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.77/0.99                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.77/0.99      inference('sup+', [status(thm)], ['72', '78'])).
% 0.77/0.99  thf('80', plain,
% 0.77/0.99      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.77/0.99      inference('split', [status(esa)], ['0'])).
% 0.77/0.99  thf('81', plain,
% 0.77/0.99      (~
% 0.77/0.99       (((k2_tops_1 @ sk_A @ sk_B)
% 0.77/0.99          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.77/0.99             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.77/0.99       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.77/0.99      inference('sup-', [status(thm)], ['79', '80'])).
% 0.77/0.99  thf('82', plain, ($false),
% 0.77/0.99      inference('sat_resolution*', [status(thm)], ['1', '26', '27', '81'])).
% 0.77/0.99  
% 0.77/0.99  % SZS output end Refutation
% 0.77/0.99  
% 0.77/1.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
