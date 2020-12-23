%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LU7hq0E9BV

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:54 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 398 expanded)
%              Number of leaves         :   35 ( 126 expanded)
%              Depth                    :   19
%              Number of atoms          : 1405 (5165 expanded)
%              Number of equality atoms :   93 ( 250 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

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
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v4_pre_topc @ X24 @ X25 )
      | ( ( k2_pre_topc @ X25 @ X24 )
        = X24 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
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
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( ( k2_tops_1 @ X31 @ X30 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X31 ) @ ( k2_pre_topc @ X31 @ X30 ) @ ( k1_tops_1 @ X31 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( ( k7_subset_1 @ X17 @ X16 @ X18 )
        = ( k4_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('21',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('27',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X33 @ X32 ) @ X32 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['28','29'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('31',plain,(
    ! [X21: $i,X23: $i] :
      ( ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( r1_tarski @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('34',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('35',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('37',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('38',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('40',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_B ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('42',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_subset_1 @ X7 @ X8 )
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('43',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_B ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['35','44'])).

thf('46',plain,(
    ! [X21: $i,X23: $i] :
      ( ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( r1_tarski @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('47',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('48',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) )
      | ( ( k4_subset_1 @ X14 @ X13 @ X15 )
        = ( k2_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('49',plain,
    ( ! [X0: $i] :
        ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
          = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['32','49'])).

thf('51',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('52',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('53',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X12 @ ( k3_subset_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('54',plain,
    ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('56',plain,
    ( ( k3_subset_1 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['51','56'])).

thf('58',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('59',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_subset_1 @ X7 @ X8 )
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('60',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['57','60'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('62',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('63',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('65',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('66',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( ( k2_pre_topc @ X35 @ X34 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X35 ) @ X34 @ ( k2_tops_1 @ X35 @ X34 ) ) )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('67',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('70',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X26 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('71',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) )
      | ( ( k4_subset_1 @ X14 @ X13 @ X15 )
        = ( k2_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['67','68','77'])).

thf('79',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['63','64','78'])).

thf('80',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['50','79'])).

thf('81',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(t25_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf('82',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_subset_1 @ X19 @ X20 @ ( k3_subset_1 @ X19 @ X20 ) )
        = ( k2_subset_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t25_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('83',plain,(
    ! [X6: $i] :
      ( ( k2_subset_1 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('84',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_subset_1 @ X19 @ X20 @ ( k3_subset_1 @ X19 @ X20 ) )
        = X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['51','56'])).

thf('87',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['80','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('90',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X28 @ X29 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('91',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['88','94'])).

thf('96',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('97',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','24','25','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LU7hq0E9BV
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:59:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.39/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.58  % Solved by: fo/fo7.sh
% 0.39/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.58  % done 263 iterations in 0.123s
% 0.39/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.58  % SZS output start Refutation
% 0.39/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.58  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.39/0.58  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.39/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.39/0.58  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.39/0.58  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.39/0.58  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.39/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.58  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.39/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.58  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.39/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.39/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.58  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.39/0.58  thf(t77_tops_1, conjecture,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.58           ( ( v4_pre_topc @ B @ A ) <=>
% 0.39/0.58             ( ( k2_tops_1 @ A @ B ) =
% 0.39/0.58               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.39/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.58    (~( ![A:$i]:
% 0.39/0.58        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.58          ( ![B:$i]:
% 0.39/0.58            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.58              ( ( v4_pre_topc @ B @ A ) <=>
% 0.39/0.58                ( ( k2_tops_1 @ A @ B ) =
% 0.39/0.58                  ( k7_subset_1 @
% 0.39/0.58                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.39/0.58    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.39/0.58  thf('0', plain,
% 0.39/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.58          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.58              (k1_tops_1 @ sk_A @ sk_B)))
% 0.39/0.58        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('1', plain,
% 0.39/0.58      (~
% 0.39/0.58       (((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.58          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.58             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.39/0.58       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.39/0.58      inference('split', [status(esa)], ['0'])).
% 0.39/0.58  thf('2', plain,
% 0.39/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.58          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.58             (k1_tops_1 @ sk_A @ sk_B)))
% 0.39/0.58        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('3', plain,
% 0.39/0.58      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.39/0.58      inference('split', [status(esa)], ['2'])).
% 0.39/0.58  thf('4', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(t52_pre_topc, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( l1_pre_topc @ A ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.58           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.39/0.58             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.39/0.58               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.39/0.58  thf('5', plain,
% 0.39/0.58      (![X24 : $i, X25 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.39/0.58          | ~ (v4_pre_topc @ X24 @ X25)
% 0.39/0.58          | ((k2_pre_topc @ X25 @ X24) = (X24))
% 0.39/0.58          | ~ (l1_pre_topc @ X25))),
% 0.39/0.58      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.39/0.58  thf('6', plain,
% 0.39/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.39/0.58        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.39/0.58        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['4', '5'])).
% 0.39/0.58  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('8', plain,
% 0.39/0.58      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['6', '7'])).
% 0.39/0.58  thf('9', plain,
% 0.39/0.58      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.39/0.58         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['3', '8'])).
% 0.39/0.58  thf('10', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(l78_tops_1, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( l1_pre_topc @ A ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.58           ( ( k2_tops_1 @ A @ B ) =
% 0.39/0.58             ( k7_subset_1 @
% 0.39/0.58               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.39/0.58               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.39/0.58  thf('11', plain,
% 0.39/0.58      (![X30 : $i, X31 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.39/0.58          | ((k2_tops_1 @ X31 @ X30)
% 0.39/0.58              = (k7_subset_1 @ (u1_struct_0 @ X31) @ 
% 0.39/0.58                 (k2_pre_topc @ X31 @ X30) @ (k1_tops_1 @ X31 @ X30)))
% 0.39/0.58          | ~ (l1_pre_topc @ X31))),
% 0.39/0.58      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.39/0.58  thf('12', plain,
% 0.39/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.39/0.58        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.58            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.58               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.39/0.58  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('14', plain,
% 0.39/0.58      (((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.58         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.39/0.58            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.39/0.58      inference('demod', [status(thm)], ['12', '13'])).
% 0.39/0.58  thf('15', plain,
% 0.39/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.58          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.58             (k1_tops_1 @ sk_A @ sk_B))))
% 0.39/0.58         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.39/0.58      inference('sup+', [status(thm)], ['9', '14'])).
% 0.39/0.58  thf('16', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(redefinition_k7_subset_1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.58       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.39/0.58  thf('17', plain,
% 0.39/0.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.39/0.58          | ((k7_subset_1 @ X17 @ X16 @ X18) = (k4_xboole_0 @ X16 @ X18)))),
% 0.39/0.58      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.39/0.58  thf('18', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.39/0.58           = (k4_xboole_0 @ sk_B @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['16', '17'])).
% 0.39/0.58  thf('19', plain,
% 0.39/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.58          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.39/0.58         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.39/0.58      inference('demod', [status(thm)], ['15', '18'])).
% 0.39/0.58  thf('20', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.39/0.58           = (k4_xboole_0 @ sk_B @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['16', '17'])).
% 0.39/0.58  thf('21', plain,
% 0.39/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.58          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.58              (k1_tops_1 @ sk_A @ sk_B))))
% 0.39/0.58         <= (~
% 0.39/0.58             (((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.39/0.58      inference('split', [status(esa)], ['0'])).
% 0.39/0.58  thf('22', plain,
% 0.39/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.58          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.39/0.58         <= (~
% 0.39/0.58             (((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['20', '21'])).
% 0.39/0.58  thf('23', plain,
% 0.39/0.58      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.39/0.58         <= (~
% 0.39/0.58             (((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.58                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.39/0.58             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['19', '22'])).
% 0.39/0.58  thf('24', plain,
% 0.39/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.58          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.58             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.39/0.58       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.39/0.58      inference('simplify', [status(thm)], ['23'])).
% 0.39/0.58  thf('25', plain,
% 0.39/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.58          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.58             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.39/0.58       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.39/0.58      inference('split', [status(esa)], ['2'])).
% 0.39/0.58  thf('26', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(t44_tops_1, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( l1_pre_topc @ A ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.58           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.39/0.58  thf('27', plain,
% 0.39/0.58      (![X32 : $i, X33 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.39/0.58          | (r1_tarski @ (k1_tops_1 @ X33 @ X32) @ X32)
% 0.39/0.58          | ~ (l1_pre_topc @ X33))),
% 0.39/0.58      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.39/0.58  thf('28', plain,
% 0.39/0.58      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['26', '27'])).
% 0.39/0.58  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('30', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.39/0.58      inference('demod', [status(thm)], ['28', '29'])).
% 0.39/0.58  thf(t3_subset, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.58  thf('31', plain,
% 0.39/0.58      (![X21 : $i, X23 : $i]:
% 0.39/0.58         ((m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X23)) | ~ (r1_tarski @ X21 @ X23))),
% 0.39/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.58  thf('32', plain,
% 0.39/0.58      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['30', '31'])).
% 0.39/0.58  thf('33', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.39/0.58           = (k4_xboole_0 @ sk_B @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['16', '17'])).
% 0.39/0.58  thf('34', plain,
% 0.39/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.58          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.58             (k1_tops_1 @ sk_A @ sk_B))))
% 0.39/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.39/0.58      inference('split', [status(esa)], ['2'])).
% 0.39/0.58  thf('35', plain,
% 0.39/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.58          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.39/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.39/0.58      inference('sup+', [status(thm)], ['33', '34'])).
% 0.39/0.58  thf('36', plain,
% 0.39/0.58      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['30', '31'])).
% 0.39/0.58  thf(dt_k3_subset_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.58       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.39/0.58  thf('37', plain,
% 0.39/0.58      (![X9 : $i, X10 : $i]:
% 0.39/0.58         ((m1_subset_1 @ (k3_subset_1 @ X9 @ X10) @ (k1_zfmisc_1 @ X9))
% 0.39/0.58          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.39/0.58  thf('38', plain,
% 0.39/0.58      ((m1_subset_1 @ (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.39/0.58        (k1_zfmisc_1 @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['36', '37'])).
% 0.39/0.58  thf('39', plain,
% 0.39/0.58      (![X21 : $i, X22 : $i]:
% 0.39/0.58         ((r1_tarski @ X21 @ X22) | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.58  thf('40', plain,
% 0.39/0.58      ((r1_tarski @ (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_B)),
% 0.39/0.58      inference('sup-', [status(thm)], ['38', '39'])).
% 0.39/0.58  thf('41', plain,
% 0.39/0.58      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['30', '31'])).
% 0.39/0.58  thf(d5_subset_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.58       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.39/0.58  thf('42', plain,
% 0.39/0.58      (![X7 : $i, X8 : $i]:
% 0.39/0.58         (((k3_subset_1 @ X7 @ X8) = (k4_xboole_0 @ X7 @ X8))
% 0.39/0.58          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.39/0.58      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.39/0.58  thf('43', plain,
% 0.39/0.58      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.39/0.58         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['41', '42'])).
% 0.39/0.58  thf('44', plain,
% 0.39/0.58      ((r1_tarski @ (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_B)),
% 0.39/0.58      inference('demod', [status(thm)], ['40', '43'])).
% 0.39/0.58  thf('45', plain,
% 0.39/0.58      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.39/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.39/0.58      inference('sup+', [status(thm)], ['35', '44'])).
% 0.39/0.58  thf('46', plain,
% 0.39/0.58      (![X21 : $i, X23 : $i]:
% 0.39/0.58         ((m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X23)) | ~ (r1_tarski @ X21 @ X23))),
% 0.39/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.58  thf('47', plain,
% 0.39/0.58      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.39/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['45', '46'])).
% 0.39/0.58  thf(redefinition_k4_subset_1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.39/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.39/0.58       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.39/0.58  thf('48', plain,
% 0.39/0.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.39/0.58          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14))
% 0.39/0.58          | ((k4_subset_1 @ X14 @ X13 @ X15) = (k2_xboole_0 @ X13 @ X15)))),
% 0.39/0.58      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.39/0.58  thf('49', plain,
% 0.39/0.58      ((![X0 : $i]:
% 0.39/0.58          (((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 0.39/0.58             = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0))
% 0.39/0.58           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B))))
% 0.39/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['47', '48'])).
% 0.39/0.58  thf('50', plain,
% 0.39/0.58      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.39/0.58          (k1_tops_1 @ sk_A @ sk_B))
% 0.39/0.58          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.39/0.58             (k1_tops_1 @ sk_A @ sk_B))))
% 0.39/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['32', '49'])).
% 0.39/0.58  thf('51', plain,
% 0.39/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.58          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.39/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.39/0.58      inference('sup+', [status(thm)], ['33', '34'])).
% 0.39/0.58  thf('52', plain,
% 0.39/0.58      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['30', '31'])).
% 0.39/0.58  thf(involutiveness_k3_subset_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.58       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.39/0.58  thf('53', plain,
% 0.39/0.58      (![X11 : $i, X12 : $i]:
% 0.39/0.58         (((k3_subset_1 @ X12 @ (k3_subset_1 @ X12 @ X11)) = (X11))
% 0.39/0.58          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.39/0.58      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.39/0.58  thf('54', plain,
% 0.39/0.58      (((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.39/0.58         = (k1_tops_1 @ sk_A @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['52', '53'])).
% 0.39/0.58  thf('55', plain,
% 0.39/0.58      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.39/0.58         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['41', '42'])).
% 0.39/0.58  thf('56', plain,
% 0.39/0.58      (((k3_subset_1 @ sk_B @ (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.39/0.58         = (k1_tops_1 @ sk_A @ sk_B))),
% 0.39/0.58      inference('demod', [status(thm)], ['54', '55'])).
% 0.39/0.58  thf('57', plain,
% 0.39/0.58      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.39/0.58          = (k1_tops_1 @ sk_A @ sk_B)))
% 0.39/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.39/0.58      inference('sup+', [status(thm)], ['51', '56'])).
% 0.39/0.58  thf('58', plain,
% 0.39/0.58      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.39/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['45', '46'])).
% 0.39/0.58  thf('59', plain,
% 0.39/0.58      (![X7 : $i, X8 : $i]:
% 0.39/0.58         (((k3_subset_1 @ X7 @ X8) = (k4_xboole_0 @ X7 @ X8))
% 0.39/0.58          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.39/0.58      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.39/0.58  thf('60', plain,
% 0.39/0.58      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.39/0.58          = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.39/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['58', '59'])).
% 0.39/0.58  thf('61', plain,
% 0.39/0.58      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.39/0.58          = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.39/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.39/0.58      inference('sup+', [status(thm)], ['57', '60'])).
% 0.39/0.58  thf(t39_xboole_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.39/0.58  thf('62', plain,
% 0.39/0.58      (![X4 : $i, X5 : $i]:
% 0.39/0.58         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 0.39/0.58           = (k2_xboole_0 @ X4 @ X5))),
% 0.39/0.58      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.58  thf('63', plain,
% 0.39/0.58      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.39/0.58          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 0.39/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.39/0.58      inference('sup+', [status(thm)], ['61', '62'])).
% 0.39/0.58  thf(commutativity_k2_xboole_0, axiom,
% 0.39/0.58    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.39/0.58  thf('64', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.58      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.58  thf('65', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(t65_tops_1, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( l1_pre_topc @ A ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.58           ( ( k2_pre_topc @ A @ B ) =
% 0.39/0.58             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.39/0.58  thf('66', plain,
% 0.39/0.58      (![X34 : $i, X35 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.39/0.58          | ((k2_pre_topc @ X35 @ X34)
% 0.39/0.58              = (k4_subset_1 @ (u1_struct_0 @ X35) @ X34 @ 
% 0.39/0.58                 (k2_tops_1 @ X35 @ X34)))
% 0.39/0.58          | ~ (l1_pre_topc @ X35))),
% 0.39/0.58      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.39/0.58  thf('67', plain,
% 0.39/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.39/0.58        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.39/0.58            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.58               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['65', '66'])).
% 0.39/0.58  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('69', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(dt_k2_tops_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ( l1_pre_topc @ A ) & 
% 0.39/0.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.39/0.58       ( m1_subset_1 @
% 0.39/0.58         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.39/0.58  thf('70', plain,
% 0.39/0.58      (![X26 : $i, X27 : $i]:
% 0.39/0.58         (~ (l1_pre_topc @ X26)
% 0.39/0.58          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.39/0.58          | (m1_subset_1 @ (k2_tops_1 @ X26 @ X27) @ 
% 0.39/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X26))))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.39/0.58  thf('71', plain,
% 0.39/0.58      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.39/0.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.58        | ~ (l1_pre_topc @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['69', '70'])).
% 0.39/0.58  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('73', plain,
% 0.39/0.58      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.39/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('demod', [status(thm)], ['71', '72'])).
% 0.39/0.58  thf('74', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('75', plain,
% 0.39/0.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.39/0.58          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14))
% 0.39/0.58          | ((k4_subset_1 @ X14 @ X13 @ X15) = (k2_xboole_0 @ X13 @ X15)))),
% 0.39/0.58      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.39/0.58  thf('76', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.39/0.58            = (k2_xboole_0 @ sk_B @ X0))
% 0.39/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['74', '75'])).
% 0.39/0.58  thf('77', plain,
% 0.39/0.58      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.39/0.58         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['73', '76'])).
% 0.39/0.58  thf('78', plain,
% 0.39/0.58      (((k2_pre_topc @ sk_A @ sk_B)
% 0.39/0.58         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.39/0.58      inference('demod', [status(thm)], ['67', '68', '77'])).
% 0.39/0.58  thf('79', plain,
% 0.39/0.58      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.39/0.58          = (k2_pre_topc @ sk_A @ sk_B)))
% 0.39/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.39/0.58      inference('demod', [status(thm)], ['63', '64', '78'])).
% 0.39/0.58  thf('80', plain,
% 0.39/0.58      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.39/0.58          (k1_tops_1 @ sk_A @ sk_B)) = (k2_pre_topc @ sk_A @ sk_B)))
% 0.39/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.39/0.58      inference('demod', [status(thm)], ['50', '79'])).
% 0.39/0.58  thf('81', plain,
% 0.39/0.58      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.39/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['45', '46'])).
% 0.39/0.58  thf(t25_subset_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.58       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.39/0.58         ( k2_subset_1 @ A ) ) ))).
% 0.39/0.58  thf('82', plain,
% 0.39/0.58      (![X19 : $i, X20 : $i]:
% 0.39/0.58         (((k4_subset_1 @ X19 @ X20 @ (k3_subset_1 @ X19 @ X20))
% 0.39/0.58            = (k2_subset_1 @ X19))
% 0.39/0.58          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t25_subset_1])).
% 0.39/0.58  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.39/0.58  thf('83', plain, (![X6 : $i]: ((k2_subset_1 @ X6) = (X6))),
% 0.39/0.58      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.39/0.58  thf('84', plain,
% 0.39/0.58      (![X19 : $i, X20 : $i]:
% 0.39/0.58         (((k4_subset_1 @ X19 @ X20 @ (k3_subset_1 @ X19 @ X20)) = (X19))
% 0.39/0.58          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.39/0.58      inference('demod', [status(thm)], ['82', '83'])).
% 0.39/0.58  thf('85', plain,
% 0.39/0.58      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.39/0.58          (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) = (sk_B)))
% 0.39/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['81', '84'])).
% 0.39/0.58  thf('86', plain,
% 0.39/0.58      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.39/0.58          = (k1_tops_1 @ sk_A @ sk_B)))
% 0.39/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.39/0.58      inference('sup+', [status(thm)], ['51', '56'])).
% 0.39/0.58  thf('87', plain,
% 0.39/0.58      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.39/0.58          (k1_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.39/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.39/0.58      inference('demod', [status(thm)], ['85', '86'])).
% 0.39/0.58  thf('88', plain,
% 0.39/0.58      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.39/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.39/0.58      inference('sup+', [status(thm)], ['80', '87'])).
% 0.39/0.58  thf('89', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(fc1_tops_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.39/0.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.39/0.58       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.39/0.58  thf('90', plain,
% 0.39/0.58      (![X28 : $i, X29 : $i]:
% 0.39/0.58         (~ (l1_pre_topc @ X28)
% 0.39/0.58          | ~ (v2_pre_topc @ X28)
% 0.39/0.58          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.39/0.58          | (v4_pre_topc @ (k2_pre_topc @ X28 @ X29) @ X28))),
% 0.39/0.58      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.39/0.58  thf('91', plain,
% 0.39/0.58      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.39/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.39/0.58        | ~ (l1_pre_topc @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['89', '90'])).
% 0.39/0.58  thf('92', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('94', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.39/0.58      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.39/0.58  thf('95', plain,
% 0.39/0.58      (((v4_pre_topc @ sk_B @ sk_A))
% 0.39/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.39/0.58      inference('sup+', [status(thm)], ['88', '94'])).
% 0.39/0.58  thf('96', plain,
% 0.39/0.58      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.39/0.58      inference('split', [status(esa)], ['0'])).
% 0.39/0.58  thf('97', plain,
% 0.39/0.58      (~
% 0.39/0.58       (((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.58          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.58             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.39/0.58       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['95', '96'])).
% 0.39/0.58  thf('98', plain, ($false),
% 0.39/0.58      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '97'])).
% 0.39/0.58  
% 0.39/0.58  % SZS output end Refutation
% 0.39/0.58  
% 0.39/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
