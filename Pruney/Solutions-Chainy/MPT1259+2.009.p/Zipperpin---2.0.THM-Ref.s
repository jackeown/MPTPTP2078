%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iSOCilN2jB

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:20 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 150 expanded)
%              Number of leaves         :   29 (  57 expanded)
%              Depth                    :   10
%              Number of atoms          :  641 (1544 expanded)
%              Number of equality atoms :   38 (  81 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t75_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) )
            = ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) )
              = ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t75_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('6',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('9',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( ( k2_tops_1 @ X22 @ X21 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X22 ) @ ( k2_pre_topc @ X22 @ X21 ) @ ( k1_tops_1 @ X22 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(l79_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ ( k2_tops_1 @ A @ B ) )
            = ( k2_tops_1 @ A @ B ) ) ) ) )).

thf('14',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( ( k2_pre_topc @ X24 @ ( k2_tops_1 @ X24 @ X23 ) )
        = ( k2_tops_1 @ X24 @ X23 ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[l79_tops_1])).

thf('15',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l80_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) )
            = k1_xboole_0 ) ) ) )).

thf('20',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( ( k1_tops_1 @ X26 @ ( k2_tops_1 @ X26 @ ( k2_tops_1 @ X26 @ X25 ) ) )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[l80_tops_1])).

thf('21',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('26',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( ( k7_subset_1 @ X17 @ X16 @ X18 )
        = ( k4_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ X0 )
      = ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('28',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X11 ) @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('29',plain,(
    ! [X8: $i] :
      ( ( k2_subset_1 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('30',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('31',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('34',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X9 @ X10 )
        = ( k4_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['36'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('38',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','40'])).

thf('42',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X9 @ X10 )
        = ( k4_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('45',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X15 @ ( k3_subset_1 @ X15 @ X14 ) )
        = X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','39'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['43','48'])).

thf('50',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','18','24','27','49'])).

thf('51',plain,(
    ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
 != ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['50','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iSOCilN2jB
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:01:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.76/0.94  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.76/0.94  % Solved by: fo/fo7.sh
% 0.76/0.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.94  % done 466 iterations in 0.446s
% 0.76/0.94  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.76/0.94  % SZS output start Refutation
% 0.76/0.94  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.76/0.94  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.94  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.76/0.94  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.76/0.94  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.76/0.94  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.76/0.94  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.76/0.94  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.76/0.94  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.94  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.76/0.94  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.94  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.94  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.94  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.76/0.94  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.76/0.94  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.76/0.94  thf(t75_tops_1, conjecture,
% 0.76/0.94    (![A:$i]:
% 0.76/0.94     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.94       ( ![B:$i]:
% 0.76/0.94         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.94           ( ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) =
% 0.76/0.94             ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.76/0.94  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.94    (~( ![A:$i]:
% 0.76/0.94        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.94          ( ![B:$i]:
% 0.76/0.94            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.94              ( ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) =
% 0.76/0.94                ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) ) ) ) )),
% 0.76/0.94    inference('cnf.neg', [status(esa)], [t75_tops_1])).
% 0.76/0.94  thf('0', plain,
% 0.76/0.94      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf(dt_k2_tops_1, axiom,
% 0.76/0.94    (![A:$i,B:$i]:
% 0.76/0.94     ( ( ( l1_pre_topc @ A ) & 
% 0.76/0.94         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.76/0.94       ( m1_subset_1 @
% 0.76/0.94         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.76/0.94  thf('1', plain,
% 0.76/0.94      (![X19 : $i, X20 : $i]:
% 0.76/0.94         (~ (l1_pre_topc @ X19)
% 0.76/0.94          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.76/0.94          | (m1_subset_1 @ (k2_tops_1 @ X19 @ X20) @ 
% 0.76/0.94             (k1_zfmisc_1 @ (u1_struct_0 @ X19))))),
% 0.76/0.94      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.76/0.94  thf('2', plain,
% 0.76/0.94      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.76/0.94         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.94        | ~ (l1_pre_topc @ sk_A))),
% 0.76/0.94      inference('sup-', [status(thm)], ['0', '1'])).
% 0.76/0.94  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('4', plain,
% 0.76/0.94      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.76/0.94        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.94      inference('demod', [status(thm)], ['2', '3'])).
% 0.76/0.94  thf('5', plain,
% 0.76/0.94      (![X19 : $i, X20 : $i]:
% 0.76/0.94         (~ (l1_pre_topc @ X19)
% 0.76/0.94          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.76/0.94          | (m1_subset_1 @ (k2_tops_1 @ X19 @ X20) @ 
% 0.76/0.94             (k1_zfmisc_1 @ (u1_struct_0 @ X19))))),
% 0.76/0.94      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.76/0.94  thf('6', plain,
% 0.76/0.94      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.76/0.94         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.94        | ~ (l1_pre_topc @ sk_A))),
% 0.76/0.94      inference('sup-', [status(thm)], ['4', '5'])).
% 0.76/0.94  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('8', plain,
% 0.76/0.94      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.76/0.94        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.94      inference('demod', [status(thm)], ['6', '7'])).
% 0.76/0.94  thf(l78_tops_1, axiom,
% 0.76/0.94    (![A:$i]:
% 0.76/0.94     ( ( l1_pre_topc @ A ) =>
% 0.76/0.94       ( ![B:$i]:
% 0.76/0.94         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.94           ( ( k2_tops_1 @ A @ B ) =
% 0.76/0.94             ( k7_subset_1 @
% 0.76/0.94               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.76/0.94               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.76/0.94  thf('9', plain,
% 0.76/0.94      (![X21 : $i, X22 : $i]:
% 0.76/0.94         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.76/0.94          | ((k2_tops_1 @ X22 @ X21)
% 0.76/0.94              = (k7_subset_1 @ (u1_struct_0 @ X22) @ 
% 0.76/0.94                 (k2_pre_topc @ X22 @ X21) @ (k1_tops_1 @ X22 @ X21)))
% 0.76/0.94          | ~ (l1_pre_topc @ X22))),
% 0.76/0.94      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.76/0.94  thf('10', plain,
% 0.76/0.94      ((~ (l1_pre_topc @ sk_A)
% 0.76/0.94        | ((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.76/0.94            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.94               (k2_pre_topc @ sk_A @ 
% 0.76/0.94                (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 0.76/0.94               (k1_tops_1 @ sk_A @ 
% 0.76/0.94                (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))))))),
% 0.76/0.94      inference('sup-', [status(thm)], ['8', '9'])).
% 0.76/0.94  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('12', plain,
% 0.76/0.94      (((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.76/0.94         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.94            (k2_pre_topc @ sk_A @ 
% 0.76/0.94             (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 0.76/0.94            (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))))),
% 0.76/0.94      inference('demod', [status(thm)], ['10', '11'])).
% 0.76/0.94  thf('13', plain,
% 0.76/0.94      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.76/0.94        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.94      inference('demod', [status(thm)], ['2', '3'])).
% 0.76/0.94  thf(l79_tops_1, axiom,
% 0.76/0.94    (![A:$i]:
% 0.76/0.94     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.94       ( ![B:$i]:
% 0.76/0.94         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.94           ( ( k2_pre_topc @ A @ ( k2_tops_1 @ A @ B ) ) =
% 0.76/0.94             ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 0.76/0.94  thf('14', plain,
% 0.76/0.94      (![X23 : $i, X24 : $i]:
% 0.76/0.94         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.76/0.94          | ((k2_pre_topc @ X24 @ (k2_tops_1 @ X24 @ X23))
% 0.76/0.94              = (k2_tops_1 @ X24 @ X23))
% 0.76/0.94          | ~ (l1_pre_topc @ X24)
% 0.76/0.94          | ~ (v2_pre_topc @ X24))),
% 0.76/0.94      inference('cnf', [status(esa)], [l79_tops_1])).
% 0.76/0.94  thf('15', plain,
% 0.76/0.94      ((~ (v2_pre_topc @ sk_A)
% 0.76/0.94        | ~ (l1_pre_topc @ sk_A)
% 0.76/0.94        | ((k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.76/0.94            = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.76/0.94      inference('sup-', [status(thm)], ['13', '14'])).
% 0.76/0.94  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('18', plain,
% 0.76/0.94      (((k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.76/0.94         = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.76/0.94      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.76/0.94  thf('19', plain,
% 0.76/0.94      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf(l80_tops_1, axiom,
% 0.76/0.94    (![A:$i]:
% 0.76/0.94     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.94       ( ![B:$i]:
% 0.76/0.94         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.94           ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) =
% 0.76/0.94             ( k1_xboole_0 ) ) ) ) ))).
% 0.76/0.94  thf('20', plain,
% 0.76/0.94      (![X25 : $i, X26 : $i]:
% 0.76/0.94         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.76/0.94          | ((k1_tops_1 @ X26 @ (k2_tops_1 @ X26 @ (k2_tops_1 @ X26 @ X25)))
% 0.76/0.94              = (k1_xboole_0))
% 0.76/0.94          | ~ (l1_pre_topc @ X26)
% 0.76/0.94          | ~ (v2_pre_topc @ X26))),
% 0.76/0.94      inference('cnf', [status(esa)], [l80_tops_1])).
% 0.76/0.94  thf('21', plain,
% 0.76/0.94      ((~ (v2_pre_topc @ sk_A)
% 0.76/0.94        | ~ (l1_pre_topc @ sk_A)
% 0.76/0.94        | ((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.76/0.94            = (k1_xboole_0)))),
% 0.76/0.94      inference('sup-', [status(thm)], ['19', '20'])).
% 0.76/0.94  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('24', plain,
% 0.76/0.94      (((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.76/0.94         = (k1_xboole_0))),
% 0.76/0.94      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.76/0.94  thf('25', plain,
% 0.76/0.94      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.76/0.94        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.94      inference('demod', [status(thm)], ['6', '7'])).
% 0.76/0.94  thf(redefinition_k7_subset_1, axiom,
% 0.76/0.94    (![A:$i,B:$i,C:$i]:
% 0.76/0.94     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.94       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.76/0.94  thf('26', plain,
% 0.76/0.94      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.76/0.94         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.76/0.94          | ((k7_subset_1 @ X17 @ X16 @ X18) = (k4_xboole_0 @ X16 @ X18)))),
% 0.76/0.94      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.76/0.94  thf('27', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.94           (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ X0)
% 0.76/0.94           = (k4_xboole_0 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ X0))),
% 0.76/0.94      inference('sup-', [status(thm)], ['25', '26'])).
% 0.76/0.94  thf(dt_k2_subset_1, axiom,
% 0.76/0.94    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.76/0.94  thf('28', plain,
% 0.76/0.94      (![X11 : $i]: (m1_subset_1 @ (k2_subset_1 @ X11) @ (k1_zfmisc_1 @ X11))),
% 0.76/0.94      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.76/0.94  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.76/0.94  thf('29', plain, (![X8 : $i]: ((k2_subset_1 @ X8) = (X8))),
% 0.76/0.94      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.76/0.94  thf('30', plain, (![X11 : $i]: (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X11))),
% 0.76/0.94      inference('demod', [status(thm)], ['28', '29'])).
% 0.76/0.94  thf(dt_k3_subset_1, axiom,
% 0.76/0.94    (![A:$i,B:$i]:
% 0.76/0.94     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.94       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.76/0.94  thf('31', plain,
% 0.76/0.94      (![X12 : $i, X13 : $i]:
% 0.76/0.94         ((m1_subset_1 @ (k3_subset_1 @ X12 @ X13) @ (k1_zfmisc_1 @ X12))
% 0.76/0.94          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.76/0.94      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.76/0.94  thf('32', plain,
% 0.76/0.94      (![X0 : $i]: (m1_subset_1 @ (k3_subset_1 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.76/0.94      inference('sup-', [status(thm)], ['30', '31'])).
% 0.76/0.94  thf('33', plain, (![X11 : $i]: (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X11))),
% 0.76/0.94      inference('demod', [status(thm)], ['28', '29'])).
% 0.76/0.94  thf(d5_subset_1, axiom,
% 0.76/0.94    (![A:$i,B:$i]:
% 0.76/0.94     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.94       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.76/0.94  thf('34', plain,
% 0.76/0.94      (![X9 : $i, X10 : $i]:
% 0.76/0.94         (((k3_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))
% 0.76/0.94          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.76/0.94      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.76/0.94  thf('35', plain,
% 0.76/0.94      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.76/0.94      inference('sup-', [status(thm)], ['33', '34'])).
% 0.76/0.94  thf(d10_xboole_0, axiom,
% 0.76/0.94    (![A:$i,B:$i]:
% 0.76/0.94     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.76/0.94  thf('36', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.76/0.94      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.76/0.94  thf('37', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.76/0.94      inference('simplify', [status(thm)], ['36'])).
% 0.76/0.94  thf(l32_xboole_1, axiom,
% 0.76/0.94    (![A:$i,B:$i]:
% 0.76/0.94     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.76/0.94  thf('38', plain,
% 0.76/0.94      (![X3 : $i, X5 : $i]:
% 0.76/0.94         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.76/0.94      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.76/0.94  thf('39', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.76/0.94      inference('sup-', [status(thm)], ['37', '38'])).
% 0.76/0.94  thf('40', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.76/0.94      inference('sup+', [status(thm)], ['35', '39'])).
% 0.76/0.94  thf('41', plain,
% 0.76/0.94      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.76/0.94      inference('demod', [status(thm)], ['32', '40'])).
% 0.76/0.94  thf('42', plain,
% 0.76/0.94      (![X9 : $i, X10 : $i]:
% 0.76/0.94         (((k3_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))
% 0.76/0.94          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.76/0.94      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.76/0.94  thf('43', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.76/0.94      inference('sup-', [status(thm)], ['41', '42'])).
% 0.76/0.94  thf('44', plain, (![X11 : $i]: (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X11))),
% 0.76/0.94      inference('demod', [status(thm)], ['28', '29'])).
% 0.76/0.94  thf(involutiveness_k3_subset_1, axiom,
% 0.76/0.94    (![A:$i,B:$i]:
% 0.76/0.94     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.94       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.76/0.94  thf('45', plain,
% 0.76/0.94      (![X14 : $i, X15 : $i]:
% 0.76/0.94         (((k3_subset_1 @ X15 @ (k3_subset_1 @ X15 @ X14)) = (X14))
% 0.76/0.94          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.76/0.94      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.76/0.94  thf('46', plain,
% 0.76/0.94      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 0.76/0.94      inference('sup-', [status(thm)], ['44', '45'])).
% 0.76/0.94  thf('47', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.76/0.94      inference('sup+', [status(thm)], ['35', '39'])).
% 0.76/0.94  thf('48', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.76/0.94      inference('demod', [status(thm)], ['46', '47'])).
% 0.76/0.94  thf('49', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.76/0.94      inference('demod', [status(thm)], ['43', '48'])).
% 0.76/0.94  thf('50', plain,
% 0.76/0.94      (((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.76/0.94         = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.76/0.94      inference('demod', [status(thm)], ['12', '18', '24', '27', '49'])).
% 0.76/0.94  thf('51', plain,
% 0.76/0.94      (((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.76/0.94         != (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('52', plain, ($false),
% 0.76/0.94      inference('simplify_reflect-', [status(thm)], ['50', '51'])).
% 0.76/0.94  
% 0.76/0.94  % SZS output end Refutation
% 0.76/0.94  
% 0.76/0.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
