%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dzTXUf3D9K

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:19 EST 2020

% Result     : Theorem 50.45s
% Output     : Refutation 50.45s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 101 expanded)
%              Number of leaves         :   20 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  633 (1248 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t51_pre_topc,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( r1_tarski @ ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( r1_tarski @ ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t51_pre_topc])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k2_pre_topc @ sk_A @ sk_C ) )
      = ( k3_xboole_0 @ X0 @ ( k2_pre_topc @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['4','11'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_C @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t49_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('24',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( r1_tarski @ X18 @ X20 )
      | ( r1_tarski @ ( k2_pre_topc @ X19 @ X18 ) @ ( k2_pre_topc @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ X0 ) ) @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_C @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ X0 ) ) @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_C @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ sk_C @ X0 ) @ sk_C )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ X0 ) ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['14','27'])).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ X0 ) ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['13','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('39',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( r1_tarski @ X18 @ X20 )
      | ( r1_tarski @ ( k2_pre_topc @ X19 @ X18 ) @ ( k2_pre_topc @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['32','43'])).

thf('45',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('47',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X4 @ X6 )
      | ( r1_tarski @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X1 ) )
      | ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['31','48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['12','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dzTXUf3D9K
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:36:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 50.45/50.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 50.45/50.65  % Solved by: fo/fo7.sh
% 50.45/50.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 50.45/50.65  % done 31734 iterations in 50.190s
% 50.45/50.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 50.45/50.65  % SZS output start Refutation
% 50.45/50.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 50.45/50.65  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 50.45/50.65  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 50.45/50.65  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 50.45/50.65  thf(sk_B_type, type, sk_B: $i).
% 50.45/50.65  thf(sk_C_type, type, sk_C: $i).
% 50.45/50.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 50.45/50.65  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 50.45/50.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 50.45/50.65  thf(sk_A_type, type, sk_A: $i).
% 50.45/50.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 50.45/50.65  thf(t51_pre_topc, conjecture,
% 50.45/50.65    (![A:$i]:
% 50.45/50.65     ( ( l1_pre_topc @ A ) =>
% 50.45/50.65       ( ![B:$i]:
% 50.45/50.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 50.45/50.65           ( ![C:$i]:
% 50.45/50.65             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 50.45/50.65               ( r1_tarski @
% 50.45/50.65                 ( k2_pre_topc @
% 50.45/50.65                   A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 50.45/50.65                 ( k9_subset_1 @
% 50.45/50.65                   ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 50.45/50.65                   ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 50.45/50.65  thf(zf_stmt_0, negated_conjecture,
% 50.45/50.65    (~( ![A:$i]:
% 50.45/50.65        ( ( l1_pre_topc @ A ) =>
% 50.45/50.65          ( ![B:$i]:
% 50.45/50.65            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 50.45/50.65              ( ![C:$i]:
% 50.45/50.65                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 50.45/50.65                  ( r1_tarski @
% 50.45/50.65                    ( k2_pre_topc @
% 50.45/50.65                      A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 50.45/50.65                    ( k9_subset_1 @
% 50.45/50.65                      ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 50.45/50.65                      ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ) )),
% 50.45/50.65    inference('cnf.neg', [status(esa)], [t51_pre_topc])).
% 50.45/50.65  thf('0', plain,
% 50.45/50.65      (~ (r1_tarski @ 
% 50.45/50.65          (k2_pre_topc @ sk_A @ 
% 50.45/50.65           (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)) @ 
% 50.45/50.65          (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 50.45/50.65           (k2_pre_topc @ sk_A @ sk_C)))),
% 50.45/50.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.45/50.65  thf('1', plain,
% 50.45/50.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.45/50.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.45/50.65  thf(redefinition_k9_subset_1, axiom,
% 50.45/50.65    (![A:$i,B:$i,C:$i]:
% 50.45/50.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 50.45/50.65       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 50.45/50.65  thf('2', plain,
% 50.45/50.65      (![X10 : $i, X11 : $i, X12 : $i]:
% 50.45/50.65         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 50.45/50.65          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 50.45/50.65      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 50.45/50.65  thf('3', plain,
% 50.45/50.65      (![X0 : $i]:
% 50.45/50.65         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 50.45/50.65           = (k3_xboole_0 @ X0 @ sk_C))),
% 50.45/50.65      inference('sup-', [status(thm)], ['1', '2'])).
% 50.45/50.65  thf('4', plain,
% 50.45/50.65      (~ (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 50.45/50.65          (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 50.45/50.65           (k2_pre_topc @ sk_A @ sk_C)))),
% 50.45/50.65      inference('demod', [status(thm)], ['0', '3'])).
% 50.45/50.65  thf('5', plain,
% 50.45/50.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.45/50.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.45/50.65  thf(dt_k2_pre_topc, axiom,
% 50.45/50.65    (![A:$i,B:$i]:
% 50.45/50.65     ( ( ( l1_pre_topc @ A ) & 
% 50.45/50.65         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 50.45/50.65       ( m1_subset_1 @
% 50.45/50.65         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 50.45/50.65  thf('6', plain,
% 50.45/50.65      (![X16 : $i, X17 : $i]:
% 50.45/50.65         (~ (l1_pre_topc @ X16)
% 50.45/50.65          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 50.45/50.65          | (m1_subset_1 @ (k2_pre_topc @ X16 @ X17) @ 
% 50.45/50.65             (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 50.45/50.65      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 50.45/50.65  thf('7', plain,
% 50.45/50.65      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 50.45/50.65         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 50.45/50.65        | ~ (l1_pre_topc @ sk_A))),
% 50.45/50.65      inference('sup-', [status(thm)], ['5', '6'])).
% 50.45/50.65  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 50.45/50.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.45/50.65  thf('9', plain,
% 50.45/50.65      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 50.45/50.65        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.45/50.65      inference('demod', [status(thm)], ['7', '8'])).
% 50.45/50.65  thf('10', plain,
% 50.45/50.65      (![X10 : $i, X11 : $i, X12 : $i]:
% 50.45/50.65         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 50.45/50.65          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 50.45/50.65      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 50.45/50.65  thf('11', plain,
% 50.45/50.65      (![X0 : $i]:
% 50.45/50.65         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 50.45/50.65           (k2_pre_topc @ sk_A @ sk_C))
% 50.45/50.65           = (k3_xboole_0 @ X0 @ (k2_pre_topc @ sk_A @ sk_C)))),
% 50.45/50.65      inference('sup-', [status(thm)], ['9', '10'])).
% 50.45/50.65  thf('12', plain,
% 50.45/50.65      (~ (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 50.45/50.65          (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 50.45/50.65           (k2_pre_topc @ sk_A @ sk_C)))),
% 50.45/50.65      inference('demod', [status(thm)], ['4', '11'])).
% 50.45/50.65  thf(commutativity_k3_xboole_0, axiom,
% 50.45/50.65    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 50.45/50.65  thf('13', plain,
% 50.45/50.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 50.45/50.65      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 50.45/50.65  thf('14', plain,
% 50.45/50.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.45/50.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.45/50.65  thf('15', plain,
% 50.45/50.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.45/50.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.45/50.65  thf(t3_subset, axiom,
% 50.45/50.65    (![A:$i,B:$i]:
% 50.45/50.65     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 50.45/50.65  thf('16', plain,
% 50.45/50.65      (![X13 : $i, X14 : $i]:
% 50.45/50.65         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 50.45/50.65      inference('cnf', [status(esa)], [t3_subset])).
% 50.45/50.65  thf('17', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 50.45/50.65      inference('sup-', [status(thm)], ['15', '16'])).
% 50.45/50.65  thf(t17_xboole_1, axiom,
% 50.45/50.65    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 50.45/50.65  thf('18', plain,
% 50.45/50.65      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 50.45/50.65      inference('cnf', [status(esa)], [t17_xboole_1])).
% 50.45/50.65  thf(t1_xboole_1, axiom,
% 50.45/50.65    (![A:$i,B:$i,C:$i]:
% 50.45/50.65     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 50.45/50.65       ( r1_tarski @ A @ C ) ))).
% 50.45/50.65  thf('19', plain,
% 50.45/50.65      (![X7 : $i, X8 : $i, X9 : $i]:
% 50.45/50.65         (~ (r1_tarski @ X7 @ X8)
% 50.45/50.65          | ~ (r1_tarski @ X8 @ X9)
% 50.45/50.65          | (r1_tarski @ X7 @ X9))),
% 50.45/50.65      inference('cnf', [status(esa)], [t1_xboole_1])).
% 50.45/50.65  thf('20', plain,
% 50.45/50.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 50.45/50.65         ((r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 50.45/50.65      inference('sup-', [status(thm)], ['18', '19'])).
% 50.45/50.65  thf('21', plain,
% 50.45/50.65      (![X0 : $i]:
% 50.45/50.65         (r1_tarski @ (k3_xboole_0 @ sk_C @ X0) @ (u1_struct_0 @ sk_A))),
% 50.45/50.65      inference('sup-', [status(thm)], ['17', '20'])).
% 50.45/50.65  thf('22', plain,
% 50.45/50.65      (![X13 : $i, X15 : $i]:
% 50.45/50.65         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 50.45/50.65      inference('cnf', [status(esa)], [t3_subset])).
% 50.45/50.65  thf('23', plain,
% 50.45/50.65      (![X0 : $i]:
% 50.45/50.65         (m1_subset_1 @ (k3_xboole_0 @ sk_C @ X0) @ 
% 50.45/50.65          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.45/50.65      inference('sup-', [status(thm)], ['21', '22'])).
% 50.45/50.65  thf(t49_pre_topc, axiom,
% 50.45/50.65    (![A:$i]:
% 50.45/50.65     ( ( l1_pre_topc @ A ) =>
% 50.45/50.65       ( ![B:$i]:
% 50.45/50.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 50.45/50.65           ( ![C:$i]:
% 50.45/50.65             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 50.45/50.65               ( ( r1_tarski @ B @ C ) =>
% 50.45/50.65                 ( r1_tarski @
% 50.45/50.65                   ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 50.45/50.65  thf('24', plain,
% 50.45/50.65      (![X18 : $i, X19 : $i, X20 : $i]:
% 50.45/50.65         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 50.45/50.65          | ~ (r1_tarski @ X18 @ X20)
% 50.45/50.65          | (r1_tarski @ (k2_pre_topc @ X19 @ X18) @ (k2_pre_topc @ X19 @ X20))
% 50.45/50.65          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 50.45/50.65          | ~ (l1_pre_topc @ X19))),
% 50.45/50.65      inference('cnf', [status(esa)], [t49_pre_topc])).
% 50.45/50.65  thf('25', plain,
% 50.45/50.65      (![X0 : $i, X1 : $i]:
% 50.45/50.65         (~ (l1_pre_topc @ sk_A)
% 50.45/50.65          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 50.45/50.65          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ X0)) @ 
% 50.45/50.65             (k2_pre_topc @ sk_A @ X1))
% 50.45/50.65          | ~ (r1_tarski @ (k3_xboole_0 @ sk_C @ X0) @ X1))),
% 50.45/50.65      inference('sup-', [status(thm)], ['23', '24'])).
% 50.45/50.65  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 50.45/50.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.45/50.65  thf('27', plain,
% 50.45/50.65      (![X0 : $i, X1 : $i]:
% 50.45/50.65         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 50.45/50.65          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ X0)) @ 
% 50.45/50.65             (k2_pre_topc @ sk_A @ X1))
% 50.45/50.65          | ~ (r1_tarski @ (k3_xboole_0 @ sk_C @ X0) @ X1))),
% 50.45/50.65      inference('demod', [status(thm)], ['25', '26'])).
% 50.45/50.65  thf('28', plain,
% 50.45/50.65      (![X0 : $i]:
% 50.45/50.65         (~ (r1_tarski @ (k3_xboole_0 @ sk_C @ X0) @ sk_C)
% 50.45/50.65          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ X0)) @ 
% 50.45/50.65             (k2_pre_topc @ sk_A @ sk_C)))),
% 50.45/50.65      inference('sup-', [status(thm)], ['14', '27'])).
% 50.45/50.65  thf('29', plain,
% 50.45/50.65      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 50.45/50.65      inference('cnf', [status(esa)], [t17_xboole_1])).
% 50.45/50.65  thf('30', plain,
% 50.45/50.65      (![X0 : $i]:
% 50.45/50.65         (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ X0)) @ 
% 50.45/50.65          (k2_pre_topc @ sk_A @ sk_C))),
% 50.45/50.65      inference('demod', [status(thm)], ['28', '29'])).
% 50.45/50.65  thf('31', plain,
% 50.45/50.65      (![X0 : $i]:
% 50.45/50.65         (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_C)) @ 
% 50.45/50.65          (k2_pre_topc @ sk_A @ sk_C))),
% 50.45/50.65      inference('sup+', [status(thm)], ['13', '30'])).
% 50.45/50.65  thf('32', plain,
% 50.45/50.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.45/50.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.45/50.65  thf('33', plain,
% 50.45/50.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.45/50.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.45/50.65  thf('34', plain,
% 50.45/50.65      (![X13 : $i, X14 : $i]:
% 50.45/50.65         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 50.45/50.65      inference('cnf', [status(esa)], [t3_subset])).
% 50.45/50.65  thf('35', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 50.45/50.65      inference('sup-', [status(thm)], ['33', '34'])).
% 50.45/50.65  thf('36', plain,
% 50.45/50.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 50.45/50.65         ((r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 50.45/50.65      inference('sup-', [status(thm)], ['18', '19'])).
% 50.45/50.65  thf('37', plain,
% 50.45/50.65      (![X0 : $i]:
% 50.45/50.65         (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 50.45/50.65      inference('sup-', [status(thm)], ['35', '36'])).
% 50.45/50.65  thf('38', plain,
% 50.45/50.65      (![X13 : $i, X15 : $i]:
% 50.45/50.65         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 50.45/50.65      inference('cnf', [status(esa)], [t3_subset])).
% 50.45/50.65  thf('39', plain,
% 50.45/50.65      (![X0 : $i]:
% 50.45/50.65         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 50.45/50.65          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.45/50.65      inference('sup-', [status(thm)], ['37', '38'])).
% 50.45/50.65  thf('40', plain,
% 50.45/50.65      (![X18 : $i, X19 : $i, X20 : $i]:
% 50.45/50.65         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 50.45/50.65          | ~ (r1_tarski @ X18 @ X20)
% 50.45/50.65          | (r1_tarski @ (k2_pre_topc @ X19 @ X18) @ (k2_pre_topc @ X19 @ X20))
% 50.45/50.65          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 50.45/50.65          | ~ (l1_pre_topc @ X19))),
% 50.45/50.65      inference('cnf', [status(esa)], [t49_pre_topc])).
% 50.45/50.65  thf('41', plain,
% 50.45/50.65      (![X0 : $i, X1 : $i]:
% 50.45/50.65         (~ (l1_pre_topc @ sk_A)
% 50.45/50.65          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 50.45/50.65          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ X0)) @ 
% 50.45/50.65             (k2_pre_topc @ sk_A @ X1))
% 50.45/50.65          | ~ (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ X1))),
% 50.45/50.65      inference('sup-', [status(thm)], ['39', '40'])).
% 50.45/50.65  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 50.45/50.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.45/50.65  thf('43', plain,
% 50.45/50.65      (![X0 : $i, X1 : $i]:
% 50.45/50.65         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 50.45/50.65          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ X0)) @ 
% 50.45/50.65             (k2_pre_topc @ sk_A @ X1))
% 50.45/50.65          | ~ (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ X1))),
% 50.45/50.65      inference('demod', [status(thm)], ['41', '42'])).
% 50.45/50.65  thf('44', plain,
% 50.45/50.65      (![X0 : $i]:
% 50.45/50.65         (~ (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ sk_B)
% 50.45/50.65          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ X0)) @ 
% 50.45/50.65             (k2_pre_topc @ sk_A @ sk_B)))),
% 50.45/50.65      inference('sup-', [status(thm)], ['32', '43'])).
% 50.45/50.65  thf('45', plain,
% 50.45/50.65      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 50.45/50.65      inference('cnf', [status(esa)], [t17_xboole_1])).
% 50.45/50.65  thf('46', plain,
% 50.45/50.65      (![X0 : $i]:
% 50.45/50.65         (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ X0)) @ 
% 50.45/50.65          (k2_pre_topc @ sk_A @ sk_B))),
% 50.45/50.65      inference('demod', [status(thm)], ['44', '45'])).
% 50.45/50.65  thf(t19_xboole_1, axiom,
% 50.45/50.65    (![A:$i,B:$i,C:$i]:
% 50.45/50.65     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 50.45/50.65       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 50.45/50.65  thf('47', plain,
% 50.45/50.65      (![X4 : $i, X5 : $i, X6 : $i]:
% 50.45/50.65         (~ (r1_tarski @ X4 @ X5)
% 50.45/50.65          | ~ (r1_tarski @ X4 @ X6)
% 50.45/50.65          | (r1_tarski @ X4 @ (k3_xboole_0 @ X5 @ X6)))),
% 50.45/50.65      inference('cnf', [status(esa)], [t19_xboole_1])).
% 50.45/50.65  thf('48', plain,
% 50.45/50.65      (![X0 : $i, X1 : $i]:
% 50.45/50.65         ((r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ X0)) @ 
% 50.45/50.65           (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X1))
% 50.45/50.65          | ~ (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ X0)) @ 
% 50.45/50.65               X1))),
% 50.45/50.65      inference('sup-', [status(thm)], ['46', '47'])).
% 50.45/50.65  thf('49', plain,
% 50.45/50.65      ((r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 50.45/50.65        (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 50.45/50.65         (k2_pre_topc @ sk_A @ sk_C)))),
% 50.45/50.65      inference('sup-', [status(thm)], ['31', '48'])).
% 50.45/50.65  thf('50', plain, ($false), inference('demod', [status(thm)], ['12', '49'])).
% 50.45/50.65  
% 50.45/50.65  % SZS output end Refutation
% 50.45/50.65  
% 50.45/50.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
