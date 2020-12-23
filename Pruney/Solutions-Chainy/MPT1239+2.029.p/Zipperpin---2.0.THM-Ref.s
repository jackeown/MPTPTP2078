%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sfB0C4VjpA

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:04 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 109 expanded)
%              Number of leaves         :   24 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :  616 (1487 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t50_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( r1_tarski @ ( k1_tops_1 @ A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( r1_tarski @ ( k1_tops_1 @ A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_tops_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( ( k7_subset_1 @ X17 @ X16 @ X18 )
        = ( k4_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('6',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( ( k7_subset_1 @ X17 @ X16 @ X18 )
        = ( k4_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['4','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X14 @ X13 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('18',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( r1_tarski @ X23 @ X25 )
      | ( r1_tarski @ ( k1_tops_1 @ X24 @ X23 ) @ ( k1_tops_1 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','22'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('27',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X22 @ X21 ) @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['28','29'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('31',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_xboole_0 @ X7 @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k4_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('36',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X22 @ X21 ) @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('40',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X6 )
      | ( r1_xboole_0 @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ X1 )
      | ~ ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r1_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['34','41'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('43',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X10 @ X12 )
      | ( r1_tarski @ X10 @ ( k4_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['25','44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['12','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sfB0C4VjpA
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:06:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.39/1.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.39/1.59  % Solved by: fo/fo7.sh
% 1.39/1.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.39/1.59  % done 2433 iterations in 1.128s
% 1.39/1.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.39/1.59  % SZS output start Refutation
% 1.39/1.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.39/1.59  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.39/1.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.39/1.59  thf(sk_B_type, type, sk_B: $i).
% 1.39/1.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.39/1.59  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.39/1.59  thf(sk_C_type, type, sk_C: $i).
% 1.39/1.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.39/1.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.39/1.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.39/1.59  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.39/1.59  thf(sk_A_type, type, sk_A: $i).
% 1.39/1.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.39/1.59  thf(t50_tops_1, conjecture,
% 1.39/1.59    (![A:$i]:
% 1.39/1.59     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.39/1.59       ( ![B:$i]:
% 1.39/1.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.39/1.59           ( ![C:$i]:
% 1.39/1.59             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.39/1.59               ( r1_tarski @
% 1.39/1.59                 ( k1_tops_1 @
% 1.39/1.59                   A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 1.39/1.59                 ( k7_subset_1 @
% 1.39/1.59                   ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 1.39/1.59                   ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 1.39/1.59  thf(zf_stmt_0, negated_conjecture,
% 1.39/1.59    (~( ![A:$i]:
% 1.39/1.59        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.39/1.59          ( ![B:$i]:
% 1.39/1.59            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.39/1.59              ( ![C:$i]:
% 1.39/1.59                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.39/1.59                  ( r1_tarski @
% 1.39/1.59                    ( k1_tops_1 @
% 1.39/1.59                      A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 1.39/1.59                    ( k7_subset_1 @
% 1.39/1.59                      ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 1.39/1.59                      ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 1.39/1.59    inference('cnf.neg', [status(esa)], [t50_tops_1])).
% 1.39/1.59  thf('0', plain,
% 1.39/1.59      (~ (r1_tarski @ 
% 1.39/1.59          (k1_tops_1 @ sk_A @ 
% 1.39/1.59           (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)) @ 
% 1.39/1.59          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.39/1.59           (k1_tops_1 @ sk_A @ sk_C)))),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf('1', plain,
% 1.39/1.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf(redefinition_k7_subset_1, axiom,
% 1.39/1.59    (![A:$i,B:$i,C:$i]:
% 1.39/1.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.39/1.59       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.39/1.59  thf('2', plain,
% 1.39/1.59      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.39/1.59         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 1.39/1.59          | ((k7_subset_1 @ X17 @ X16 @ X18) = (k4_xboole_0 @ X16 @ X18)))),
% 1.39/1.59      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.39/1.59  thf('3', plain,
% 1.39/1.59      (![X0 : $i]:
% 1.39/1.59         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.39/1.59           = (k4_xboole_0 @ sk_B @ X0))),
% 1.39/1.59      inference('sup-', [status(thm)], ['1', '2'])).
% 1.39/1.59  thf('4', plain,
% 1.39/1.59      (~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 1.39/1.59          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.39/1.59           (k1_tops_1 @ sk_A @ sk_C)))),
% 1.39/1.59      inference('demod', [status(thm)], ['0', '3'])).
% 1.39/1.59  thf('5', plain,
% 1.39/1.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf(dt_k1_tops_1, axiom,
% 1.39/1.59    (![A:$i,B:$i]:
% 1.39/1.59     ( ( ( l1_pre_topc @ A ) & 
% 1.39/1.59         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.39/1.59       ( m1_subset_1 @
% 1.39/1.59         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.39/1.59  thf('6', plain,
% 1.39/1.59      (![X19 : $i, X20 : $i]:
% 1.39/1.59         (~ (l1_pre_topc @ X19)
% 1.39/1.59          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 1.39/1.59          | (m1_subset_1 @ (k1_tops_1 @ X19 @ X20) @ 
% 1.39/1.59             (k1_zfmisc_1 @ (u1_struct_0 @ X19))))),
% 1.39/1.59      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 1.39/1.59  thf('7', plain,
% 1.39/1.59      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.39/1.59         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.39/1.59        | ~ (l1_pre_topc @ sk_A))),
% 1.39/1.59      inference('sup-', [status(thm)], ['5', '6'])).
% 1.39/1.59  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf('9', plain,
% 1.39/1.59      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.39/1.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.39/1.59      inference('demod', [status(thm)], ['7', '8'])).
% 1.39/1.59  thf('10', plain,
% 1.39/1.59      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.39/1.59         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 1.39/1.59          | ((k7_subset_1 @ X17 @ X16 @ X18) = (k4_xboole_0 @ X16 @ X18)))),
% 1.39/1.59      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.39/1.59  thf('11', plain,
% 1.39/1.59      (![X0 : $i]:
% 1.39/1.59         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 1.39/1.59           = (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 1.39/1.59      inference('sup-', [status(thm)], ['9', '10'])).
% 1.39/1.59  thf('12', plain,
% 1.39/1.59      (~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 1.39/1.59          (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 1.39/1.59      inference('demod', [status(thm)], ['4', '11'])).
% 1.39/1.59  thf('13', plain,
% 1.39/1.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf('14', plain,
% 1.39/1.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf(dt_k7_subset_1, axiom,
% 1.39/1.59    (![A:$i,B:$i,C:$i]:
% 1.39/1.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.39/1.59       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.39/1.59  thf('15', plain,
% 1.39/1.59      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.39/1.59         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 1.39/1.59          | (m1_subset_1 @ (k7_subset_1 @ X14 @ X13 @ X15) @ 
% 1.39/1.59             (k1_zfmisc_1 @ X14)))),
% 1.39/1.59      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 1.39/1.59  thf('16', plain,
% 1.39/1.59      (![X0 : $i]:
% 1.39/1.59         (m1_subset_1 @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 1.39/1.59          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.39/1.59      inference('sup-', [status(thm)], ['14', '15'])).
% 1.39/1.59  thf('17', plain,
% 1.39/1.59      (![X0 : $i]:
% 1.39/1.59         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.39/1.59           = (k4_xboole_0 @ sk_B @ X0))),
% 1.39/1.59      inference('sup-', [status(thm)], ['1', '2'])).
% 1.39/1.59  thf('18', plain,
% 1.39/1.59      (![X0 : $i]:
% 1.39/1.59         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 1.39/1.59          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.39/1.59      inference('demod', [status(thm)], ['16', '17'])).
% 1.39/1.59  thf(t48_tops_1, axiom,
% 1.39/1.59    (![A:$i]:
% 1.39/1.59     ( ( l1_pre_topc @ A ) =>
% 1.39/1.59       ( ![B:$i]:
% 1.39/1.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.39/1.59           ( ![C:$i]:
% 1.39/1.59             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.39/1.59               ( ( r1_tarski @ B @ C ) =>
% 1.39/1.59                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 1.39/1.59  thf('19', plain,
% 1.39/1.59      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.39/1.59         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.39/1.59          | ~ (r1_tarski @ X23 @ X25)
% 1.39/1.59          | (r1_tarski @ (k1_tops_1 @ X24 @ X23) @ (k1_tops_1 @ X24 @ X25))
% 1.39/1.59          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.39/1.59          | ~ (l1_pre_topc @ X24))),
% 1.39/1.59      inference('cnf', [status(esa)], [t48_tops_1])).
% 1.39/1.59  thf('20', plain,
% 1.39/1.59      (![X0 : $i, X1 : $i]:
% 1.39/1.59         (~ (l1_pre_topc @ sk_A)
% 1.39/1.59          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.39/1.59          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 1.39/1.59             (k1_tops_1 @ sk_A @ X1))
% 1.39/1.59          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1))),
% 1.39/1.59      inference('sup-', [status(thm)], ['18', '19'])).
% 1.39/1.59  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf('22', plain,
% 1.39/1.59      (![X0 : $i, X1 : $i]:
% 1.39/1.59         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.39/1.59          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 1.39/1.59             (k1_tops_1 @ sk_A @ X1))
% 1.39/1.59          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1))),
% 1.39/1.59      inference('demod', [status(thm)], ['20', '21'])).
% 1.39/1.59  thf('23', plain,
% 1.39/1.59      (![X0 : $i]:
% 1.39/1.59         (~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ sk_B)
% 1.39/1.59          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 1.39/1.59             (k1_tops_1 @ sk_A @ sk_B)))),
% 1.39/1.59      inference('sup-', [status(thm)], ['13', '22'])).
% 1.39/1.59  thf(t36_xboole_1, axiom,
% 1.39/1.59    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.39/1.59  thf('24', plain,
% 1.39/1.59      (![X2 : $i, X3 : $i]: (r1_tarski @ (k4_xboole_0 @ X2 @ X3) @ X2)),
% 1.39/1.59      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.39/1.59  thf('25', plain,
% 1.39/1.59      (![X0 : $i]:
% 1.39/1.59         (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 1.39/1.59          (k1_tops_1 @ sk_A @ sk_B))),
% 1.39/1.59      inference('demod', [status(thm)], ['23', '24'])).
% 1.39/1.59  thf('26', plain,
% 1.39/1.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf(t44_tops_1, axiom,
% 1.39/1.59    (![A:$i]:
% 1.39/1.59     ( ( l1_pre_topc @ A ) =>
% 1.39/1.59       ( ![B:$i]:
% 1.39/1.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.39/1.59           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 1.39/1.59  thf('27', plain,
% 1.39/1.59      (![X21 : $i, X22 : $i]:
% 1.39/1.59         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.39/1.59          | (r1_tarski @ (k1_tops_1 @ X22 @ X21) @ X21)
% 1.39/1.59          | ~ (l1_pre_topc @ X22))),
% 1.39/1.59      inference('cnf', [status(esa)], [t44_tops_1])).
% 1.39/1.59  thf('28', plain,
% 1.39/1.59      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 1.39/1.59      inference('sup-', [status(thm)], ['26', '27'])).
% 1.39/1.59  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf('30', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 1.39/1.59      inference('demod', [status(thm)], ['28', '29'])).
% 1.39/1.59  thf(t85_xboole_1, axiom,
% 1.39/1.59    (![A:$i,B:$i,C:$i]:
% 1.39/1.59     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 1.39/1.59  thf('31', plain,
% 1.39/1.59      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.39/1.59         (~ (r1_tarski @ X7 @ X8)
% 1.39/1.59          | (r1_xboole_0 @ X7 @ (k4_xboole_0 @ X9 @ X8)))),
% 1.39/1.59      inference('cnf', [status(esa)], [t85_xboole_1])).
% 1.39/1.59  thf('32', plain,
% 1.39/1.59      (![X0 : $i]:
% 1.39/1.59         (r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C) @ (k4_xboole_0 @ X0 @ sk_C))),
% 1.39/1.59      inference('sup-', [status(thm)], ['30', '31'])).
% 1.39/1.59  thf(symmetry_r1_xboole_0, axiom,
% 1.39/1.59    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.39/1.59  thf('33', plain,
% 1.39/1.59      (![X0 : $i, X1 : $i]:
% 1.39/1.59         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.39/1.59      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.39/1.59  thf('34', plain,
% 1.39/1.59      (![X0 : $i]:
% 1.39/1.59         (r1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ (k1_tops_1 @ sk_A @ sk_C))),
% 1.39/1.59      inference('sup-', [status(thm)], ['32', '33'])).
% 1.39/1.59  thf('35', plain,
% 1.39/1.59      (![X0 : $i]:
% 1.39/1.59         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 1.39/1.59          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.39/1.59      inference('demod', [status(thm)], ['16', '17'])).
% 1.39/1.59  thf('36', plain,
% 1.39/1.59      (![X21 : $i, X22 : $i]:
% 1.39/1.59         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.39/1.59          | (r1_tarski @ (k1_tops_1 @ X22 @ X21) @ X21)
% 1.39/1.59          | ~ (l1_pre_topc @ X22))),
% 1.39/1.59      inference('cnf', [status(esa)], [t44_tops_1])).
% 1.39/1.59  thf('37', plain,
% 1.39/1.59      (![X0 : $i]:
% 1.39/1.59         (~ (l1_pre_topc @ sk_A)
% 1.39/1.59          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 1.39/1.59             (k4_xboole_0 @ sk_B @ X0)))),
% 1.39/1.59      inference('sup-', [status(thm)], ['35', '36'])).
% 1.39/1.59  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf('39', plain,
% 1.39/1.59      (![X0 : $i]:
% 1.39/1.59         (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 1.39/1.59          (k4_xboole_0 @ sk_B @ X0))),
% 1.39/1.59      inference('demod', [status(thm)], ['37', '38'])).
% 1.39/1.59  thf(t63_xboole_1, axiom,
% 1.39/1.59    (![A:$i,B:$i,C:$i]:
% 1.39/1.59     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 1.39/1.59       ( r1_xboole_0 @ A @ C ) ))).
% 1.39/1.59  thf('40', plain,
% 1.39/1.59      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.39/1.59         (~ (r1_tarski @ X4 @ X5)
% 1.39/1.59          | ~ (r1_xboole_0 @ X5 @ X6)
% 1.39/1.59          | (r1_xboole_0 @ X4 @ X6))),
% 1.39/1.59      inference('cnf', [status(esa)], [t63_xboole_1])).
% 1.39/1.59  thf('41', plain,
% 1.39/1.59      (![X0 : $i, X1 : $i]:
% 1.39/1.59         ((r1_xboole_0 @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ X1)
% 1.39/1.59          | ~ (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ X0) @ X1))),
% 1.39/1.59      inference('sup-', [status(thm)], ['39', '40'])).
% 1.39/1.59  thf('42', plain,
% 1.39/1.59      ((r1_xboole_0 @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 1.39/1.59        (k1_tops_1 @ sk_A @ sk_C))),
% 1.39/1.59      inference('sup-', [status(thm)], ['34', '41'])).
% 1.39/1.59  thf(t86_xboole_1, axiom,
% 1.39/1.59    (![A:$i,B:$i,C:$i]:
% 1.39/1.59     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 1.39/1.59       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 1.39/1.59  thf('43', plain,
% 1.39/1.59      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.39/1.59         (~ (r1_tarski @ X10 @ X11)
% 1.39/1.59          | ~ (r1_xboole_0 @ X10 @ X12)
% 1.39/1.59          | (r1_tarski @ X10 @ (k4_xboole_0 @ X11 @ X12)))),
% 1.39/1.59      inference('cnf', [status(esa)], [t86_xboole_1])).
% 1.39/1.59  thf('44', plain,
% 1.39/1.59      (![X0 : $i]:
% 1.39/1.59         ((r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 1.39/1.59           (k4_xboole_0 @ X0 @ (k1_tops_1 @ sk_A @ sk_C)))
% 1.39/1.59          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 1.39/1.59               X0))),
% 1.39/1.59      inference('sup-', [status(thm)], ['42', '43'])).
% 1.39/1.59  thf('45', plain,
% 1.39/1.59      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 1.39/1.59        (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 1.39/1.59      inference('sup-', [status(thm)], ['25', '44'])).
% 1.39/1.59  thf('46', plain, ($false), inference('demod', [status(thm)], ['12', '45'])).
% 1.39/1.59  
% 1.39/1.59  % SZS output end Refutation
% 1.39/1.59  
% 1.39/1.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
