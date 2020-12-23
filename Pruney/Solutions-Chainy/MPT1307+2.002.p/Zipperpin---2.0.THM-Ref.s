%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jt16kKbCDP

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:26 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 124 expanded)
%              Number of leaves         :   25 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :  586 (1411 expanded)
%              Number of equality atoms :   14 (  28 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_tops_2_type,type,(
    v2_tops_2: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t25_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( v2_tops_2 @ B @ A )
               => ( v2_tops_2 @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ( ( v2_tops_2 @ B @ A )
                 => ( v2_tops_2 @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_tops_2])).

thf('0',plain,(
    ~ ( v2_tops_2 @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( ( k7_subset_1 @ X7 @ X6 @ X8 )
        = ( k4_xboole_0 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v2_tops_2 @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X1 @ X0 @ X2 ) @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('9',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(d2_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v2_tops_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r2_hidden @ C @ B )
                 => ( v4_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) )
      | ( r2_hidden @ ( sk_C @ X17 @ X18 ) @ X17 )
      | ( v2_tops_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('14',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ ( k8_setfam_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_setfam_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_setfam_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( ( B != k1_xboole_0 )
         => ( ( k8_setfam_1 @ A @ B )
            = ( k6_setfam_1 @ A @ B ) ) )
        & ( ( B = k1_xboole_0 )
         => ( ( k8_setfam_1 @ A @ B )
            = A ) ) ) ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X11 @ X10 )
        = X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('18',plain,(
    ! [X11: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) )
      | ( ( k8_setfam_1 @ X11 @ k1_xboole_0 )
        = X11 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('20',plain,(
    ! [X11: $i] :
      ( ( k8_setfam_1 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X1 @ X0 @ X2 ) @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ X0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('24',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k7_subset_1 @ X0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','20'])).

thf('27',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( ( k7_subset_1 @ X7 @ X6 @ X8 )
        = ( k4_xboole_0 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( v2_tops_2 @ X17 @ X18 )
      | ~ ( r2_hidden @ X19 @ X17 )
      | ( v4_pre_topc @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_2])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v2_tops_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v2_tops_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('38',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( m1_subset_1 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v2_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ( v4_pre_topc @ ( sk_C @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('43',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( v4_pre_topc @ ( sk_C @ X17 @ X18 ) @ X18 )
      | ( v2_tops_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_2])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ ( sk_C @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ ( sk_C @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( v2_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ),
    inference(clc,[status(thm)],['41','46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['4','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jt16kKbCDP
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:57:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.50/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.50/0.70  % Solved by: fo/fo7.sh
% 0.50/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.70  % done 362 iterations in 0.229s
% 0.50/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.50/0.70  % SZS output start Refutation
% 0.50/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.70  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.50/0.70  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 0.50/0.70  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.50/0.70  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.50/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.50/0.70  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.50/0.70  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.50/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.50/0.70  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.50/0.70  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.50/0.70  thf(v2_tops_2_type, type, v2_tops_2: $i > $i > $o).
% 0.50/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.50/0.70  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.50/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.50/0.70  thf(t25_tops_2, conjecture,
% 0.50/0.70    (![A:$i]:
% 0.50/0.70     ( ( l1_pre_topc @ A ) =>
% 0.50/0.70       ( ![B:$i]:
% 0.50/0.70         ( ( m1_subset_1 @
% 0.50/0.70             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.50/0.70           ( ![C:$i]:
% 0.50/0.70             ( ( m1_subset_1 @
% 0.50/0.70                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.50/0.70               ( ( v2_tops_2 @ B @ A ) =>
% 0.50/0.70                 ( v2_tops_2 @
% 0.50/0.70                   ( k7_subset_1 @
% 0.50/0.70                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 0.50/0.70                   A ) ) ) ) ) ) ))).
% 0.50/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.70    (~( ![A:$i]:
% 0.50/0.70        ( ( l1_pre_topc @ A ) =>
% 0.50/0.70          ( ![B:$i]:
% 0.50/0.70            ( ( m1_subset_1 @
% 0.50/0.70                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.50/0.70              ( ![C:$i]:
% 0.50/0.70                ( ( m1_subset_1 @
% 0.50/0.70                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.50/0.70                  ( ( v2_tops_2 @ B @ A ) =>
% 0.50/0.70                    ( v2_tops_2 @
% 0.50/0.70                      ( k7_subset_1 @
% 0.50/0.70                        ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 0.50/0.70                      A ) ) ) ) ) ) ) )),
% 0.50/0.70    inference('cnf.neg', [status(esa)], [t25_tops_2])).
% 0.50/0.70  thf('0', plain,
% 0.50/0.70      (~ (v2_tops_2 @ 
% 0.50/0.70          (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C_1) @ 
% 0.50/0.70          sk_A)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('1', plain,
% 0.50/0.70      ((m1_subset_1 @ sk_B @ 
% 0.50/0.70        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf(redefinition_k7_subset_1, axiom,
% 0.50/0.70    (![A:$i,B:$i,C:$i]:
% 0.50/0.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.70       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.50/0.70  thf('2', plain,
% 0.50/0.70      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.50/0.70         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.50/0.70          | ((k7_subset_1 @ X7 @ X6 @ X8) = (k4_xboole_0 @ X6 @ X8)))),
% 0.50/0.70      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.50/0.70  thf('3', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         ((k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0)
% 0.50/0.70           = (k4_xboole_0 @ sk_B @ X0))),
% 0.50/0.70      inference('sup-', [status(thm)], ['1', '2'])).
% 0.50/0.70  thf('4', plain, (~ (v2_tops_2 @ (k4_xboole_0 @ sk_B @ sk_C_1) @ sk_A)),
% 0.50/0.70      inference('demod', [status(thm)], ['0', '3'])).
% 0.50/0.70  thf('5', plain,
% 0.50/0.70      ((m1_subset_1 @ sk_B @ 
% 0.50/0.70        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf(dt_k7_subset_1, axiom,
% 0.50/0.70    (![A:$i,B:$i,C:$i]:
% 0.50/0.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.70       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.50/0.70  thf('6', plain,
% 0.50/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.70         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.50/0.70          | (m1_subset_1 @ (k7_subset_1 @ X1 @ X0 @ X2) @ (k1_zfmisc_1 @ X1)))),
% 0.50/0.70      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 0.50/0.70  thf('7', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         (m1_subset_1 @ 
% 0.50/0.70          (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0) @ 
% 0.50/0.70          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.50/0.70      inference('sup-', [status(thm)], ['5', '6'])).
% 0.50/0.70  thf('8', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         ((k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0)
% 0.50/0.70           = (k4_xboole_0 @ sk_B @ X0))),
% 0.50/0.70      inference('sup-', [status(thm)], ['1', '2'])).
% 0.50/0.70  thf('9', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 0.50/0.70          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.50/0.70      inference('demod', [status(thm)], ['7', '8'])).
% 0.50/0.70  thf(d2_tops_2, axiom,
% 0.50/0.70    (![A:$i]:
% 0.50/0.70     ( ( l1_pre_topc @ A ) =>
% 0.50/0.70       ( ![B:$i]:
% 0.50/0.70         ( ( m1_subset_1 @
% 0.50/0.70             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.50/0.70           ( ( v2_tops_2 @ B @ A ) <=>
% 0.50/0.70             ( ![C:$i]:
% 0.50/0.70               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.70                 ( ( r2_hidden @ C @ B ) => ( v4_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.50/0.70  thf('10', plain,
% 0.50/0.70      (![X17 : $i, X18 : $i]:
% 0.50/0.70         (~ (m1_subset_1 @ X17 @ 
% 0.50/0.70             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18))))
% 0.50/0.70          | (r2_hidden @ (sk_C @ X17 @ X18) @ X17)
% 0.50/0.70          | (v2_tops_2 @ X17 @ X18)
% 0.50/0.70          | ~ (l1_pre_topc @ X18))),
% 0.50/0.70      inference('cnf', [status(esa)], [d2_tops_2])).
% 0.50/0.70  thf('11', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         (~ (l1_pre_topc @ sk_A)
% 0.50/0.70          | (v2_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.50/0.70          | (r2_hidden @ (sk_C @ (k4_xboole_0 @ sk_B @ X0) @ sk_A) @ 
% 0.50/0.70             (k4_xboole_0 @ sk_B @ X0)))),
% 0.50/0.70      inference('sup-', [status(thm)], ['9', '10'])).
% 0.50/0.70  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('13', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         ((v2_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.50/0.70          | (r2_hidden @ (sk_C @ (k4_xboole_0 @ sk_B @ X0) @ sk_A) @ 
% 0.50/0.70             (k4_xboole_0 @ sk_B @ X0)))),
% 0.50/0.70      inference('demod', [status(thm)], ['11', '12'])).
% 0.50/0.70  thf(t4_subset_1, axiom,
% 0.50/0.70    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.50/0.70  thf('14', plain,
% 0.50/0.70      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.50/0.70      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.50/0.70  thf(dt_k8_setfam_1, axiom,
% 0.50/0.70    (![A:$i,B:$i]:
% 0.50/0.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.50/0.70       ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.50/0.70  thf('15', plain,
% 0.50/0.70      (![X12 : $i, X13 : $i]:
% 0.50/0.70         ((m1_subset_1 @ (k8_setfam_1 @ X12 @ X13) @ (k1_zfmisc_1 @ X12))
% 0.50/0.70          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X12))))),
% 0.50/0.70      inference('cnf', [status(esa)], [dt_k8_setfam_1])).
% 0.50/0.70  thf('16', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         (m1_subset_1 @ (k8_setfam_1 @ X0 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.50/0.70      inference('sup-', [status(thm)], ['14', '15'])).
% 0.50/0.70  thf(d10_setfam_1, axiom,
% 0.50/0.70    (![A:$i,B:$i]:
% 0.50/0.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.50/0.70       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.50/0.70           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 0.50/0.70         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 0.50/0.70  thf('17', plain,
% 0.50/0.70      (![X10 : $i, X11 : $i]:
% 0.50/0.70         (((X10) != (k1_xboole_0))
% 0.50/0.70          | ((k8_setfam_1 @ X11 @ X10) = (X11))
% 0.50/0.70          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11))))),
% 0.50/0.70      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.50/0.70  thf('18', plain,
% 0.50/0.70      (![X11 : $i]:
% 0.50/0.70         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11)))
% 0.50/0.70          | ((k8_setfam_1 @ X11 @ k1_xboole_0) = (X11)))),
% 0.50/0.70      inference('simplify', [status(thm)], ['17'])).
% 0.50/0.70  thf('19', plain,
% 0.50/0.70      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.50/0.70      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.50/0.70  thf('20', plain, (![X11 : $i]: ((k8_setfam_1 @ X11 @ k1_xboole_0) = (X11))),
% 0.50/0.70      inference('demod', [status(thm)], ['18', '19'])).
% 0.50/0.70  thf('21', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.50/0.70      inference('demod', [status(thm)], ['16', '20'])).
% 0.50/0.70  thf('22', plain,
% 0.50/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.70         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.50/0.70          | (m1_subset_1 @ (k7_subset_1 @ X1 @ X0 @ X2) @ (k1_zfmisc_1 @ X1)))),
% 0.50/0.70      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 0.50/0.70  thf('23', plain,
% 0.50/0.70      (![X0 : $i, X1 : $i]:
% 0.50/0.70         (m1_subset_1 @ (k7_subset_1 @ X0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.50/0.70      inference('sup-', [status(thm)], ['21', '22'])).
% 0.50/0.70  thf(l3_subset_1, axiom,
% 0.50/0.70    (![A:$i,B:$i]:
% 0.50/0.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.70       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.50/0.70  thf('24', plain,
% 0.50/0.70      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.50/0.70         (~ (r2_hidden @ X3 @ X4)
% 0.50/0.70          | (r2_hidden @ X3 @ X5)
% 0.50/0.70          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.50/0.70      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.50/0.70  thf('25', plain,
% 0.50/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.70         ((r2_hidden @ X2 @ X0)
% 0.50/0.70          | ~ (r2_hidden @ X2 @ (k7_subset_1 @ X0 @ X0 @ X1)))),
% 0.50/0.70      inference('sup-', [status(thm)], ['23', '24'])).
% 0.50/0.70  thf('26', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.50/0.70      inference('demod', [status(thm)], ['16', '20'])).
% 0.50/0.70  thf('27', plain,
% 0.50/0.70      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.50/0.70         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.50/0.70          | ((k7_subset_1 @ X7 @ X6 @ X8) = (k4_xboole_0 @ X6 @ X8)))),
% 0.50/0.70      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.50/0.70  thf('28', plain,
% 0.50/0.70      (![X0 : $i, X1 : $i]:
% 0.50/0.70         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 0.50/0.70      inference('sup-', [status(thm)], ['26', '27'])).
% 0.50/0.70  thf('29', plain,
% 0.50/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.70         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.50/0.70      inference('demod', [status(thm)], ['25', '28'])).
% 0.50/0.70  thf('30', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         ((v2_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.50/0.70          | (r2_hidden @ (sk_C @ (k4_xboole_0 @ sk_B @ X0) @ sk_A) @ sk_B))),
% 0.50/0.70      inference('sup-', [status(thm)], ['13', '29'])).
% 0.50/0.70  thf('31', plain,
% 0.50/0.70      ((m1_subset_1 @ sk_B @ 
% 0.50/0.70        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('32', plain,
% 0.50/0.70      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.50/0.70         (~ (m1_subset_1 @ X17 @ 
% 0.50/0.70             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18))))
% 0.50/0.70          | ~ (v2_tops_2 @ X17 @ X18)
% 0.50/0.70          | ~ (r2_hidden @ X19 @ X17)
% 0.50/0.70          | (v4_pre_topc @ X19 @ X18)
% 0.50/0.70          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.50/0.70          | ~ (l1_pre_topc @ X18))),
% 0.50/0.70      inference('cnf', [status(esa)], [d2_tops_2])).
% 0.50/0.70  thf('33', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         (~ (l1_pre_topc @ sk_A)
% 0.50/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.70          | (v4_pre_topc @ X0 @ sk_A)
% 0.50/0.70          | ~ (r2_hidden @ X0 @ sk_B)
% 0.50/0.70          | ~ (v2_tops_2 @ sk_B @ sk_A))),
% 0.50/0.70      inference('sup-', [status(thm)], ['31', '32'])).
% 0.50/0.70  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('35', plain, ((v2_tops_2 @ sk_B @ sk_A)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('36', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.70          | (v4_pre_topc @ X0 @ sk_A)
% 0.50/0.70          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.50/0.70      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.50/0.70  thf('37', plain,
% 0.50/0.70      ((m1_subset_1 @ sk_B @ 
% 0.50/0.70        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf(t4_subset, axiom,
% 0.50/0.70    (![A:$i,B:$i,C:$i]:
% 0.50/0.70     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.50/0.70       ( m1_subset_1 @ A @ C ) ))).
% 0.50/0.70  thf('38', plain,
% 0.50/0.70      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.50/0.70         (~ (r2_hidden @ X14 @ X15)
% 0.50/0.70          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.50/0.70          | (m1_subset_1 @ X14 @ X16))),
% 0.50/0.70      inference('cnf', [status(esa)], [t4_subset])).
% 0.50/0.70  thf('39', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.70          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.50/0.70      inference('sup-', [status(thm)], ['37', '38'])).
% 0.50/0.70  thf('40', plain,
% 0.50/0.70      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_B) | (v4_pre_topc @ X0 @ sk_A))),
% 0.50/0.70      inference('clc', [status(thm)], ['36', '39'])).
% 0.50/0.70  thf('41', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         ((v2_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.50/0.70          | (v4_pre_topc @ (sk_C @ (k4_xboole_0 @ sk_B @ X0) @ sk_A) @ sk_A))),
% 0.50/0.70      inference('sup-', [status(thm)], ['30', '40'])).
% 0.50/0.70  thf('42', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 0.50/0.70          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.50/0.70      inference('demod', [status(thm)], ['7', '8'])).
% 0.50/0.70  thf('43', plain,
% 0.50/0.70      (![X17 : $i, X18 : $i]:
% 0.50/0.70         (~ (m1_subset_1 @ X17 @ 
% 0.50/0.70             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18))))
% 0.50/0.70          | ~ (v4_pre_topc @ (sk_C @ X17 @ X18) @ X18)
% 0.50/0.70          | (v2_tops_2 @ X17 @ X18)
% 0.50/0.70          | ~ (l1_pre_topc @ X18))),
% 0.50/0.70      inference('cnf', [status(esa)], [d2_tops_2])).
% 0.50/0.70  thf('44', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         (~ (l1_pre_topc @ sk_A)
% 0.50/0.70          | (v2_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.50/0.70          | ~ (v4_pre_topc @ (sk_C @ (k4_xboole_0 @ sk_B @ X0) @ sk_A) @ sk_A))),
% 0.50/0.70      inference('sup-', [status(thm)], ['42', '43'])).
% 0.50/0.70  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('46', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         ((v2_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.50/0.70          | ~ (v4_pre_topc @ (sk_C @ (k4_xboole_0 @ sk_B @ X0) @ sk_A) @ sk_A))),
% 0.50/0.70      inference('demod', [status(thm)], ['44', '45'])).
% 0.50/0.70  thf('47', plain,
% 0.50/0.70      (![X0 : $i]: (v2_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)),
% 0.50/0.70      inference('clc', [status(thm)], ['41', '46'])).
% 0.50/0.70  thf('48', plain, ($false), inference('demod', [status(thm)], ['4', '47'])).
% 0.50/0.70  
% 0.50/0.70  % SZS output end Refutation
% 0.50/0.70  
% 0.50/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
