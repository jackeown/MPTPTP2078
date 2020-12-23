%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lPDE3NieHr

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:39 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 120 expanded)
%              Number of leaves         :   25 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :  573 (1808 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(t20_compts_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v8_pre_topc @ A )
                  & ( v2_compts_1 @ B @ A )
                  & ( v2_compts_1 @ C @ A ) )
               => ( v2_compts_1 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v8_pre_topc @ A )
                    & ( v2_compts_1 @ B @ A )
                    & ( v2_compts_1 @ C @ A ) )
                 => ( v2_compts_1 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_compts_1])).

thf('0',plain,(
    ~ ( v2_compts_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
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
    ~ ( v2_compts_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc4_tops_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( v4_pre_topc @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ( v4_pre_topc @ C @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k3_xboole_0 @ B @ C ) @ A ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v4_pre_topc @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ~ ( v4_pre_topc @ X15 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v4_pre_topc @ ( k3_xboole_0 @ X13 @ X15 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc4_tops_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t16_compts_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v8_pre_topc @ A )
              & ( v2_compts_1 @ B @ A ) )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v4_pre_topc @ X16 @ X17 )
      | ~ ( v2_compts_1 @ X16 @ X17 )
      | ~ ( v8_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t16_compts_1])).

thf('13',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v2_compts_1 @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v2_compts_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9','10','18'])).

thf('20',plain,
    ( ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['5','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v4_pre_topc @ X16 @ X17 )
      | ~ ( v2_compts_1 @ X16 @ X17 )
      | ~ ( v8_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t16_compts_1])).

thf('23',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v2_compts_1 @ sk_C @ sk_A )
    | ( v4_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_compts_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v4_pre_topc @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['23','24','25','26','27'])).

thf('29',plain,(
    v4_pre_topc @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['20','28'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('32',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X5 @ X4 @ X6 ) @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('35',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( ( k7_subset_1 @ X8 @ X7 @ X9 )
        = ( k4_xboole_0 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['30','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t18_compts_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v2_compts_1 @ B @ A )
                  & ( r1_tarski @ C @ B )
                  & ( v4_pre_topc @ C @ A ) )
               => ( v2_compts_1 @ C @ A ) ) ) ) ) )).

thf('40',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v2_compts_1 @ X18 @ X19 )
      | ~ ( r1_tarski @ X20 @ X18 )
      | ~ ( v4_pre_topc @ X20 @ X19 )
      | ( v2_compts_1 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t18_compts_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_compts_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v2_compts_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ~ ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ( v2_compts_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','45'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ( v2_compts_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    v2_compts_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['29','48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['4','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lPDE3NieHr
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:51:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 73 iterations in 0.045s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.50  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.22/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.50  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.50  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.22/0.50  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.22/0.50  thf(t20_compts_1, conjecture,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50           ( ![C:$i]:
% 0.22/0.50             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50               ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) & 
% 0.22/0.50                   ( v2_compts_1 @ C @ A ) ) =>
% 0.22/0.50                 ( v2_compts_1 @
% 0.22/0.50                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i]:
% 0.22/0.50        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.50          ( ![B:$i]:
% 0.22/0.50            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50              ( ![C:$i]:
% 0.22/0.50                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50                  ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) & 
% 0.22/0.50                      ( v2_compts_1 @ C @ A ) ) =>
% 0.22/0.50                    ( v2_compts_1 @
% 0.22/0.50                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t20_compts_1])).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      (~ (v2_compts_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.22/0.50          sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(redefinition_k9_subset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.50       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.50         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 0.22/0.50          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.22/0.50           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.50  thf('4', plain, (~ (v2_compts_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.22/0.50      inference('demod', [status(thm)], ['0', '3'])).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(fc4_tops_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & ( v4_pre_topc @ B @ A ) & 
% 0.22/0.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.22/0.50         ( v4_pre_topc @ C @ A ) & 
% 0.22/0.50         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.50       ( v4_pre_topc @ ( k3_xboole_0 @ B @ C ) @ A ) ))).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.22/0.50          | ~ (v4_pre_topc @ X13 @ X14)
% 0.22/0.50          | ~ (l1_pre_topc @ X14)
% 0.22/0.50          | ~ (v2_pre_topc @ X14)
% 0.22/0.50          | ~ (v4_pre_topc @ X15 @ X14)
% 0.22/0.50          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.22/0.50          | (v4_pre_topc @ (k3_xboole_0 @ X13 @ X15) @ X14))),
% 0.22/0.50      inference('cnf', [status(esa)], [fc4_tops_1])).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((v4_pre_topc @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.22/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.50          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.22/0.50          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.50          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.50  thf('9', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t16_compts_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50           ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) ) =>
% 0.22/0.50             ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (![X16 : $i, X17 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.22/0.50          | (v4_pre_topc @ X16 @ X17)
% 0.22/0.50          | ~ (v2_compts_1 @ X16 @ X17)
% 0.22/0.50          | ~ (v8_pre_topc @ X17)
% 0.22/0.50          | ~ (l1_pre_topc @ X17)
% 0.22/0.50          | ~ (v2_pre_topc @ X17))),
% 0.22/0.50      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      ((~ (v2_pre_topc @ sk_A)
% 0.22/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.50        | ~ (v8_pre_topc @ sk_A)
% 0.22/0.50        | ~ (v2_compts_1 @ sk_B @ sk_A)
% 0.22/0.50        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.50  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('16', plain, ((v8_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('17', plain, ((v2_compts_1 @ sk_B @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('18', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.22/0.50      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.22/0.50  thf('19', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((v4_pre_topc @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.22/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.50          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['8', '9', '10', '18'])).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      ((~ (v4_pre_topc @ sk_C @ sk_A)
% 0.22/0.50        | (v4_pre_topc @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['5', '19'])).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('22', plain,
% 0.22/0.50      (![X16 : $i, X17 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.22/0.50          | (v4_pre_topc @ X16 @ X17)
% 0.22/0.50          | ~ (v2_compts_1 @ X16 @ X17)
% 0.22/0.50          | ~ (v8_pre_topc @ X17)
% 0.22/0.50          | ~ (l1_pre_topc @ X17)
% 0.22/0.50          | ~ (v2_pre_topc @ X17))),
% 0.22/0.51      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.22/0.51  thf('23', plain,
% 0.22/0.51      ((~ (v2_pre_topc @ sk_A)
% 0.22/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.51        | ~ (v8_pre_topc @ sk_A)
% 0.22/0.51        | ~ (v2_compts_1 @ sk_C @ sk_A)
% 0.22/0.51        | (v4_pre_topc @ sk_C @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.51  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('26', plain, ((v8_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('27', plain, ((v2_compts_1 @ sk_C @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('28', plain, ((v4_pre_topc @ sk_C @ sk_A)),
% 0.22/0.51      inference('demod', [status(thm)], ['23', '24', '25', '26', '27'])).
% 0.22/0.51  thf('29', plain, ((v4_pre_topc @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.22/0.51      inference('demod', [status(thm)], ['20', '28'])).
% 0.22/0.51  thf(t48_xboole_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.51  thf('30', plain,
% 0.22/0.51      (![X2 : $i, X3 : $i]:
% 0.22/0.51         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.22/0.51           = (k3_xboole_0 @ X2 @ X3))),
% 0.22/0.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.51  thf('31', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(dt_k7_subset_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.51       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.51  thf('32', plain,
% 0.22/0.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.22/0.51          | (m1_subset_1 @ (k7_subset_1 @ X5 @ X4 @ X6) @ (k1_zfmisc_1 @ X5)))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 0.22/0.51  thf('33', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (m1_subset_1 @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.22/0.51          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['31', '32'])).
% 0.22/0.51  thf('34', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(redefinition_k7_subset_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.51       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.22/0.51  thf('35', plain,
% 0.22/0.51      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.22/0.51          | ((k7_subset_1 @ X8 @ X7 @ X9) = (k4_xboole_0 @ X7 @ X9)))),
% 0.22/0.51      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.22/0.51  thf('36', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.22/0.51           = (k4_xboole_0 @ sk_B @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.51  thf('37', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 0.22/0.51          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('demod', [status(thm)], ['33', '36'])).
% 0.22/0.51  thf('38', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 0.22/0.51          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('sup+', [status(thm)], ['30', '37'])).
% 0.22/0.51  thf('39', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(t18_compts_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51           ( ![C:$i]:
% 0.22/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51               ( ( ( v2_compts_1 @ B @ A ) & ( r1_tarski @ C @ B ) & 
% 0.22/0.51                   ( v4_pre_topc @ C @ A ) ) =>
% 0.22/0.51                 ( v2_compts_1 @ C @ A ) ) ) ) ) ) ))).
% 0.22/0.51  thf('40', plain,
% 0.22/0.51      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.22/0.51          | ~ (v2_compts_1 @ X18 @ X19)
% 0.22/0.51          | ~ (r1_tarski @ X20 @ X18)
% 0.22/0.51          | ~ (v4_pre_topc @ X20 @ X19)
% 0.22/0.51          | (v2_compts_1 @ X20 @ X19)
% 0.22/0.51          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.22/0.51          | ~ (l1_pre_topc @ X19)
% 0.22/0.51          | ~ (v2_pre_topc @ X19))),
% 0.22/0.51      inference('cnf', [status(esa)], [t18_compts_1])).
% 0.22/0.51  thf('41', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (v2_pre_topc @ sk_A)
% 0.22/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.51          | (v2_compts_1 @ X0 @ sk_A)
% 0.22/0.51          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.22/0.51          | ~ (r1_tarski @ X0 @ sk_B)
% 0.22/0.51          | ~ (v2_compts_1 @ sk_B @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['39', '40'])).
% 0.22/0.51  thf('42', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('44', plain, ((v2_compts_1 @ sk_B @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('45', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.51          | (v2_compts_1 @ X0 @ sk_A)
% 0.22/0.51          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.22/0.51          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.22/0.51      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 0.22/0.51  thf('46', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ sk_B)
% 0.22/0.51          | ~ (v4_pre_topc @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.22/0.51          | (v2_compts_1 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['38', '45'])).
% 0.22/0.51  thf(t17_xboole_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.22/0.51  thf('47', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.22/0.51      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.22/0.51  thf('48', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (v4_pre_topc @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.22/0.51          | (v2_compts_1 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['46', '47'])).
% 0.22/0.51  thf('49', plain, ((v2_compts_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.22/0.51      inference('sup-', [status(thm)], ['29', '48'])).
% 0.22/0.51  thf('50', plain, ($false), inference('demod', [status(thm)], ['4', '49'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
