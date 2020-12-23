%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SRDQSt2FuX

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:14 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 114 expanded)
%              Number of leaves         :   28 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :  547 ( 917 expanded)
%              Number of equality atoms :   45 (  74 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t32_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( k7_subset_1 @ A @ B @ C )
              = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t32_subset_1])).

thf('0',plain,(
    ( k7_subset_1 @ sk_A @ sk_B @ sk_C_1 )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ( ( k7_subset_1 @ X25 @ X24 @ X26 )
        = ( k4_xboole_0 @ X24 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k6_subset_1 @ X22 @ X23 )
      = ( k4_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ( ( k7_subset_1 @ X25 @ X24 @ X26 )
        = ( k6_subset_1 @ X24 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ sk_A @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ( k6_subset_1 @ sk_B @ sk_C_1 )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X17 @ X18 )
        = ( k4_xboole_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('9',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k6_subset_1 @ X22 @ X23 )
      = ( k4_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('10',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X17 @ X18 )
        = ( k6_subset_1 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k6_subset_1 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('12',plain,(
    ! [X19: $i,X20: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('13',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k9_subset_1 @ X29 @ X27 @ X28 )
        = ( k3_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
      = ( k3_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('17',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ X15 )
      | ( r2_hidden @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('19',plain,(
    ! [X21: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('20',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['18','19'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('21',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( r1_tarski @ X12 @ X10 )
      | ( X11
       != ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('22',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_tarski @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['20','22'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('24',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('25',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['23','24'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('28',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k6_subset_1 @ X22 @ X23 )
      = ( k4_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k6_subset_1 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,
    ( ( k6_subset_1 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['25','30'])).

thf('32',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k6_subset_1 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('33',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ X15 )
      | ( r2_hidden @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('36',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X21: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('38',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_tarski @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('40',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('42',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('44',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X4 @ X6 ) @ ( k3_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ sk_B @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,
    ( ( k6_subset_1 @ sk_B @ sk_C_1 )
    = ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['33','49'])).

thf('51',plain,(
    ( k6_subset_1 @ sk_B @ sk_C_1 )
 != ( k6_subset_1 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['6','15','50'])).

thf('52',plain,(
    $false ),
    inference(simplify,[status(thm)],['51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SRDQSt2FuX
% 0.14/0.33  % Computer   : n021.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 16:36:34 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  % Running portfolio for 600 s
% 0.14/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.33  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.60/0.82  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.60/0.82  % Solved by: fo/fo7.sh
% 0.60/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.82  % done 615 iterations in 0.377s
% 0.60/0.82  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.60/0.82  % SZS output start Refutation
% 0.60/0.82  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.60/0.82  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.60/0.82  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.60/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.82  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.60/0.82  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.60/0.82  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.60/0.82  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.82  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.60/0.82  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.60/0.82  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.60/0.82  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.60/0.82  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.60/0.82  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.60/0.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.82  thf(t32_subset_1, conjecture,
% 0.60/0.82    (![A:$i,B:$i]:
% 0.60/0.82     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.60/0.82       ( ![C:$i]:
% 0.60/0.82         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.60/0.82           ( ( k7_subset_1 @ A @ B @ C ) =
% 0.60/0.82             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.60/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.82    (~( ![A:$i,B:$i]:
% 0.60/0.82        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.60/0.82          ( ![C:$i]:
% 0.60/0.82            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.60/0.82              ( ( k7_subset_1 @ A @ B @ C ) =
% 0.60/0.82                ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ) )),
% 0.60/0.82    inference('cnf.neg', [status(esa)], [t32_subset_1])).
% 0.60/0.82  thf('0', plain,
% 0.60/0.82      (((k7_subset_1 @ sk_A @ sk_B @ sk_C_1)
% 0.60/0.82         != (k9_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf('1', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf(redefinition_k7_subset_1, axiom,
% 0.60/0.82    (![A:$i,B:$i,C:$i]:
% 0.60/0.82     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.60/0.82       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.60/0.82  thf('2', plain,
% 0.60/0.82      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.60/0.82         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25))
% 0.60/0.82          | ((k7_subset_1 @ X25 @ X24 @ X26) = (k4_xboole_0 @ X24 @ X26)))),
% 0.60/0.82      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.60/0.82  thf(redefinition_k6_subset_1, axiom,
% 0.60/0.82    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.60/0.82  thf('3', plain,
% 0.60/0.82      (![X22 : $i, X23 : $i]:
% 0.60/0.82         ((k6_subset_1 @ X22 @ X23) = (k4_xboole_0 @ X22 @ X23))),
% 0.60/0.82      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.60/0.82  thf('4', plain,
% 0.60/0.82      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.60/0.82         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25))
% 0.60/0.82          | ((k7_subset_1 @ X25 @ X24 @ X26) = (k6_subset_1 @ X24 @ X26)))),
% 0.60/0.82      inference('demod', [status(thm)], ['2', '3'])).
% 0.60/0.82  thf('5', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         ((k7_subset_1 @ sk_A @ sk_B @ X0) = (k6_subset_1 @ sk_B @ X0))),
% 0.60/0.82      inference('sup-', [status(thm)], ['1', '4'])).
% 0.60/0.82  thf('6', plain,
% 0.60/0.82      (((k6_subset_1 @ sk_B @ sk_C_1)
% 0.60/0.82         != (k9_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.60/0.82      inference('demod', [status(thm)], ['0', '5'])).
% 0.60/0.82  thf('7', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf(d5_subset_1, axiom,
% 0.60/0.82    (![A:$i,B:$i]:
% 0.60/0.82     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.60/0.82       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.60/0.82  thf('8', plain,
% 0.60/0.82      (![X17 : $i, X18 : $i]:
% 0.60/0.82         (((k3_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))
% 0.60/0.82          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.60/0.82      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.60/0.82  thf('9', plain,
% 0.60/0.82      (![X22 : $i, X23 : $i]:
% 0.60/0.82         ((k6_subset_1 @ X22 @ X23) = (k4_xboole_0 @ X22 @ X23))),
% 0.60/0.82      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.60/0.82  thf('10', plain,
% 0.60/0.82      (![X17 : $i, X18 : $i]:
% 0.60/0.82         (((k3_subset_1 @ X17 @ X18) = (k6_subset_1 @ X17 @ X18))
% 0.60/0.82          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.60/0.82      inference('demod', [status(thm)], ['8', '9'])).
% 0.60/0.82  thf('11', plain,
% 0.60/0.82      (((k3_subset_1 @ sk_A @ sk_C_1) = (k6_subset_1 @ sk_A @ sk_C_1))),
% 0.60/0.82      inference('sup-', [status(thm)], ['7', '10'])).
% 0.60/0.82  thf(dt_k6_subset_1, axiom,
% 0.60/0.82    (![A:$i,B:$i]:
% 0.60/0.82     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.60/0.82  thf('12', plain,
% 0.60/0.82      (![X19 : $i, X20 : $i]:
% 0.60/0.82         (m1_subset_1 @ (k6_subset_1 @ X19 @ X20) @ (k1_zfmisc_1 @ X19))),
% 0.60/0.82      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.60/0.82  thf('13', plain,
% 0.60/0.82      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.60/0.82      inference('sup+', [status(thm)], ['11', '12'])).
% 0.60/0.82  thf(redefinition_k9_subset_1, axiom,
% 0.60/0.82    (![A:$i,B:$i,C:$i]:
% 0.60/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.60/0.82       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.60/0.82  thf('14', plain,
% 0.60/0.82      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.60/0.82         (((k9_subset_1 @ X29 @ X27 @ X28) = (k3_xboole_0 @ X27 @ X28))
% 0.60/0.82          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29)))),
% 0.60/0.82      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.60/0.82  thf('15', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         ((k9_subset_1 @ sk_A @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))
% 0.60/0.82           = (k3_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.60/0.82      inference('sup-', [status(thm)], ['13', '14'])).
% 0.60/0.82  thf('16', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf(d2_subset_1, axiom,
% 0.60/0.82    (![A:$i,B:$i]:
% 0.60/0.82     ( ( ( v1_xboole_0 @ A ) =>
% 0.60/0.82         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.60/0.82       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.60/0.82         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.60/0.82  thf('17', plain,
% 0.60/0.82      (![X14 : $i, X15 : $i]:
% 0.60/0.82         (~ (m1_subset_1 @ X14 @ X15)
% 0.60/0.82          | (r2_hidden @ X14 @ X15)
% 0.60/0.82          | (v1_xboole_0 @ X15))),
% 0.60/0.82      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.60/0.82  thf('18', plain,
% 0.60/0.82      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.60/0.82        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.60/0.82      inference('sup-', [status(thm)], ['16', '17'])).
% 0.60/0.82  thf(fc1_subset_1, axiom,
% 0.60/0.82    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.60/0.82  thf('19', plain, (![X21 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X21))),
% 0.60/0.82      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.60/0.82  thf('20', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.60/0.82      inference('clc', [status(thm)], ['18', '19'])).
% 0.60/0.82  thf(d1_zfmisc_1, axiom,
% 0.60/0.82    (![A:$i,B:$i]:
% 0.60/0.82     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.60/0.82       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.60/0.82  thf('21', plain,
% 0.60/0.82      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.60/0.82         (~ (r2_hidden @ X12 @ X11)
% 0.60/0.82          | (r1_tarski @ X12 @ X10)
% 0.60/0.82          | ((X11) != (k1_zfmisc_1 @ X10)))),
% 0.60/0.82      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.60/0.82  thf('22', plain,
% 0.60/0.82      (![X10 : $i, X12 : $i]:
% 0.60/0.82         ((r1_tarski @ X12 @ X10) | ~ (r2_hidden @ X12 @ (k1_zfmisc_1 @ X10)))),
% 0.60/0.82      inference('simplify', [status(thm)], ['21'])).
% 0.60/0.82  thf('23', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 0.60/0.82      inference('sup-', [status(thm)], ['20', '22'])).
% 0.60/0.82  thf(t28_xboole_1, axiom,
% 0.60/0.82    (![A:$i,B:$i]:
% 0.60/0.82     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.60/0.82  thf('24', plain,
% 0.60/0.82      (![X7 : $i, X8 : $i]:
% 0.60/0.82         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.60/0.82      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.60/0.82  thf('25', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 0.60/0.82      inference('sup-', [status(thm)], ['23', '24'])).
% 0.60/0.82  thf(commutativity_k3_xboole_0, axiom,
% 0.60/0.82    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.60/0.82  thf('26', plain,
% 0.60/0.82      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.60/0.82      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.60/0.82  thf(t100_xboole_1, axiom,
% 0.60/0.82    (![A:$i,B:$i]:
% 0.60/0.82     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.60/0.82  thf('27', plain,
% 0.60/0.82      (![X2 : $i, X3 : $i]:
% 0.60/0.82         ((k4_xboole_0 @ X2 @ X3)
% 0.60/0.82           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.60/0.82      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.60/0.82  thf('28', plain,
% 0.60/0.82      (![X22 : $i, X23 : $i]:
% 0.60/0.82         ((k6_subset_1 @ X22 @ X23) = (k4_xboole_0 @ X22 @ X23))),
% 0.60/0.82      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.60/0.82  thf('29', plain,
% 0.60/0.82      (![X2 : $i, X3 : $i]:
% 0.60/0.82         ((k6_subset_1 @ X2 @ X3)
% 0.60/0.82           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.60/0.82      inference('demod', [status(thm)], ['27', '28'])).
% 0.60/0.82  thf('30', plain,
% 0.60/0.82      (![X0 : $i, X1 : $i]:
% 0.60/0.82         ((k6_subset_1 @ X0 @ X1)
% 0.60/0.82           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.60/0.82      inference('sup+', [status(thm)], ['26', '29'])).
% 0.60/0.82  thf('31', plain,
% 0.60/0.82      (((k6_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 0.60/0.82      inference('sup+', [status(thm)], ['25', '30'])).
% 0.60/0.82  thf('32', plain,
% 0.60/0.82      (((k3_subset_1 @ sk_A @ sk_C_1) = (k6_subset_1 @ sk_A @ sk_C_1))),
% 0.60/0.82      inference('sup-', [status(thm)], ['7', '10'])).
% 0.60/0.82  thf('33', plain,
% 0.60/0.82      (((k3_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 0.60/0.82      inference('demod', [status(thm)], ['31', '32'])).
% 0.60/0.82  thf('34', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf('35', plain,
% 0.60/0.82      (![X14 : $i, X15 : $i]:
% 0.60/0.82         (~ (m1_subset_1 @ X14 @ X15)
% 0.60/0.82          | (r2_hidden @ X14 @ X15)
% 0.60/0.82          | (v1_xboole_0 @ X15))),
% 0.60/0.82      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.60/0.82  thf('36', plain,
% 0.60/0.82      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.60/0.82        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.60/0.82      inference('sup-', [status(thm)], ['34', '35'])).
% 0.60/0.82  thf('37', plain, (![X21 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X21))),
% 0.60/0.82      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.60/0.82  thf('38', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.60/0.82      inference('clc', [status(thm)], ['36', '37'])).
% 0.60/0.82  thf('39', plain,
% 0.60/0.82      (![X10 : $i, X12 : $i]:
% 0.60/0.82         ((r1_tarski @ X12 @ X10) | ~ (r2_hidden @ X12 @ (k1_zfmisc_1 @ X10)))),
% 0.60/0.82      inference('simplify', [status(thm)], ['21'])).
% 0.60/0.82  thf('40', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.60/0.82      inference('sup-', [status(thm)], ['38', '39'])).
% 0.60/0.82  thf('41', plain,
% 0.60/0.82      (![X7 : $i, X8 : $i]:
% 0.60/0.82         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.60/0.82      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.60/0.82  thf('42', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.60/0.82      inference('sup-', [status(thm)], ['40', '41'])).
% 0.60/0.82  thf('43', plain,
% 0.60/0.82      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.60/0.82      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.60/0.82  thf(t112_xboole_1, axiom,
% 0.60/0.82    (![A:$i,B:$i,C:$i]:
% 0.60/0.82     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 0.60/0.82       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 0.60/0.82  thf('44', plain,
% 0.60/0.82      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.60/0.82         ((k5_xboole_0 @ (k3_xboole_0 @ X4 @ X6) @ (k3_xboole_0 @ X5 @ X6))
% 0.60/0.82           = (k3_xboole_0 @ (k5_xboole_0 @ X4 @ X5) @ X6))),
% 0.60/0.82      inference('cnf', [status(esa)], [t112_xboole_1])).
% 0.60/0.82  thf('45', plain,
% 0.60/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.82         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X2 @ X1))
% 0.60/0.82           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X2) @ X1))),
% 0.60/0.82      inference('sup+', [status(thm)], ['43', '44'])).
% 0.60/0.82  thf('46', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         ((k5_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_B))
% 0.60/0.82           = (k3_xboole_0 @ (k5_xboole_0 @ sk_A @ X0) @ sk_B))),
% 0.60/0.82      inference('sup+', [status(thm)], ['42', '45'])).
% 0.60/0.82  thf('47', plain,
% 0.60/0.82      (![X0 : $i, X1 : $i]:
% 0.60/0.82         ((k6_subset_1 @ X0 @ X1)
% 0.60/0.82           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.60/0.82      inference('sup+', [status(thm)], ['26', '29'])).
% 0.60/0.82  thf('48', plain,
% 0.60/0.82      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.60/0.82      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.60/0.82  thf('49', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         ((k6_subset_1 @ sk_B @ X0)
% 0.60/0.82           = (k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ X0)))),
% 0.60/0.82      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.60/0.82  thf('50', plain,
% 0.60/0.82      (((k6_subset_1 @ sk_B @ sk_C_1)
% 0.60/0.82         = (k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.60/0.82      inference('sup+', [status(thm)], ['33', '49'])).
% 0.60/0.82  thf('51', plain,
% 0.60/0.82      (((k6_subset_1 @ sk_B @ sk_C_1) != (k6_subset_1 @ sk_B @ sk_C_1))),
% 0.60/0.82      inference('demod', [status(thm)], ['6', '15', '50'])).
% 0.60/0.82  thf('52', plain, ($false), inference('simplify', [status(thm)], ['51'])).
% 0.60/0.82  
% 0.60/0.82  % SZS output end Refutation
% 0.60/0.82  
% 0.60/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
