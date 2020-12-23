%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BVJjnjvRej

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:24 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 113 expanded)
%              Number of leaves         :   26 (  44 expanded)
%              Depth                    :   16
%              Number of atoms          :  529 ( 894 expanded)
%              Number of equality atoms :   23 (  43 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t57_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ A )
         => ! [D: $i] :
              ( ( m1_subset_1 @ D @ A )
             => ( ( A != k1_xboole_0 )
               => ( m1_subset_1 @ ( k1_enumset1 @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ A )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ A )
           => ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( A != k1_xboole_0 )
                 => ( m1_subset_1 @ ( k1_enumset1 @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t57_subset_1])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( k1_enumset1 @ sk_B @ sk_C_2 @ sk_D ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ A )
     => ( ( A != k1_xboole_0 )
       => ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X40: $i,X41: $i] :
      ( ( X40 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X41 @ X40 )
      | ( m1_subset_1 @ ( k1_tarski @ X41 ) @ ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t55_subset_1])).

thf('3',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['3','4'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('6',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ X34 )
      | ( r2_hidden @ X33 @ X34 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('7',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X36: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('9',plain,(
    r2_hidden @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('10',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X24 @ X23 )
      | ( r1_tarski @ X24 @ X22 )
      | ( X23
       != ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('11',plain,(
    ! [X22: $i,X24: $i] :
      ( ( r1_tarski @ X24 @ X22 )
      | ~ ( r2_hidden @ X24 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    r1_tarski @ ( k1_tarski @ sk_D ) @ sk_A ),
    inference('sup-',[status(thm)],['9','11'])).

thf(t37_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('13',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r2_hidden @ X26 @ X27 )
      | ~ ( r1_tarski @ ( k1_tarski @ X26 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[t37_zfmisc_1])).

thf('14',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X40: $i,X41: $i] :
      ( ( X40 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X41 @ X40 )
      | ( m1_subset_1 @ ( k1_tarski @ X41 ) @ ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t55_subset_1])).

thf('17',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ X34 )
      | ( r2_hidden @ X33 @ X34 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('21',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X36: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('23',plain,(
    r2_hidden @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X22: $i,X24: $i] :
      ( ( r1_tarski @ X24 @ X22 )
      | ~ ( r2_hidden @ X24 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('25',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r2_hidden @ X26 @ X27 )
      | ~ ( r1_tarski @ ( k1_tarski @ X26 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[t37_zfmisc_1])).

thf('27',plain,(
    r2_hidden @ sk_C_2 @ sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('28',plain,(
    ! [X29: $i,X31: $i,X32: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X29 @ X31 ) @ X32 )
      | ~ ( r2_hidden @ X31 @ X32 )
      | ~ ( r2_hidden @ X29 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_C_2 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r1_tarski @ ( k2_tarski @ sk_D @ sk_C_2 ) @ sk_A ),
    inference('sup-',[status(thm)],['14','29'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('31',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X6 @ X5 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('32',plain,(
    r1_tarski @ ( k2_tarski @ sk_C_2 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X40: $i,X41: $i] :
      ( ( X40 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X41 @ X40 )
      | ( m1_subset_1 @ ( k1_tarski @ X41 ) @ ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t55_subset_1])).

thf('35',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ X34 )
      | ( r2_hidden @ X33 @ X34 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X36: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('41',plain,(
    r2_hidden @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X22: $i,X24: $i] :
      ( ( r1_tarski @ X24 @ X22 )
      | ~ ( r2_hidden @ X24 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('43',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('44',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X4 @ X3 )
      | ( r1_tarski @ ( k2_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C_2 @ sk_D ) ) @ sk_A ),
    inference('sup-',[status(thm)],['32','45'])).

thf('47',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X6 @ X5 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('48',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k1_enumset1 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ ( k2_tarski @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf(t98_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ A @ C @ B ) ) )).

thf('50',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k1_enumset1 @ X15 @ X17 @ X16 )
      = ( k1_enumset1 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('51',plain,(
    r1_tarski @ ( k1_enumset1 @ sk_B @ sk_C_2 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['46','49','50'])).

thf('52',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X21 @ X22 )
      | ( r2_hidden @ X21 @ X23 )
      | ( X23
       != ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('53',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r2_hidden @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    r2_hidden @ ( k1_enumset1 @ sk_B @ sk_C_2 @ sk_D ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X33 @ X34 )
      | ( m1_subset_1 @ X33 @ X34 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('57',plain,(
    ! [X33: $i,X34: $i] :
      ( ( m1_subset_1 @ X33 @ X34 )
      | ~ ( r2_hidden @ X33 @ X34 ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ ( k1_enumset1 @ sk_B @ sk_C_2 @ sk_D ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['0','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BVJjnjvRej
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:51:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.65  % Solved by: fo/fo7.sh
% 0.46/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.65  % done 594 iterations in 0.193s
% 0.46/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.65  % SZS output start Refutation
% 0.46/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.65  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.46/0.65  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.65  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.65  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.46/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.65  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.65  thf(t57_subset_1, conjecture,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ B @ A ) =>
% 0.46/0.65       ( ![C:$i]:
% 0.46/0.65         ( ( m1_subset_1 @ C @ A ) =>
% 0.46/0.65           ( ![D:$i]:
% 0.46/0.65             ( ( m1_subset_1 @ D @ A ) =>
% 0.46/0.65               ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.46/0.65                 ( m1_subset_1 @
% 0.46/0.65                   ( k1_enumset1 @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) ) ) ) ) ))).
% 0.46/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.65    (~( ![A:$i,B:$i]:
% 0.46/0.65        ( ( m1_subset_1 @ B @ A ) =>
% 0.46/0.65          ( ![C:$i]:
% 0.46/0.65            ( ( m1_subset_1 @ C @ A ) =>
% 0.46/0.65              ( ![D:$i]:
% 0.46/0.65                ( ( m1_subset_1 @ D @ A ) =>
% 0.46/0.65                  ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.46/0.65                    ( m1_subset_1 @
% 0.46/0.65                      ( k1_enumset1 @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) ) ) ) ) ) )),
% 0.46/0.65    inference('cnf.neg', [status(esa)], [t57_subset_1])).
% 0.46/0.65  thf('0', plain,
% 0.46/0.65      (~ (m1_subset_1 @ (k1_enumset1 @ sk_B @ sk_C_2 @ sk_D) @ 
% 0.46/0.65          (k1_zfmisc_1 @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('1', plain, ((m1_subset_1 @ sk_D @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(t55_subset_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ B @ A ) =>
% 0.46/0.65       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.46/0.65         ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.46/0.65  thf('2', plain,
% 0.46/0.65      (![X40 : $i, X41 : $i]:
% 0.46/0.65         (((X40) = (k1_xboole_0))
% 0.46/0.65          | ~ (m1_subset_1 @ X41 @ X40)
% 0.46/0.65          | (m1_subset_1 @ (k1_tarski @ X41) @ (k1_zfmisc_1 @ X40)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t55_subset_1])).
% 0.46/0.65  thf('3', plain,
% 0.46/0.65      (((m1_subset_1 @ (k1_tarski @ sk_D) @ (k1_zfmisc_1 @ sk_A))
% 0.46/0.65        | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.65  thf('4', plain, (((sk_A) != (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('5', plain, ((m1_subset_1 @ (k1_tarski @ sk_D) @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.65      inference('simplify_reflect-', [status(thm)], ['3', '4'])).
% 0.46/0.65  thf(d2_subset_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( v1_xboole_0 @ A ) =>
% 0.46/0.65         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.46/0.65       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.65         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.46/0.65  thf('6', plain,
% 0.46/0.65      (![X33 : $i, X34 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X33 @ X34)
% 0.46/0.65          | (r2_hidden @ X33 @ X34)
% 0.46/0.65          | (v1_xboole_0 @ X34))),
% 0.46/0.65      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.46/0.65  thf('7', plain,
% 0.46/0.65      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.46/0.65        | (r2_hidden @ (k1_tarski @ sk_D) @ (k1_zfmisc_1 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.65  thf(fc1_subset_1, axiom,
% 0.46/0.65    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.46/0.65  thf('8', plain, (![X36 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X36))),
% 0.46/0.65      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.46/0.65  thf('9', plain, ((r2_hidden @ (k1_tarski @ sk_D) @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.65      inference('clc', [status(thm)], ['7', '8'])).
% 0.46/0.65  thf(d1_zfmisc_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.46/0.65       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.46/0.65  thf('10', plain,
% 0.46/0.65      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X24 @ X23)
% 0.46/0.65          | (r1_tarski @ X24 @ X22)
% 0.46/0.65          | ((X23) != (k1_zfmisc_1 @ X22)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.46/0.65  thf('11', plain,
% 0.46/0.65      (![X22 : $i, X24 : $i]:
% 0.46/0.65         ((r1_tarski @ X24 @ X22) | ~ (r2_hidden @ X24 @ (k1_zfmisc_1 @ X22)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['10'])).
% 0.46/0.65  thf('12', plain, ((r1_tarski @ (k1_tarski @ sk_D) @ sk_A)),
% 0.46/0.65      inference('sup-', [status(thm)], ['9', '11'])).
% 0.46/0.65  thf(t37_zfmisc_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.46/0.65  thf('13', plain,
% 0.46/0.65      (![X26 : $i, X27 : $i]:
% 0.46/0.65         ((r2_hidden @ X26 @ X27) | ~ (r1_tarski @ (k1_tarski @ X26) @ X27))),
% 0.46/0.65      inference('cnf', [status(esa)], [t37_zfmisc_1])).
% 0.46/0.65  thf('14', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.46/0.65      inference('sup-', [status(thm)], ['12', '13'])).
% 0.46/0.65  thf('15', plain, ((m1_subset_1 @ sk_C_2 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('16', plain,
% 0.46/0.65      (![X40 : $i, X41 : $i]:
% 0.46/0.65         (((X40) = (k1_xboole_0))
% 0.46/0.65          | ~ (m1_subset_1 @ X41 @ X40)
% 0.46/0.65          | (m1_subset_1 @ (k1_tarski @ X41) @ (k1_zfmisc_1 @ X40)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t55_subset_1])).
% 0.46/0.65  thf('17', plain,
% 0.46/0.65      (((m1_subset_1 @ (k1_tarski @ sk_C_2) @ (k1_zfmisc_1 @ sk_A))
% 0.46/0.65        | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['15', '16'])).
% 0.46/0.65  thf('18', plain, (((sk_A) != (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('19', plain,
% 0.46/0.65      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.65      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.46/0.65  thf('20', plain,
% 0.46/0.65      (![X33 : $i, X34 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X33 @ X34)
% 0.46/0.65          | (r2_hidden @ X33 @ X34)
% 0.46/0.65          | (v1_xboole_0 @ X34))),
% 0.46/0.65      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.46/0.65  thf('21', plain,
% 0.46/0.65      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.46/0.65        | (r2_hidden @ (k1_tarski @ sk_C_2) @ (k1_zfmisc_1 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['19', '20'])).
% 0.46/0.65  thf('22', plain, (![X36 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X36))),
% 0.46/0.65      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.46/0.65  thf('23', plain, ((r2_hidden @ (k1_tarski @ sk_C_2) @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.65      inference('clc', [status(thm)], ['21', '22'])).
% 0.46/0.65  thf('24', plain,
% 0.46/0.65      (![X22 : $i, X24 : $i]:
% 0.46/0.65         ((r1_tarski @ X24 @ X22) | ~ (r2_hidden @ X24 @ (k1_zfmisc_1 @ X22)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['10'])).
% 0.46/0.65  thf('25', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ sk_A)),
% 0.46/0.65      inference('sup-', [status(thm)], ['23', '24'])).
% 0.46/0.65  thf('26', plain,
% 0.46/0.65      (![X26 : $i, X27 : $i]:
% 0.46/0.65         ((r2_hidden @ X26 @ X27) | ~ (r1_tarski @ (k1_tarski @ X26) @ X27))),
% 0.46/0.65      inference('cnf', [status(esa)], [t37_zfmisc_1])).
% 0.46/0.65  thf('27', plain, ((r2_hidden @ sk_C_2 @ sk_A)),
% 0.46/0.65      inference('sup-', [status(thm)], ['25', '26'])).
% 0.46/0.65  thf(t38_zfmisc_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.46/0.65       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.46/0.65  thf('28', plain,
% 0.46/0.65      (![X29 : $i, X31 : $i, X32 : $i]:
% 0.46/0.65         ((r1_tarski @ (k2_tarski @ X29 @ X31) @ X32)
% 0.46/0.65          | ~ (r2_hidden @ X31 @ X32)
% 0.46/0.65          | ~ (r2_hidden @ X29 @ X32))),
% 0.46/0.65      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.46/0.65  thf('29', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X0 @ sk_A)
% 0.46/0.65          | (r1_tarski @ (k2_tarski @ X0 @ sk_C_2) @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['27', '28'])).
% 0.46/0.65  thf('30', plain, ((r1_tarski @ (k2_tarski @ sk_D @ sk_C_2) @ sk_A)),
% 0.46/0.65      inference('sup-', [status(thm)], ['14', '29'])).
% 0.46/0.65  thf(commutativity_k2_tarski, axiom,
% 0.46/0.65    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.46/0.65  thf('31', plain,
% 0.46/0.65      (![X5 : $i, X6 : $i]: ((k2_tarski @ X6 @ X5) = (k2_tarski @ X5 @ X6))),
% 0.46/0.65      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.46/0.65  thf('32', plain, ((r1_tarski @ (k2_tarski @ sk_C_2 @ sk_D) @ sk_A)),
% 0.46/0.65      inference('demod', [status(thm)], ['30', '31'])).
% 0.46/0.65  thf('33', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('34', plain,
% 0.46/0.65      (![X40 : $i, X41 : $i]:
% 0.46/0.65         (((X40) = (k1_xboole_0))
% 0.46/0.65          | ~ (m1_subset_1 @ X41 @ X40)
% 0.46/0.65          | (m1_subset_1 @ (k1_tarski @ X41) @ (k1_zfmisc_1 @ X40)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t55_subset_1])).
% 0.46/0.65  thf('35', plain,
% 0.46/0.65      (((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.46/0.65        | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['33', '34'])).
% 0.46/0.65  thf('36', plain, (((sk_A) != (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('37', plain, ((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.65      inference('simplify_reflect-', [status(thm)], ['35', '36'])).
% 0.46/0.65  thf('38', plain,
% 0.46/0.65      (![X33 : $i, X34 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X33 @ X34)
% 0.46/0.65          | (r2_hidden @ X33 @ X34)
% 0.46/0.65          | (v1_xboole_0 @ X34))),
% 0.46/0.65      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.46/0.65  thf('39', plain,
% 0.46/0.65      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.46/0.65        | (r2_hidden @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['37', '38'])).
% 0.46/0.65  thf('40', plain, (![X36 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X36))),
% 0.46/0.65      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.46/0.65  thf('41', plain, ((r2_hidden @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.65      inference('clc', [status(thm)], ['39', '40'])).
% 0.46/0.65  thf('42', plain,
% 0.46/0.65      (![X22 : $i, X24 : $i]:
% 0.46/0.65         ((r1_tarski @ X24 @ X22) | ~ (r2_hidden @ X24 @ (k1_zfmisc_1 @ X22)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['10'])).
% 0.46/0.65  thf('43', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ sk_A)),
% 0.46/0.65      inference('sup-', [status(thm)], ['41', '42'])).
% 0.46/0.65  thf(t8_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.46/0.65       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.46/0.65  thf('44', plain,
% 0.46/0.65      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.65         (~ (r1_tarski @ X2 @ X3)
% 0.46/0.65          | ~ (r1_tarski @ X4 @ X3)
% 0.46/0.65          | (r1_tarski @ (k2_xboole_0 @ X2 @ X4) @ X3))),
% 0.46/0.65      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.46/0.65  thf('45', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_B) @ X0) @ sk_A)
% 0.46/0.65          | ~ (r1_tarski @ X0 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['43', '44'])).
% 0.46/0.65  thf('46', plain,
% 0.46/0.65      ((r1_tarski @ 
% 0.46/0.65        (k2_xboole_0 @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_C_2 @ sk_D)) @ sk_A)),
% 0.46/0.65      inference('sup-', [status(thm)], ['32', '45'])).
% 0.46/0.65  thf('47', plain,
% 0.46/0.65      (![X5 : $i, X6 : $i]: ((k2_tarski @ X6 @ X5) = (k2_tarski @ X5 @ X6))),
% 0.46/0.65      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.46/0.65  thf(t42_enumset1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.46/0.65       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.46/0.65  thf('48', plain,
% 0.46/0.65      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.46/0.65         ((k1_enumset1 @ X12 @ X13 @ X14)
% 0.46/0.65           = (k2_xboole_0 @ (k1_tarski @ X12) @ (k2_tarski @ X13 @ X14)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.46/0.65  thf('49', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         ((k1_enumset1 @ X2 @ X0 @ X1)
% 0.46/0.65           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['47', '48'])).
% 0.46/0.65  thf(t98_enumset1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ))).
% 0.46/0.65  thf('50', plain,
% 0.46/0.65      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.65         ((k1_enumset1 @ X15 @ X17 @ X16) = (k1_enumset1 @ X15 @ X16 @ X17))),
% 0.46/0.65      inference('cnf', [status(esa)], [t98_enumset1])).
% 0.46/0.65  thf('51', plain, ((r1_tarski @ (k1_enumset1 @ sk_B @ sk_C_2 @ sk_D) @ sk_A)),
% 0.46/0.65      inference('demod', [status(thm)], ['46', '49', '50'])).
% 0.46/0.65  thf('52', plain,
% 0.46/0.65      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.65         (~ (r1_tarski @ X21 @ X22)
% 0.46/0.65          | (r2_hidden @ X21 @ X23)
% 0.46/0.65          | ((X23) != (k1_zfmisc_1 @ X22)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.46/0.65  thf('53', plain,
% 0.46/0.65      (![X21 : $i, X22 : $i]:
% 0.46/0.65         ((r2_hidden @ X21 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X21 @ X22))),
% 0.46/0.65      inference('simplify', [status(thm)], ['52'])).
% 0.46/0.65  thf('54', plain,
% 0.46/0.65      ((r2_hidden @ (k1_enumset1 @ sk_B @ sk_C_2 @ sk_D) @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['51', '53'])).
% 0.46/0.65  thf('55', plain,
% 0.46/0.65      (![X33 : $i, X34 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X33 @ X34)
% 0.46/0.65          | (m1_subset_1 @ X33 @ X34)
% 0.46/0.65          | (v1_xboole_0 @ X34))),
% 0.46/0.65      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.46/0.65  thf(t7_boole, axiom,
% 0.46/0.65    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( v1_xboole_0 @ B ) ) ))).
% 0.46/0.65  thf('56', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [t7_boole])).
% 0.46/0.65  thf('57', plain,
% 0.46/0.65      (![X33 : $i, X34 : $i]:
% 0.46/0.65         ((m1_subset_1 @ X33 @ X34) | ~ (r2_hidden @ X33 @ X34))),
% 0.46/0.65      inference('clc', [status(thm)], ['55', '56'])).
% 0.46/0.65  thf('58', plain,
% 0.46/0.65      ((m1_subset_1 @ (k1_enumset1 @ sk_B @ sk_C_2 @ sk_D) @ 
% 0.46/0.65        (k1_zfmisc_1 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['54', '57'])).
% 0.46/0.65  thf('59', plain, ($false), inference('demod', [status(thm)], ['0', '58'])).
% 0.46/0.65  
% 0.46/0.65  % SZS output end Refutation
% 0.46/0.65  
% 0.46/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
