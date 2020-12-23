%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eZwnjKA7y9

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:41 EST 2020

% Result     : Theorem 4.09s
% Output     : Refutation 4.09s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 174 expanded)
%              Number of leaves         :   27 (  64 expanded)
%              Depth                    :   17
%              Number of atoms          :  536 (1319 expanded)
%              Number of equality atoms :   39 ( 105 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t40_subset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( ( r1_tarski @ B @ C )
          & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
       => ( B = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
       => ( ( ( r1_tarski @ B @ C )
            & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
         => ( B = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_subset_1])).

thf('0',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
           => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ( r1_tarski @ X25 @ ( k3_subset_1 @ X26 @ X27 ) )
      | ~ ( r1_tarski @ X27 @ ( k3_subset_1 @ X26 @ X25 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t35_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ sk_C_1 @ ( k3_subset_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
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

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ X17 )
      | ( r2_hidden @ X16 @ X17 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('7',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X22: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('9',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ( r1_tarski @ X14 @ X12 )
      | ( X13
       != ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('11',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r1_tarski @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['9','11'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('17',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = sk_B ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k3_xboole_0 @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = ( k3_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['14','19'])).

thf('21',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = sk_B ),
    inference('sup-',[status(thm)],['15','16'])).

thf('22',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['20','21'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('26',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('27',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ ( k6_subset_1 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('28',plain,(
    ! [X20: $i,X21: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['22','30'])).

thf('32',plain,(
    r1_tarski @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['4','31'])).

thf('33',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('34',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('36',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = sk_B ),
    inference('sup-',[status(thm)],['15','16'])).

thf('38',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('40',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ ( k6_subset_1 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('41',plain,(
    ! [X20: $i,X21: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('42',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ X17 )
      | ( r2_hidden @ X16 @ X17 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ ( k6_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X22: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k6_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r1_tarski @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['40','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['39','48'])).

thf('50',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['38','49'])).

thf(t38_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf('51',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X29 @ ( k3_subset_1 @ X28 @ X29 ) )
      | ( X29
        = ( k1_subset_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t38_subset_1])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('52',plain,(
    ! [X19: $i] :
      ( ( k1_subset_1 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('53',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X29 @ ( k3_subset_1 @ X28 @ X29 ) )
      | ( X29 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['22','30'])).

thf('56',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['56','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eZwnjKA7y9
% 0.11/0.34  % Computer   : n024.cluster.edu
% 0.11/0.34  % Model      : x86_64 x86_64
% 0.11/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.34  % Memory     : 8042.1875MB
% 0.11/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.34  % CPULimit   : 60
% 0.11/0.34  % DateTime   : Tue Dec  1 09:22:36 EST 2020
% 0.11/0.34  % CPUTime    : 
% 0.11/0.34  % Running portfolio for 600 s
% 0.11/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.34  % Number of cores: 8
% 0.11/0.34  % Python version: Python 3.6.8
% 0.11/0.34  % Running in FO mode
% 4.09/4.27  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.09/4.27  % Solved by: fo/fo7.sh
% 4.09/4.27  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.09/4.27  % done 2284 iterations in 3.824s
% 4.09/4.27  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.09/4.27  % SZS output start Refutation
% 4.09/4.27  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.09/4.27  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.09/4.27  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.09/4.27  thf(sk_B_type, type, sk_B: $i).
% 4.09/4.27  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 4.09/4.27  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.09/4.27  thf(sk_A_type, type, sk_A: $i).
% 4.09/4.27  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.09/4.27  thf(sk_C_1_type, type, sk_C_1: $i).
% 4.09/4.27  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 4.09/4.27  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.09/4.27  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.09/4.27  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 4.09/4.27  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.09/4.27  thf(t40_subset_1, conjecture,
% 4.09/4.27    (![A:$i,B:$i,C:$i]:
% 4.09/4.27     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 4.09/4.27       ( ( ( r1_tarski @ B @ C ) & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 4.09/4.27         ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 4.09/4.27  thf(zf_stmt_0, negated_conjecture,
% 4.09/4.27    (~( ![A:$i,B:$i,C:$i]:
% 4.09/4.27        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 4.09/4.27          ( ( ( r1_tarski @ B @ C ) & 
% 4.09/4.27              ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 4.09/4.27            ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 4.09/4.27    inference('cnf.neg', [status(esa)], [t40_subset_1])).
% 4.09/4.27  thf('0', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))),
% 4.09/4.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.09/4.27  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 4.09/4.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.09/4.27  thf(t35_subset_1, axiom,
% 4.09/4.27    (![A:$i,B:$i]:
% 4.09/4.27     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.09/4.27       ( ![C:$i]:
% 4.09/4.27         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 4.09/4.27           ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 4.09/4.27             ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 4.09/4.27  thf('2', plain,
% 4.09/4.27      (![X25 : $i, X26 : $i, X27 : $i]:
% 4.09/4.27         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 4.09/4.27          | (r1_tarski @ X25 @ (k3_subset_1 @ X26 @ X27))
% 4.09/4.27          | ~ (r1_tarski @ X27 @ (k3_subset_1 @ X26 @ X25))
% 4.09/4.27          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 4.09/4.27      inference('cnf', [status(esa)], [t35_subset_1])).
% 4.09/4.27  thf('3', plain,
% 4.09/4.27      (![X0 : $i]:
% 4.09/4.27         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 4.09/4.27          | ~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))
% 4.09/4.27          | (r1_tarski @ sk_C_1 @ (k3_subset_1 @ sk_A @ X0)))),
% 4.09/4.27      inference('sup-', [status(thm)], ['1', '2'])).
% 4.09/4.27  thf('4', plain,
% 4.09/4.27      (((r1_tarski @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_B))
% 4.09/4.27        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 4.09/4.27      inference('sup-', [status(thm)], ['0', '3'])).
% 4.09/4.27  thf('5', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 4.09/4.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.09/4.27  thf(d2_subset_1, axiom,
% 4.09/4.27    (![A:$i,B:$i]:
% 4.09/4.27     ( ( ( v1_xboole_0 @ A ) =>
% 4.09/4.27         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 4.09/4.27       ( ( ~( v1_xboole_0 @ A ) ) =>
% 4.09/4.27         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 4.09/4.27  thf('6', plain,
% 4.09/4.27      (![X16 : $i, X17 : $i]:
% 4.09/4.27         (~ (m1_subset_1 @ X16 @ X17)
% 4.09/4.27          | (r2_hidden @ X16 @ X17)
% 4.09/4.27          | (v1_xboole_0 @ X17))),
% 4.09/4.27      inference('cnf', [status(esa)], [d2_subset_1])).
% 4.09/4.27  thf('7', plain,
% 4.09/4.27      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 4.09/4.27        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 4.09/4.27      inference('sup-', [status(thm)], ['5', '6'])).
% 4.09/4.27  thf(fc1_subset_1, axiom,
% 4.09/4.27    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 4.09/4.27  thf('8', plain, (![X22 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X22))),
% 4.09/4.27      inference('cnf', [status(esa)], [fc1_subset_1])).
% 4.09/4.27  thf('9', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 4.09/4.27      inference('clc', [status(thm)], ['7', '8'])).
% 4.09/4.27  thf(d1_zfmisc_1, axiom,
% 4.09/4.27    (![A:$i,B:$i]:
% 4.09/4.27     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 4.09/4.27       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 4.09/4.27  thf('10', plain,
% 4.09/4.27      (![X12 : $i, X13 : $i, X14 : $i]:
% 4.09/4.27         (~ (r2_hidden @ X14 @ X13)
% 4.09/4.27          | (r1_tarski @ X14 @ X12)
% 4.09/4.27          | ((X13) != (k1_zfmisc_1 @ X12)))),
% 4.09/4.27      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 4.09/4.27  thf('11', plain,
% 4.09/4.27      (![X12 : $i, X14 : $i]:
% 4.09/4.27         ((r1_tarski @ X14 @ X12) | ~ (r2_hidden @ X14 @ (k1_zfmisc_1 @ X12)))),
% 4.09/4.27      inference('simplify', [status(thm)], ['10'])).
% 4.09/4.27  thf('12', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 4.09/4.27      inference('sup-', [status(thm)], ['9', '11'])).
% 4.09/4.27  thf(t28_xboole_1, axiom,
% 4.09/4.27    (![A:$i,B:$i]:
% 4.09/4.27     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 4.09/4.27  thf('13', plain,
% 4.09/4.27      (![X7 : $i, X8 : $i]:
% 4.09/4.27         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 4.09/4.27      inference('cnf', [status(esa)], [t28_xboole_1])).
% 4.09/4.27  thf('14', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 4.09/4.27      inference('sup-', [status(thm)], ['12', '13'])).
% 4.09/4.27  thf('15', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 4.09/4.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.09/4.27  thf('16', plain,
% 4.09/4.27      (![X7 : $i, X8 : $i]:
% 4.09/4.27         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 4.09/4.28      inference('cnf', [status(esa)], [t28_xboole_1])).
% 4.09/4.28  thf('17', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (sk_B))),
% 4.09/4.28      inference('sup-', [status(thm)], ['15', '16'])).
% 4.09/4.28  thf(t16_xboole_1, axiom,
% 4.09/4.28    (![A:$i,B:$i,C:$i]:
% 4.09/4.28     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 4.09/4.28       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 4.09/4.28  thf('18', plain,
% 4.09/4.28      (![X4 : $i, X5 : $i, X6 : $i]:
% 4.09/4.28         ((k3_xboole_0 @ (k3_xboole_0 @ X4 @ X5) @ X6)
% 4.09/4.28           = (k3_xboole_0 @ X4 @ (k3_xboole_0 @ X5 @ X6)))),
% 4.09/4.28      inference('cnf', [status(esa)], [t16_xboole_1])).
% 4.09/4.28  thf('19', plain,
% 4.09/4.28      (![X0 : $i]:
% 4.09/4.28         ((k3_xboole_0 @ sk_B @ X0)
% 4.09/4.28           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_1 @ X0)))),
% 4.09/4.28      inference('sup+', [status(thm)], ['17', '18'])).
% 4.09/4.28  thf('20', plain,
% 4.09/4.28      (((k3_xboole_0 @ sk_B @ sk_A) = (k3_xboole_0 @ sk_B @ sk_C_1))),
% 4.09/4.28      inference('sup+', [status(thm)], ['14', '19'])).
% 4.09/4.28  thf('21', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (sk_B))),
% 4.09/4.28      inference('sup-', [status(thm)], ['15', '16'])).
% 4.09/4.28  thf('22', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 4.09/4.28      inference('demod', [status(thm)], ['20', '21'])).
% 4.09/4.28  thf(commutativity_k3_xboole_0, axiom,
% 4.09/4.28    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 4.09/4.28  thf('23', plain,
% 4.09/4.28      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.09/4.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.09/4.28  thf(t48_xboole_1, axiom,
% 4.09/4.28    (![A:$i,B:$i]:
% 4.09/4.28     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 4.09/4.28  thf('24', plain,
% 4.09/4.28      (![X9 : $i, X10 : $i]:
% 4.09/4.28         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 4.09/4.28           = (k3_xboole_0 @ X9 @ X10))),
% 4.09/4.28      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.09/4.28  thf(redefinition_k6_subset_1, axiom,
% 4.09/4.28    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 4.09/4.28  thf('25', plain,
% 4.09/4.28      (![X23 : $i, X24 : $i]:
% 4.09/4.28         ((k6_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))),
% 4.09/4.28      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 4.09/4.28  thf('26', plain,
% 4.09/4.28      (![X23 : $i, X24 : $i]:
% 4.09/4.28         ((k6_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))),
% 4.09/4.28      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 4.09/4.28  thf('27', plain,
% 4.09/4.28      (![X9 : $i, X10 : $i]:
% 4.09/4.28         ((k6_subset_1 @ X9 @ (k6_subset_1 @ X9 @ X10))
% 4.09/4.28           = (k3_xboole_0 @ X9 @ X10))),
% 4.09/4.28      inference('demod', [status(thm)], ['24', '25', '26'])).
% 4.09/4.28  thf(dt_k6_subset_1, axiom,
% 4.09/4.28    (![A:$i,B:$i]:
% 4.09/4.28     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 4.09/4.28  thf('28', plain,
% 4.09/4.28      (![X20 : $i, X21 : $i]:
% 4.09/4.28         (m1_subset_1 @ (k6_subset_1 @ X20 @ X21) @ (k1_zfmisc_1 @ X20))),
% 4.09/4.28      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 4.09/4.28  thf('29', plain,
% 4.09/4.28      (![X0 : $i, X1 : $i]:
% 4.09/4.28         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 4.09/4.28      inference('sup+', [status(thm)], ['27', '28'])).
% 4.09/4.28  thf('30', plain,
% 4.09/4.28      (![X0 : $i, X1 : $i]:
% 4.09/4.28         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 4.09/4.28      inference('sup+', [status(thm)], ['23', '29'])).
% 4.09/4.28  thf('31', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 4.09/4.28      inference('sup+', [status(thm)], ['22', '30'])).
% 4.09/4.28  thf('32', plain, ((r1_tarski @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_B))),
% 4.09/4.28      inference('demod', [status(thm)], ['4', '31'])).
% 4.09/4.28  thf('33', plain,
% 4.09/4.28      (![X7 : $i, X8 : $i]:
% 4.09/4.28         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 4.09/4.28      inference('cnf', [status(esa)], [t28_xboole_1])).
% 4.09/4.28  thf('34', plain,
% 4.09/4.28      (((k3_xboole_0 @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_C_1))),
% 4.09/4.28      inference('sup-', [status(thm)], ['32', '33'])).
% 4.09/4.28  thf('35', plain,
% 4.09/4.28      (![X0 : $i]:
% 4.09/4.28         ((k3_xboole_0 @ sk_B @ X0)
% 4.09/4.28           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_1 @ X0)))),
% 4.09/4.28      inference('sup+', [status(thm)], ['17', '18'])).
% 4.09/4.28  thf('36', plain,
% 4.09/4.28      (((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 4.09/4.28         = (k3_xboole_0 @ sk_B @ sk_C_1))),
% 4.09/4.28      inference('sup+', [status(thm)], ['34', '35'])).
% 4.09/4.28  thf('37', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (sk_B))),
% 4.09/4.28      inference('sup-', [status(thm)], ['15', '16'])).
% 4.09/4.28  thf('38', plain,
% 4.09/4.28      (((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 4.09/4.28      inference('demod', [status(thm)], ['36', '37'])).
% 4.09/4.28  thf('39', plain,
% 4.09/4.28      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.09/4.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.09/4.28  thf('40', plain,
% 4.09/4.28      (![X9 : $i, X10 : $i]:
% 4.09/4.28         ((k6_subset_1 @ X9 @ (k6_subset_1 @ X9 @ X10))
% 4.09/4.28           = (k3_xboole_0 @ X9 @ X10))),
% 4.09/4.28      inference('demod', [status(thm)], ['24', '25', '26'])).
% 4.09/4.28  thf('41', plain,
% 4.09/4.28      (![X20 : $i, X21 : $i]:
% 4.09/4.28         (m1_subset_1 @ (k6_subset_1 @ X20 @ X21) @ (k1_zfmisc_1 @ X20))),
% 4.09/4.28      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 4.09/4.28  thf('42', plain,
% 4.09/4.28      (![X16 : $i, X17 : $i]:
% 4.09/4.28         (~ (m1_subset_1 @ X16 @ X17)
% 4.09/4.28          | (r2_hidden @ X16 @ X17)
% 4.09/4.28          | (v1_xboole_0 @ X17))),
% 4.09/4.28      inference('cnf', [status(esa)], [d2_subset_1])).
% 4.09/4.28  thf('43', plain,
% 4.09/4.28      (![X0 : $i, X1 : $i]:
% 4.09/4.28         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 4.09/4.28          | (r2_hidden @ (k6_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 4.09/4.28      inference('sup-', [status(thm)], ['41', '42'])).
% 4.09/4.28  thf('44', plain, (![X22 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X22))),
% 4.09/4.28      inference('cnf', [status(esa)], [fc1_subset_1])).
% 4.09/4.28  thf('45', plain,
% 4.09/4.28      (![X0 : $i, X1 : $i]:
% 4.09/4.28         (r2_hidden @ (k6_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 4.09/4.28      inference('clc', [status(thm)], ['43', '44'])).
% 4.09/4.28  thf('46', plain,
% 4.09/4.28      (![X12 : $i, X14 : $i]:
% 4.09/4.28         ((r1_tarski @ X14 @ X12) | ~ (r2_hidden @ X14 @ (k1_zfmisc_1 @ X12)))),
% 4.09/4.28      inference('simplify', [status(thm)], ['10'])).
% 4.09/4.28  thf('47', plain,
% 4.09/4.28      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)),
% 4.09/4.28      inference('sup-', [status(thm)], ['45', '46'])).
% 4.09/4.28  thf('48', plain,
% 4.09/4.28      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 4.09/4.28      inference('sup+', [status(thm)], ['40', '47'])).
% 4.09/4.28  thf('49', plain,
% 4.09/4.28      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 4.09/4.28      inference('sup+', [status(thm)], ['39', '48'])).
% 4.09/4.28  thf('50', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))),
% 4.09/4.28      inference('sup+', [status(thm)], ['38', '49'])).
% 4.09/4.28  thf(t38_subset_1, axiom,
% 4.09/4.28    (![A:$i,B:$i]:
% 4.09/4.28     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.09/4.28       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 4.09/4.28         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 4.09/4.28  thf('51', plain,
% 4.09/4.28      (![X28 : $i, X29 : $i]:
% 4.09/4.28         (~ (r1_tarski @ X29 @ (k3_subset_1 @ X28 @ X29))
% 4.09/4.28          | ((X29) = (k1_subset_1 @ X28))
% 4.09/4.28          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 4.09/4.28      inference('cnf', [status(esa)], [t38_subset_1])).
% 4.09/4.28  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 4.09/4.28  thf('52', plain, (![X19 : $i]: ((k1_subset_1 @ X19) = (k1_xboole_0))),
% 4.09/4.28      inference('cnf', [status(esa)], [d3_subset_1])).
% 4.09/4.28  thf('53', plain,
% 4.09/4.28      (![X28 : $i, X29 : $i]:
% 4.09/4.28         (~ (r1_tarski @ X29 @ (k3_subset_1 @ X28 @ X29))
% 4.09/4.28          | ((X29) = (k1_xboole_0))
% 4.09/4.28          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 4.09/4.28      inference('demod', [status(thm)], ['51', '52'])).
% 4.09/4.28  thf('54', plain,
% 4.09/4.28      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))
% 4.09/4.28        | ((sk_B) = (k1_xboole_0)))),
% 4.09/4.28      inference('sup-', [status(thm)], ['50', '53'])).
% 4.09/4.28  thf('55', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 4.09/4.28      inference('sup+', [status(thm)], ['22', '30'])).
% 4.09/4.28  thf('56', plain, (((sk_B) = (k1_xboole_0))),
% 4.09/4.28      inference('demod', [status(thm)], ['54', '55'])).
% 4.09/4.28  thf('57', plain, (((sk_B) != (k1_xboole_0))),
% 4.09/4.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.09/4.28  thf('58', plain, ($false),
% 4.09/4.28      inference('simplify_reflect-', [status(thm)], ['56', '57'])).
% 4.09/4.28  
% 4.09/4.28  % SZS output end Refutation
% 4.09/4.28  
% 4.09/4.28  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
