%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.q1tNhyZXnP

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:38 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 328 expanded)
%              Number of leaves         :   23 ( 105 expanded)
%              Depth                    :   22
%              Number of atoms          :  548 (2506 expanded)
%              Number of equality atoms :   63 ( 364 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t44_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ( B != C )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t44_zfmisc_1])).

thf('1',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_tarski @ X27 @ X26 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X61: $i,X62: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X61 @ X62 ) )
      = ( k2_xboole_0 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X61: $i,X62: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X61 @ X62 ) )
      = ( k2_xboole_0 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ sk_C_2 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_C_2 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf('13',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r2_hidden @ ( sk_B @ sk_C_2 ) @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('15',plain,(
    ! [X28: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X31 @ X30 )
      | ( X31 = X28 )
      | ( X30
       != ( k1_tarski @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('16',plain,(
    ! [X28: $i,X31: $i] :
      ( ( X31 = X28 )
      | ~ ( r2_hidden @ X31 @ ( k1_tarski @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( sk_B @ sk_C_2 )
    = sk_A ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('19',plain,
    ( ( r2_hidden @ sk_A @ sk_C_2 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r2_hidden @ sk_A @ sk_C_2 ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('25',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X28: $i,X31: $i] :
      ( ( X31 = X28 )
      | ~ ( r2_hidden @ X31 @ ( k1_tarski @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( ( sk_C @ X0 @ sk_B_1 )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_A @ X0 )
      | ( r1_tarski @ sk_B_1 @ X0 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    r1_tarski @ sk_B_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['21','33'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X9: $i,X11: $i] :
      ( ( X9 = X11 )
      | ~ ( r1_tarski @ X11 @ X9 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('36',plain,
    ( ~ ( r1_tarski @ sk_C_2 @ sk_B_1 )
    | ( sk_C_2 = sk_B_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    sk_B_1 != sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ~ ( r1_tarski @ sk_C_2 @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('41',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X28: $i,X31: $i] :
      ( ( X31 = X28 )
      | ~ ( r2_hidden @ X31 @ ( k1_tarski @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('45',plain,
    ( ( sk_B @ sk_B_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('47',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['47','48'])).

thf('50',plain,(
    r1_tarski @ sk_B_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['21','33'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('51',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ X15 @ X14 )
        = X14 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('52',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_C_2 )
    = sk_C_2 ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k1_tarski @ sk_A )
    = sk_C_2 ),
    inference('sup+',[status(thm)],['52','53'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('55',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('56',plain,(
    ! [X61: $i,X62: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X61 @ X62 ) )
      = ( k2_xboole_0 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('58',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k3_tarski @ sk_C_2 )
    = sk_A ),
    inference('sup+',[status(thm)],['54','59'])).

thf('61',plain,(
    r2_hidden @ ( k3_tarski @ sk_C_2 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['49','60'])).

thf('62',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('63',plain,
    ( ( k1_tarski @ sk_A )
    = sk_C_2 ),
    inference('sup+',[status(thm)],['52','53'])).

thf('64',plain,
    ( ( k3_tarski @ sk_C_2 )
    = sk_A ),
    inference('sup+',[status(thm)],['54','59'])).

thf('65',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_C_2 ) )
    = sk_C_2 ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X28: $i,X31: $i] :
      ( ( X31 = X28 )
      | ~ ( r2_hidden @ X31 @ ( k1_tarski @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_2 )
      | ( X0
        = ( k3_tarski @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( ( sk_C @ X0 @ sk_C_2 )
        = ( k3_tarski @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['62','67'])).

thf('69',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k3_tarski @ sk_C_2 ) @ X0 )
      | ( r1_tarski @ sk_C_2 @ X0 )
      | ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ~ ( r2_hidden @ ( k3_tarski @ sk_C_2 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    r1_tarski @ sk_C_2 @ sk_B_1 ),
    inference('sup-',[status(thm)],['61','71'])).

thf('73',plain,(
    $false ),
    inference(demod,[status(thm)],['38','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.q1tNhyZXnP
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:47:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 647 iterations in 0.188s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.64  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.46/0.64  thf(sk_B_type, type, sk_B: $i > $i).
% 0.46/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.64  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.64  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.46/0.64  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.64  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.64  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.64  thf(t7_xboole_0, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.46/0.64          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.46/0.64  thf('0', plain,
% 0.46/0.64      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.46/0.64      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.64  thf(t44_zfmisc_1, conjecture,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.46/0.64          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.46/0.64          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.64    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.64        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.46/0.64             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.46/0.64             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 0.46/0.64    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 0.46/0.64  thf('1', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(commutativity_k2_tarski, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.46/0.64  thf('2', plain,
% 0.46/0.64      (![X26 : $i, X27 : $i]:
% 0.46/0.64         ((k2_tarski @ X27 @ X26) = (k2_tarski @ X26 @ X27))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.46/0.64  thf(l51_zfmisc_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.64  thf('3', plain,
% 0.46/0.64      (![X61 : $i, X62 : $i]:
% 0.46/0.64         ((k3_tarski @ (k2_tarski @ X61 @ X62)) = (k2_xboole_0 @ X61 @ X62))),
% 0.46/0.64      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.46/0.64  thf('4', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('sup+', [status(thm)], ['2', '3'])).
% 0.46/0.64  thf('5', plain,
% 0.46/0.64      (![X61 : $i, X62 : $i]:
% 0.46/0.64         ((k3_tarski @ (k2_tarski @ X61 @ X62)) = (k2_xboole_0 @ X61 @ X62))),
% 0.46/0.64      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.46/0.64  thf('6', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('sup+', [status(thm)], ['4', '5'])).
% 0.46/0.64  thf(t7_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.64  thf('7', plain,
% 0.46/0.64      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 0.46/0.64      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.46/0.64  thf('8', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['6', '7'])).
% 0.46/0.64  thf('9', plain, ((r1_tarski @ sk_C_2 @ (k1_tarski @ sk_A))),
% 0.46/0.64      inference('sup+', [status(thm)], ['1', '8'])).
% 0.46/0.64  thf(d3_tarski, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( r1_tarski @ A @ B ) <=>
% 0.46/0.64       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.46/0.64  thf('10', plain,
% 0.46/0.64      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X2 @ X3)
% 0.46/0.64          | (r2_hidden @ X2 @ X4)
% 0.46/0.64          | ~ (r1_tarski @ X3 @ X4))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.64  thf('11', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.46/0.64      inference('sup-', [status(thm)], ['9', '10'])).
% 0.46/0.64  thf('12', plain,
% 0.46/0.64      ((((sk_C_2) = (k1_xboole_0))
% 0.46/0.64        | (r2_hidden @ (sk_B @ sk_C_2) @ (k1_tarski @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['0', '11'])).
% 0.46/0.64  thf('13', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('14', plain, ((r2_hidden @ (sk_B @ sk_C_2) @ (k1_tarski @ sk_A))),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.46/0.64  thf(d1_tarski, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.46/0.64       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.46/0.64  thf('15', plain,
% 0.46/0.64      (![X28 : $i, X30 : $i, X31 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X31 @ X30)
% 0.46/0.64          | ((X31) = (X28))
% 0.46/0.64          | ((X30) != (k1_tarski @ X28)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d1_tarski])).
% 0.46/0.64  thf('16', plain,
% 0.46/0.64      (![X28 : $i, X31 : $i]:
% 0.46/0.64         (((X31) = (X28)) | ~ (r2_hidden @ X31 @ (k1_tarski @ X28)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['15'])).
% 0.46/0.64  thf('17', plain, (((sk_B @ sk_C_2) = (sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['14', '16'])).
% 0.46/0.64  thf('18', plain,
% 0.46/0.64      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.46/0.64      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.64  thf('19', plain,
% 0.46/0.64      (((r2_hidden @ sk_A @ sk_C_2) | ((sk_C_2) = (k1_xboole_0)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['17', '18'])).
% 0.46/0.64  thf('20', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('21', plain, ((r2_hidden @ sk_A @ sk_C_2)),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.46/0.64  thf('22', plain,
% 0.46/0.64      (![X3 : $i, X5 : $i]:
% 0.46/0.64         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.64  thf('23', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('24', plain,
% 0.46/0.64      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 0.46/0.64      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.46/0.64  thf('25', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.46/0.64      inference('sup+', [status(thm)], ['23', '24'])).
% 0.46/0.64  thf('26', plain,
% 0.46/0.64      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X2 @ X3)
% 0.46/0.64          | (r2_hidden @ X2 @ X4)
% 0.46/0.64          | ~ (r1_tarski @ X3 @ X4))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.64  thf('27', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['25', '26'])).
% 0.46/0.64  thf('28', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((r1_tarski @ sk_B_1 @ X0)
% 0.46/0.64          | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ (k1_tarski @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['22', '27'])).
% 0.46/0.64  thf('29', plain,
% 0.46/0.64      (![X28 : $i, X31 : $i]:
% 0.46/0.64         (((X31) = (X28)) | ~ (r2_hidden @ X31 @ (k1_tarski @ X28)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['15'])).
% 0.46/0.64  thf('30', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((r1_tarski @ sk_B_1 @ X0) | ((sk_C @ X0 @ sk_B_1) = (sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['28', '29'])).
% 0.46/0.64  thf('31', plain,
% 0.46/0.64      (![X3 : $i, X5 : $i]:
% 0.46/0.64         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.64  thf('32', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (r2_hidden @ sk_A @ X0)
% 0.46/0.64          | (r1_tarski @ sk_B_1 @ X0)
% 0.46/0.64          | (r1_tarski @ sk_B_1 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['30', '31'])).
% 0.46/0.64  thf('33', plain,
% 0.46/0.64      (![X0 : $i]: ((r1_tarski @ sk_B_1 @ X0) | ~ (r2_hidden @ sk_A @ X0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['32'])).
% 0.46/0.64  thf('34', plain, ((r1_tarski @ sk_B_1 @ sk_C_2)),
% 0.46/0.64      inference('sup-', [status(thm)], ['21', '33'])).
% 0.46/0.64  thf(d10_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.64  thf('35', plain,
% 0.46/0.64      (![X9 : $i, X11 : $i]:
% 0.46/0.64         (((X9) = (X11)) | ~ (r1_tarski @ X11 @ X9) | ~ (r1_tarski @ X9 @ X11))),
% 0.46/0.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.64  thf('36', plain, ((~ (r1_tarski @ sk_C_2 @ sk_B_1) | ((sk_C_2) = (sk_B_1)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['34', '35'])).
% 0.46/0.64  thf('37', plain, (((sk_B_1) != (sk_C_2))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('38', plain, (~ (r1_tarski @ sk_C_2 @ sk_B_1)),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 0.46/0.64  thf('39', plain,
% 0.46/0.64      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.46/0.64      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.64  thf('40', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['25', '26'])).
% 0.46/0.64  thf('41', plain,
% 0.46/0.64      ((((sk_B_1) = (k1_xboole_0))
% 0.46/0.64        | (r2_hidden @ (sk_B @ sk_B_1) @ (k1_tarski @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['39', '40'])).
% 0.46/0.64  thf('42', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('43', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (k1_tarski @ sk_A))),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['41', '42'])).
% 0.46/0.64  thf('44', plain,
% 0.46/0.64      (![X28 : $i, X31 : $i]:
% 0.46/0.64         (((X31) = (X28)) | ~ (r2_hidden @ X31 @ (k1_tarski @ X28)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['15'])).
% 0.46/0.64  thf('45', plain, (((sk_B @ sk_B_1) = (sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['43', '44'])).
% 0.46/0.64  thf('46', plain,
% 0.46/0.64      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.46/0.64      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.64  thf('47', plain,
% 0.46/0.64      (((r2_hidden @ sk_A @ sk_B_1) | ((sk_B_1) = (k1_xboole_0)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['45', '46'])).
% 0.46/0.64  thf('48', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('49', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['47', '48'])).
% 0.46/0.64  thf('50', plain, ((r1_tarski @ sk_B_1 @ sk_C_2)),
% 0.46/0.64      inference('sup-', [status(thm)], ['21', '33'])).
% 0.46/0.64  thf(t12_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.46/0.64  thf('51', plain,
% 0.46/0.64      (![X14 : $i, X15 : $i]:
% 0.46/0.64         (((k2_xboole_0 @ X15 @ X14) = (X14)) | ~ (r1_tarski @ X15 @ X14))),
% 0.46/0.64      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.46/0.64  thf('52', plain, (((k2_xboole_0 @ sk_B_1 @ sk_C_2) = (sk_C_2))),
% 0.46/0.64      inference('sup-', [status(thm)], ['50', '51'])).
% 0.46/0.64  thf('53', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('54', plain, (((k1_tarski @ sk_A) = (sk_C_2))),
% 0.46/0.64      inference('sup+', [status(thm)], ['52', '53'])).
% 0.46/0.64  thf(t69_enumset1, axiom,
% 0.46/0.64    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.46/0.64  thf('55', plain,
% 0.46/0.64      (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 0.46/0.64      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.64  thf('56', plain,
% 0.46/0.64      (![X61 : $i, X62 : $i]:
% 0.46/0.64         ((k3_tarski @ (k2_tarski @ X61 @ X62)) = (k2_xboole_0 @ X61 @ X62))),
% 0.46/0.64      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.46/0.64  thf('57', plain,
% 0.46/0.64      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['55', '56'])).
% 0.46/0.64  thf(idempotence_k2_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.46/0.64  thf('58', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ X6) = (X6))),
% 0.46/0.64      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.46/0.64  thf('59', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['57', '58'])).
% 0.46/0.64  thf('60', plain, (((k3_tarski @ sk_C_2) = (sk_A))),
% 0.46/0.64      inference('sup+', [status(thm)], ['54', '59'])).
% 0.46/0.64  thf('61', plain, ((r2_hidden @ (k3_tarski @ sk_C_2) @ sk_B_1)),
% 0.46/0.64      inference('demod', [status(thm)], ['49', '60'])).
% 0.46/0.64  thf('62', plain,
% 0.46/0.64      (![X3 : $i, X5 : $i]:
% 0.46/0.64         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.64  thf('63', plain, (((k1_tarski @ sk_A) = (sk_C_2))),
% 0.46/0.64      inference('sup+', [status(thm)], ['52', '53'])).
% 0.46/0.64  thf('64', plain, (((k3_tarski @ sk_C_2) = (sk_A))),
% 0.46/0.64      inference('sup+', [status(thm)], ['54', '59'])).
% 0.46/0.64  thf('65', plain, (((k1_tarski @ (k3_tarski @ sk_C_2)) = (sk_C_2))),
% 0.46/0.64      inference('demod', [status(thm)], ['63', '64'])).
% 0.46/0.64  thf('66', plain,
% 0.46/0.64      (![X28 : $i, X31 : $i]:
% 0.46/0.64         (((X31) = (X28)) | ~ (r2_hidden @ X31 @ (k1_tarski @ X28)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['15'])).
% 0.46/0.64  thf('67', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X0 @ sk_C_2) | ((X0) = (k3_tarski @ sk_C_2)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['65', '66'])).
% 0.46/0.64  thf('68', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((r1_tarski @ sk_C_2 @ X0)
% 0.46/0.64          | ((sk_C @ X0 @ sk_C_2) = (k3_tarski @ sk_C_2)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['62', '67'])).
% 0.46/0.64  thf('69', plain,
% 0.46/0.64      (![X3 : $i, X5 : $i]:
% 0.46/0.64         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.64  thf('70', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (r2_hidden @ (k3_tarski @ sk_C_2) @ X0)
% 0.46/0.64          | (r1_tarski @ sk_C_2 @ X0)
% 0.46/0.64          | (r1_tarski @ sk_C_2 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['68', '69'])).
% 0.46/0.64  thf('71', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((r1_tarski @ sk_C_2 @ X0) | ~ (r2_hidden @ (k3_tarski @ sk_C_2) @ X0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['70'])).
% 0.46/0.64  thf('72', plain, ((r1_tarski @ sk_C_2 @ sk_B_1)),
% 0.46/0.64      inference('sup-', [status(thm)], ['61', '71'])).
% 0.46/0.64  thf('73', plain, ($false), inference('demod', [status(thm)], ['38', '72'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.46/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
