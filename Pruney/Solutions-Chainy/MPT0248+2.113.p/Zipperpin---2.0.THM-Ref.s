%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Rm69TYffLZ

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:34 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 181 expanded)
%              Number of leaves         :   21 (  54 expanded)
%              Depth                    :   19
%              Number of atoms          :  571 (1999 expanded)
%              Number of equality atoms :   94 ( 420 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(t43_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B = k1_xboole_0 )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B = k1_xboole_0 )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_2 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X9 )
      | ( X9
       != ( k2_xboole_0 @ X10 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('3',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X7 @ ( k2_xboole_0 @ X10 @ X8 ) )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    r1_tarski @ sk_C_2 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['0','7'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('9',plain,(
    ! [X33: $i,X34: $i] :
      ( ( X34
        = ( k1_tarski @ X33 ) )
      | ( X34 = k1_xboole_0 )
      | ~ ( r1_tarski @ X34 @ ( k1_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('10',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( sk_C_2
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_B_2 != k1_xboole_0 )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('14',plain,
    ( ( sk_B_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_2 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('18',plain,(
    r1_tarski @ sk_B_2 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X33: $i,X34: $i] :
      ( ( X34
        = ( k1_tarski @ X33 ) )
      | ( X34 = k1_xboole_0 )
      | ~ ( r1_tarski @ X34 @ ( k1_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('20',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( sk_B_2
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_B_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( sk_B_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,
    ( ( ( sk_B_2 != sk_B_2 )
      | ( sk_B_2 = k1_xboole_0 ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( sk_B_2 != k1_xboole_0 )
   <= ( sk_B_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('26',plain,
    ( ( sk_B_2 != sk_B_2 )
   <= ( ( sk_B_2 != k1_xboole_0 )
      & ( sk_B_2
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( sk_B_2
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['13','15','27'])).

thf('29',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['12','28'])).

thf('30',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('31',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('32',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r1_tarski @ X34 @ ( k1_tarski @ X35 ) )
      | ( X34 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('33',plain,(
    ! [X35: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X35 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ k1_xboole_0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','35'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('37',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ( X21 = X18 )
      | ( X20
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('38',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21 = X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( sk_B @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( sk_B @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('44',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ! [X0: $i] :
        ( ( X0 = sk_B_2 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_2 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('52',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ X15 @ X14 )
        = X14 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['48','53'])).

thf('55',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['12','28'])).

thf('56',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference('simplify_reflect-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','56'])).

thf('58',plain,
    ( ! [X0: $i] :
        ~ ( v1_xboole_0 @ X0 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ! [X0: $i,X1: $i] : ( X0 = X1 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','58'])).

thf('60',plain,
    ( ( sk_B_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['21'])).

thf('61',plain,
    ( ! [X0: $i] : ( sk_B_2 != X0 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( sk_B_2
    = ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( sk_C_2 != k1_xboole_0 )
    | ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['21'])).

thf('64',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['62','63'])).

thf('65',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['30','64'])).

thf('66',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['10','29','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Rm69TYffLZ
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:51:39 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.77/1.02  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.77/1.02  % Solved by: fo/fo7.sh
% 0.77/1.02  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/1.02  % done 1368 iterations in 0.561s
% 0.77/1.02  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.77/1.02  % SZS output start Refutation
% 0.77/1.02  thf(sk_A_type, type, sk_A: $i).
% 0.77/1.02  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.77/1.02  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.77/1.02  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.77/1.02  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.77/1.02  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.77/1.02  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.77/1.02  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.77/1.02  thf(sk_B_type, type, sk_B: $i > $i).
% 0.77/1.02  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.77/1.02  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.77/1.02  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.77/1.02  thf(t43_zfmisc_1, conjecture,
% 0.77/1.02    (![A:$i,B:$i,C:$i]:
% 0.77/1.02     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.77/1.02          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.77/1.02          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.77/1.02          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.77/1.02  thf(zf_stmt_0, negated_conjecture,
% 0.77/1.02    (~( ![A:$i,B:$i,C:$i]:
% 0.77/1.02        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.77/1.02             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.77/1.02             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.77/1.02             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.77/1.02    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.77/1.02  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_2 @ sk_C_2))),
% 0.77/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.02  thf(d3_tarski, axiom,
% 0.77/1.02    (![A:$i,B:$i]:
% 0.77/1.02     ( ( r1_tarski @ A @ B ) <=>
% 0.77/1.02       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.77/1.02  thf('1', plain,
% 0.77/1.02      (![X4 : $i, X6 : $i]:
% 0.77/1.02         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.77/1.02      inference('cnf', [status(esa)], [d3_tarski])).
% 0.77/1.02  thf(d3_xboole_0, axiom,
% 0.77/1.02    (![A:$i,B:$i,C:$i]:
% 0.77/1.02     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.77/1.02       ( ![D:$i]:
% 0.77/1.02         ( ( r2_hidden @ D @ C ) <=>
% 0.77/1.02           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.77/1.02  thf('2', plain,
% 0.77/1.02      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.77/1.02         (~ (r2_hidden @ X7 @ X8)
% 0.77/1.02          | (r2_hidden @ X7 @ X9)
% 0.77/1.02          | ((X9) != (k2_xboole_0 @ X10 @ X8)))),
% 0.77/1.02      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.77/1.02  thf('3', plain,
% 0.77/1.02      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.77/1.02         ((r2_hidden @ X7 @ (k2_xboole_0 @ X10 @ X8)) | ~ (r2_hidden @ X7 @ X8))),
% 0.77/1.02      inference('simplify', [status(thm)], ['2'])).
% 0.77/1.02  thf('4', plain,
% 0.77/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/1.02         ((r1_tarski @ X0 @ X1)
% 0.77/1.02          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_xboole_0 @ X2 @ X0)))),
% 0.77/1.02      inference('sup-', [status(thm)], ['1', '3'])).
% 0.77/1.02  thf('5', plain,
% 0.77/1.02      (![X4 : $i, X6 : $i]:
% 0.77/1.02         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.77/1.02      inference('cnf', [status(esa)], [d3_tarski])).
% 0.77/1.02  thf('6', plain,
% 0.77/1.02      (![X0 : $i, X1 : $i]:
% 0.77/1.02         ((r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.77/1.02          | (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.77/1.02      inference('sup-', [status(thm)], ['4', '5'])).
% 0.77/1.02  thf('7', plain,
% 0.77/1.02      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.77/1.02      inference('simplify', [status(thm)], ['6'])).
% 0.77/1.02  thf('8', plain, ((r1_tarski @ sk_C_2 @ (k1_tarski @ sk_A))),
% 0.77/1.02      inference('sup+', [status(thm)], ['0', '7'])).
% 0.77/1.02  thf(l3_zfmisc_1, axiom,
% 0.77/1.02    (![A:$i,B:$i]:
% 0.77/1.02     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.77/1.02       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.77/1.02  thf('9', plain,
% 0.77/1.02      (![X33 : $i, X34 : $i]:
% 0.77/1.02         (((X34) = (k1_tarski @ X33))
% 0.77/1.02          | ((X34) = (k1_xboole_0))
% 0.77/1.02          | ~ (r1_tarski @ X34 @ (k1_tarski @ X33)))),
% 0.77/1.02      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.77/1.02  thf('10', plain,
% 0.77/1.02      ((((sk_C_2) = (k1_xboole_0)) | ((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.77/1.02      inference('sup-', [status(thm)], ['8', '9'])).
% 0.77/1.02  thf('11', plain,
% 0.77/1.02      ((((sk_B_2) != (k1_xboole_0)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.77/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.02  thf('12', plain,
% 0.77/1.02      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 0.77/1.02         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.77/1.02      inference('split', [status(esa)], ['11'])).
% 0.77/1.02  thf('13', plain,
% 0.77/1.02      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B_2) = (k1_xboole_0)))),
% 0.77/1.02      inference('split', [status(esa)], ['11'])).
% 0.77/1.02  thf('14', plain,
% 0.77/1.02      ((((sk_B_2) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.77/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.02  thf('15', plain,
% 0.77/1.02      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | 
% 0.77/1.02       ~ (((sk_B_2) = (k1_tarski @ sk_A)))),
% 0.77/1.02      inference('split', [status(esa)], ['14'])).
% 0.77/1.02  thf('16', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_2 @ sk_C_2))),
% 0.77/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.02  thf(t7_xboole_1, axiom,
% 0.77/1.02    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.77/1.02  thf('17', plain,
% 0.77/1.02      (![X16 : $i, X17 : $i]: (r1_tarski @ X16 @ (k2_xboole_0 @ X16 @ X17))),
% 0.77/1.02      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.77/1.02  thf('18', plain, ((r1_tarski @ sk_B_2 @ (k1_tarski @ sk_A))),
% 0.77/1.02      inference('sup+', [status(thm)], ['16', '17'])).
% 0.77/1.02  thf('19', plain,
% 0.77/1.02      (![X33 : $i, X34 : $i]:
% 0.77/1.02         (((X34) = (k1_tarski @ X33))
% 0.77/1.02          | ((X34) = (k1_xboole_0))
% 0.77/1.02          | ~ (r1_tarski @ X34 @ (k1_tarski @ X33)))),
% 0.77/1.02      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.77/1.02  thf('20', plain,
% 0.77/1.02      ((((sk_B_2) = (k1_xboole_0)) | ((sk_B_2) = (k1_tarski @ sk_A)))),
% 0.77/1.02      inference('sup-', [status(thm)], ['18', '19'])).
% 0.77/1.02  thf('21', plain,
% 0.77/1.02      ((((sk_B_2) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_xboole_0)))),
% 0.77/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.02  thf('22', plain,
% 0.77/1.02      ((((sk_B_2) != (k1_tarski @ sk_A)))
% 0.77/1.02         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.77/1.02      inference('split', [status(esa)], ['21'])).
% 0.77/1.02  thf('23', plain,
% 0.77/1.02      (((((sk_B_2) != (sk_B_2)) | ((sk_B_2) = (k1_xboole_0))))
% 0.77/1.02         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.77/1.02      inference('sup-', [status(thm)], ['20', '22'])).
% 0.77/1.02  thf('24', plain,
% 0.77/1.02      ((((sk_B_2) = (k1_xboole_0))) <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.77/1.02      inference('simplify', [status(thm)], ['23'])).
% 0.77/1.02  thf('25', plain,
% 0.77/1.02      ((((sk_B_2) != (k1_xboole_0))) <= (~ (((sk_B_2) = (k1_xboole_0))))),
% 0.77/1.02      inference('split', [status(esa)], ['11'])).
% 0.77/1.02  thf('26', plain,
% 0.77/1.02      ((((sk_B_2) != (sk_B_2)))
% 0.77/1.02         <= (~ (((sk_B_2) = (k1_xboole_0))) & 
% 0.77/1.02             ~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.77/1.02      inference('sup-', [status(thm)], ['24', '25'])).
% 0.77/1.02  thf('27', plain,
% 0.77/1.02      ((((sk_B_2) = (k1_xboole_0))) | (((sk_B_2) = (k1_tarski @ sk_A)))),
% 0.77/1.02      inference('simplify', [status(thm)], ['26'])).
% 0.77/1.02  thf('28', plain, (~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.77/1.02      inference('sat_resolution*', [status(thm)], ['13', '15', '27'])).
% 0.77/1.02  thf('29', plain, (((sk_C_2) != (k1_tarski @ sk_A))),
% 0.77/1.02      inference('simpl_trail', [status(thm)], ['12', '28'])).
% 0.77/1.02  thf('30', plain,
% 0.77/1.02      ((((sk_C_2) != (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 0.77/1.02      inference('split', [status(esa)], ['21'])).
% 0.77/1.02  thf(d1_xboole_0, axiom,
% 0.77/1.02    (![A:$i]:
% 0.77/1.02     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.77/1.02  thf('31', plain,
% 0.77/1.02      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.77/1.02      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.77/1.02  thf('32', plain,
% 0.77/1.02      (![X34 : $i, X35 : $i]:
% 0.77/1.02         ((r1_tarski @ X34 @ (k1_tarski @ X35)) | ((X34) != (k1_xboole_0)))),
% 0.77/1.02      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.77/1.02  thf('33', plain,
% 0.77/1.02      (![X35 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X35))),
% 0.77/1.02      inference('simplify', [status(thm)], ['32'])).
% 0.77/1.02  thf('34', plain,
% 0.77/1.02      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.77/1.02         (~ (r2_hidden @ X3 @ X4)
% 0.77/1.02          | (r2_hidden @ X3 @ X5)
% 0.77/1.02          | ~ (r1_tarski @ X4 @ X5))),
% 0.77/1.02      inference('cnf', [status(esa)], [d3_tarski])).
% 0.77/1.02  thf('35', plain,
% 0.77/1.02      (![X0 : $i, X1 : $i]:
% 0.77/1.02         ((r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.77/1.02          | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.77/1.02      inference('sup-', [status(thm)], ['33', '34'])).
% 0.77/1.02  thf('36', plain,
% 0.77/1.02      (![X0 : $i]:
% 0.77/1.02         ((v1_xboole_0 @ k1_xboole_0)
% 0.77/1.02          | (r2_hidden @ (sk_B @ k1_xboole_0) @ (k1_tarski @ X0)))),
% 0.77/1.02      inference('sup-', [status(thm)], ['31', '35'])).
% 0.77/1.02  thf(d1_tarski, axiom,
% 0.77/1.02    (![A:$i,B:$i]:
% 0.77/1.02     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.77/1.02       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.77/1.02  thf('37', plain,
% 0.77/1.02      (![X18 : $i, X20 : $i, X21 : $i]:
% 0.77/1.02         (~ (r2_hidden @ X21 @ X20)
% 0.77/1.02          | ((X21) = (X18))
% 0.77/1.02          | ((X20) != (k1_tarski @ X18)))),
% 0.77/1.02      inference('cnf', [status(esa)], [d1_tarski])).
% 0.77/1.02  thf('38', plain,
% 0.77/1.02      (![X18 : $i, X21 : $i]:
% 0.77/1.02         (((X21) = (X18)) | ~ (r2_hidden @ X21 @ (k1_tarski @ X18)))),
% 0.77/1.02      inference('simplify', [status(thm)], ['37'])).
% 0.77/1.02  thf('39', plain,
% 0.77/1.02      (![X0 : $i]:
% 0.77/1.02         ((v1_xboole_0 @ k1_xboole_0) | ((sk_B @ k1_xboole_0) = (X0)))),
% 0.77/1.02      inference('sup-', [status(thm)], ['36', '38'])).
% 0.77/1.02  thf('40', plain,
% 0.77/1.02      (![X0 : $i]:
% 0.77/1.02         ((v1_xboole_0 @ k1_xboole_0) | ((sk_B @ k1_xboole_0) = (X0)))),
% 0.77/1.02      inference('sup-', [status(thm)], ['36', '38'])).
% 0.77/1.02  thf('41', plain,
% 0.77/1.02      (![X0 : $i, X1 : $i]:
% 0.77/1.02         (((X0) = (X1))
% 0.77/1.02          | (v1_xboole_0 @ k1_xboole_0)
% 0.77/1.02          | (v1_xboole_0 @ k1_xboole_0))),
% 0.77/1.02      inference('sup+', [status(thm)], ['39', '40'])).
% 0.77/1.02  thf('42', plain,
% 0.77/1.02      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ k1_xboole_0) | ((X0) = (X1)))),
% 0.77/1.02      inference('simplify', [status(thm)], ['41'])).
% 0.77/1.02  thf('43', plain,
% 0.77/1.02      ((((sk_B_2) = (k1_xboole_0))) <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.77/1.02      inference('simplify', [status(thm)], ['23'])).
% 0.77/1.02  thf(t7_xboole_0, axiom,
% 0.77/1.02    (![A:$i]:
% 0.77/1.02     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.77/1.02          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.77/1.02  thf('44', plain,
% 0.77/1.02      (![X13 : $i]:
% 0.77/1.02         (((X13) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X13) @ X13))),
% 0.77/1.02      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.77/1.02  thf('45', plain,
% 0.77/1.02      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.77/1.02      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.77/1.02  thf('46', plain,
% 0.77/1.02      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.77/1.02      inference('sup-', [status(thm)], ['44', '45'])).
% 0.77/1.02  thf('47', plain,
% 0.77/1.02      ((![X0 : $i]: (((X0) = (sk_B_2)) | ~ (v1_xboole_0 @ X0)))
% 0.77/1.02         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.77/1.02      inference('sup+', [status(thm)], ['43', '46'])).
% 0.77/1.02  thf('48', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_2 @ sk_C_2))),
% 0.77/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.02  thf('49', plain,
% 0.77/1.02      (![X4 : $i, X6 : $i]:
% 0.77/1.02         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.77/1.02      inference('cnf', [status(esa)], [d3_tarski])).
% 0.77/1.02  thf('50', plain,
% 0.77/1.02      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.77/1.02      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.77/1.02  thf('51', plain,
% 0.77/1.02      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.77/1.02      inference('sup-', [status(thm)], ['49', '50'])).
% 0.77/1.02  thf(t12_xboole_1, axiom,
% 0.77/1.02    (![A:$i,B:$i]:
% 0.77/1.02     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.77/1.02  thf('52', plain,
% 0.77/1.02      (![X14 : $i, X15 : $i]:
% 0.77/1.02         (((k2_xboole_0 @ X15 @ X14) = (X14)) | ~ (r1_tarski @ X15 @ X14))),
% 0.77/1.02      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.77/1.02  thf('53', plain,
% 0.77/1.02      (![X0 : $i, X1 : $i]:
% 0.77/1.02         (~ (v1_xboole_0 @ X1) | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 0.77/1.02      inference('sup-', [status(thm)], ['51', '52'])).
% 0.77/1.02  thf('54', plain,
% 0.77/1.02      ((((k1_tarski @ sk_A) = (sk_C_2)) | ~ (v1_xboole_0 @ sk_B_2))),
% 0.77/1.02      inference('sup+', [status(thm)], ['48', '53'])).
% 0.77/1.02  thf('55', plain, (((sk_C_2) != (k1_tarski @ sk_A))),
% 0.77/1.02      inference('simpl_trail', [status(thm)], ['12', '28'])).
% 0.77/1.02  thf('56', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.77/1.02      inference('simplify_reflect-', [status(thm)], ['54', '55'])).
% 0.77/1.02  thf('57', plain,
% 0.77/1.02      ((![X0 : $i]: (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0)))
% 0.77/1.02         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.77/1.02      inference('sup-', [status(thm)], ['47', '56'])).
% 0.77/1.02  thf('58', plain,
% 0.77/1.02      ((![X0 : $i]: ~ (v1_xboole_0 @ X0))
% 0.77/1.02         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.77/1.02      inference('simplify', [status(thm)], ['57'])).
% 0.77/1.02  thf('59', plain,
% 0.77/1.02      ((![X0 : $i, X1 : $i]: ((X0) = (X1)))
% 0.77/1.02         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.77/1.02      inference('sup-', [status(thm)], ['42', '58'])).
% 0.77/1.02  thf('60', plain,
% 0.77/1.02      ((((sk_B_2) != (k1_tarski @ sk_A)))
% 0.77/1.02         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.77/1.02      inference('split', [status(esa)], ['21'])).
% 0.77/1.02  thf('61', plain,
% 0.77/1.02      ((![X0 : $i]: ((sk_B_2) != (X0)))
% 0.77/1.02         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.77/1.02      inference('sup-', [status(thm)], ['59', '60'])).
% 0.77/1.02  thf('62', plain, ((((sk_B_2) = (k1_tarski @ sk_A)))),
% 0.77/1.02      inference('simplify', [status(thm)], ['61'])).
% 0.77/1.02  thf('63', plain,
% 0.77/1.02      (~ (((sk_C_2) = (k1_xboole_0))) | ~ (((sk_B_2) = (k1_tarski @ sk_A)))),
% 0.77/1.02      inference('split', [status(esa)], ['21'])).
% 0.77/1.02  thf('64', plain, (~ (((sk_C_2) = (k1_xboole_0)))),
% 0.77/1.02      inference('sat_resolution*', [status(thm)], ['62', '63'])).
% 0.77/1.02  thf('65', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.77/1.02      inference('simpl_trail', [status(thm)], ['30', '64'])).
% 0.77/1.02  thf('66', plain, ($false),
% 0.77/1.02      inference('simplify_reflect-', [status(thm)], ['10', '29', '65'])).
% 0.77/1.02  
% 0.77/1.02  % SZS output end Refutation
% 0.77/1.02  
% 0.87/1.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
