%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8U3eqWLNkg

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:43 EST 2020

% Result     : Theorem 1.23s
% Output     : Refutation 1.23s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 201 expanded)
%              Number of leaves         :   31 (  67 expanded)
%              Depth                    :   17
%              Number of atoms          :  675 (1425 expanded)
%              Number of equality atoms :   49 ( 129 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t13_ordinal1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
      <=> ( ( r2_hidden @ A @ B )
          | ( A = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t13_ordinal1])).

thf('0',plain,
    ( ( sk_A = sk_B )
    | ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_A != sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( sk_A != sk_B )
   <= ( sk_A != sk_B ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,
    ( ( sk_A != sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['1'])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('4',plain,(
    ! [X42: $i] :
      ( r2_hidden @ X42 @ ( k1_ordinal1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('5',plain,
    ( ( sk_A = sk_B )
    | ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
    | ( sk_A != sk_B ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    sk_A != sk_B ),
    inference('sat_resolution*',[status(thm)],['3','10'])).

thf('12',plain,(
    sk_A != sk_B ),
    inference(simpl_trail,[status(thm)],['2','11'])).

thf('13',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['0','12'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('14',plain,(
    ! [X41: $i] :
      ( ( k1_ordinal1 @ X41 )
      = ( k2_xboole_0 @ X41 @ ( k1_tarski @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ),
    inference(clc,[status(thm)],['13','18'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('20',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('21',plain,(
    ! [X41: $i] :
      ( ( k1_ordinal1 @ X41 )
      = ( k2_xboole_0 @ X41 @ ( k1_tarski @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k1_ordinal1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( ~ ( r2_hidden @ C @ A )
            & ( r2_hidden @ C @ B ) )
        & ~ ( ~ ( r2_hidden @ C @ B )
            & ( r2_hidden @ C @ A ) )
        & ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( r2_hidden @ C @ A )
        & ~ ( r2_hidden @ C @ B ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
     => ( ( r2_hidden @ C @ B )
        & ~ ( r2_hidden @ C @ A ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ A @ B )
        & ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) )
        & ~ ( zip_tseitin_1 @ C @ B @ A )
        & ~ ( zip_tseitin_0 @ C @ B @ A ) ) )).

thf('23',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_xboole_0 @ X10 @ X11 )
      | ( zip_tseitin_0 @ X12 @ X11 @ X10 )
      | ( zip_tseitin_1 @ X12 @ X11 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( zip_tseitin_1 @ X1 @ ( k2_tarski @ X0 @ X0 ) @ X0 )
      | ( zip_tseitin_0 @ X1 @ ( k2_tarski @ X0 @ X0 ) @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ ( k2_tarski @ sk_B @ sk_B ) )
    | ( zip_tseitin_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_B ) @ sk_B )
    | ( zip_tseitin_1 @ sk_A @ ( k2_tarski @ sk_B @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('27',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('28',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('29',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_B ) )
    | ( zip_tseitin_0 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_B )
    | ( zip_tseitin_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('30',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_enumset1 @ X27 @ X27 @ X28 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('31',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('34',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k4_xboole_0 @ X39 @ ( k1_tarski @ X40 ) )
        = X39 )
      | ( r2_hidden @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('35',plain,(
    ! [X18: $i,X20: $i] :
      ( ( r1_xboole_0 @ X18 @ X20 )
      | ( ( k4_xboole_0 @ X18 @ X20 )
       != X18 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_enumset1 @ X0 @ X0 @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','37'])).

thf('39',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('40',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('41',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('42',plain,(
    ! [X21: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X24 @ X23 )
      | ( X24 = X21 )
      | ( X23
       != ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('43',plain,(
    ! [X21: $i,X24: $i] :
      ( ( X24 = X21 )
      | ~ ( r2_hidden @ X24 @ ( k1_tarski @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X1 @ ( k2_tarski @ X0 @ X0 ) )
        = X0 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','44'])).

thf('46',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( X22 != X21 )
      | ( r2_hidden @ X22 @ X23 )
      | ( X23
       != ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('47',plain,(
    ! [X21: $i] :
      ( r2_hidden @ X21 @ ( k1_tarski @ X21 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('48',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( r2_hidden @ X43 @ X44 )
      | ~ ( r1_tarski @ X44 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('49',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( sk_C @ X0 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['45','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( sk_C @ X0 @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['39','50'])).

thf('52',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('55',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ X0 ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k1_enumset1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','56'])).

thf('58',plain,
    ( ( zip_tseitin_0 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_B )
    | ( zip_tseitin_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['29','57'])).

thf('59',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ~ ( zip_tseitin_1 @ X7 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('60',plain,
    ( ( zip_tseitin_0 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('62',plain,(
    r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ),
    inference(clc,[status(thm)],['13','18'])).

thf('63',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('64',plain,(
    r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('66',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['61','66'])).

thf('68',plain,(
    zip_tseitin_0 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['60','67'])).

thf('69',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ~ ( zip_tseitin_0 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('70',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X21: $i,X24: $i] :
      ( ( X24 = X21 )
      | ~ ( r2_hidden @ X24 @ ( k1_tarski @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('72',plain,(
    sk_A = sk_B ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    sk_A != sk_B ),
    inference(simpl_trail,[status(thm)],['2','11'])).

thf('74',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['72','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8U3eqWLNkg
% 0.14/0.37  % Computer   : n008.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 14:14:00 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 1.23/1.43  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.23/1.43  % Solved by: fo/fo7.sh
% 1.23/1.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.23/1.43  % done 2876 iterations in 0.944s
% 1.23/1.43  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.23/1.43  % SZS output start Refutation
% 1.23/1.43  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.23/1.43  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.23/1.43  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.23/1.43  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.23/1.43  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.23/1.43  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 1.23/1.43  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.23/1.43  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.23/1.43  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.23/1.43  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.23/1.43  thf(sk_A_type, type, sk_A: $i).
% 1.23/1.43  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 1.23/1.43  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.23/1.43  thf(sk_B_type, type, sk_B: $i).
% 1.23/1.43  thf(t13_ordinal1, conjecture,
% 1.23/1.43    (![A:$i,B:$i]:
% 1.23/1.43     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 1.23/1.43       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 1.23/1.43  thf(zf_stmt_0, negated_conjecture,
% 1.23/1.43    (~( ![A:$i,B:$i]:
% 1.23/1.43        ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 1.23/1.43          ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ) )),
% 1.23/1.43    inference('cnf.neg', [status(esa)], [t13_ordinal1])).
% 1.23/1.43  thf('0', plain,
% 1.23/1.43      ((((sk_A) = (sk_B))
% 1.23/1.43        | (r2_hidden @ sk_A @ sk_B)
% 1.23/1.43        | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 1.23/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.23/1.43  thf('1', plain,
% 1.23/1.43      ((((sk_A) != (sk_B)) | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 1.23/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.23/1.43  thf('2', plain, ((((sk_A) != (sk_B))) <= (~ (((sk_A) = (sk_B))))),
% 1.23/1.43      inference('split', [status(esa)], ['1'])).
% 1.23/1.43  thf('3', plain,
% 1.23/1.43      (~ (((sk_A) = (sk_B))) | ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 1.23/1.43      inference('split', [status(esa)], ['1'])).
% 1.23/1.43  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 1.23/1.43  thf('4', plain, (![X42 : $i]: (r2_hidden @ X42 @ (k1_ordinal1 @ X42))),
% 1.23/1.43      inference('cnf', [status(esa)], [t10_ordinal1])).
% 1.23/1.43  thf('5', plain,
% 1.23/1.43      ((((sk_A) = (sk_B))
% 1.23/1.43        | (r2_hidden @ sk_A @ sk_B)
% 1.23/1.43        | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 1.23/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.23/1.43  thf('6', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 1.23/1.43      inference('split', [status(esa)], ['5'])).
% 1.23/1.43  thf('7', plain,
% 1.23/1.43      ((~ (r2_hidden @ sk_A @ sk_B)
% 1.23/1.43        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 1.23/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.23/1.43  thf('8', plain,
% 1.23/1.43      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 1.23/1.43         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.23/1.43      inference('split', [status(esa)], ['7'])).
% 1.23/1.43  thf('9', plain,
% 1.23/1.43      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 1.23/1.43         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 1.23/1.43             (((sk_A) = (sk_B))))),
% 1.23/1.43      inference('sup-', [status(thm)], ['6', '8'])).
% 1.23/1.43  thf('10', plain,
% 1.23/1.43      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) | ~ (((sk_A) = (sk_B)))),
% 1.23/1.43      inference('sup-', [status(thm)], ['4', '9'])).
% 1.23/1.43  thf('11', plain, (~ (((sk_A) = (sk_B)))),
% 1.23/1.43      inference('sat_resolution*', [status(thm)], ['3', '10'])).
% 1.23/1.43  thf('12', plain, (((sk_A) != (sk_B))),
% 1.23/1.43      inference('simpl_trail', [status(thm)], ['2', '11'])).
% 1.23/1.43  thf('13', plain,
% 1.23/1.43      (((r2_hidden @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 1.23/1.43      inference('simplify_reflect-', [status(thm)], ['0', '12'])).
% 1.23/1.43  thf(d1_ordinal1, axiom,
% 1.23/1.43    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 1.23/1.43  thf('14', plain,
% 1.23/1.43      (![X41 : $i]:
% 1.23/1.43         ((k1_ordinal1 @ X41) = (k2_xboole_0 @ X41 @ (k1_tarski @ X41)))),
% 1.23/1.43      inference('cnf', [status(esa)], [d1_ordinal1])).
% 1.23/1.43  thf(t7_xboole_1, axiom,
% 1.23/1.43    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.23/1.43  thf('15', plain,
% 1.23/1.43      (![X16 : $i, X17 : $i]: (r1_tarski @ X16 @ (k2_xboole_0 @ X16 @ X17))),
% 1.23/1.43      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.23/1.43  thf('16', plain, (![X0 : $i]: (r1_tarski @ X0 @ (k1_ordinal1 @ X0))),
% 1.23/1.43      inference('sup+', [status(thm)], ['14', '15'])).
% 1.23/1.43  thf(d3_tarski, axiom,
% 1.23/1.43    (![A:$i,B:$i]:
% 1.23/1.43     ( ( r1_tarski @ A @ B ) <=>
% 1.23/1.43       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.23/1.43  thf('17', plain,
% 1.23/1.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.23/1.43         (~ (r2_hidden @ X0 @ X1)
% 1.23/1.43          | (r2_hidden @ X0 @ X2)
% 1.23/1.43          | ~ (r1_tarski @ X1 @ X2))),
% 1.23/1.43      inference('cnf', [status(esa)], [d3_tarski])).
% 1.23/1.43  thf('18', plain,
% 1.23/1.43      (![X0 : $i, X1 : $i]:
% 1.23/1.43         ((r2_hidden @ X1 @ (k1_ordinal1 @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 1.23/1.43      inference('sup-', [status(thm)], ['16', '17'])).
% 1.23/1.43  thf('19', plain, ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))),
% 1.23/1.43      inference('clc', [status(thm)], ['13', '18'])).
% 1.23/1.43  thf(t69_enumset1, axiom,
% 1.23/1.43    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.23/1.43  thf('20', plain,
% 1.23/1.43      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 1.23/1.43      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.23/1.43  thf('21', plain,
% 1.23/1.43      (![X41 : $i]:
% 1.23/1.43         ((k1_ordinal1 @ X41) = (k2_xboole_0 @ X41 @ (k1_tarski @ X41)))),
% 1.23/1.43      inference('cnf', [status(esa)], [d1_ordinal1])).
% 1.23/1.43  thf('22', plain,
% 1.23/1.43      (![X0 : $i]:
% 1.23/1.43         ((k1_ordinal1 @ X0) = (k2_xboole_0 @ X0 @ (k2_tarski @ X0 @ X0)))),
% 1.23/1.43      inference('sup+', [status(thm)], ['20', '21'])).
% 1.23/1.43  thf(t5_xboole_0, axiom,
% 1.23/1.43    (![A:$i,B:$i,C:$i]:
% 1.23/1.43     ( ~( ( ~( ( ~( r2_hidden @ C @ A ) ) & ( r2_hidden @ C @ B ) ) ) & 
% 1.23/1.43          ( ~( ( ~( r2_hidden @ C @ B ) ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.23/1.43          ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) ) & ( r1_xboole_0 @ A @ B ) ) ))).
% 1.23/1.43  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.23/1.43  thf(zf_stmt_2, axiom,
% 1.23/1.43    (![C:$i,B:$i,A:$i]:
% 1.23/1.43     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.23/1.43       ( ( r2_hidden @ C @ A ) & ( ~( r2_hidden @ C @ B ) ) ) ))).
% 1.23/1.43  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $o).
% 1.23/1.43  thf(zf_stmt_4, axiom,
% 1.23/1.43    (![C:$i,B:$i,A:$i]:
% 1.23/1.43     ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 1.23/1.43       ( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ))).
% 1.23/1.43  thf(zf_stmt_5, axiom,
% 1.23/1.43    (![A:$i,B:$i,C:$i]:
% 1.23/1.43     ( ~( ( r1_xboole_0 @ A @ B ) & 
% 1.23/1.43          ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) ) & 
% 1.23/1.43          ( ~( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.23/1.43          ( ~( zip_tseitin_0 @ C @ B @ A ) ) ) ))).
% 1.23/1.43  thf('23', plain,
% 1.23/1.43      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.23/1.43         (~ (r1_xboole_0 @ X10 @ X11)
% 1.23/1.43          | (zip_tseitin_0 @ X12 @ X11 @ X10)
% 1.23/1.43          | (zip_tseitin_1 @ X12 @ X11 @ X10)
% 1.23/1.43          | ~ (r2_hidden @ X12 @ (k2_xboole_0 @ X10 @ X11)))),
% 1.23/1.43      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.23/1.43  thf('24', plain,
% 1.23/1.43      (![X0 : $i, X1 : $i]:
% 1.23/1.43         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 1.23/1.43          | (zip_tseitin_1 @ X1 @ (k2_tarski @ X0 @ X0) @ X0)
% 1.23/1.43          | (zip_tseitin_0 @ X1 @ (k2_tarski @ X0 @ X0) @ X0)
% 1.23/1.43          | ~ (r1_xboole_0 @ X0 @ (k2_tarski @ X0 @ X0)))),
% 1.23/1.43      inference('sup-', [status(thm)], ['22', '23'])).
% 1.23/1.43  thf('25', plain,
% 1.23/1.43      ((~ (r1_xboole_0 @ sk_B @ (k2_tarski @ sk_B @ sk_B))
% 1.23/1.43        | (zip_tseitin_0 @ sk_A @ (k2_tarski @ sk_B @ sk_B) @ sk_B)
% 1.23/1.43        | (zip_tseitin_1 @ sk_A @ (k2_tarski @ sk_B @ sk_B) @ sk_B))),
% 1.23/1.43      inference('sup-', [status(thm)], ['19', '24'])).
% 1.23/1.43  thf('26', plain,
% 1.23/1.43      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 1.23/1.43      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.23/1.43  thf('27', plain,
% 1.23/1.43      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 1.23/1.43      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.23/1.43  thf('28', plain,
% 1.23/1.43      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 1.23/1.43      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.23/1.43  thf('29', plain,
% 1.23/1.43      ((~ (r1_xboole_0 @ sk_B @ (k1_tarski @ sk_B))
% 1.23/1.43        | (zip_tseitin_0 @ sk_A @ (k1_tarski @ sk_B) @ sk_B)
% 1.23/1.43        | (zip_tseitin_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_B))),
% 1.23/1.43      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 1.23/1.43  thf(t70_enumset1, axiom,
% 1.23/1.43    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.23/1.43  thf('30', plain,
% 1.23/1.43      (![X27 : $i, X28 : $i]:
% 1.23/1.43         ((k1_enumset1 @ X27 @ X27 @ X28) = (k2_tarski @ X27 @ X28))),
% 1.23/1.43      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.23/1.43  thf('31', plain,
% 1.23/1.43      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 1.23/1.43      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.23/1.43  thf('32', plain,
% 1.23/1.43      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 1.23/1.43      inference('sup+', [status(thm)], ['30', '31'])).
% 1.23/1.43  thf('33', plain,
% 1.23/1.43      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 1.23/1.43      inference('sup+', [status(thm)], ['30', '31'])).
% 1.23/1.43  thf(t65_zfmisc_1, axiom,
% 1.23/1.43    (![A:$i,B:$i]:
% 1.23/1.43     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 1.23/1.43       ( ~( r2_hidden @ B @ A ) ) ))).
% 1.23/1.43  thf('34', plain,
% 1.23/1.43      (![X39 : $i, X40 : $i]:
% 1.23/1.43         (((k4_xboole_0 @ X39 @ (k1_tarski @ X40)) = (X39))
% 1.23/1.43          | (r2_hidden @ X40 @ X39))),
% 1.23/1.43      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 1.23/1.43  thf(t83_xboole_1, axiom,
% 1.23/1.43    (![A:$i,B:$i]:
% 1.23/1.43     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.23/1.43  thf('35', plain,
% 1.23/1.43      (![X18 : $i, X20 : $i]:
% 1.23/1.43         ((r1_xboole_0 @ X18 @ X20) | ((k4_xboole_0 @ X18 @ X20) != (X18)))),
% 1.23/1.43      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.23/1.43  thf('36', plain,
% 1.23/1.43      (![X0 : $i, X1 : $i]:
% 1.23/1.43         (((X0) != (X0))
% 1.23/1.43          | (r2_hidden @ X1 @ X0)
% 1.23/1.43          | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 1.23/1.43      inference('sup-', [status(thm)], ['34', '35'])).
% 1.23/1.43  thf('37', plain,
% 1.23/1.43      (![X0 : $i, X1 : $i]:
% 1.23/1.43         ((r1_xboole_0 @ X0 @ (k1_tarski @ X1)) | (r2_hidden @ X1 @ X0))),
% 1.23/1.43      inference('simplify', [status(thm)], ['36'])).
% 1.23/1.43  thf('38', plain,
% 1.23/1.43      (![X0 : $i, X1 : $i]:
% 1.23/1.43         ((r1_xboole_0 @ X1 @ (k1_enumset1 @ X0 @ X0 @ X0))
% 1.23/1.43          | (r2_hidden @ X0 @ X1))),
% 1.23/1.43      inference('sup+', [status(thm)], ['33', '37'])).
% 1.23/1.43  thf('39', plain,
% 1.23/1.43      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 1.23/1.43      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.23/1.43  thf('40', plain,
% 1.23/1.43      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 1.23/1.43      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.23/1.43  thf('41', plain,
% 1.23/1.43      (![X1 : $i, X3 : $i]:
% 1.23/1.43         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.23/1.43      inference('cnf', [status(esa)], [d3_tarski])).
% 1.23/1.43  thf(d1_tarski, axiom,
% 1.23/1.43    (![A:$i,B:$i]:
% 1.23/1.43     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.23/1.43       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.23/1.43  thf('42', plain,
% 1.23/1.43      (![X21 : $i, X23 : $i, X24 : $i]:
% 1.23/1.43         (~ (r2_hidden @ X24 @ X23)
% 1.23/1.43          | ((X24) = (X21))
% 1.23/1.43          | ((X23) != (k1_tarski @ X21)))),
% 1.23/1.43      inference('cnf', [status(esa)], [d1_tarski])).
% 1.23/1.43  thf('43', plain,
% 1.23/1.43      (![X21 : $i, X24 : $i]:
% 1.23/1.43         (((X24) = (X21)) | ~ (r2_hidden @ X24 @ (k1_tarski @ X21)))),
% 1.23/1.43      inference('simplify', [status(thm)], ['42'])).
% 1.23/1.43  thf('44', plain,
% 1.23/1.43      (![X0 : $i, X1 : $i]:
% 1.23/1.43         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 1.23/1.43          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 1.23/1.43      inference('sup-', [status(thm)], ['41', '43'])).
% 1.23/1.43  thf('45', plain,
% 1.23/1.43      (![X0 : $i, X1 : $i]:
% 1.23/1.43         (((sk_C @ X1 @ (k2_tarski @ X0 @ X0)) = (X0))
% 1.23/1.43          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 1.23/1.43      inference('sup+', [status(thm)], ['40', '44'])).
% 1.23/1.43  thf('46', plain,
% 1.23/1.43      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.23/1.43         (((X22) != (X21))
% 1.23/1.43          | (r2_hidden @ X22 @ X23)
% 1.23/1.43          | ((X23) != (k1_tarski @ X21)))),
% 1.23/1.43      inference('cnf', [status(esa)], [d1_tarski])).
% 1.23/1.43  thf('47', plain, (![X21 : $i]: (r2_hidden @ X21 @ (k1_tarski @ X21))),
% 1.23/1.43      inference('simplify', [status(thm)], ['46'])).
% 1.23/1.43  thf(t7_ordinal1, axiom,
% 1.23/1.43    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.23/1.43  thf('48', plain,
% 1.23/1.43      (![X43 : $i, X44 : $i]:
% 1.23/1.43         (~ (r2_hidden @ X43 @ X44) | ~ (r1_tarski @ X44 @ X43))),
% 1.23/1.43      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.23/1.43  thf('49', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ X0)),
% 1.23/1.43      inference('sup-', [status(thm)], ['47', '48'])).
% 1.23/1.43  thf('50', plain, (![X0 : $i]: ((sk_C @ X0 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 1.23/1.43      inference('sup-', [status(thm)], ['45', '49'])).
% 1.23/1.43  thf('51', plain, (![X0 : $i]: ((sk_C @ X0 @ (k1_tarski @ X0)) = (X0))),
% 1.23/1.43      inference('sup+', [status(thm)], ['39', '50'])).
% 1.23/1.43  thf('52', plain,
% 1.23/1.43      (![X1 : $i, X3 : $i]:
% 1.23/1.43         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.23/1.43      inference('cnf', [status(esa)], [d3_tarski])).
% 1.23/1.43  thf('53', plain,
% 1.23/1.43      (![X0 : $i]:
% 1.23/1.43         (~ (r2_hidden @ X0 @ X0) | (r1_tarski @ (k1_tarski @ X0) @ X0))),
% 1.23/1.43      inference('sup-', [status(thm)], ['51', '52'])).
% 1.23/1.43  thf('54', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ X0)),
% 1.23/1.43      inference('sup-', [status(thm)], ['47', '48'])).
% 1.23/1.43  thf('55', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ X0)),
% 1.23/1.43      inference('clc', [status(thm)], ['53', '54'])).
% 1.23/1.43  thf('56', plain,
% 1.23/1.43      (![X0 : $i]: (r1_xboole_0 @ X0 @ (k1_enumset1 @ X0 @ X0 @ X0))),
% 1.23/1.43      inference('sup-', [status(thm)], ['38', '55'])).
% 1.23/1.43  thf('57', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ (k1_tarski @ X0))),
% 1.23/1.43      inference('sup+', [status(thm)], ['32', '56'])).
% 1.23/1.43  thf('58', plain,
% 1.23/1.43      (((zip_tseitin_0 @ sk_A @ (k1_tarski @ sk_B) @ sk_B)
% 1.23/1.43        | (zip_tseitin_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_B))),
% 1.23/1.43      inference('demod', [status(thm)], ['29', '57'])).
% 1.23/1.43  thf('59', plain,
% 1.23/1.43      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.23/1.43         ((r2_hidden @ X7 @ X8) | ~ (zip_tseitin_1 @ X7 @ X9 @ X8))),
% 1.23/1.43      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.23/1.43  thf('60', plain,
% 1.23/1.43      (((zip_tseitin_0 @ sk_A @ (k1_tarski @ sk_B) @ sk_B)
% 1.23/1.43        | (r2_hidden @ sk_A @ sk_B))),
% 1.23/1.43      inference('sup-', [status(thm)], ['58', '59'])).
% 1.23/1.43  thf('61', plain,
% 1.23/1.43      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 1.23/1.43      inference('split', [status(esa)], ['7'])).
% 1.23/1.43  thf('62', plain, ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))),
% 1.23/1.43      inference('clc', [status(thm)], ['13', '18'])).
% 1.23/1.43  thf('63', plain,
% 1.23/1.43      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 1.23/1.43         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.23/1.43      inference('split', [status(esa)], ['7'])).
% 1.23/1.43  thf('64', plain, (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 1.23/1.43      inference('sup-', [status(thm)], ['62', '63'])).
% 1.23/1.43  thf('65', plain,
% 1.23/1.43      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 1.23/1.43       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 1.23/1.43      inference('split', [status(esa)], ['7'])).
% 1.23/1.43  thf('66', plain, (~ ((r2_hidden @ sk_A @ sk_B))),
% 1.23/1.43      inference('sat_resolution*', [status(thm)], ['64', '65'])).
% 1.23/1.43  thf('67', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 1.23/1.43      inference('simpl_trail', [status(thm)], ['61', '66'])).
% 1.23/1.43  thf('68', plain, ((zip_tseitin_0 @ sk_A @ (k1_tarski @ sk_B) @ sk_B)),
% 1.23/1.43      inference('clc', [status(thm)], ['60', '67'])).
% 1.23/1.43  thf('69', plain,
% 1.23/1.43      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.23/1.43         ((r2_hidden @ X4 @ X5) | ~ (zip_tseitin_0 @ X4 @ X5 @ X6))),
% 1.23/1.43      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.23/1.43  thf('70', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 1.23/1.43      inference('sup-', [status(thm)], ['68', '69'])).
% 1.23/1.43  thf('71', plain,
% 1.23/1.43      (![X21 : $i, X24 : $i]:
% 1.23/1.43         (((X24) = (X21)) | ~ (r2_hidden @ X24 @ (k1_tarski @ X21)))),
% 1.23/1.43      inference('simplify', [status(thm)], ['42'])).
% 1.23/1.43  thf('72', plain, (((sk_A) = (sk_B))),
% 1.23/1.43      inference('sup-', [status(thm)], ['70', '71'])).
% 1.23/1.43  thf('73', plain, (((sk_A) != (sk_B))),
% 1.23/1.43      inference('simpl_trail', [status(thm)], ['2', '11'])).
% 1.23/1.43  thf('74', plain, ($false),
% 1.23/1.43      inference('simplify_reflect-', [status(thm)], ['72', '73'])).
% 1.23/1.43  
% 1.23/1.43  % SZS output end Refutation
% 1.23/1.43  
% 1.23/1.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
