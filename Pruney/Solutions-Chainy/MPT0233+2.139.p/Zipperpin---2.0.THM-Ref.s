%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OPKo9dK9Rg

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:52 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 969 expanded)
%              Number of leaves         :   21 ( 285 expanded)
%              Depth                    :   49
%              Number of atoms          : 1415 (11942 expanded)
%              Number of equality atoms :  237 (1963 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t28_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
        & ( A != C )
        & ( A != D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
          & ( A != C )
          & ( A != D ) ) ),
    inference('cnf.neg',[status(esa)],[t28_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( X25
        = ( k2_tarski @ X23 @ X24 ) )
      | ( X25
        = ( k1_tarski @ X24 ) )
      | ( X25
        = ( k1_tarski @ X23 ) )
      | ( X25 = k1_xboole_0 )
      | ~ ( r1_tarski @ X25 @ ( k2_tarski @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('3',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X23: $i,X25: $i,X26: $i] :
      ( ( r1_tarski @ X25 @ ( k2_tarski @ X23 @ X26 ) )
      | ( X25
       != ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('5',plain,(
    ! [X23: $i,X26: $i] :
      ( r1_tarski @ ( k1_tarski @ X23 ) @ ( k2_tarski @ X23 @ X26 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_A @ sk_B ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( X25
        = ( k2_tarski @ X23 @ X24 ) )
      | ( X25
        = ( k1_tarski @ X24 ) )
      | ( X25
        = ( k1_tarski @ X23 ) )
      | ( X25 = k1_xboole_0 )
      | ~ ( r1_tarski @ X25 @ ( k2_tarski @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('8',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D ) )
    | ( ( k1_tarski @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ sk_B ) )
    | ( ( k1_tarski @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ sk_B ) )
    | ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X23: $i,X26: $i] :
      ( r1_tarski @ ( k1_tarski @ X23 ) @ ( k2_tarski @ X23 @ X26 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('11',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_D ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k1_tarski @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('12',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t26_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
     => ( A = C ) ) )).

thf('13',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( X28 = X27 )
      | ~ ( r1_tarski @ ( k2_tarski @ X28 @ X29 ) @ ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t26_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ sk_B ) )
    | ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_A = sk_D ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    sk_A != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ sk_B ) )
    | ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X23: $i,X26: $i] :
      ( r1_tarski @ ( k1_tarski @ X23 ) @ ( k2_tarski @ X23 @ X26 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('19',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('21',plain,
    ( ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ sk_B ) )
    | ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ sk_B ) )
    | ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( X28 = X27 )
      | ~ ( r1_tarski @ ( k2_tarski @ X28 @ X29 ) @ ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t26_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ sk_C )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_C )
        = ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_C )
        = ( k1_tarski @ sk_B ) )
      | ( sk_A = X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_C )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_C )
        = ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_C )
        = ( k1_tarski @ sk_B ) )
      | ( sk_A = X0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_C )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_C )
        = ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_C )
        = ( k1_tarski @ sk_B ) )
      | ( sk_A = X0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( ( k1_tarski @ sk_C )
        = ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_C )
        = ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_C )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_C )
        = ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_C )
        = ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_C )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ sk_C )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_C )
        = ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_C )
        = ( k1_tarski @ sk_B ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_C )
       != X0 )
      | ( ( k1_tarski @ sk_B )
        = X0 )
      | ( ( k1_tarski @ sk_C )
        = ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_C )
        = k1_xboole_0 ) ) ),
    inference(eq_fact,[status(thm)],['30'])).

thf('32',plain,
    ( ( ( k1_tarski @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_B )
      = ( k1_tarski @ sk_C ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('34',plain,(
    ! [X23: $i,X26: $i] :
      ( r1_tarski @ ( k1_tarski @ X23 ) @ ( k2_tarski @ X23 @ X26 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_C ) )
    | ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('38',plain,
    ( ( ( k1_tarski @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( sk_B = sk_C ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('40',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_A ) )
    | ( sk_B = sk_C )
    | ( ( k1_tarski @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('42',plain,
    ( ( ( k1_tarski @ sk_C )
      = k1_xboole_0 )
    | ( sk_B = sk_C )
    | ( sk_C = sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( ( k1_tarski @ sk_C )
      = k1_xboole_0 )
    | ( sk_B = sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( sk_B = sk_C )
      | ( sk_C = X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( sk_B = sk_C )
      | ( sk_C = X0 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    sk_B = sk_C ),
    inference(condensation,[status(thm)],['48'])).

thf('50',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_C ) @ ( k2_tarski @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','49'])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('51',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( zip_tseitin_0 @ X2 @ X3 @ X4 @ X5 )
      | ( X2 = X3 )
      | ( X2 = X4 )
      | ( X2 = X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('52',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( zip_tseitin_0 @ X2 @ X3 @ X4 @ X5 )
      | ( X2 = X3 )
      | ( X2 = X4 )
      | ( X2 = X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('53',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( zip_tseitin_0 @ X2 @ X3 @ X4 @ X5 )
      | ( X2 = X3 )
      | ( X2 = X4 )
      | ( X2 = X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('54',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('55',plain,(
    sk_B = sk_C ),
    inference(condensation,[status(thm)],['48'])).

thf('56',plain,(
    sk_B = sk_C ),
    inference(condensation,[status(thm)],['48'])).

thf('57',plain,(
    sk_B = sk_C ),
    inference(condensation,[status(thm)],['48'])).

thf('58',plain,(
    sk_B = sk_C ),
    inference(condensation,[status(thm)],['48'])).

thf('59',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_D ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['54','55','56','57','58'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('60',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_enumset1 @ X14 @ X14 @ X15 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('61',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 )
      | ( r2_hidden @ X6 @ X10 )
      | ( X10
       != ( k1_enumset1 @ X9 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('62',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X6 @ ( k1_enumset1 @ X9 @ X8 @ X7 ) )
      | ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['60','62'])).

thf('64',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X2 != X3 )
      | ~ ( zip_tseitin_0 @ X2 @ X3 @ X4 @ X1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('65',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ~ ( zip_tseitin_0 @ X3 @ X3 @ X4 @ X1 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['63','65'])).

thf('67',plain,
    ( ( r2_hidden @ sk_D @ ( k2_tarski @ sk_A @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_D ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['59','66'])).

thf('68',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_enumset1 @ X14 @ X14 @ X15 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('69',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ~ ( zip_tseitin_0 @ X11 @ X7 @ X8 @ X9 )
      | ( X10
       != ( k1_enumset1 @ X9 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('70',plain,(
    ! [X7: $i,X8: $i,X9: $i,X11: $i] :
      ( ~ ( zip_tseitin_0 @ X11 @ X7 @ X8 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k1_enumset1 @ X9 @ X8 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['68','70'])).

thf('72',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_D ) )
    | ~ ( zip_tseitin_0 @ sk_D @ sk_C @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['67','71'])).

thf('73',plain,
    ( ( sk_D = sk_A )
    | ( sk_D = sk_A )
    | ( sk_D = sk_C )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_D ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','72'])).

thf('74',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_D ) )
    | ( sk_D = sk_C )
    | ( sk_D = sk_A ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    sk_A != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_D ) )
    | ( sk_D = sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['60','62'])).

thf('78',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X2 != X1 )
      | ~ ( zip_tseitin_0 @ X2 @ X3 @ X4 @ X1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('79',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ~ ( zip_tseitin_0 @ X1 @ X3 @ X4 @ X1 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['77','79'])).

thf('81',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_D ) )
    | ( sk_D = sk_C )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['76','80'])).

thf('82',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_enumset1 @ X14 @ X14 @ X15 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('83',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X7: $i,X8: $i,X9: $i,X11: $i] :
      ( ~ ( zip_tseitin_0 @ X11 @ X7 @ X8 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k1_enumset1 @ X9 @ X8 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( sk_D = sk_C )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_D @ sk_D @ sk_D ) ),
    inference('sup-',[status(thm)],['81','86'])).

thf('88',plain,
    ( ( sk_A = sk_D )
    | ( sk_A = sk_D )
    | ( sk_A = sk_D )
    | ( sk_D = sk_C )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','87'])).

thf('89',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( sk_D = sk_C )
    | ( sk_A = sk_D ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    sk_A != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( sk_D = sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['77','79'])).

thf('93',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C ) )
    | ( sk_D = sk_C )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('95',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( sk_D = sk_C )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_C @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_C )
    | ( sk_A = sk_C )
    | ( sk_D = sk_C )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','95'])).

thf('97',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( sk_D = sk_C )
    | ( sk_A = sk_C ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( sk_D = sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( X28 = X27 )
      | ~ ( r1_tarski @ ( k2_tarski @ X28 @ X29 ) @ ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t26_zfmisc_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( sk_D = sk_C )
      | ( sk_A = X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( sk_D = sk_C )
      | ( sk_A = X0 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    sk_B = sk_C ),
    inference(condensation,[status(thm)],['48'])).

thf('105',plain,
    ( ( sk_A = sk_C )
    | ( sk_D = sk_C ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    sk_D = sk_C ),
    inference('simplify_reflect-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('109',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_C ) @ ( k1_tarski @ sk_C ) ),
    inference(demod,[status(thm)],['50','107','108'])).

thf('110',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( X28 = X27 )
      | ~ ( r1_tarski @ ( k2_tarski @ X28 @ X29 ) @ ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t26_zfmisc_1])).

thf('111',plain,(
    sk_A = sk_C ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['111','112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OPKo9dK9Rg
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:56:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.41/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.62  % Solved by: fo/fo7.sh
% 0.41/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.62  % done 232 iterations in 0.168s
% 0.41/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.62  % SZS output start Refutation
% 0.41/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.62  thf(sk_D_type, type, sk_D: $i).
% 0.41/0.62  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.41/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.41/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.41/0.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.41/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.62  thf(t28_zfmisc_1, conjecture,
% 0.41/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.62     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.41/0.62          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.41/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.62    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.62        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.41/0.62             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.41/0.62    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 0.41/0.62  thf('0', plain,
% 0.41/0.62      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('1', plain,
% 0.41/0.62      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(l45_zfmisc_1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.41/0.62       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.41/0.62            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.41/0.62  thf('2', plain,
% 0.41/0.62      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.41/0.62         (((X25) = (k2_tarski @ X23 @ X24))
% 0.41/0.62          | ((X25) = (k1_tarski @ X24))
% 0.41/0.62          | ((X25) = (k1_tarski @ X23))
% 0.41/0.62          | ((X25) = (k1_xboole_0))
% 0.41/0.62          | ~ (r1_tarski @ X25 @ (k2_tarski @ X23 @ X24)))),
% 0.41/0.62      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.41/0.62  thf('3', plain,
% 0.41/0.62      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.41/0.62        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.41/0.62        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D))
% 0.41/0.62        | ((k2_tarski @ sk_A @ sk_B) = (k2_tarski @ sk_C @ sk_D)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.41/0.62  thf('4', plain,
% 0.41/0.62      (![X23 : $i, X25 : $i, X26 : $i]:
% 0.41/0.62         ((r1_tarski @ X25 @ (k2_tarski @ X23 @ X26))
% 0.41/0.62          | ((X25) != (k1_tarski @ X23)))),
% 0.41/0.62      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.41/0.62  thf('5', plain,
% 0.41/0.62      (![X23 : $i, X26 : $i]:
% 0.41/0.62         (r1_tarski @ (k1_tarski @ X23) @ (k2_tarski @ X23 @ X26))),
% 0.41/0.62      inference('simplify', [status(thm)], ['4'])).
% 0.41/0.62  thf('6', plain,
% 0.41/0.62      (((r1_tarski @ (k1_tarski @ sk_C) @ (k2_tarski @ sk_A @ sk_B))
% 0.41/0.62        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D))
% 0.41/0.62        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.41/0.62        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['3', '5'])).
% 0.41/0.62  thf('7', plain,
% 0.41/0.62      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.41/0.62         (((X25) = (k2_tarski @ X23 @ X24))
% 0.41/0.62          | ((X25) = (k1_tarski @ X24))
% 0.41/0.62          | ((X25) = (k1_tarski @ X23))
% 0.41/0.62          | ((X25) = (k1_xboole_0))
% 0.41/0.62          | ~ (r1_tarski @ X25 @ (k2_tarski @ X23 @ X24)))),
% 0.41/0.62      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.41/0.62  thf('8', plain,
% 0.41/0.62      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.41/0.62        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.41/0.62        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D))
% 0.41/0.62        | ((k1_tarski @ sk_C) = (k1_xboole_0))
% 0.41/0.62        | ((k1_tarski @ sk_C) = (k1_tarski @ sk_A))
% 0.41/0.62        | ((k1_tarski @ sk_C) = (k1_tarski @ sk_B))
% 0.41/0.62        | ((k1_tarski @ sk_C) = (k2_tarski @ sk_A @ sk_B)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['6', '7'])).
% 0.41/0.62  thf('9', plain,
% 0.41/0.62      ((((k1_tarski @ sk_C) = (k1_tarski @ sk_B))
% 0.41/0.62        | ((k1_tarski @ sk_C) = (k1_tarski @ sk_A))
% 0.41/0.62        | ((k1_tarski @ sk_C) = (k1_xboole_0))
% 0.41/0.62        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D))
% 0.41/0.62        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.41/0.62        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.41/0.62      inference('simplify', [status(thm)], ['8'])).
% 0.41/0.62  thf('10', plain,
% 0.41/0.62      (![X23 : $i, X26 : $i]:
% 0.41/0.62         (r1_tarski @ (k1_tarski @ X23) @ (k2_tarski @ X23 @ X26))),
% 0.41/0.62      inference('simplify', [status(thm)], ['4'])).
% 0.41/0.62  thf('11', plain,
% 0.41/0.62      (((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_D))
% 0.41/0.62        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.41/0.62        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.41/0.62        | ((k1_tarski @ sk_C) = (k1_xboole_0))
% 0.41/0.62        | ((k1_tarski @ sk_C) = (k1_tarski @ sk_A))
% 0.41/0.62        | ((k1_tarski @ sk_C) = (k1_tarski @ sk_B)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['9', '10'])).
% 0.41/0.62  thf(t69_enumset1, axiom,
% 0.41/0.62    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.41/0.62  thf('12', plain,
% 0.41/0.62      (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.41/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.41/0.62  thf(t26_zfmisc_1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.41/0.62       ( ( A ) = ( C ) ) ))).
% 0.41/0.62  thf('13', plain,
% 0.41/0.62      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.41/0.62         (((X28) = (X27))
% 0.41/0.62          | ~ (r1_tarski @ (k2_tarski @ X28 @ X29) @ (k1_tarski @ X27)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t26_zfmisc_1])).
% 0.41/0.62  thf('14', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         (~ (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X1)) | ((X0) = (X1)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['12', '13'])).
% 0.41/0.62  thf('15', plain,
% 0.41/0.62      ((((k1_tarski @ sk_C) = (k1_tarski @ sk_B))
% 0.41/0.62        | ((k1_tarski @ sk_C) = (k1_tarski @ sk_A))
% 0.41/0.62        | ((k1_tarski @ sk_C) = (k1_xboole_0))
% 0.41/0.62        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.41/0.62        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.41/0.62        | ((sk_A) = (sk_D)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['11', '14'])).
% 0.41/0.62  thf('16', plain, (((sk_A) != (sk_D))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('17', plain,
% 0.41/0.62      ((((k1_tarski @ sk_C) = (k1_tarski @ sk_B))
% 0.41/0.62        | ((k1_tarski @ sk_C) = (k1_tarski @ sk_A))
% 0.41/0.62        | ((k1_tarski @ sk_C) = (k1_xboole_0))
% 0.41/0.62        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.41/0.62        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.41/0.62      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 0.41/0.62  thf('18', plain,
% 0.41/0.62      (![X23 : $i, X26 : $i]:
% 0.41/0.62         (r1_tarski @ (k1_tarski @ X23) @ (k2_tarski @ X23 @ X26))),
% 0.41/0.62      inference('simplify', [status(thm)], ['4'])).
% 0.41/0.62  thf('19', plain,
% 0.41/0.62      (((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))
% 0.41/0.62        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.41/0.62        | ((k1_tarski @ sk_C) = (k1_xboole_0))
% 0.41/0.62        | ((k1_tarski @ sk_C) = (k1_tarski @ sk_A))
% 0.41/0.62        | ((k1_tarski @ sk_C) = (k1_tarski @ sk_B)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['17', '18'])).
% 0.41/0.62  thf('20', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         (~ (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X1)) | ((X0) = (X1)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['12', '13'])).
% 0.41/0.62  thf('21', plain,
% 0.41/0.62      ((((k1_tarski @ sk_C) = (k1_tarski @ sk_B))
% 0.41/0.62        | ((k1_tarski @ sk_C) = (k1_tarski @ sk_A))
% 0.41/0.62        | ((k1_tarski @ sk_C) = (k1_xboole_0))
% 0.41/0.62        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.41/0.62        | ((sk_A) = (sk_C)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['19', '20'])).
% 0.41/0.62  thf('22', plain, (((sk_A) != (sk_C))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('23', plain,
% 0.41/0.62      ((((k1_tarski @ sk_C) = (k1_tarski @ sk_B))
% 0.41/0.62        | ((k1_tarski @ sk_C) = (k1_tarski @ sk_A))
% 0.41/0.62        | ((k1_tarski @ sk_C) = (k1_xboole_0))
% 0.41/0.62        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.41/0.62      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.41/0.62  thf('24', plain,
% 0.41/0.62      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.41/0.62         (((X28) = (X27))
% 0.41/0.62          | ~ (r1_tarski @ (k2_tarski @ X28 @ X29) @ (k1_tarski @ X27)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t26_zfmisc_1])).
% 0.41/0.62  thf('25', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.41/0.62          | ((k1_tarski @ sk_C) = (k1_xboole_0))
% 0.41/0.62          | ((k1_tarski @ sk_C) = (k1_tarski @ sk_A))
% 0.41/0.62          | ((k1_tarski @ sk_C) = (k1_tarski @ sk_B))
% 0.41/0.62          | ((sk_A) = (X0)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['23', '24'])).
% 0.41/0.62  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.41/0.63  thf('26', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.41/0.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.41/0.63  thf('27', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         (((k1_tarski @ sk_C) = (k1_xboole_0))
% 0.41/0.63          | ((k1_tarski @ sk_C) = (k1_tarski @ sk_A))
% 0.41/0.63          | ((k1_tarski @ sk_C) = (k1_tarski @ sk_B))
% 0.41/0.63          | ((sk_A) = (X0)))),
% 0.41/0.63      inference('demod', [status(thm)], ['25', '26'])).
% 0.41/0.63  thf('28', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         (((k1_tarski @ sk_C) = (k1_xboole_0))
% 0.41/0.63          | ((k1_tarski @ sk_C) = (k1_tarski @ sk_A))
% 0.41/0.63          | ((k1_tarski @ sk_C) = (k1_tarski @ sk_B))
% 0.41/0.63          | ((sk_A) = (X0)))),
% 0.41/0.63      inference('demod', [status(thm)], ['25', '26'])).
% 0.41/0.63  thf('29', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i]:
% 0.41/0.63         (((X0) = (X1))
% 0.41/0.63          | ((k1_tarski @ sk_C) = (k1_tarski @ sk_B))
% 0.41/0.63          | ((k1_tarski @ sk_C) = (k1_tarski @ sk_A))
% 0.41/0.63          | ((k1_tarski @ sk_C) = (k1_xboole_0))
% 0.41/0.63          | ((k1_tarski @ sk_C) = (k1_tarski @ sk_B))
% 0.41/0.63          | ((k1_tarski @ sk_C) = (k1_tarski @ sk_A))
% 0.41/0.63          | ((k1_tarski @ sk_C) = (k1_xboole_0)))),
% 0.41/0.63      inference('sup+', [status(thm)], ['27', '28'])).
% 0.41/0.63  thf('30', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i]:
% 0.41/0.63         (((k1_tarski @ sk_C) = (k1_xboole_0))
% 0.41/0.63          | ((k1_tarski @ sk_C) = (k1_tarski @ sk_A))
% 0.41/0.63          | ((k1_tarski @ sk_C) = (k1_tarski @ sk_B))
% 0.41/0.63          | ((X0) = (X1)))),
% 0.41/0.63      inference('simplify', [status(thm)], ['29'])).
% 0.41/0.63  thf('31', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         (((k1_tarski @ sk_C) != (X0))
% 0.41/0.63          | ((k1_tarski @ sk_B) = (X0))
% 0.41/0.63          | ((k1_tarski @ sk_C) = (k1_tarski @ sk_A))
% 0.41/0.63          | ((k1_tarski @ sk_C) = (k1_xboole_0)))),
% 0.41/0.63      inference('eq_fact', [status(thm)], ['30'])).
% 0.41/0.63  thf('32', plain,
% 0.41/0.63      ((((k1_tarski @ sk_C) = (k1_xboole_0))
% 0.41/0.63        | ((k1_tarski @ sk_C) = (k1_tarski @ sk_A))
% 0.41/0.63        | ((k1_tarski @ sk_B) = (k1_tarski @ sk_C)))),
% 0.41/0.63      inference('simplify', [status(thm)], ['31'])).
% 0.41/0.63  thf('33', plain,
% 0.41/0.63      (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.41/0.63      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.41/0.63  thf('34', plain,
% 0.41/0.63      (![X23 : $i, X26 : $i]:
% 0.41/0.63         (r1_tarski @ (k1_tarski @ X23) @ (k2_tarski @ X23 @ X26))),
% 0.41/0.63      inference('simplify', [status(thm)], ['4'])).
% 0.41/0.63  thf('35', plain,
% 0.41/0.63      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.41/0.63      inference('sup+', [status(thm)], ['33', '34'])).
% 0.41/0.63  thf('36', plain,
% 0.41/0.63      (((r1_tarski @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_C))
% 0.41/0.63        | ((k1_tarski @ sk_C) = (k1_tarski @ sk_A))
% 0.41/0.63        | ((k1_tarski @ sk_C) = (k1_xboole_0)))),
% 0.41/0.63      inference('sup+', [status(thm)], ['32', '35'])).
% 0.41/0.63  thf('37', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i]:
% 0.41/0.63         (~ (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X1)) | ((X0) = (X1)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['12', '13'])).
% 0.41/0.63  thf('38', plain,
% 0.41/0.63      ((((k1_tarski @ sk_C) = (k1_xboole_0))
% 0.41/0.63        | ((k1_tarski @ sk_C) = (k1_tarski @ sk_A))
% 0.41/0.63        | ((sk_B) = (sk_C)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['36', '37'])).
% 0.41/0.63  thf('39', plain,
% 0.41/0.63      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.41/0.63      inference('sup+', [status(thm)], ['33', '34'])).
% 0.41/0.63  thf('40', plain,
% 0.41/0.63      (((r1_tarski @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_A))
% 0.41/0.63        | ((sk_B) = (sk_C))
% 0.41/0.63        | ((k1_tarski @ sk_C) = (k1_xboole_0)))),
% 0.41/0.63      inference('sup+', [status(thm)], ['38', '39'])).
% 0.41/0.63  thf('41', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i]:
% 0.41/0.63         (~ (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X1)) | ((X0) = (X1)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['12', '13'])).
% 0.41/0.63  thf('42', plain,
% 0.41/0.63      ((((k1_tarski @ sk_C) = (k1_xboole_0))
% 0.41/0.63        | ((sk_B) = (sk_C))
% 0.41/0.63        | ((sk_C) = (sk_A)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['40', '41'])).
% 0.41/0.63  thf('43', plain, (((sk_A) != (sk_C))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('44', plain,
% 0.41/0.63      ((((k1_tarski @ sk_C) = (k1_xboole_0)) | ((sk_B) = (sk_C)))),
% 0.41/0.63      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 0.41/0.63  thf('45', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i]:
% 0.41/0.63         (~ (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X1)) | ((X0) = (X1)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['12', '13'])).
% 0.41/0.63  thf('46', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         (~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.41/0.63          | ((sk_B) = (sk_C))
% 0.41/0.63          | ((sk_C) = (X0)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['44', '45'])).
% 0.41/0.63  thf('47', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.41/0.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.41/0.63  thf('48', plain, (![X0 : $i]: (((sk_B) = (sk_C)) | ((sk_C) = (X0)))),
% 0.41/0.63      inference('demod', [status(thm)], ['46', '47'])).
% 0.41/0.63  thf('49', plain, (((sk_B) = (sk_C))),
% 0.41/0.63      inference('condensation', [status(thm)], ['48'])).
% 0.41/0.63  thf('50', plain,
% 0.41/0.63      ((r1_tarski @ (k2_tarski @ sk_A @ sk_C) @ (k2_tarski @ sk_C @ sk_D))),
% 0.41/0.63      inference('demod', [status(thm)], ['0', '49'])).
% 0.41/0.63  thf(d1_enumset1, axiom,
% 0.41/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.63     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.41/0.63       ( ![E:$i]:
% 0.41/0.63         ( ( r2_hidden @ E @ D ) <=>
% 0.41/0.63           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.41/0.63  thf(zf_stmt_1, axiom,
% 0.41/0.63    (![E:$i,C:$i,B:$i,A:$i]:
% 0.41/0.63     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.41/0.63       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.41/0.63  thf('51', plain,
% 0.41/0.63      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.41/0.63         ((zip_tseitin_0 @ X2 @ X3 @ X4 @ X5)
% 0.41/0.63          | ((X2) = (X3))
% 0.41/0.63          | ((X2) = (X4))
% 0.41/0.63          | ((X2) = (X5)))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.41/0.63  thf('52', plain,
% 0.41/0.63      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.41/0.63         ((zip_tseitin_0 @ X2 @ X3 @ X4 @ X5)
% 0.41/0.63          | ((X2) = (X3))
% 0.41/0.63          | ((X2) = (X4))
% 0.41/0.63          | ((X2) = (X5)))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.41/0.63  thf('53', plain,
% 0.41/0.63      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.41/0.63         ((zip_tseitin_0 @ X2 @ X3 @ X4 @ X5)
% 0.41/0.63          | ((X2) = (X3))
% 0.41/0.63          | ((X2) = (X4))
% 0.41/0.63          | ((X2) = (X5)))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.41/0.63  thf('54', plain,
% 0.41/0.63      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.41/0.63        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.41/0.63        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D))
% 0.41/0.63        | ((k2_tarski @ sk_A @ sk_B) = (k2_tarski @ sk_C @ sk_D)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['1', '2'])).
% 0.41/0.63  thf('55', plain, (((sk_B) = (sk_C))),
% 0.41/0.63      inference('condensation', [status(thm)], ['48'])).
% 0.41/0.63  thf('56', plain, (((sk_B) = (sk_C))),
% 0.41/0.63      inference('condensation', [status(thm)], ['48'])).
% 0.41/0.63  thf('57', plain, (((sk_B) = (sk_C))),
% 0.41/0.63      inference('condensation', [status(thm)], ['48'])).
% 0.41/0.63  thf('58', plain, (((sk_B) = (sk_C))),
% 0.41/0.63      inference('condensation', [status(thm)], ['48'])).
% 0.41/0.63  thf('59', plain,
% 0.41/0.63      ((((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0))
% 0.41/0.63        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C))
% 0.41/0.63        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_D))
% 0.41/0.63        | ((k2_tarski @ sk_A @ sk_C) = (k2_tarski @ sk_C @ sk_D)))),
% 0.41/0.63      inference('demod', [status(thm)], ['54', '55', '56', '57', '58'])).
% 0.41/0.63  thf(t70_enumset1, axiom,
% 0.41/0.63    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.41/0.63  thf('60', plain,
% 0.41/0.63      (![X14 : $i, X15 : $i]:
% 0.41/0.63         ((k1_enumset1 @ X14 @ X14 @ X15) = (k2_tarski @ X14 @ X15))),
% 0.41/0.63      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.41/0.63  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.41/0.63  thf(zf_stmt_3, axiom,
% 0.41/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.63     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.41/0.63       ( ![E:$i]:
% 0.41/0.63         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.41/0.63  thf('61', plain,
% 0.41/0.63      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.41/0.63         ((zip_tseitin_0 @ X6 @ X7 @ X8 @ X9)
% 0.41/0.63          | (r2_hidden @ X6 @ X10)
% 0.41/0.63          | ((X10) != (k1_enumset1 @ X9 @ X8 @ X7)))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.41/0.63  thf('62', plain,
% 0.41/0.63      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.41/0.63         ((r2_hidden @ X6 @ (k1_enumset1 @ X9 @ X8 @ X7))
% 0.41/0.63          | (zip_tseitin_0 @ X6 @ X7 @ X8 @ X9))),
% 0.41/0.63      inference('simplify', [status(thm)], ['61'])).
% 0.41/0.63  thf('63', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.63         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.41/0.63          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.41/0.63      inference('sup+', [status(thm)], ['60', '62'])).
% 0.41/0.63  thf('64', plain,
% 0.41/0.63      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.41/0.63         (((X2) != (X3)) | ~ (zip_tseitin_0 @ X2 @ X3 @ X4 @ X1))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.41/0.63  thf('65', plain,
% 0.41/0.63      (![X1 : $i, X3 : $i, X4 : $i]: ~ (zip_tseitin_0 @ X3 @ X3 @ X4 @ X1)),
% 0.41/0.63      inference('simplify', [status(thm)], ['64'])).
% 0.41/0.63  thf('66', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.41/0.63      inference('sup-', [status(thm)], ['63', '65'])).
% 0.41/0.63  thf('67', plain,
% 0.41/0.63      (((r2_hidden @ sk_D @ (k2_tarski @ sk_A @ sk_C))
% 0.41/0.63        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_D))
% 0.41/0.63        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C))
% 0.41/0.63        | ((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0)))),
% 0.41/0.63      inference('sup+', [status(thm)], ['59', '66'])).
% 0.41/0.63  thf('68', plain,
% 0.41/0.63      (![X14 : $i, X15 : $i]:
% 0.41/0.63         ((k1_enumset1 @ X14 @ X14 @ X15) = (k2_tarski @ X14 @ X15))),
% 0.41/0.63      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.41/0.63  thf('69', plain,
% 0.41/0.63      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.41/0.63         (~ (r2_hidden @ X11 @ X10)
% 0.41/0.63          | ~ (zip_tseitin_0 @ X11 @ X7 @ X8 @ X9)
% 0.41/0.63          | ((X10) != (k1_enumset1 @ X9 @ X8 @ X7)))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.41/0.63  thf('70', plain,
% 0.41/0.63      (![X7 : $i, X8 : $i, X9 : $i, X11 : $i]:
% 0.41/0.63         (~ (zip_tseitin_0 @ X11 @ X7 @ X8 @ X9)
% 0.41/0.63          | ~ (r2_hidden @ X11 @ (k1_enumset1 @ X9 @ X8 @ X7)))),
% 0.41/0.63      inference('simplify', [status(thm)], ['69'])).
% 0.41/0.63  thf('71', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.63         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.41/0.63          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.41/0.63      inference('sup-', [status(thm)], ['68', '70'])).
% 0.41/0.63  thf('72', plain,
% 0.41/0.63      ((((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0))
% 0.41/0.63        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C))
% 0.41/0.63        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_D))
% 0.41/0.63        | ~ (zip_tseitin_0 @ sk_D @ sk_C @ sk_A @ sk_A))),
% 0.41/0.63      inference('sup-', [status(thm)], ['67', '71'])).
% 0.41/0.63  thf('73', plain,
% 0.41/0.63      ((((sk_D) = (sk_A))
% 0.41/0.63        | ((sk_D) = (sk_A))
% 0.41/0.63        | ((sk_D) = (sk_C))
% 0.41/0.63        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_D))
% 0.41/0.63        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C))
% 0.41/0.63        | ((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['53', '72'])).
% 0.41/0.63  thf('74', plain,
% 0.41/0.63      ((((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0))
% 0.41/0.63        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C))
% 0.41/0.63        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_D))
% 0.41/0.63        | ((sk_D) = (sk_C))
% 0.41/0.63        | ((sk_D) = (sk_A)))),
% 0.41/0.63      inference('simplify', [status(thm)], ['73'])).
% 0.41/0.63  thf('75', plain, (((sk_A) != (sk_D))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('76', plain,
% 0.41/0.63      ((((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0))
% 0.41/0.63        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C))
% 0.41/0.63        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_D))
% 0.41/0.63        | ((sk_D) = (sk_C)))),
% 0.41/0.63      inference('simplify_reflect-', [status(thm)], ['74', '75'])).
% 0.41/0.63  thf('77', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.63         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.41/0.63          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.41/0.63      inference('sup+', [status(thm)], ['60', '62'])).
% 0.41/0.63  thf('78', plain,
% 0.41/0.63      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.41/0.63         (((X2) != (X1)) | ~ (zip_tseitin_0 @ X2 @ X3 @ X4 @ X1))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.41/0.63  thf('79', plain,
% 0.41/0.63      (![X1 : $i, X3 : $i, X4 : $i]: ~ (zip_tseitin_0 @ X1 @ X3 @ X4 @ X1)),
% 0.41/0.63      inference('simplify', [status(thm)], ['78'])).
% 0.41/0.63  thf('80', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.41/0.63      inference('sup-', [status(thm)], ['77', '79'])).
% 0.41/0.63  thf('81', plain,
% 0.41/0.63      (((r2_hidden @ sk_A @ (k1_tarski @ sk_D))
% 0.41/0.63        | ((sk_D) = (sk_C))
% 0.41/0.63        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C))
% 0.41/0.63        | ((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0)))),
% 0.41/0.63      inference('sup+', [status(thm)], ['76', '80'])).
% 0.41/0.63  thf('82', plain,
% 0.41/0.63      (![X14 : $i, X15 : $i]:
% 0.41/0.63         ((k1_enumset1 @ X14 @ X14 @ X15) = (k2_tarski @ X14 @ X15))),
% 0.41/0.63      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.41/0.63  thf('83', plain,
% 0.41/0.63      (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.41/0.63      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.41/0.63  thf('84', plain,
% 0.41/0.63      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.41/0.63      inference('sup+', [status(thm)], ['82', '83'])).
% 0.41/0.63  thf('85', plain,
% 0.41/0.63      (![X7 : $i, X8 : $i, X9 : $i, X11 : $i]:
% 0.41/0.63         (~ (zip_tseitin_0 @ X11 @ X7 @ X8 @ X9)
% 0.41/0.63          | ~ (r2_hidden @ X11 @ (k1_enumset1 @ X9 @ X8 @ X7)))),
% 0.41/0.63      inference('simplify', [status(thm)], ['69'])).
% 0.41/0.63  thf('86', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i]:
% 0.41/0.63         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.41/0.63          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.41/0.63      inference('sup-', [status(thm)], ['84', '85'])).
% 0.41/0.63  thf('87', plain,
% 0.41/0.63      ((((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0))
% 0.41/0.63        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C))
% 0.41/0.63        | ((sk_D) = (sk_C))
% 0.41/0.63        | ~ (zip_tseitin_0 @ sk_A @ sk_D @ sk_D @ sk_D))),
% 0.41/0.63      inference('sup-', [status(thm)], ['81', '86'])).
% 0.41/0.63  thf('88', plain,
% 0.41/0.63      ((((sk_A) = (sk_D))
% 0.41/0.63        | ((sk_A) = (sk_D))
% 0.41/0.63        | ((sk_A) = (sk_D))
% 0.41/0.63        | ((sk_D) = (sk_C))
% 0.41/0.63        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C))
% 0.41/0.63        | ((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['52', '87'])).
% 0.41/0.63  thf('89', plain,
% 0.41/0.63      ((((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0))
% 0.41/0.63        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C))
% 0.41/0.63        | ((sk_D) = (sk_C))
% 0.41/0.63        | ((sk_A) = (sk_D)))),
% 0.41/0.63      inference('simplify', [status(thm)], ['88'])).
% 0.41/0.63  thf('90', plain, (((sk_A) != (sk_D))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('91', plain,
% 0.41/0.63      ((((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0))
% 0.41/0.63        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C))
% 0.41/0.63        | ((sk_D) = (sk_C)))),
% 0.41/0.63      inference('simplify_reflect-', [status(thm)], ['89', '90'])).
% 0.41/0.63  thf('92', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.41/0.63      inference('sup-', [status(thm)], ['77', '79'])).
% 0.41/0.63  thf('93', plain,
% 0.41/0.63      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C))
% 0.41/0.63        | ((sk_D) = (sk_C))
% 0.41/0.63        | ((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0)))),
% 0.41/0.63      inference('sup+', [status(thm)], ['91', '92'])).
% 0.41/0.63  thf('94', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i]:
% 0.41/0.63         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.41/0.63          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.41/0.63      inference('sup-', [status(thm)], ['84', '85'])).
% 0.41/0.63  thf('95', plain,
% 0.41/0.63      ((((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0))
% 0.41/0.63        | ((sk_D) = (sk_C))
% 0.41/0.63        | ~ (zip_tseitin_0 @ sk_A @ sk_C @ sk_C @ sk_C))),
% 0.41/0.63      inference('sup-', [status(thm)], ['93', '94'])).
% 0.41/0.63  thf('96', plain,
% 0.41/0.63      ((((sk_A) = (sk_C))
% 0.41/0.63        | ((sk_A) = (sk_C))
% 0.41/0.63        | ((sk_A) = (sk_C))
% 0.41/0.63        | ((sk_D) = (sk_C))
% 0.41/0.63        | ((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['51', '95'])).
% 0.41/0.63  thf('97', plain,
% 0.41/0.63      ((((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0))
% 0.41/0.63        | ((sk_D) = (sk_C))
% 0.41/0.63        | ((sk_A) = (sk_C)))),
% 0.41/0.63      inference('simplify', [status(thm)], ['96'])).
% 0.41/0.63  thf('98', plain, (((sk_A) != (sk_C))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('99', plain,
% 0.41/0.63      ((((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0)) | ((sk_D) = (sk_C)))),
% 0.41/0.63      inference('simplify_reflect-', [status(thm)], ['97', '98'])).
% 0.41/0.63  thf('100', plain,
% 0.41/0.63      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.41/0.63         (((X28) = (X27))
% 0.41/0.63          | ~ (r1_tarski @ (k2_tarski @ X28 @ X29) @ (k1_tarski @ X27)))),
% 0.41/0.63      inference('cnf', [status(esa)], [t26_zfmisc_1])).
% 0.41/0.63  thf('101', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         (~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.41/0.63          | ((sk_D) = (sk_C))
% 0.41/0.63          | ((sk_A) = (X0)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['99', '100'])).
% 0.41/0.63  thf('102', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.41/0.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.41/0.63  thf('103', plain, (![X0 : $i]: (((sk_D) = (sk_C)) | ((sk_A) = (X0)))),
% 0.41/0.63      inference('demod', [status(thm)], ['101', '102'])).
% 0.41/0.63  thf('104', plain, (((sk_B) = (sk_C))),
% 0.41/0.63      inference('condensation', [status(thm)], ['48'])).
% 0.41/0.63  thf('105', plain, ((((sk_A) = (sk_C)) | ((sk_D) = (sk_C)))),
% 0.41/0.63      inference('sup+', [status(thm)], ['103', '104'])).
% 0.41/0.63  thf('106', plain, (((sk_A) != (sk_C))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('107', plain, (((sk_D) = (sk_C))),
% 0.41/0.63      inference('simplify_reflect-', [status(thm)], ['105', '106'])).
% 0.41/0.63  thf('108', plain,
% 0.41/0.63      (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.41/0.63      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.41/0.63  thf('109', plain,
% 0.41/0.63      ((r1_tarski @ (k2_tarski @ sk_A @ sk_C) @ (k1_tarski @ sk_C))),
% 0.41/0.63      inference('demod', [status(thm)], ['50', '107', '108'])).
% 0.41/0.63  thf('110', plain,
% 0.41/0.63      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.41/0.63         (((X28) = (X27))
% 0.41/0.63          | ~ (r1_tarski @ (k2_tarski @ X28 @ X29) @ (k1_tarski @ X27)))),
% 0.41/0.63      inference('cnf', [status(esa)], [t26_zfmisc_1])).
% 0.41/0.63  thf('111', plain, (((sk_A) = (sk_C))),
% 0.41/0.63      inference('sup-', [status(thm)], ['109', '110'])).
% 0.41/0.63  thf('112', plain, (((sk_A) != (sk_C))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('113', plain, ($false),
% 0.41/0.63      inference('simplify_reflect-', [status(thm)], ['111', '112'])).
% 0.41/0.63  
% 0.41/0.63  % SZS output end Refutation
% 0.41/0.63  
% 0.46/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
