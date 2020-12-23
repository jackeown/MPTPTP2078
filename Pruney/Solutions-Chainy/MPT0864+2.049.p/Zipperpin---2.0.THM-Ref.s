%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WWpUuvg6O4

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:06 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 165 expanded)
%              Number of leaves         :   32 (  62 expanded)
%              Depth                    :   16
%              Number of atoms          :  582 (1441 expanded)
%              Number of equality atoms :   73 ( 171 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t20_mcart_1,conjecture,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ? [B: $i,C: $i] :
            ( A
            = ( k4_tarski @ B @ C ) )
       => ( ( A
           != ( k1_mcart_1 @ A ) )
          & ( A
           != ( k2_mcart_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_mcart_1])).

thf('0',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('1',plain,(
    ! [X46: $i,X48: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X46 @ X48 ) )
      = X48 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('2',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k1_enumset1 @ X2 @ X2 @ X3 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('9',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_enumset1 @ X4 @ X4 @ X5 @ X6 )
      = ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k3_enumset1 @ X7 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_enumset1 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(d3_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( F
        = ( k3_enumset1 @ A @ B @ C @ D @ E ) )
    <=> ! [G: $i] :
          ( ( r2_hidden @ G @ F )
        <=> ~ ( ( G != E )
              & ( G != D )
              & ( G != C )
              & ( G != B )
              & ( G != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [G: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A )
    <=> ( ( G != A )
        & ( G != B )
        & ( G != C )
        & ( G != D )
        & ( G != E ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( F
        = ( k3_enumset1 @ A @ B @ C @ D @ E ) )
    <=> ! [G: $i] :
          ( ( r2_hidden @ G @ F )
        <=> ~ ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 )
      | ( r2_hidden @ X32 @ X38 )
      | ( X38
       != ( k3_enumset1 @ X37 @ X36 @ X35 @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('14',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( r2_hidden @ X32 @ ( k3_enumset1 @ X37 @ X36 @ X35 @ X34 @ X33 ) )
      | ( zip_tseitin_0 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 ) ) ),
    inference('sup+',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( X26 != X25 )
      | ~ ( zip_tseitin_0 @ X26 @ X27 @ X28 @ X29 @ X30 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('17',plain,(
    ! [X25: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ~ ( zip_tseitin_0 @ X25 @ X27 @ X28 @ X29 @ X30 @ X25 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','19'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('22',plain,(
    ! [X16: $i,X17: $i,X18: $i,X20: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X16 @ X18 ) @ ( k2_zfmisc_1 @ X17 @ X20 ) )
      | ~ ( r2_hidden @ X18 @ X20 )
      | ~ ( r2_hidden @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,
    ( ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['7','24'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('26',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X11 ) @ X13 )
      | ~ ( r2_hidden @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('27',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X46 @ X47 ) )
      = X46 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('30',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('32',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('36',plain,
    ( ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X11 ) @ X13 )
      | ~ ( r2_hidden @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('38',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t135_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) )
        | ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('39',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X21 = k1_xboole_0 )
      | ~ ( r1_tarski @ X21 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('40',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('42',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X23 ) @ X24 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    sk_A
 != ( k1_mcart_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['40','43'])).

thf('45',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('46',plain,
    ( sk_A
    = ( k2_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['44','45'])).

thf('47',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['27','46'])).

thf('48',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X21 = k1_xboole_0 )
      | ~ ( r1_tarski @ X21 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('49',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('51',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['49','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WWpUuvg6O4
% 0.15/0.36  % Computer   : n020.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 20:07:22 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.41/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.60  % Solved by: fo/fo7.sh
% 0.41/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.60  % done 324 iterations in 0.124s
% 0.41/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.60  % SZS output start Refutation
% 0.41/0.60  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.41/0.60  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o).
% 0.41/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.60  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.41/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.41/0.60  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.41/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.60  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.41/0.60  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.41/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.41/0.60  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.41/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.41/0.60  thf(t20_mcart_1, conjecture,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.41/0.60       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.41/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.60    (~( ![A:$i]:
% 0.41/0.60        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.41/0.60          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.41/0.60    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.41/0.60  thf('0', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(t7_mcart_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.41/0.60       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.41/0.60  thf('1', plain,
% 0.41/0.60      (![X46 : $i, X48 : $i]: ((k2_mcart_1 @ (k4_tarski @ X46 @ X48)) = (X48))),
% 0.41/0.60      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.41/0.60  thf('2', plain, (((k2_mcart_1 @ sk_A) = (sk_C))),
% 0.41/0.60      inference('sup+', [status(thm)], ['0', '1'])).
% 0.41/0.60  thf('3', plain,
% 0.41/0.60      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('4', plain,
% 0.41/0.60      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.41/0.60      inference('split', [status(esa)], ['3'])).
% 0.41/0.60  thf('5', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.41/0.60      inference('sup+', [status(thm)], ['2', '4'])).
% 0.41/0.60  thf('6', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('7', plain,
% 0.41/0.60      ((((sk_A) = (k4_tarski @ sk_B @ sk_A)))
% 0.41/0.60         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.41/0.60      inference('sup+', [status(thm)], ['5', '6'])).
% 0.41/0.60  thf(t70_enumset1, axiom,
% 0.41/0.60    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.41/0.60  thf('8', plain,
% 0.41/0.60      (![X2 : $i, X3 : $i]:
% 0.41/0.60         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 0.41/0.60      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.41/0.60  thf(t69_enumset1, axiom,
% 0.41/0.60    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.41/0.60  thf('9', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.41/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.41/0.60  thf('10', plain,
% 0.41/0.60      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['8', '9'])).
% 0.41/0.60  thf(t71_enumset1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.41/0.60  thf('11', plain,
% 0.41/0.60      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.41/0.60         ((k2_enumset1 @ X4 @ X4 @ X5 @ X6) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 0.41/0.60      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.41/0.60  thf(t72_enumset1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.60     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.41/0.60  thf('12', plain,
% 0.41/0.60      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.41/0.60         ((k3_enumset1 @ X7 @ X7 @ X8 @ X9 @ X10)
% 0.41/0.60           = (k2_enumset1 @ X7 @ X8 @ X9 @ X10))),
% 0.41/0.60      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.41/0.60  thf(d3_enumset1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.41/0.60     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 0.41/0.60       ( ![G:$i]:
% 0.41/0.60         ( ( r2_hidden @ G @ F ) <=>
% 0.41/0.60           ( ~( ( ( G ) != ( E ) ) & ( ( G ) != ( D ) ) & ( ( G ) != ( C ) ) & 
% 0.41/0.60                ( ( G ) != ( B ) ) & ( ( G ) != ( A ) ) ) ) ) ) ))).
% 0.41/0.60  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $o).
% 0.41/0.60  thf(zf_stmt_2, axiom,
% 0.41/0.60    (![G:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.41/0.60     ( ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) <=>
% 0.41/0.60       ( ( ( G ) != ( A ) ) & ( ( G ) != ( B ) ) & ( ( G ) != ( C ) ) & 
% 0.41/0.60         ( ( G ) != ( D ) ) & ( ( G ) != ( E ) ) ) ))).
% 0.41/0.60  thf(zf_stmt_3, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.41/0.60     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 0.41/0.60       ( ![G:$i]:
% 0.41/0.60         ( ( r2_hidden @ G @ F ) <=>
% 0.41/0.60           ( ~( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.41/0.60  thf('13', plain,
% 0.41/0.60      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.41/0.60         ((zip_tseitin_0 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37)
% 0.41/0.60          | (r2_hidden @ X32 @ X38)
% 0.41/0.60          | ((X38) != (k3_enumset1 @ X37 @ X36 @ X35 @ X34 @ X33)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.41/0.60  thf('14', plain,
% 0.41/0.60      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.41/0.60         ((r2_hidden @ X32 @ (k3_enumset1 @ X37 @ X36 @ X35 @ X34 @ X33))
% 0.41/0.60          | (zip_tseitin_0 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37))),
% 0.41/0.60      inference('simplify', [status(thm)], ['13'])).
% 0.41/0.60  thf('15', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.41/0.60         ((r2_hidden @ X4 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.41/0.60          | (zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3))),
% 0.41/0.60      inference('sup+', [status(thm)], ['12', '14'])).
% 0.41/0.60  thf('16', plain,
% 0.41/0.60      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.41/0.60         (((X26) != (X25))
% 0.41/0.60          | ~ (zip_tseitin_0 @ X26 @ X27 @ X28 @ X29 @ X30 @ X25))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.41/0.60  thf('17', plain,
% 0.41/0.60      (![X25 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.41/0.60         ~ (zip_tseitin_0 @ X25 @ X27 @ X28 @ X29 @ X30 @ X25)),
% 0.41/0.60      inference('simplify', [status(thm)], ['16'])).
% 0.41/0.60  thf('18', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.41/0.60         (r2_hidden @ X0 @ (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.41/0.60      inference('sup-', [status(thm)], ['15', '17'])).
% 0.41/0.60  thf('19', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.60         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['11', '18'])).
% 0.41/0.60  thf('20', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['10', '19'])).
% 0.41/0.60  thf('21', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['10', '19'])).
% 0.41/0.60  thf(l54_zfmisc_1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.60     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.41/0.60       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.41/0.60  thf('22', plain,
% 0.41/0.60      (![X16 : $i, X17 : $i, X18 : $i, X20 : $i]:
% 0.41/0.60         ((r2_hidden @ (k4_tarski @ X16 @ X18) @ (k2_zfmisc_1 @ X17 @ X20))
% 0.41/0.60          | ~ (r2_hidden @ X18 @ X20)
% 0.41/0.60          | ~ (r2_hidden @ X16 @ X17))),
% 0.41/0.60      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.41/0.60  thf('23', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X2 @ X1)
% 0.41/0.60          | (r2_hidden @ (k4_tarski @ X2 @ X0) @ 
% 0.41/0.60             (k2_zfmisc_1 @ X1 @ (k1_tarski @ X0))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['21', '22'])).
% 0.41/0.60  thf('24', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (r2_hidden @ (k4_tarski @ X0 @ X1) @ 
% 0.41/0.60          (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['20', '23'])).
% 0.41/0.60  thf('25', plain,
% 0.41/0.60      (((r2_hidden @ sk_A @ 
% 0.41/0.60         (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))))
% 0.41/0.60         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.41/0.60      inference('sup+', [status(thm)], ['7', '24'])).
% 0.41/0.60  thf(l1_zfmisc_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.41/0.60  thf('26', plain,
% 0.41/0.60      (![X11 : $i, X13 : $i]:
% 0.41/0.60         ((r1_tarski @ (k1_tarski @ X11) @ X13) | ~ (r2_hidden @ X11 @ X13))),
% 0.41/0.60      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.41/0.60  thf('27', plain,
% 0.41/0.60      (((r1_tarski @ (k1_tarski @ sk_A) @ 
% 0.41/0.60         (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))))
% 0.41/0.60         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['25', '26'])).
% 0.41/0.60  thf('28', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('29', plain,
% 0.41/0.60      (![X46 : $i, X47 : $i]: ((k1_mcart_1 @ (k4_tarski @ X46 @ X47)) = (X46))),
% 0.41/0.60      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.41/0.60  thf('30', plain, (((k1_mcart_1 @ sk_A) = (sk_B))),
% 0.41/0.60      inference('sup+', [status(thm)], ['28', '29'])).
% 0.41/0.60  thf('31', plain,
% 0.41/0.60      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.41/0.60      inference('split', [status(esa)], ['3'])).
% 0.41/0.60  thf('32', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.41/0.60      inference('sup+', [status(thm)], ['30', '31'])).
% 0.41/0.60  thf('33', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('34', plain,
% 0.41/0.60      ((((sk_A) = (k4_tarski @ sk_A @ sk_C)))
% 0.41/0.60         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.41/0.60      inference('sup+', [status(thm)], ['32', '33'])).
% 0.41/0.60  thf('35', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (r2_hidden @ (k4_tarski @ X0 @ X1) @ 
% 0.41/0.60          (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['20', '23'])).
% 0.41/0.60  thf('36', plain,
% 0.41/0.60      (((r2_hidden @ sk_A @ 
% 0.41/0.60         (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))))
% 0.41/0.60         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.41/0.60      inference('sup+', [status(thm)], ['34', '35'])).
% 0.41/0.60  thf('37', plain,
% 0.41/0.60      (![X11 : $i, X13 : $i]:
% 0.41/0.60         ((r1_tarski @ (k1_tarski @ X11) @ X13) | ~ (r2_hidden @ X11 @ X13))),
% 0.41/0.60      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.41/0.60  thf('38', plain,
% 0.41/0.60      (((r1_tarski @ (k1_tarski @ sk_A) @ 
% 0.41/0.60         (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))))
% 0.41/0.60         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['36', '37'])).
% 0.41/0.60  thf(t135_zfmisc_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) ) | 
% 0.41/0.60         ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.41/0.60       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.41/0.60  thf('39', plain,
% 0.41/0.60      (![X21 : $i, X22 : $i]:
% 0.41/0.60         (((X21) = (k1_xboole_0))
% 0.41/0.60          | ~ (r1_tarski @ X21 @ (k2_zfmisc_1 @ X21 @ X22)))),
% 0.41/0.60      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.41/0.60  thf('40', plain,
% 0.41/0.60      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.41/0.60         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['38', '39'])).
% 0.41/0.60  thf(t1_boole, axiom,
% 0.41/0.60    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.41/0.60  thf('41', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.41/0.60      inference('cnf', [status(esa)], [t1_boole])).
% 0.41/0.60  thf(t49_zfmisc_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.41/0.60  thf('42', plain,
% 0.41/0.60      (![X23 : $i, X24 : $i]:
% 0.41/0.60         ((k2_xboole_0 @ (k1_tarski @ X23) @ X24) != (k1_xboole_0))),
% 0.41/0.60      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.41/0.60  thf('43', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['41', '42'])).
% 0.41/0.60  thf('44', plain, (~ (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.41/0.60      inference('simplify_reflect-', [status(thm)], ['40', '43'])).
% 0.41/0.60  thf('45', plain,
% 0.41/0.60      ((((sk_A) = (k2_mcart_1 @ sk_A))) | (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.41/0.60      inference('split', [status(esa)], ['3'])).
% 0.41/0.60  thf('46', plain, ((((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.41/0.60      inference('sat_resolution*', [status(thm)], ['44', '45'])).
% 0.41/0.60  thf('47', plain,
% 0.41/0.60      ((r1_tarski @ (k1_tarski @ sk_A) @ 
% 0.41/0.60        (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.41/0.60      inference('simpl_trail', [status(thm)], ['27', '46'])).
% 0.41/0.60  thf('48', plain,
% 0.41/0.60      (![X21 : $i, X22 : $i]:
% 0.41/0.60         (((X21) = (k1_xboole_0))
% 0.41/0.60          | ~ (r1_tarski @ X21 @ (k2_zfmisc_1 @ X22 @ X21)))),
% 0.41/0.60      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.41/0.60  thf('49', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['47', '48'])).
% 0.41/0.60  thf('50', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['41', '42'])).
% 0.41/0.60  thf('51', plain, ($false),
% 0.41/0.60      inference('simplify_reflect-', [status(thm)], ['49', '50'])).
% 0.41/0.60  
% 0.41/0.60  % SZS output end Refutation
% 0.41/0.60  
% 0.44/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
