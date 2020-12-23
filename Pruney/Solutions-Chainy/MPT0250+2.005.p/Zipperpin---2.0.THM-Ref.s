%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hadWaANmCz

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:47 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 105 expanded)
%              Number of leaves         :   25 (  42 expanded)
%              Depth                    :   14
%              Number of atoms          :  564 ( 868 expanded)
%              Number of equality atoms :   36 (  58 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_enumset1 @ X38 @ X38 @ X39 )
      = ( k2_tarski @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 @ X32 @ X33 )
      | ( r2_hidden @ X30 @ X34 )
      | ( X34
       != ( k1_enumset1 @ X33 @ X32 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('2',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( r2_hidden @ X30 @ ( k1_enumset1 @ X33 @ X32 @ X31 ) )
      | ( zip_tseitin_0 @ X30 @ X31 @ X32 @ X33 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( X26 != X25 )
      | ~ ( zip_tseitin_0 @ X26 @ X27 @ X28 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('5',plain,(
    ! [X25: $i,X27: $i,X28: $i] :
      ~ ( zip_tseitin_0 @ X25 @ X27 @ X28 @ X25 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 @ X28 @ X29 )
      | ( X26 = X27 )
      | ( X26 = X28 )
      | ( X26 = X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('9',plain,(
    ! [X37: $i] :
      ( ( k2_tarski @ X37 @ X37 )
      = ( k1_tarski @ X37 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('10',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_enumset1 @ X38 @ X38 @ X39 )
      = ( k2_tarski @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('11',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X35 @ X34 )
      | ~ ( zip_tseitin_0 @ X35 @ X31 @ X32 @ X33 )
      | ( X34
       != ( k1_enumset1 @ X33 @ X32 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('12',plain,(
    ! [X31: $i,X32: $i,X33: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X31 @ X32 @ X33 )
      | ~ ( r2_hidden @ X35 @ ( k1_enumset1 @ X33 @ X32 @ X31 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t45_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
     => ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
       => ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t45_zfmisc_1])).

thf('21',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('23',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( sk_B
      = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('24',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_tarski @ X24 @ X23 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X58: $i,X59: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X58 @ X59 ) )
      = ( k2_xboole_0 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X58: $i,X59: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X58 @ X59 ) )
      = ( k2_xboole_0 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('31',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','28','29','30'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('32',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ( r1_xboole_0 @ X15 @ X18 )
      | ~ ( r1_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_B )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','33'])).

thf('35',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('36',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('37',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ sk_B )
      | ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X37: $i] :
      ( ( k2_tarski @ X37 @ X37 )
      = ( k1_tarski @ X37 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_A @ X0 ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf('50',plain,(
    $false ),
    inference('sup-',[status(thm)],['6','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hadWaANmCz
% 0.17/0.38  % Computer   : n019.cluster.edu
% 0.17/0.38  % Model      : x86_64 x86_64
% 0.17/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.38  % Memory     : 8042.1875MB
% 0.17/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.38  % CPULimit   : 60
% 0.17/0.38  % DateTime   : Tue Dec  1 18:45:38 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.39  % Number of cores: 8
% 0.17/0.39  % Python version: Python 3.6.8
% 0.17/0.39  % Running in FO mode
% 0.51/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.51/0.73  % Solved by: fo/fo7.sh
% 0.51/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.73  % done 475 iterations in 0.234s
% 0.51/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.51/0.73  % SZS output start Refutation
% 0.51/0.73  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.51/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.51/0.73  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.51/0.73  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.51/0.73  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.51/0.73  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.51/0.73  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.51/0.73  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.51/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.73  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.51/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.51/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.73  thf(t70_enumset1, axiom,
% 0.51/0.73    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.51/0.73  thf('0', plain,
% 0.51/0.73      (![X38 : $i, X39 : $i]:
% 0.51/0.73         ((k1_enumset1 @ X38 @ X38 @ X39) = (k2_tarski @ X38 @ X39))),
% 0.51/0.73      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.51/0.73  thf(d1_enumset1, axiom,
% 0.51/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.51/0.73     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.51/0.73       ( ![E:$i]:
% 0.51/0.73         ( ( r2_hidden @ E @ D ) <=>
% 0.51/0.73           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.51/0.73  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.51/0.73  thf(zf_stmt_1, axiom,
% 0.51/0.73    (![E:$i,C:$i,B:$i,A:$i]:
% 0.51/0.73     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.51/0.73       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.51/0.73  thf(zf_stmt_2, axiom,
% 0.51/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.51/0.73     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.51/0.73       ( ![E:$i]:
% 0.51/0.73         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.51/0.73  thf('1', plain,
% 0.51/0.73      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.51/0.73         ((zip_tseitin_0 @ X30 @ X31 @ X32 @ X33)
% 0.51/0.73          | (r2_hidden @ X30 @ X34)
% 0.51/0.73          | ((X34) != (k1_enumset1 @ X33 @ X32 @ X31)))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.51/0.73  thf('2', plain,
% 0.51/0.73      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.51/0.73         ((r2_hidden @ X30 @ (k1_enumset1 @ X33 @ X32 @ X31))
% 0.51/0.73          | (zip_tseitin_0 @ X30 @ X31 @ X32 @ X33))),
% 0.51/0.73      inference('simplify', [status(thm)], ['1'])).
% 0.51/0.73  thf('3', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.73         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.51/0.73          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.51/0.73      inference('sup+', [status(thm)], ['0', '2'])).
% 0.51/0.73  thf('4', plain,
% 0.51/0.73      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.51/0.73         (((X26) != (X25)) | ~ (zip_tseitin_0 @ X26 @ X27 @ X28 @ X25))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.51/0.73  thf('5', plain,
% 0.51/0.73      (![X25 : $i, X27 : $i, X28 : $i]:
% 0.51/0.73         ~ (zip_tseitin_0 @ X25 @ X27 @ X28 @ X25)),
% 0.51/0.73      inference('simplify', [status(thm)], ['4'])).
% 0.51/0.73  thf('6', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.51/0.73      inference('sup-', [status(thm)], ['3', '5'])).
% 0.51/0.73  thf('7', plain,
% 0.51/0.73      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.51/0.73         ((zip_tseitin_0 @ X26 @ X27 @ X28 @ X29)
% 0.51/0.73          | ((X26) = (X27))
% 0.51/0.73          | ((X26) = (X28))
% 0.51/0.73          | ((X26) = (X29)))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.51/0.73  thf(t3_xboole_0, axiom,
% 0.51/0.73    (![A:$i,B:$i]:
% 0.51/0.73     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.51/0.73            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.51/0.73       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.51/0.73            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.51/0.73  thf('8', plain,
% 0.51/0.73      (![X6 : $i, X7 : $i]:
% 0.51/0.73         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.51/0.73      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.51/0.73  thf(t69_enumset1, axiom,
% 0.51/0.73    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.51/0.73  thf('9', plain, (![X37 : $i]: ((k2_tarski @ X37 @ X37) = (k1_tarski @ X37))),
% 0.51/0.73      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.51/0.73  thf('10', plain,
% 0.51/0.73      (![X38 : $i, X39 : $i]:
% 0.51/0.73         ((k1_enumset1 @ X38 @ X38 @ X39) = (k2_tarski @ X38 @ X39))),
% 0.51/0.73      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.51/0.73  thf('11', plain,
% 0.51/0.73      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.51/0.73         (~ (r2_hidden @ X35 @ X34)
% 0.51/0.73          | ~ (zip_tseitin_0 @ X35 @ X31 @ X32 @ X33)
% 0.51/0.73          | ((X34) != (k1_enumset1 @ X33 @ X32 @ X31)))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.51/0.73  thf('12', plain,
% 0.51/0.73      (![X31 : $i, X32 : $i, X33 : $i, X35 : $i]:
% 0.51/0.73         (~ (zip_tseitin_0 @ X35 @ X31 @ X32 @ X33)
% 0.51/0.73          | ~ (r2_hidden @ X35 @ (k1_enumset1 @ X33 @ X32 @ X31)))),
% 0.51/0.73      inference('simplify', [status(thm)], ['11'])).
% 0.51/0.73  thf('13', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.73         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.51/0.73          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.51/0.73      inference('sup-', [status(thm)], ['10', '12'])).
% 0.51/0.73  thf('14', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.51/0.73          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.51/0.73      inference('sup-', [status(thm)], ['9', '13'])).
% 0.51/0.73  thf('15', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.51/0.73          | ~ (zip_tseitin_0 @ (sk_C @ X1 @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 0.51/0.73      inference('sup-', [status(thm)], ['8', '14'])).
% 0.51/0.73  thf('16', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         (((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.51/0.73          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.51/0.73          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.51/0.73          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.51/0.73      inference('sup-', [status(thm)], ['7', '15'])).
% 0.51/0.73  thf('17', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.51/0.73          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.51/0.73      inference('simplify', [status(thm)], ['16'])).
% 0.51/0.73  thf('18', plain,
% 0.51/0.73      (![X6 : $i, X7 : $i]:
% 0.51/0.73         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.51/0.73      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.51/0.73  thf('19', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         ((r2_hidden @ X0 @ X1)
% 0.51/0.73          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.51/0.73          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.51/0.73      inference('sup+', [status(thm)], ['17', '18'])).
% 0.51/0.73  thf('20', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.51/0.73      inference('simplify', [status(thm)], ['19'])).
% 0.51/0.73  thf(t45_zfmisc_1, conjecture,
% 0.51/0.73    (![A:$i,B:$i]:
% 0.51/0.73     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.51/0.73       ( r2_hidden @ A @ B ) ))).
% 0.51/0.73  thf(zf_stmt_3, negated_conjecture,
% 0.51/0.73    (~( ![A:$i,B:$i]:
% 0.51/0.73        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.51/0.73          ( r2_hidden @ A @ B ) ) )),
% 0.51/0.73    inference('cnf.neg', [status(esa)], [t45_zfmisc_1])).
% 0.51/0.73  thf('21', plain,
% 0.51/0.73      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.51/0.73  thf(d10_xboole_0, axiom,
% 0.51/0.73    (![A:$i,B:$i]:
% 0.51/0.73     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.51/0.73  thf('22', plain,
% 0.51/0.73      (![X10 : $i, X12 : $i]:
% 0.51/0.73         (((X10) = (X12))
% 0.51/0.73          | ~ (r1_tarski @ X12 @ X10)
% 0.51/0.73          | ~ (r1_tarski @ X10 @ X12))),
% 0.51/0.73      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.51/0.73  thf('23', plain,
% 0.51/0.73      ((~ (r1_tarski @ sk_B @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 0.51/0.73        | ((sk_B) = (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.51/0.73      inference('sup-', [status(thm)], ['21', '22'])).
% 0.51/0.73  thf(commutativity_k2_tarski, axiom,
% 0.51/0.73    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.51/0.73  thf('24', plain,
% 0.51/0.73      (![X23 : $i, X24 : $i]:
% 0.51/0.73         ((k2_tarski @ X24 @ X23) = (k2_tarski @ X23 @ X24))),
% 0.51/0.73      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.51/0.73  thf(l51_zfmisc_1, axiom,
% 0.51/0.73    (![A:$i,B:$i]:
% 0.51/0.73     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.51/0.73  thf('25', plain,
% 0.51/0.73      (![X58 : $i, X59 : $i]:
% 0.51/0.73         ((k3_tarski @ (k2_tarski @ X58 @ X59)) = (k2_xboole_0 @ X58 @ X59))),
% 0.51/0.73      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.51/0.73  thf('26', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.51/0.73      inference('sup+', [status(thm)], ['24', '25'])).
% 0.51/0.73  thf('27', plain,
% 0.51/0.73      (![X58 : $i, X59 : $i]:
% 0.51/0.73         ((k3_tarski @ (k2_tarski @ X58 @ X59)) = (k2_xboole_0 @ X58 @ X59))),
% 0.51/0.73      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.51/0.73  thf('28', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.51/0.73      inference('sup+', [status(thm)], ['26', '27'])).
% 0.51/0.73  thf(t7_xboole_1, axiom,
% 0.51/0.73    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.51/0.73  thf('29', plain,
% 0.51/0.73      (![X21 : $i, X22 : $i]: (r1_tarski @ X21 @ (k2_xboole_0 @ X21 @ X22))),
% 0.51/0.73      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.51/0.73  thf('30', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.51/0.73      inference('sup+', [status(thm)], ['26', '27'])).
% 0.51/0.73  thf('31', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.51/0.73      inference('demod', [status(thm)], ['23', '28', '29', '30'])).
% 0.51/0.73  thf(t70_xboole_1, axiom,
% 0.51/0.73    (![A:$i,B:$i,C:$i]:
% 0.51/0.73     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.51/0.73            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.51/0.73       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.51/0.73            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.51/0.73  thf('32', plain,
% 0.51/0.73      (![X15 : $i, X16 : $i, X18 : $i]:
% 0.51/0.73         ((r1_xboole_0 @ X15 @ X18)
% 0.51/0.73          | ~ (r1_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X18)))),
% 0.51/0.73      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.51/0.73  thf('33', plain,
% 0.51/0.73      (![X0 : $i]:
% 0.51/0.73         (~ (r1_xboole_0 @ X0 @ sk_B) | (r1_xboole_0 @ X0 @ (k1_tarski @ sk_A)))),
% 0.51/0.73      inference('sup-', [status(thm)], ['31', '32'])).
% 0.51/0.73  thf('34', plain,
% 0.51/0.73      (![X0 : $i]:
% 0.51/0.73         ((r2_hidden @ X0 @ sk_B)
% 0.51/0.73          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ sk_A)))),
% 0.51/0.73      inference('sup-', [status(thm)], ['20', '33'])).
% 0.51/0.73  thf('35', plain,
% 0.51/0.73      (![X6 : $i, X7 : $i]:
% 0.51/0.73         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.51/0.73      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.51/0.73  thf('36', plain,
% 0.51/0.73      (![X6 : $i, X7 : $i]:
% 0.51/0.73         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.51/0.73      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.51/0.73  thf('37', plain,
% 0.51/0.73      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.51/0.73         (~ (r2_hidden @ X8 @ X6)
% 0.51/0.73          | ~ (r2_hidden @ X8 @ X9)
% 0.51/0.73          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.51/0.73      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.51/0.73  thf('38', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.73         ((r1_xboole_0 @ X0 @ X1)
% 0.51/0.73          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.51/0.73          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.51/0.73      inference('sup-', [status(thm)], ['36', '37'])).
% 0.51/0.73  thf('39', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         ((r1_xboole_0 @ X0 @ X1)
% 0.51/0.73          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.51/0.73          | (r1_xboole_0 @ X0 @ X1))),
% 0.51/0.73      inference('sup-', [status(thm)], ['35', '38'])).
% 0.51/0.73  thf('40', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.51/0.73      inference('simplify', [status(thm)], ['39'])).
% 0.51/0.73  thf('41', plain,
% 0.51/0.73      (![X0 : $i]:
% 0.51/0.73         ((r2_hidden @ sk_A @ sk_B) | (r1_xboole_0 @ (k1_tarski @ sk_A) @ X0))),
% 0.51/0.73      inference('sup-', [status(thm)], ['34', '40'])).
% 0.51/0.73  thf('42', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.51/0.73  thf('43', plain, (![X0 : $i]: (r1_xboole_0 @ (k1_tarski @ sk_A) @ X0)),
% 0.51/0.73      inference('clc', [status(thm)], ['41', '42'])).
% 0.51/0.73  thf('44', plain,
% 0.51/0.73      (![X37 : $i]: ((k2_tarski @ X37 @ X37) = (k1_tarski @ X37))),
% 0.51/0.73      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.51/0.73  thf('45', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.51/0.73      inference('sup-', [status(thm)], ['3', '5'])).
% 0.51/0.73  thf('46', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.51/0.73      inference('sup+', [status(thm)], ['44', '45'])).
% 0.51/0.73  thf('47', plain,
% 0.51/0.73      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.51/0.73         (~ (r2_hidden @ X8 @ X6)
% 0.51/0.73          | ~ (r2_hidden @ X8 @ X9)
% 0.51/0.73          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.51/0.73      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.51/0.73  thf('48', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.51/0.73      inference('sup-', [status(thm)], ['46', '47'])).
% 0.51/0.73  thf('49', plain, (![X0 : $i]: ~ (r2_hidden @ sk_A @ X0)),
% 0.51/0.73      inference('sup-', [status(thm)], ['43', '48'])).
% 0.51/0.73  thf('50', plain, ($false), inference('sup-', [status(thm)], ['6', '49'])).
% 0.51/0.73  
% 0.51/0.73  % SZS output end Refutation
% 0.51/0.73  
% 0.51/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
