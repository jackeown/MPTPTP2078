%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8v6H0fc1vO

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 163 expanded)
%              Number of leaves         :   34 (  62 expanded)
%              Depth                    :   15
%              Number of atoms          :  626 (1551 expanded)
%              Number of equality atoms :   71 ( 177 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(l44_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('0',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X11 @ X10 ) @ X10 )
      | ( X10
        = ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf(t14_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( k1_relat_1 @ B )
            = ( k1_tarski @ A ) )
         => ( ( k2_relat_1 @ B )
            = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_funct_1])).

thf('1',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X30: $i] :
      ( ( ( k9_relat_1 @ X30 @ ( k1_relat_1 @ X30 ) )
        = ( k2_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('3',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('6',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k11_relat_1 @ X28 @ X29 )
        = ( k9_relat_1 @ X28 @ ( k1_tarski @ X29 ) ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('7',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('10',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X31 @ ( k11_relat_1 @ X32 @ X33 ) )
      | ( r2_hidden @ ( k4_tarski @ X33 @ X31 ) @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','13'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('15',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X36 @ X38 ) @ X37 )
      | ( X38
        = ( k1_funct_1 @ X37 @ X36 ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X2 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('22',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X3 @ X3 @ X4 @ X5 )
      = ( k1_enumset1 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('23',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k3_enumset1 @ X6 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
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

thf('24',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 )
      | ( r2_hidden @ X19 @ X25 )
      | ( X25
       != ( k3_enumset1 @ X24 @ X23 @ X22 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('25',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ X19 @ ( k3_enumset1 @ X24 @ X23 @ X22 @ X21 @ X20 ) )
      | ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 ) ) ),
    inference('sup+',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X13 != X12 )
      | ~ ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 @ X17 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('28',plain,(
    ! [X12: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ~ ( zip_tseitin_0 @ X12 @ X14 @ X15 @ X16 @ X17 @ X12 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','31'])).

thf('33',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t205_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf('34',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X35 @ ( k1_relat_1 @ X34 ) )
      | ( ( k11_relat_1 @ X34 @ X35 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k11_relat_1 @ sk_B @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k11_relat_1 @ sk_B @ X0 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('40',plain,(
    ( k2_relat_1 @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['19','40'])).

thf('42',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( ( sk_C @ X11 @ X10 )
       != X11 )
      | ( X10
        = ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ sk_A )
       != X0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_B )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ( k2_relat_1 @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['38','39'])).

thf('47',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['44','45','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8v6H0fc1vO
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:38:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 58 iterations in 0.045s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.50  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.20/0.50  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o).
% 0.20/0.50  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.50  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.20/0.50  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.20/0.50  thf(l44_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.50          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (![X10 : $i, X11 : $i]:
% 0.20/0.50         (((X10) = (k1_xboole_0))
% 0.20/0.50          | (r2_hidden @ (sk_C @ X11 @ X10) @ X10)
% 0.20/0.50          | ((X10) = (k1_tarski @ X11)))),
% 0.20/0.50      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 0.20/0.50  thf(t14_funct_1, conjecture,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.50       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.20/0.50         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i]:
% 0.20/0.50        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.50          ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.20/0.50            ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t14_funct_1])).
% 0.20/0.50  thf('1', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t146_relat_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) =>
% 0.20/0.50       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X30 : $i]:
% 0.20/0.50         (((k9_relat_1 @ X30 @ (k1_relat_1 @ X30)) = (k2_relat_1 @ X30))
% 0.20/0.50          | ~ (v1_relat_1 @ X30))),
% 0.20/0.50      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      ((((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k2_relat_1 @ sk_B))
% 0.20/0.50        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.50      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf('4', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k2_relat_1 @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.50  thf(d16_relat_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X28 : $i, X29 : $i]:
% 0.20/0.50         (((k11_relat_1 @ X28 @ X29) = (k9_relat_1 @ X28 @ (k1_tarski @ X29)))
% 0.20/0.50          | ~ (v1_relat_1 @ X28))),
% 0.20/0.50      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      ((((k11_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ sk_B))
% 0.20/0.50        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.50      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.50  thf('8', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('9', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.50  thf(t204_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ C ) =>
% 0.20/0.50       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.20/0.50         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X31 @ (k11_relat_1 @ X32 @ X33))
% 0.20/0.50          | (r2_hidden @ (k4_tarski @ X33 @ X31) @ X32)
% 0.20/0.50          | ~ (v1_relat_1 @ X32))),
% 0.20/0.50      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 0.20/0.50          | ~ (v1_relat_1 @ sk_B)
% 0.20/0.50          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.50  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 0.20/0.50          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.20/0.50          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.20/0.50          | (r2_hidden @ 
% 0.20/0.50             (k4_tarski @ sk_A @ (sk_C @ X0 @ (k2_relat_1 @ sk_B))) @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '13'])).
% 0.20/0.50  thf(t8_funct_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.50       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.20/0.50         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.50           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.20/0.50         (~ (r2_hidden @ (k4_tarski @ X36 @ X38) @ X37)
% 0.20/0.50          | ((X38) = (k1_funct_1 @ X37 @ X36))
% 0.20/0.50          | ~ (v1_funct_1 @ X37)
% 0.20/0.50          | ~ (v1_relat_1 @ X37))),
% 0.20/0.50      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.20/0.50          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.20/0.50          | ~ (v1_relat_1 @ sk_B)
% 0.20/0.50          | ~ (v1_funct_1 @ sk_B)
% 0.20/0.50          | ((sk_C @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.50  thf('17', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('18', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.20/0.50          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.20/0.50          | ((sk_C @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.20/0.50  thf(t69_enumset1, axiom,
% 0.20/0.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.50  thf('20', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.50  thf(t70_enumset1, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X1 : $i, X2 : $i]:
% 0.20/0.50         ((k1_enumset1 @ X1 @ X1 @ X2) = (k2_tarski @ X1 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.50  thf(t71_enumset1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.50         ((k2_enumset1 @ X3 @ X3 @ X4 @ X5) = (k1_enumset1 @ X3 @ X4 @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.20/0.50  thf(t72_enumset1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.50         ((k3_enumset1 @ X6 @ X6 @ X7 @ X8 @ X9)
% 0.20/0.50           = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.20/0.50  thf(d3_enumset1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.50     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 0.20/0.50       ( ![G:$i]:
% 0.20/0.50         ( ( r2_hidden @ G @ F ) <=>
% 0.20/0.50           ( ~( ( ( G ) != ( E ) ) & ( ( G ) != ( D ) ) & ( ( G ) != ( C ) ) & 
% 0.20/0.50                ( ( G ) != ( B ) ) & ( ( G ) != ( A ) ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $o).
% 0.20/0.50  thf(zf_stmt_2, axiom,
% 0.20/0.50    (![G:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.20/0.50     ( ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) <=>
% 0.20/0.50       ( ( ( G ) != ( A ) ) & ( ( G ) != ( B ) ) & ( ( G ) != ( C ) ) & 
% 0.20/0.50         ( ( G ) != ( D ) ) & ( ( G ) != ( E ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_3, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.50     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 0.20/0.50       ( ![G:$i]:
% 0.20/0.50         ( ( r2_hidden @ G @ F ) <=>
% 0.20/0.50           ( ~( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.50         ((zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24)
% 0.20/0.50          | (r2_hidden @ X19 @ X25)
% 0.20/0.50          | ((X25) != (k3_enumset1 @ X24 @ X23 @ X22 @ X21 @ X20)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.50         ((r2_hidden @ X19 @ (k3_enumset1 @ X24 @ X23 @ X22 @ X21 @ X20))
% 0.20/0.50          | (zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24))),
% 0.20/0.50      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.50         ((r2_hidden @ X4 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.50          | (zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3))),
% 0.20/0.50      inference('sup+', [status(thm)], ['23', '25'])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.50         (((X13) != (X12))
% 0.20/0.50          | ~ (zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 @ X17 @ X12))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (![X12 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.50         ~ (zip_tseitin_0 @ X12 @ X14 @ X15 @ X16 @ X17 @ X12)),
% 0.20/0.50      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         (r2_hidden @ X0 @ (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.20/0.50      inference('sup-', [status(thm)], ['26', '28'])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['22', '29'])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['21', '30'])).
% 0.20/0.50  thf('32', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['20', '31'])).
% 0.20/0.50  thf('33', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t205_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ B ) =>
% 0.20/0.50       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.20/0.50         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (![X34 : $i, X35 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X35 @ (k1_relat_1 @ X34))
% 0.20/0.50          | ((k11_relat_1 @ X34 @ X35) != (k1_xboole_0))
% 0.20/0.50          | ~ (v1_relat_1 @ X34))),
% 0.20/0.50      inference('cnf', [status(esa)], [t205_relat_1])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.20/0.50          | ~ (v1_relat_1 @ sk_B)
% 0.20/0.50          | ((k11_relat_1 @ sk_B @ X0) != (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.50  thf('36', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.20/0.50          | ((k11_relat_1 @ sk_B @ X0) != (k1_xboole_0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf('38', plain, (((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['32', '37'])).
% 0.20/0.50  thf('39', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.50  thf('40', plain, (((k2_relat_1 @ sk_B) != (k1_xboole_0))),
% 0.20/0.50      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.20/0.50          | ((sk_C @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['19', '40'])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      (![X10 : $i, X11 : $i]:
% 0.20/0.50         (((X10) = (k1_xboole_0))
% 0.20/0.50          | ((sk_C @ X11 @ X10) != (X11))
% 0.20/0.50          | ((X10) = (k1_tarski @ X11)))),
% 0.20/0.50      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k1_funct_1 @ sk_B @ sk_A) != (X0))
% 0.20/0.50          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.20/0.50          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.20/0.50          | ((k2_relat_1 @ sk_B) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      ((((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.20/0.50        | ((k2_relat_1 @ sk_B) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.20/0.50      inference('simplify', [status(thm)], ['43'])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      (((k2_relat_1 @ sk_B) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('46', plain, (((k2_relat_1 @ sk_B) != (k1_xboole_0))),
% 0.20/0.50      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.50  thf('47', plain, ($false),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['44', '45', '46'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
