%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MCM0xONy46

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:23 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 173 expanded)
%              Number of leaves         :   36 (  68 expanded)
%              Depth                    :   16
%              Number of atoms          :  825 (1832 expanded)
%              Number of equality atoms :  103 ( 196 expanded)
%              Maximal formula depth    :   23 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('1',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X33 ) @ ( k2_tarski @ X34 @ X35 ) )
      = ( k2_tarski @ ( k4_tarski @ X33 @ X34 ) @ ( k4_tarski @ X33 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t195_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = A )
            & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = B ) ) ) )).

thf('5',plain,(
    ! [X59: $i,X60: $i] :
      ( ( X59 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X59 @ X60 ) )
        = X59 )
      | ( X60 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
        = ( k1_tarski @ X1 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('7',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ( k3_mcart_1 @ X61 @ X62 @ X63 )
      = ( k4_tarski @ ( k4_tarski @ X61 @ X62 ) @ X63 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
        = ( k1_tarski @ X1 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) )
        = ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) )
      | ( ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t97_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_relat_1 @ ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) )
      = ( k1_tarski @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k1_relat_1 @ ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) )
        = ( k1_tarski @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t97_mcart_1])).

thf('10',plain,(
    ( k1_relat_1 @ ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) ) ) )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) )
     != ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,
    ( ( ( k1_tarski @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('15',plain,(
    ! [X28: $i,X29: $i] :
      ( ( X28 = k1_xboole_0 )
      | ( X29 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X29 @ X28 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,
    ( ( ( k1_tarski @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X2 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

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

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('24',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k4_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 @ X14 )
      = ( k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('25',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k5_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k4_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('26',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k6_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 )
      = ( k5_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(d6_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( I
        = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) )
    <=> ! [J: $i] :
          ( ( r2_hidden @ J @ I )
        <=> ~ ( ( J != H )
              & ( J != G )
              & ( J != F )
              & ( J != E )
              & ( J != D )
              & ( J != C )
              & ( J != B )
              & ( J != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [J: $i,H: $i,G: $i,F: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A )
    <=> ( ( J != A )
        & ( J != B )
        & ( J != C )
        & ( J != D )
        & ( J != E )
        & ( J != F )
        & ( J != G )
        & ( J != H ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( I
        = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) )
    <=> ! [J: $i] :
          ( ( r2_hidden @ J @ I )
        <=> ~ ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( zip_tseitin_0 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 )
      | ( r2_hidden @ X47 @ X56 )
      | ( X56
       != ( k6_enumset1 @ X55 @ X54 @ X53 @ X52 @ X51 @ X50 @ X49 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('28',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( r2_hidden @ X47 @ ( k6_enumset1 @ X55 @ X54 @ X53 @ X52 @ X51 @ X50 @ X49 @ X48 ) )
      | ( zip_tseitin_0 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6 ) ) ),
    inference('sup+',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( X38 != X37 )
      | ~ ( zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('31',plain,(
    ! [X37: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ~ ( zip_tseitin_0 @ X37 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X37 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( r2_hidden @ X0 @ ( k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( r2_hidden @ X5 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X4 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','36'])).

thf('38',plain,
    ( ( r2_hidden @ sk_C @ k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','37'])).

thf('39',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k2_zfmisc_1 @ X29 @ X30 )
        = k1_xboole_0 )
      | ( X30 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('40',plain,(
    ! [X29: $i] :
      ( ( k2_zfmisc_1 @ X29 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('41',plain,(
    ! [X31: $i,X32: $i] :
      ~ ( r2_hidden @ X31 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('42',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['38','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','36'])).

thf('45',plain,
    ( ( r2_hidden @ sk_B @ k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('47',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','36'])).

thf('49',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('51',plain,(
    $false ),
    inference('sup-',[status(thm)],['49','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MCM0xONy46
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:22:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.54/0.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.77  % Solved by: fo/fo7.sh
% 0.54/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.77  % done 477 iterations in 0.352s
% 0.54/0.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.77  % SZS output start Refutation
% 0.54/0.77  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.54/0.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.77  thf(sk_C_type, type, sk_C: $i).
% 0.54/0.77  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.54/0.77  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 0.54/0.77                                               $i > $i > $i > $o).
% 0.54/0.77  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.54/0.77                                           $i > $i).
% 0.54/0.77  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.54/0.77  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.54/0.77  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.54/0.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.78  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.54/0.78  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.54/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.78  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.54/0.78  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.54/0.78  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.54/0.78  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.54/0.78  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.54/0.78  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.78  thf(t69_enumset1, axiom,
% 0.54/0.78    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.54/0.78  thf('0', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.54/0.78      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.54/0.78  thf(t36_zfmisc_1, axiom,
% 0.54/0.78    (![A:$i,B:$i,C:$i]:
% 0.54/0.78     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 0.54/0.78         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 0.54/0.78       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 0.54/0.78         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 0.54/0.78  thf('1', plain,
% 0.54/0.78      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.54/0.78         ((k2_zfmisc_1 @ (k1_tarski @ X33) @ (k2_tarski @ X34 @ X35))
% 0.54/0.78           = (k2_tarski @ (k4_tarski @ X33 @ X34) @ (k4_tarski @ X33 @ X35)))),
% 0.54/0.78      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.54/0.78  thf('2', plain,
% 0.54/0.78      (![X0 : $i, X1 : $i]:
% 0.54/0.78         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0))
% 0.54/0.78           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.54/0.78      inference('sup+', [status(thm)], ['0', '1'])).
% 0.54/0.78  thf('3', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.54/0.78      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.54/0.78  thf('4', plain,
% 0.54/0.78      (![X0 : $i, X1 : $i]:
% 0.54/0.78         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.54/0.78           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.54/0.78      inference('demod', [status(thm)], ['2', '3'])).
% 0.54/0.78  thf(t195_relat_1, axiom,
% 0.54/0.78    (![A:$i,B:$i]:
% 0.54/0.78     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.54/0.78          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 0.54/0.78               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 0.54/0.78  thf('5', plain,
% 0.54/0.78      (![X59 : $i, X60 : $i]:
% 0.54/0.78         (((X59) = (k1_xboole_0))
% 0.54/0.78          | ((k1_relat_1 @ (k2_zfmisc_1 @ X59 @ X60)) = (X59))
% 0.54/0.78          | ((X60) = (k1_xboole_0)))),
% 0.54/0.78      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.54/0.78  thf('6', plain,
% 0.54/0.78      (![X0 : $i, X1 : $i]:
% 0.54/0.78         (((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.54/0.78            = (k1_tarski @ X1))
% 0.54/0.78          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.54/0.78          | ((k1_tarski @ X1) = (k1_xboole_0)))),
% 0.54/0.78      inference('sup+', [status(thm)], ['4', '5'])).
% 0.54/0.78  thf(d3_mcart_1, axiom,
% 0.54/0.78    (![A:$i,B:$i,C:$i]:
% 0.54/0.78     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.54/0.78  thf('7', plain,
% 0.54/0.78      (![X61 : $i, X62 : $i, X63 : $i]:
% 0.54/0.78         ((k3_mcart_1 @ X61 @ X62 @ X63)
% 0.54/0.78           = (k4_tarski @ (k4_tarski @ X61 @ X62) @ X63))),
% 0.54/0.78      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.54/0.78  thf('8', plain,
% 0.54/0.78      (![X0 : $i, X1 : $i]:
% 0.54/0.78         (((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.54/0.78            = (k1_tarski @ X1))
% 0.54/0.78          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.54/0.78          | ((k1_tarski @ X1) = (k1_xboole_0)))),
% 0.54/0.78      inference('sup+', [status(thm)], ['4', '5'])).
% 0.54/0.78  thf('9', plain,
% 0.54/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.78         (((k1_relat_1 @ (k1_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0)))
% 0.54/0.78            = (k1_tarski @ (k4_tarski @ X2 @ X1)))
% 0.54/0.78          | ((k1_tarski @ (k4_tarski @ X2 @ X1)) = (k1_xboole_0))
% 0.54/0.78          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.54/0.78      inference('sup+', [status(thm)], ['7', '8'])).
% 0.54/0.78  thf(t97_mcart_1, conjecture,
% 0.54/0.78    (![A:$i,B:$i,C:$i]:
% 0.54/0.78     ( ( k1_relat_1 @
% 0.54/0.78         ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) ) =
% 0.54/0.78       ( k1_tarski @ A ) ))).
% 0.54/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.78    (~( ![A:$i,B:$i,C:$i]:
% 0.54/0.78        ( ( k1_relat_1 @
% 0.54/0.78            ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) ) =
% 0.54/0.78          ( k1_tarski @ A ) ) )),
% 0.54/0.78    inference('cnf.neg', [status(esa)], [t97_mcart_1])).
% 0.54/0.78  thf('10', plain,
% 0.54/0.78      (((k1_relat_1 @ 
% 0.54/0.78         (k1_relat_1 @ (k1_tarski @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C))))
% 0.54/0.78         != (k1_tarski @ sk_A))),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.78  thf('11', plain,
% 0.54/0.78      ((((k1_relat_1 @ (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))
% 0.54/0.78          != (k1_tarski @ sk_A))
% 0.54/0.78        | ((k1_tarski @ sk_C) = (k1_xboole_0))
% 0.54/0.78        | ((k1_tarski @ (k4_tarski @ sk_A @ sk_B)) = (k1_xboole_0)))),
% 0.54/0.78      inference('sup-', [status(thm)], ['9', '10'])).
% 0.54/0.78  thf('12', plain,
% 0.54/0.78      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.54/0.78        | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.54/0.78        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.54/0.78        | ((k1_tarski @ (k4_tarski @ sk_A @ sk_B)) = (k1_xboole_0))
% 0.54/0.78        | ((k1_tarski @ sk_C) = (k1_xboole_0)))),
% 0.54/0.78      inference('sup-', [status(thm)], ['6', '11'])).
% 0.54/0.78  thf('13', plain,
% 0.54/0.78      ((((k1_tarski @ sk_C) = (k1_xboole_0))
% 0.54/0.78        | ((k1_tarski @ (k4_tarski @ sk_A @ sk_B)) = (k1_xboole_0))
% 0.54/0.78        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.54/0.78        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.54/0.78      inference('simplify', [status(thm)], ['12'])).
% 0.54/0.78  thf('14', plain,
% 0.54/0.78      (![X0 : $i, X1 : $i]:
% 0.54/0.78         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.54/0.78           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.54/0.78      inference('demod', [status(thm)], ['2', '3'])).
% 0.54/0.78  thf(t113_zfmisc_1, axiom,
% 0.54/0.78    (![A:$i,B:$i]:
% 0.54/0.78     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.54/0.78       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.54/0.78  thf('15', plain,
% 0.54/0.78      (![X28 : $i, X29 : $i]:
% 0.54/0.78         (((X28) = (k1_xboole_0))
% 0.54/0.78          | ((X29) = (k1_xboole_0))
% 0.54/0.78          | ((k2_zfmisc_1 @ X29 @ X28) != (k1_xboole_0)))),
% 0.54/0.78      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.54/0.78  thf('16', plain,
% 0.54/0.78      (![X0 : $i, X1 : $i]:
% 0.54/0.78         (((k1_tarski @ (k4_tarski @ X1 @ X0)) != (k1_xboole_0))
% 0.54/0.78          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.54/0.78          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.54/0.78      inference('sup-', [status(thm)], ['14', '15'])).
% 0.54/0.78  thf('17', plain,
% 0.54/0.78      ((((k1_xboole_0) != (k1_xboole_0))
% 0.54/0.78        | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.54/0.78        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.54/0.78        | ((k1_tarski @ sk_C) = (k1_xboole_0))
% 0.54/0.78        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.54/0.78        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.54/0.78      inference('sup-', [status(thm)], ['13', '16'])).
% 0.54/0.78  thf('18', plain,
% 0.54/0.78      ((((k1_tarski @ sk_C) = (k1_xboole_0))
% 0.54/0.78        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.54/0.78        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.54/0.78      inference('simplify', [status(thm)], ['17'])).
% 0.54/0.78  thf(t70_enumset1, axiom,
% 0.54/0.78    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.54/0.78  thf('19', plain,
% 0.54/0.78      (![X1 : $i, X2 : $i]:
% 0.54/0.78         ((k1_enumset1 @ X1 @ X1 @ X2) = (k2_tarski @ X1 @ X2))),
% 0.54/0.78      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.54/0.78  thf('20', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.54/0.78      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.54/0.78  thf('21', plain,
% 0.54/0.78      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.54/0.78      inference('sup+', [status(thm)], ['19', '20'])).
% 0.54/0.78  thf(t71_enumset1, axiom,
% 0.54/0.78    (![A:$i,B:$i,C:$i]:
% 0.54/0.78     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.54/0.78  thf('22', plain,
% 0.54/0.78      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.54/0.78         ((k2_enumset1 @ X3 @ X3 @ X4 @ X5) = (k1_enumset1 @ X3 @ X4 @ X5))),
% 0.54/0.78      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.54/0.78  thf(t72_enumset1, axiom,
% 0.54/0.78    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.78     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.54/0.78  thf('23', plain,
% 0.54/0.78      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.54/0.78         ((k3_enumset1 @ X6 @ X6 @ X7 @ X8 @ X9)
% 0.54/0.78           = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 0.54/0.78      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.54/0.78  thf(t73_enumset1, axiom,
% 0.54/0.78    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.54/0.78     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.54/0.78       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.54/0.78  thf('24', plain,
% 0.54/0.78      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.54/0.78         ((k4_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 @ X14)
% 0.54/0.78           = (k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14))),
% 0.54/0.78      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.54/0.78  thf(t74_enumset1, axiom,
% 0.54/0.78    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.54/0.78     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.54/0.78       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.54/0.78  thf('25', plain,
% 0.54/0.78      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.54/0.78         ((k5_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20)
% 0.54/0.78           = (k4_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20))),
% 0.54/0.78      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.54/0.78  thf(t75_enumset1, axiom,
% 0.54/0.78    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.54/0.78     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.54/0.78       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.54/0.78  thf('26', plain,
% 0.54/0.78      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.54/0.78         ((k6_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27)
% 0.54/0.78           = (k5_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27))),
% 0.54/0.78      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.54/0.78  thf(d6_enumset1, axiom,
% 0.54/0.78    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.54/0.78     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 0.54/0.78       ( ![J:$i]:
% 0.54/0.78         ( ( r2_hidden @ J @ I ) <=>
% 0.54/0.78           ( ~( ( ( J ) != ( H ) ) & ( ( J ) != ( G ) ) & ( ( J ) != ( F ) ) & 
% 0.54/0.78                ( ( J ) != ( E ) ) & ( ( J ) != ( D ) ) & ( ( J ) != ( C ) ) & 
% 0.54/0.78                ( ( J ) != ( B ) ) & ( ( J ) != ( A ) ) ) ) ) ) ))).
% 0.54/0.78  thf(zf_stmt_1, type, zip_tseitin_0 :
% 0.54/0.78      $i > $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 0.54/0.78  thf(zf_stmt_2, axiom,
% 0.54/0.78    (![J:$i,H:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.54/0.78     ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) <=>
% 0.54/0.78       ( ( ( J ) != ( A ) ) & ( ( J ) != ( B ) ) & ( ( J ) != ( C ) ) & 
% 0.54/0.78         ( ( J ) != ( D ) ) & ( ( J ) != ( E ) ) & ( ( J ) != ( F ) ) & 
% 0.54/0.78         ( ( J ) != ( G ) ) & ( ( J ) != ( H ) ) ) ))).
% 0.54/0.78  thf(zf_stmt_3, axiom,
% 0.54/0.78    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.54/0.78     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 0.54/0.78       ( ![J:$i]:
% 0.54/0.78         ( ( r2_hidden @ J @ I ) <=>
% 0.54/0.78           ( ~( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.54/0.78  thf('27', plain,
% 0.54/0.78      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, 
% 0.54/0.78         X54 : $i, X55 : $i, X56 : $i]:
% 0.54/0.78         ((zip_tseitin_0 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55)
% 0.54/0.78          | (r2_hidden @ X47 @ X56)
% 0.54/0.78          | ((X56)
% 0.54/0.78              != (k6_enumset1 @ X55 @ X54 @ X53 @ X52 @ X51 @ X50 @ X49 @ X48)))),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.54/0.78  thf('28', plain,
% 0.54/0.78      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, 
% 0.54/0.78         X54 : $i, X55 : $i]:
% 0.54/0.78         ((r2_hidden @ X47 @ 
% 0.54/0.78           (k6_enumset1 @ X55 @ X54 @ X53 @ X52 @ X51 @ X50 @ X49 @ X48))
% 0.54/0.78          | (zip_tseitin_0 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ 
% 0.54/0.78             X55))),
% 0.54/0.78      inference('simplify', [status(thm)], ['27'])).
% 0.54/0.78  thf('29', plain,
% 0.54/0.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.54/0.78         ((r2_hidden @ X7 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.54/0.78          | (zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6))),
% 0.54/0.78      inference('sup+', [status(thm)], ['26', '28'])).
% 0.54/0.78  thf('30', plain,
% 0.54/0.78      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, 
% 0.54/0.78         X44 : $i, X45 : $i]:
% 0.54/0.78         (((X38) != (X37))
% 0.54/0.78          | ~ (zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ 
% 0.54/0.78               X37))),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.54/0.78  thf('31', plain,
% 0.54/0.78      (![X37 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, 
% 0.54/0.78         X45 : $i]:
% 0.54/0.78         ~ (zip_tseitin_0 @ X37 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X37)),
% 0.54/0.78      inference('simplify', [status(thm)], ['30'])).
% 0.54/0.78  thf('32', plain,
% 0.54/0.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.54/0.78         (r2_hidden @ X0 @ (k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6))),
% 0.54/0.78      inference('sup-', [status(thm)], ['29', '31'])).
% 0.54/0.78  thf('33', plain,
% 0.54/0.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.54/0.78         (r2_hidden @ X5 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.54/0.78      inference('sup+', [status(thm)], ['25', '32'])).
% 0.54/0.78  thf('34', plain,
% 0.54/0.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.54/0.78         (r2_hidden @ X4 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.54/0.78      inference('sup+', [status(thm)], ['24', '33'])).
% 0.54/0.78  thf('35', plain,
% 0.54/0.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.54/0.78         (r2_hidden @ X3 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.54/0.78      inference('sup+', [status(thm)], ['23', '34'])).
% 0.54/0.78  thf('36', plain,
% 0.54/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.78         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.54/0.78      inference('sup+', [status(thm)], ['22', '35'])).
% 0.54/0.78  thf('37', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.54/0.78      inference('sup+', [status(thm)], ['21', '36'])).
% 0.54/0.78  thf('38', plain,
% 0.54/0.78      (((r2_hidden @ sk_C @ k1_xboole_0)
% 0.54/0.78        | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.54/0.78        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.54/0.78      inference('sup+', [status(thm)], ['18', '37'])).
% 0.54/0.78  thf('39', plain,
% 0.54/0.78      (![X29 : $i, X30 : $i]:
% 0.54/0.78         (((k2_zfmisc_1 @ X29 @ X30) = (k1_xboole_0))
% 0.54/0.78          | ((X30) != (k1_xboole_0)))),
% 0.54/0.78      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.54/0.78  thf('40', plain,
% 0.54/0.78      (![X29 : $i]: ((k2_zfmisc_1 @ X29 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.78      inference('simplify', [status(thm)], ['39'])).
% 0.54/0.78  thf(t152_zfmisc_1, axiom,
% 0.54/0.78    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.54/0.78  thf('41', plain,
% 0.54/0.78      (![X31 : $i, X32 : $i]: ~ (r2_hidden @ X31 @ (k2_zfmisc_1 @ X31 @ X32))),
% 0.54/0.78      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.54/0.78  thf('42', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.54/0.78      inference('sup-', [status(thm)], ['40', '41'])).
% 0.54/0.78  thf('43', plain,
% 0.54/0.78      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.54/0.78        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.54/0.78      inference('clc', [status(thm)], ['38', '42'])).
% 0.54/0.78  thf('44', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.54/0.78      inference('sup+', [status(thm)], ['21', '36'])).
% 0.54/0.78  thf('45', plain,
% 0.54/0.78      (((r2_hidden @ sk_B @ k1_xboole_0) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.54/0.78      inference('sup+', [status(thm)], ['43', '44'])).
% 0.54/0.78  thf('46', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.54/0.78      inference('sup-', [status(thm)], ['40', '41'])).
% 0.54/0.78  thf('47', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.54/0.78      inference('clc', [status(thm)], ['45', '46'])).
% 0.54/0.78  thf('48', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.54/0.78      inference('sup+', [status(thm)], ['21', '36'])).
% 0.54/0.78  thf('49', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.54/0.78      inference('sup+', [status(thm)], ['47', '48'])).
% 0.54/0.78  thf('50', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.54/0.78      inference('sup-', [status(thm)], ['40', '41'])).
% 0.54/0.78  thf('51', plain, ($false), inference('sup-', [status(thm)], ['49', '50'])).
% 0.54/0.78  
% 0.54/0.78  % SZS output end Refutation
% 0.54/0.78  
% 0.54/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
