%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.D23rXGtkkx

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:29 EST 2020

% Result     : Theorem 1.15s
% Output     : Refutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :   77 (  80 expanded)
%              Number of leaves         :   38 (  40 expanded)
%              Depth                    :   15
%              Number of atoms          :  648 ( 683 expanded)
%              Number of equality atoms :   52 (  55 expanded)
%              Maximal formula depth    :   23 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_enumset1 @ X28 @ X28 @ X29 )
      = ( k2_tarski @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('1',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( k3_enumset1 @ X33 @ X33 @ X34 @ X35 @ X36 )
      = ( k2_enumset1 @ X33 @ X34 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('2',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k2_enumset1 @ X30 @ X30 @ X31 @ X32 )
      = ( k1_enumset1 @ X30 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('4',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( k5_enumset1 @ X42 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 )
      = ( k4_enumset1 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('5',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( k4_enumset1 @ X37 @ X37 @ X38 @ X39 @ X40 @ X41 )
      = ( k3_enumset1 @ X37 @ X38 @ X39 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('7',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( k6_enumset1 @ X48 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 )
      = ( k5_enumset1 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 ) ) ),
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

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
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

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( I
        = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) )
    <=> ! [J: $i] :
          ( ( r2_hidden @ J @ I )
        <=> ~ ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X67: $i,X68: $i,X69: $i,X70: $i,X71: $i,X72: $i,X73: $i,X74: $i,X75: $i,X76: $i] :
      ( ( zip_tseitin_0 @ X67 @ X68 @ X69 @ X70 @ X71 @ X72 @ X73 @ X74 @ X75 )
      | ( r2_hidden @ X67 @ X76 )
      | ( X76
       != ( k6_enumset1 @ X75 @ X74 @ X73 @ X72 @ X71 @ X70 @ X69 @ X68 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('9',plain,(
    ! [X67: $i,X68: $i,X69: $i,X70: $i,X71: $i,X72: $i,X73: $i,X74: $i,X75: $i] :
      ( ( r2_hidden @ X67 @ ( k6_enumset1 @ X75 @ X74 @ X73 @ X72 @ X71 @ X70 @ X69 @ X68 ) )
      | ( zip_tseitin_0 @ X67 @ X68 @ X69 @ X70 @ X71 @ X72 @ X73 @ X74 @ X75 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6 ) ) ),
    inference('sup+',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X57: $i,X58: $i,X59: $i,X60: $i,X61: $i,X62: $i,X63: $i,X64: $i,X65: $i] :
      ( ( X58 != X57 )
      | ~ ( zip_tseitin_0 @ X58 @ X59 @ X60 @ X61 @ X62 @ X63 @ X64 @ X65 @ X57 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('12',plain,(
    ! [X57: $i,X59: $i,X60: $i,X61: $i,X62: $i,X63: $i,X64: $i,X65: $i] :
      ~ ( zip_tseitin_0 @ X57 @ X59 @ X60 @ X61 @ X62 @ X63 @ X64 @ X65 @ X57 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( r2_hidden @ X0 @ ( k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X4 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','15'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('17',plain,(
    ! [X83: $i,X84: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X83 ) @ X84 )
      | ~ ( r2_hidden @ X84 @ X83 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X81: $i,X82: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X81 @ X82 ) )
      = ( k3_xboole_0 @ X81 @ X82 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t110_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('23',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X7 @ X6 )
      | ( r1_tarski @ ( k5_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t110_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['20','24'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('28',plain,(
    ! [X85: $i,X86: $i] :
      ( ~ ( r1_tarski @ X85 @ ( k1_relat_1 @ X86 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X86 @ X85 ) )
        = X85 )
      | ~ ( v1_relat_1 @ X86 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t191_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) )
          = ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t191_relat_1])).

thf('30',plain,(
    ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
 != ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X79: $i,X80: $i] :
      ( ( k6_subset_1 @ X79 @ X80 )
      = ( k4_xboole_0 @ X79 @ X80 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('32',plain,(
    ! [X79: $i,X80: $i] :
      ( ( k6_subset_1 @ X79 @ X80 )
      = ( k4_xboole_0 @ X79 @ X80 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('33',plain,(
    ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
 != ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
     != ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('36',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
 != ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    $false ),
    inference(simplify,[status(thm)],['36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.D23rXGtkkx
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:25:17 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.15/1.35  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.15/1.35  % Solved by: fo/fo7.sh
% 1.15/1.35  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.15/1.35  % done 972 iterations in 0.891s
% 1.15/1.35  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.15/1.35  % SZS output start Refutation
% 1.15/1.35  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.15/1.35  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 1.15/1.35  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.15/1.35  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.15/1.35  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.15/1.35  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 1.15/1.35                                           $i > $i).
% 1.15/1.35  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.15/1.35  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.15/1.35  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 1.15/1.35  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.15/1.35  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 1.15/1.35  thf(sk_A_type, type, sk_A: $i).
% 1.15/1.35  thf(sk_B_type, type, sk_B: $i).
% 1.15/1.35  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.15/1.35  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.15/1.35  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 1.15/1.35  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.15/1.35  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.15/1.35  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.15/1.35  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 1.15/1.35                                               $i > $i > $i > $o).
% 1.15/1.35  thf(t70_enumset1, axiom,
% 1.15/1.35    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.15/1.35  thf('0', plain,
% 1.15/1.35      (![X28 : $i, X29 : $i]:
% 1.15/1.35         ((k1_enumset1 @ X28 @ X28 @ X29) = (k2_tarski @ X28 @ X29))),
% 1.15/1.35      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.15/1.35  thf(t72_enumset1, axiom,
% 1.15/1.35    (![A:$i,B:$i,C:$i,D:$i]:
% 1.15/1.35     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 1.15/1.35  thf('1', plain,
% 1.15/1.35      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 1.15/1.35         ((k3_enumset1 @ X33 @ X33 @ X34 @ X35 @ X36)
% 1.15/1.35           = (k2_enumset1 @ X33 @ X34 @ X35 @ X36))),
% 1.15/1.35      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.15/1.35  thf(t71_enumset1, axiom,
% 1.15/1.35    (![A:$i,B:$i,C:$i]:
% 1.15/1.35     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 1.15/1.35  thf('2', plain,
% 1.15/1.35      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.15/1.35         ((k2_enumset1 @ X30 @ X30 @ X31 @ X32)
% 1.15/1.35           = (k1_enumset1 @ X30 @ X31 @ X32))),
% 1.15/1.35      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.15/1.35  thf('3', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.35         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.15/1.35      inference('sup+', [status(thm)], ['1', '2'])).
% 1.15/1.35  thf(t74_enumset1, axiom,
% 1.15/1.35    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.15/1.35     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 1.15/1.35       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 1.15/1.35  thf('4', plain,
% 1.15/1.35      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 1.15/1.35         ((k5_enumset1 @ X42 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47)
% 1.15/1.35           = (k4_enumset1 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47))),
% 1.15/1.35      inference('cnf', [status(esa)], [t74_enumset1])).
% 1.15/1.35  thf(t73_enumset1, axiom,
% 1.15/1.35    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.15/1.35     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 1.15/1.35       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 1.15/1.35  thf('5', plain,
% 1.15/1.35      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 1.15/1.35         ((k4_enumset1 @ X37 @ X37 @ X38 @ X39 @ X40 @ X41)
% 1.15/1.35           = (k3_enumset1 @ X37 @ X38 @ X39 @ X40 @ X41))),
% 1.15/1.35      inference('cnf', [status(esa)], [t73_enumset1])).
% 1.15/1.35  thf('6', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.15/1.35         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 1.15/1.35           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 1.15/1.35      inference('sup+', [status(thm)], ['4', '5'])).
% 1.15/1.35  thf(t75_enumset1, axiom,
% 1.15/1.35    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 1.15/1.35     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 1.15/1.35       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 1.15/1.35  thf('7', plain,
% 1.15/1.35      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 1.15/1.35         ((k6_enumset1 @ X48 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54)
% 1.15/1.35           = (k5_enumset1 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54))),
% 1.15/1.35      inference('cnf', [status(esa)], [t75_enumset1])).
% 1.15/1.35  thf(d6_enumset1, axiom,
% 1.15/1.35    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 1.15/1.35     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 1.15/1.35       ( ![J:$i]:
% 1.15/1.35         ( ( r2_hidden @ J @ I ) <=>
% 1.15/1.35           ( ~( ( ( J ) != ( H ) ) & ( ( J ) != ( G ) ) & ( ( J ) != ( F ) ) & 
% 1.15/1.35                ( ( J ) != ( E ) ) & ( ( J ) != ( D ) ) & ( ( J ) != ( C ) ) & 
% 1.15/1.35                ( ( J ) != ( B ) ) & ( ( J ) != ( A ) ) ) ) ) ) ))).
% 1.15/1.35  thf(zf_stmt_0, type, zip_tseitin_0 :
% 1.15/1.35      $i > $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 1.15/1.35  thf(zf_stmt_1, axiom,
% 1.15/1.35    (![J:$i,H:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 1.15/1.35     ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) <=>
% 1.15/1.35       ( ( ( J ) != ( A ) ) & ( ( J ) != ( B ) ) & ( ( J ) != ( C ) ) & 
% 1.15/1.35         ( ( J ) != ( D ) ) & ( ( J ) != ( E ) ) & ( ( J ) != ( F ) ) & 
% 1.15/1.35         ( ( J ) != ( G ) ) & ( ( J ) != ( H ) ) ) ))).
% 1.15/1.35  thf(zf_stmt_2, axiom,
% 1.15/1.35    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 1.15/1.35     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 1.15/1.35       ( ![J:$i]:
% 1.15/1.35         ( ( r2_hidden @ J @ I ) <=>
% 1.15/1.35           ( ~( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 1.15/1.35  thf('8', plain,
% 1.15/1.35      (![X67 : $i, X68 : $i, X69 : $i, X70 : $i, X71 : $i, X72 : $i, X73 : $i, 
% 1.15/1.35         X74 : $i, X75 : $i, X76 : $i]:
% 1.15/1.35         ((zip_tseitin_0 @ X67 @ X68 @ X69 @ X70 @ X71 @ X72 @ X73 @ X74 @ X75)
% 1.15/1.35          | (r2_hidden @ X67 @ X76)
% 1.15/1.35          | ((X76)
% 1.15/1.35              != (k6_enumset1 @ X75 @ X74 @ X73 @ X72 @ X71 @ X70 @ X69 @ X68)))),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.15/1.35  thf('9', plain,
% 1.15/1.35      (![X67 : $i, X68 : $i, X69 : $i, X70 : $i, X71 : $i, X72 : $i, X73 : $i, 
% 1.15/1.35         X74 : $i, X75 : $i]:
% 1.15/1.35         ((r2_hidden @ X67 @ 
% 1.15/1.35           (k6_enumset1 @ X75 @ X74 @ X73 @ X72 @ X71 @ X70 @ X69 @ X68))
% 1.15/1.35          | (zip_tseitin_0 @ X67 @ X68 @ X69 @ X70 @ X71 @ X72 @ X73 @ X74 @ 
% 1.15/1.35             X75))),
% 1.15/1.35      inference('simplify', [status(thm)], ['8'])).
% 1.15/1.35  thf('10', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 1.15/1.35         ((r2_hidden @ X7 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 1.15/1.35          | (zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6))),
% 1.15/1.35      inference('sup+', [status(thm)], ['7', '9'])).
% 1.15/1.35  thf('11', plain,
% 1.15/1.35      (![X57 : $i, X58 : $i, X59 : $i, X60 : $i, X61 : $i, X62 : $i, X63 : $i, 
% 1.15/1.35         X64 : $i, X65 : $i]:
% 1.15/1.35         (((X58) != (X57))
% 1.15/1.35          | ~ (zip_tseitin_0 @ X58 @ X59 @ X60 @ X61 @ X62 @ X63 @ X64 @ X65 @ 
% 1.15/1.35               X57))),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.15/1.35  thf('12', plain,
% 1.15/1.35      (![X57 : $i, X59 : $i, X60 : $i, X61 : $i, X62 : $i, X63 : $i, X64 : $i, 
% 1.15/1.35         X65 : $i]:
% 1.15/1.35         ~ (zip_tseitin_0 @ X57 @ X59 @ X60 @ X61 @ X62 @ X63 @ X64 @ X65 @ X57)),
% 1.15/1.35      inference('simplify', [status(thm)], ['11'])).
% 1.15/1.35  thf('13', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.15/1.35         (r2_hidden @ X0 @ (k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6))),
% 1.15/1.35      inference('sup-', [status(thm)], ['10', '12'])).
% 1.15/1.35  thf('14', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.15/1.35         (r2_hidden @ X4 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 1.15/1.35      inference('sup+', [status(thm)], ['6', '13'])).
% 1.15/1.35  thf('15', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.35         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.15/1.35      inference('sup+', [status(thm)], ['3', '14'])).
% 1.15/1.35  thf('16', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 1.15/1.35      inference('sup+', [status(thm)], ['0', '15'])).
% 1.15/1.35  thf(t4_setfam_1, axiom,
% 1.15/1.35    (![A:$i,B:$i]:
% 1.15/1.35     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 1.15/1.35  thf('17', plain,
% 1.15/1.35      (![X83 : $i, X84 : $i]:
% 1.15/1.35         ((r1_tarski @ (k1_setfam_1 @ X83) @ X84) | ~ (r2_hidden @ X84 @ X83))),
% 1.15/1.35      inference('cnf', [status(esa)], [t4_setfam_1])).
% 1.15/1.35  thf('18', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X1)),
% 1.15/1.35      inference('sup-', [status(thm)], ['16', '17'])).
% 1.15/1.35  thf(t12_setfam_1, axiom,
% 1.15/1.35    (![A:$i,B:$i]:
% 1.15/1.35     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.15/1.35  thf('19', plain,
% 1.15/1.35      (![X81 : $i, X82 : $i]:
% 1.15/1.35         ((k1_setfam_1 @ (k2_tarski @ X81 @ X82)) = (k3_xboole_0 @ X81 @ X82))),
% 1.15/1.35      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.15/1.35  thf('20', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 1.15/1.35      inference('demod', [status(thm)], ['18', '19'])).
% 1.15/1.35  thf(d10_xboole_0, axiom,
% 1.15/1.35    (![A:$i,B:$i]:
% 1.15/1.35     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.15/1.35  thf('21', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.15/1.35      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.15/1.35  thf('22', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.15/1.35      inference('simplify', [status(thm)], ['21'])).
% 1.15/1.35  thf(t110_xboole_1, axiom,
% 1.15/1.35    (![A:$i,B:$i,C:$i]:
% 1.15/1.35     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 1.15/1.35       ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 1.15/1.35  thf('23', plain,
% 1.15/1.35      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.15/1.35         (~ (r1_tarski @ X5 @ X6)
% 1.15/1.35          | ~ (r1_tarski @ X7 @ X6)
% 1.15/1.35          | (r1_tarski @ (k5_xboole_0 @ X5 @ X7) @ X6))),
% 1.15/1.35      inference('cnf', [status(esa)], [t110_xboole_1])).
% 1.15/1.35  thf('24', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((r1_tarski @ (k5_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 1.15/1.35      inference('sup-', [status(thm)], ['22', '23'])).
% 1.15/1.35  thf('25', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         (r1_tarski @ (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) @ X0)),
% 1.15/1.35      inference('sup-', [status(thm)], ['20', '24'])).
% 1.15/1.35  thf(t100_xboole_1, axiom,
% 1.15/1.35    (![A:$i,B:$i]:
% 1.15/1.35     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.15/1.35  thf('26', plain,
% 1.15/1.35      (![X3 : $i, X4 : $i]:
% 1.15/1.35         ((k4_xboole_0 @ X3 @ X4)
% 1.15/1.35           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 1.15/1.35      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.15/1.35  thf('27', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 1.15/1.35      inference('demod', [status(thm)], ['25', '26'])).
% 1.15/1.35  thf(t91_relat_1, axiom,
% 1.15/1.35    (![A:$i,B:$i]:
% 1.15/1.35     ( ( v1_relat_1 @ B ) =>
% 1.15/1.35       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 1.15/1.35         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 1.15/1.35  thf('28', plain,
% 1.15/1.35      (![X85 : $i, X86 : $i]:
% 1.15/1.35         (~ (r1_tarski @ X85 @ (k1_relat_1 @ X86))
% 1.15/1.35          | ((k1_relat_1 @ (k7_relat_1 @ X86 @ X85)) = (X85))
% 1.15/1.35          | ~ (v1_relat_1 @ X86))),
% 1.15/1.35      inference('cnf', [status(esa)], [t91_relat_1])).
% 1.15/1.35  thf('29', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         (~ (v1_relat_1 @ X0)
% 1.15/1.35          | ((k1_relat_1 @ 
% 1.15/1.35              (k7_relat_1 @ X0 @ (k4_xboole_0 @ (k1_relat_1 @ X0) @ X1)))
% 1.15/1.35              = (k4_xboole_0 @ (k1_relat_1 @ X0) @ X1)))),
% 1.15/1.35      inference('sup-', [status(thm)], ['27', '28'])).
% 1.15/1.35  thf(t191_relat_1, conjecture,
% 1.15/1.35    (![A:$i,B:$i]:
% 1.15/1.35     ( ( v1_relat_1 @ B ) =>
% 1.15/1.35       ( ( k1_relat_1 @
% 1.15/1.35           ( k7_relat_1 @ B @ ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) =
% 1.15/1.35         ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.15/1.35  thf(zf_stmt_3, negated_conjecture,
% 1.15/1.35    (~( ![A:$i,B:$i]:
% 1.15/1.35        ( ( v1_relat_1 @ B ) =>
% 1.15/1.35          ( ( k1_relat_1 @
% 1.15/1.35              ( k7_relat_1 @ B @ ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) =
% 1.15/1.35            ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 1.15/1.35    inference('cnf.neg', [status(esa)], [t191_relat_1])).
% 1.15/1.35  thf('30', plain,
% 1.15/1.35      (((k1_relat_1 @ 
% 1.15/1.35         (k7_relat_1 @ sk_B @ (k6_subset_1 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 1.15/1.35         != (k6_subset_1 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.15/1.35  thf(redefinition_k6_subset_1, axiom,
% 1.15/1.35    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.15/1.35  thf('31', plain,
% 1.15/1.35      (![X79 : $i, X80 : $i]:
% 1.15/1.35         ((k6_subset_1 @ X79 @ X80) = (k4_xboole_0 @ X79 @ X80))),
% 1.15/1.35      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.15/1.35  thf('32', plain,
% 1.15/1.35      (![X79 : $i, X80 : $i]:
% 1.15/1.35         ((k6_subset_1 @ X79 @ X80) = (k4_xboole_0 @ X79 @ X80))),
% 1.15/1.35      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.15/1.35  thf('33', plain,
% 1.15/1.35      (((k1_relat_1 @ 
% 1.15/1.35         (k7_relat_1 @ sk_B @ (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 1.15/1.35         != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 1.15/1.35      inference('demod', [status(thm)], ['30', '31', '32'])).
% 1.15/1.35  thf('34', plain,
% 1.15/1.35      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 1.15/1.35          != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 1.15/1.35        | ~ (v1_relat_1 @ sk_B))),
% 1.15/1.35      inference('sup-', [status(thm)], ['29', '33'])).
% 1.15/1.35  thf('35', plain, ((v1_relat_1 @ sk_B)),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.15/1.35  thf('36', plain,
% 1.15/1.35      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 1.15/1.35         != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 1.15/1.35      inference('demod', [status(thm)], ['34', '35'])).
% 1.15/1.35  thf('37', plain, ($false), inference('simplify', [status(thm)], ['36'])).
% 1.15/1.35  
% 1.15/1.35  % SZS output end Refutation
% 1.15/1.35  
% 1.15/1.36  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
