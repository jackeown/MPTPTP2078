%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RpYVn9EiKw

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:28 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :   84 (  92 expanded)
%              Number of leaves         :   39 (  44 expanded)
%              Depth                    :   17
%              Number of atoms          :  692 ( 765 expanded)
%              Number of equality atoms :   57 (  65 expanded)
%              Maximal formula depth    :   23 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_enumset1 @ X10 @ X10 @ X11 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k2_enumset1 @ X12 @ X12 @ X13 @ X14 )
      = ( k1_enumset1 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k3_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k4_enumset1 @ X19 @ X19 @ X20 @ X21 @ X22 @ X23 )
      = ( k3_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('4',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k5_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 )
      = ( k4_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('5',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( k6_enumset1 @ X30 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 )
      = ( k5_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 ) ) ),
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

thf('6',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( zip_tseitin_0 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 )
      | ( r2_hidden @ X47 @ X56 )
      | ( X56
       != ( k6_enumset1 @ X55 @ X54 @ X53 @ X52 @ X51 @ X50 @ X49 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('7',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( r2_hidden @ X47 @ ( k6_enumset1 @ X55 @ X54 @ X53 @ X52 @ X51 @ X50 @ X49 @ X48 ) )
      | ( zip_tseitin_0 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6 ) ) ),
    inference('sup+',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( X38 != X37 )
      | ~ ( zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,(
    ! [X37: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ~ ( zip_tseitin_0 @ X37 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X37 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( r2_hidden @ X0 @ ( k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( r2_hidden @ X5 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X4 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','15'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('17',plain,(
    ! [X63: $i,X64: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X63 ) @ X64 )
      | ~ ( r2_hidden @ X64 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('19',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_tarski @ X9 @ X8 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X61: $i,X62: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X61 @ X62 ) )
      = ( k3_xboole_0 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 ) ),
    inference(demod,[status(thm)],['18','21'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t110_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('25',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X7 @ X6 )
      | ( r1_tarski @ ( k5_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t110_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['22','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('29',plain,(
    ! [X61: $i,X62: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X61 @ X62 ) )
      = ( k3_xboole_0 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('31',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['27','32'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('34',plain,(
    ! [X65: $i,X66: $i] :
      ( ~ ( r1_tarski @ X65 @ ( k1_relat_1 @ X66 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X66 @ X65 ) )
        = X65 )
      | ~ ( v1_relat_1 @ X66 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

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

thf('36',plain,(
    ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
 != ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('37',plain,(
    ! [X59: $i,X60: $i] :
      ( ( k6_subset_1 @ X59 @ X60 )
      = ( k4_xboole_0 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('38',plain,(
    ! [X59: $i,X60: $i] :
      ( ( k6_subset_1 @ X59 @ X60 )
      = ( k4_xboole_0 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('39',plain,(
    ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
 != ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
     != ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['35','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('42',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
 != ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    $false ),
    inference(simplify,[status(thm)],['42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RpYVn9EiKw
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:05:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.55/0.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.55/0.74  % Solved by: fo/fo7.sh
% 0.55/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.74  % done 281 iterations in 0.281s
% 0.55/0.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.55/0.74  % SZS output start Refutation
% 0.55/0.74  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.55/0.74  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.55/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.74  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.55/0.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.55/0.74  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 0.55/0.74                                               $i > $i > $i > $o).
% 0.55/0.74  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.55/0.74  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.55/0.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.55/0.74  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.55/0.74  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.55/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.74  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.55/0.74  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.55/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.74  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.55/0.74                                           $i > $i).
% 0.55/0.74  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.55/0.74  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.55/0.74  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.55/0.74  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.55/0.74  thf(t70_enumset1, axiom,
% 0.55/0.74    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.55/0.74  thf('0', plain,
% 0.55/0.74      (![X10 : $i, X11 : $i]:
% 0.55/0.74         ((k1_enumset1 @ X10 @ X10 @ X11) = (k2_tarski @ X10 @ X11))),
% 0.55/0.74      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.55/0.74  thf(t71_enumset1, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i]:
% 0.55/0.74     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.55/0.74  thf('1', plain,
% 0.55/0.74      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.55/0.74         ((k2_enumset1 @ X12 @ X12 @ X13 @ X14)
% 0.55/0.74           = (k1_enumset1 @ X12 @ X13 @ X14))),
% 0.55/0.74      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.55/0.74  thf(t72_enumset1, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.74     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.55/0.74  thf('2', plain,
% 0.55/0.74      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.55/0.74         ((k3_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18)
% 0.55/0.74           = (k2_enumset1 @ X15 @ X16 @ X17 @ X18))),
% 0.55/0.74      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.55/0.74  thf(t73_enumset1, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.55/0.74     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.55/0.74       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.55/0.74  thf('3', plain,
% 0.55/0.74      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.55/0.74         ((k4_enumset1 @ X19 @ X19 @ X20 @ X21 @ X22 @ X23)
% 0.55/0.74           = (k3_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23))),
% 0.55/0.74      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.55/0.74  thf(t74_enumset1, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.55/0.74     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.55/0.74       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.55/0.74  thf('4', plain,
% 0.55/0.74      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.55/0.74         ((k5_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29)
% 0.55/0.74           = (k4_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29))),
% 0.55/0.74      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.55/0.74  thf(t75_enumset1, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.55/0.74     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.55/0.74       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.55/0.74  thf('5', plain,
% 0.55/0.74      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.55/0.74         ((k6_enumset1 @ X30 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36)
% 0.55/0.74           = (k5_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36))),
% 0.55/0.74      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.55/0.74  thf(d6_enumset1, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.55/0.74     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 0.55/0.74       ( ![J:$i]:
% 0.55/0.74         ( ( r2_hidden @ J @ I ) <=>
% 0.55/0.74           ( ~( ( ( J ) != ( H ) ) & ( ( J ) != ( G ) ) & ( ( J ) != ( F ) ) & 
% 0.55/0.74                ( ( J ) != ( E ) ) & ( ( J ) != ( D ) ) & ( ( J ) != ( C ) ) & 
% 0.55/0.75                ( ( J ) != ( B ) ) & ( ( J ) != ( A ) ) ) ) ) ) ))).
% 0.55/0.75  thf(zf_stmt_0, type, zip_tseitin_0 :
% 0.55/0.75      $i > $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 0.55/0.75  thf(zf_stmt_1, axiom,
% 0.55/0.75    (![J:$i,H:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.55/0.75     ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) <=>
% 0.55/0.75       ( ( ( J ) != ( A ) ) & ( ( J ) != ( B ) ) & ( ( J ) != ( C ) ) & 
% 0.55/0.75         ( ( J ) != ( D ) ) & ( ( J ) != ( E ) ) & ( ( J ) != ( F ) ) & 
% 0.55/0.75         ( ( J ) != ( G ) ) & ( ( J ) != ( H ) ) ) ))).
% 0.55/0.75  thf(zf_stmt_2, axiom,
% 0.55/0.75    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.55/0.75     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 0.55/0.75       ( ![J:$i]:
% 0.55/0.75         ( ( r2_hidden @ J @ I ) <=>
% 0.55/0.75           ( ~( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.55/0.75  thf('6', plain,
% 0.55/0.75      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, 
% 0.55/0.75         X54 : $i, X55 : $i, X56 : $i]:
% 0.55/0.75         ((zip_tseitin_0 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55)
% 0.55/0.75          | (r2_hidden @ X47 @ X56)
% 0.55/0.75          | ((X56)
% 0.55/0.75              != (k6_enumset1 @ X55 @ X54 @ X53 @ X52 @ X51 @ X50 @ X49 @ X48)))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.55/0.75  thf('7', plain,
% 0.55/0.75      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, 
% 0.55/0.75         X54 : $i, X55 : $i]:
% 0.55/0.75         ((r2_hidden @ X47 @ 
% 0.55/0.75           (k6_enumset1 @ X55 @ X54 @ X53 @ X52 @ X51 @ X50 @ X49 @ X48))
% 0.55/0.75          | (zip_tseitin_0 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ 
% 0.55/0.75             X55))),
% 0.55/0.75      inference('simplify', [status(thm)], ['6'])).
% 0.55/0.75  thf('8', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.55/0.75         ((r2_hidden @ X7 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.55/0.75          | (zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6))),
% 0.55/0.75      inference('sup+', [status(thm)], ['5', '7'])).
% 0.55/0.75  thf('9', plain,
% 0.55/0.75      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, 
% 0.55/0.75         X44 : $i, X45 : $i]:
% 0.55/0.75         (((X38) != (X37))
% 0.55/0.75          | ~ (zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ 
% 0.55/0.75               X37))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.55/0.75  thf('10', plain,
% 0.55/0.75      (![X37 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, 
% 0.55/0.75         X45 : $i]:
% 0.55/0.75         ~ (zip_tseitin_0 @ X37 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X37)),
% 0.55/0.75      inference('simplify', [status(thm)], ['9'])).
% 0.55/0.75  thf('11', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.55/0.75         (r2_hidden @ X0 @ (k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6))),
% 0.55/0.75      inference('sup-', [status(thm)], ['8', '10'])).
% 0.55/0.75  thf('12', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.55/0.75         (r2_hidden @ X5 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.55/0.75      inference('sup+', [status(thm)], ['4', '11'])).
% 0.55/0.75  thf('13', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.55/0.75         (r2_hidden @ X4 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.55/0.75      inference('sup+', [status(thm)], ['3', '12'])).
% 0.55/0.75  thf('14', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.55/0.75         (r2_hidden @ X3 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.55/0.75      inference('sup+', [status(thm)], ['2', '13'])).
% 0.55/0.75  thf('15', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.75         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.55/0.75      inference('sup+', [status(thm)], ['1', '14'])).
% 0.55/0.75  thf('16', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.55/0.75      inference('sup+', [status(thm)], ['0', '15'])).
% 0.55/0.75  thf(t4_setfam_1, axiom,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 0.55/0.75  thf('17', plain,
% 0.55/0.75      (![X63 : $i, X64 : $i]:
% 0.55/0.75         ((r1_tarski @ (k1_setfam_1 @ X63) @ X64) | ~ (r2_hidden @ X64 @ X63))),
% 0.55/0.75      inference('cnf', [status(esa)], [t4_setfam_1])).
% 0.55/0.75  thf('18', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X1)),
% 0.55/0.75      inference('sup-', [status(thm)], ['16', '17'])).
% 0.55/0.75  thf(commutativity_k2_tarski, axiom,
% 0.55/0.75    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.55/0.75  thf('19', plain,
% 0.55/0.75      (![X8 : $i, X9 : $i]: ((k2_tarski @ X9 @ X8) = (k2_tarski @ X8 @ X9))),
% 0.55/0.75      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.55/0.75  thf(t12_setfam_1, axiom,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.55/0.75  thf('20', plain,
% 0.55/0.75      (![X61 : $i, X62 : $i]:
% 0.55/0.75         ((k1_setfam_1 @ (k2_tarski @ X61 @ X62)) = (k3_xboole_0 @ X61 @ X62))),
% 0.55/0.75      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.55/0.75  thf('21', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.55/0.75      inference('sup+', [status(thm)], ['19', '20'])).
% 0.55/0.75  thf('22', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X1)),
% 0.55/0.75      inference('demod', [status(thm)], ['18', '21'])).
% 0.55/0.75  thf(d10_xboole_0, axiom,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.55/0.75  thf('23', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.55/0.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.55/0.75  thf('24', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.55/0.75      inference('simplify', [status(thm)], ['23'])).
% 0.55/0.75  thf(t110_xboole_1, axiom,
% 0.55/0.75    (![A:$i,B:$i,C:$i]:
% 0.55/0.75     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.55/0.75       ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 0.55/0.75  thf('25', plain,
% 0.55/0.75      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.55/0.75         (~ (r1_tarski @ X5 @ X6)
% 0.55/0.75          | ~ (r1_tarski @ X7 @ X6)
% 0.55/0.75          | (r1_tarski @ (k5_xboole_0 @ X5 @ X7) @ X6))),
% 0.55/0.75      inference('cnf', [status(esa)], [t110_xboole_1])).
% 0.55/0.75  thf('26', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         ((r1_tarski @ (k5_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 0.55/0.75      inference('sup-', [status(thm)], ['24', '25'])).
% 0.55/0.75  thf('27', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         (r1_tarski @ (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) @ X0)),
% 0.55/0.75      inference('sup-', [status(thm)], ['22', '26'])).
% 0.55/0.75  thf('28', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.55/0.75      inference('sup+', [status(thm)], ['19', '20'])).
% 0.55/0.75  thf('29', plain,
% 0.55/0.75      (![X61 : $i, X62 : $i]:
% 0.55/0.75         ((k1_setfam_1 @ (k2_tarski @ X61 @ X62)) = (k3_xboole_0 @ X61 @ X62))),
% 0.55/0.75      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.55/0.75  thf('30', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.55/0.75      inference('sup+', [status(thm)], ['28', '29'])).
% 0.55/0.75  thf(t100_xboole_1, axiom,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.55/0.75  thf('31', plain,
% 0.55/0.75      (![X3 : $i, X4 : $i]:
% 0.55/0.75         ((k4_xboole_0 @ X3 @ X4)
% 0.55/0.75           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.55/0.75      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.55/0.75  thf('32', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         ((k4_xboole_0 @ X0 @ X1)
% 0.55/0.75           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.55/0.75      inference('sup+', [status(thm)], ['30', '31'])).
% 0.55/0.75  thf('33', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.55/0.75      inference('demod', [status(thm)], ['27', '32'])).
% 0.55/0.75  thf(t91_relat_1, axiom,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( v1_relat_1 @ B ) =>
% 0.55/0.75       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.55/0.75         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.55/0.75  thf('34', plain,
% 0.55/0.75      (![X65 : $i, X66 : $i]:
% 0.55/0.75         (~ (r1_tarski @ X65 @ (k1_relat_1 @ X66))
% 0.55/0.75          | ((k1_relat_1 @ (k7_relat_1 @ X66 @ X65)) = (X65))
% 0.55/0.75          | ~ (v1_relat_1 @ X66))),
% 0.55/0.75      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.55/0.75  thf('35', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         (~ (v1_relat_1 @ X0)
% 0.55/0.75          | ((k1_relat_1 @ 
% 0.55/0.75              (k7_relat_1 @ X0 @ (k4_xboole_0 @ (k1_relat_1 @ X0) @ X1)))
% 0.55/0.75              = (k4_xboole_0 @ (k1_relat_1 @ X0) @ X1)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['33', '34'])).
% 0.55/0.75  thf(t191_relat_1, conjecture,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( v1_relat_1 @ B ) =>
% 0.55/0.75       ( ( k1_relat_1 @
% 0.55/0.75           ( k7_relat_1 @ B @ ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) =
% 0.55/0.75         ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.55/0.75  thf(zf_stmt_3, negated_conjecture,
% 0.55/0.75    (~( ![A:$i,B:$i]:
% 0.55/0.75        ( ( v1_relat_1 @ B ) =>
% 0.55/0.75          ( ( k1_relat_1 @
% 0.55/0.75              ( k7_relat_1 @ B @ ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) =
% 0.55/0.75            ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 0.55/0.75    inference('cnf.neg', [status(esa)], [t191_relat_1])).
% 0.55/0.75  thf('36', plain,
% 0.55/0.75      (((k1_relat_1 @ 
% 0.55/0.75         (k7_relat_1 @ sk_B @ (k6_subset_1 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 0.55/0.75         != (k6_subset_1 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.55/0.75  thf(redefinition_k6_subset_1, axiom,
% 0.55/0.75    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.55/0.75  thf('37', plain,
% 0.55/0.75      (![X59 : $i, X60 : $i]:
% 0.55/0.75         ((k6_subset_1 @ X59 @ X60) = (k4_xboole_0 @ X59 @ X60))),
% 0.55/0.75      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.55/0.75  thf('38', plain,
% 0.55/0.75      (![X59 : $i, X60 : $i]:
% 0.55/0.75         ((k6_subset_1 @ X59 @ X60) = (k4_xboole_0 @ X59 @ X60))),
% 0.55/0.75      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.55/0.75  thf('39', plain,
% 0.55/0.75      (((k1_relat_1 @ 
% 0.55/0.75         (k7_relat_1 @ sk_B @ (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 0.55/0.75         != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.55/0.75      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.55/0.75  thf('40', plain,
% 0.55/0.75      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.55/0.75          != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.55/0.75        | ~ (v1_relat_1 @ sk_B))),
% 0.55/0.75      inference('sup-', [status(thm)], ['35', '39'])).
% 0.55/0.75  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.55/0.75  thf('42', plain,
% 0.55/0.75      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.55/0.75         != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.55/0.75      inference('demod', [status(thm)], ['40', '41'])).
% 0.55/0.75  thf('43', plain, ($false), inference('simplify', [status(thm)], ['42'])).
% 0.55/0.75  
% 0.55/0.75  % SZS output end Refutation
% 0.55/0.75  
% 0.55/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
