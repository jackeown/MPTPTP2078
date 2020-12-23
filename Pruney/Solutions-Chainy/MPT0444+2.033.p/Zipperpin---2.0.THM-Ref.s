%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PgYZyjMVyG

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:49 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   81 (  94 expanded)
%              Number of leaves         :   34 (  43 expanded)
%              Depth                    :   16
%              Number of atoms          :  735 ( 868 expanded)
%              Number of equality atoms :   38 (  44 expanded)
%              Maximal formula depth    :   23 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( v1_relat_1 @ X58 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X58 @ X59 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X54 @ X55 ) )
      = ( k3_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( v1_relat_1 @ X58 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X58 @ X59 ) ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X5 @ X5 @ X6 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X7 @ X7 @ X8 @ X9 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k3_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k4_enumset1 @ X14 @ X14 @ X15 @ X16 @ X17 @ X18 )
      = ( k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('7',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( k5_enumset1 @ X19 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 )
      = ( k4_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('8',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k6_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 )
      = ( k5_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 ) ) ),
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

thf('9',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( zip_tseitin_0 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 )
      | ( r2_hidden @ X42 @ X51 )
      | ( X51
       != ( k6_enumset1 @ X50 @ X49 @ X48 @ X47 @ X46 @ X45 @ X44 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('10',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( r2_hidden @ X42 @ ( k6_enumset1 @ X50 @ X49 @ X48 @ X47 @ X46 @ X45 @ X44 @ X43 ) )
      | ( zip_tseitin_0 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6 ) ) ),
    inference('sup+',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( X33 != X34 )
      | ~ ( zip_tseitin_0 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('13',plain,(
    ! [X32: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ~ ( zip_tseitin_0 @ X34 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X32 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( r2_hidden @ X6 @ ( k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( r2_hidden @ X0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','18'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('20',plain,(
    ! [X56: $i,X57: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X56 ) @ X57 )
      | ~ ( r2_hidden @ X57 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X60: $i,X61: $i] :
      ( ~ ( v1_relat_1 @ X60 )
      | ( r1_tarski @ ( k2_relat_1 @ X61 ) @ ( k2_relat_1 @ X60 ) )
      | ~ ( r1_tarski @ X61 @ X60 )
      | ~ ( v1_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','23'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('26',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X54 @ X55 ) )
      = ( k3_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X60: $i,X61: $i] :
      ( ~ ( v1_relat_1 @ X60 )
      | ( r1_tarski @ ( k2_relat_1 @ X61 ) @ ( k2_relat_1 @ X60 ) )
      | ~ ( r1_tarski @ X61 @ X60 )
      | ~ ( v1_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( v1_relat_1 @ X58 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X58 @ X59 ) ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('32',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('33',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X54 @ X55 ) )
      = ( k3_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('34',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X3 @ X4 ) ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ X0 ) @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf(t27_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_relat_1])).

thf('38',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('39',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X54 @ X55 ) )
      = ( k3_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('40',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X54 @ X55 ) )
      = ( k3_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('41',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('44',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['42','43','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PgYZyjMVyG
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:31:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.48/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.48/0.69  % Solved by: fo/fo7.sh
% 0.48/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.69  % done 365 iterations in 0.235s
% 0.48/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.48/0.69  % SZS output start Refutation
% 0.48/0.69  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.48/0.69  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.48/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.48/0.69  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.48/0.69  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.48/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.48/0.69  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 0.48/0.69                                               $i > $i > $i > $o).
% 0.48/0.69  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.48/0.69  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.48/0.69  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.48/0.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.48/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.69  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.48/0.69  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.48/0.69                                           $i > $i).
% 0.48/0.69  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.48/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.69  thf(fc1_relat_1, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.48/0.69  thf('0', plain,
% 0.48/0.69      (![X58 : $i, X59 : $i]:
% 0.48/0.69         (~ (v1_relat_1 @ X58) | (v1_relat_1 @ (k3_xboole_0 @ X58 @ X59)))),
% 0.48/0.69      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.48/0.69  thf(t12_setfam_1, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.48/0.69  thf('1', plain,
% 0.48/0.69      (![X54 : $i, X55 : $i]:
% 0.48/0.69         ((k1_setfam_1 @ (k2_tarski @ X54 @ X55)) = (k3_xboole_0 @ X54 @ X55))),
% 0.48/0.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.48/0.69  thf('2', plain,
% 0.48/0.69      (![X58 : $i, X59 : $i]:
% 0.48/0.69         (~ (v1_relat_1 @ X58)
% 0.48/0.69          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X58 @ X59))))),
% 0.48/0.69      inference('demod', [status(thm)], ['0', '1'])).
% 0.48/0.69  thf(t70_enumset1, axiom,
% 0.48/0.69    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.48/0.69  thf('3', plain,
% 0.48/0.69      (![X5 : $i, X6 : $i]:
% 0.48/0.69         ((k1_enumset1 @ X5 @ X5 @ X6) = (k2_tarski @ X5 @ X6))),
% 0.48/0.69      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.48/0.69  thf(t71_enumset1, axiom,
% 0.48/0.69    (![A:$i,B:$i,C:$i]:
% 0.48/0.69     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.48/0.69  thf('4', plain,
% 0.48/0.69      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.48/0.69         ((k2_enumset1 @ X7 @ X7 @ X8 @ X9) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 0.48/0.69      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.48/0.69  thf(t72_enumset1, axiom,
% 0.48/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.69     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.48/0.69  thf('5', plain,
% 0.48/0.69      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.48/0.69         ((k3_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13)
% 0.48/0.69           = (k2_enumset1 @ X10 @ X11 @ X12 @ X13))),
% 0.48/0.69      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.48/0.69  thf(t73_enumset1, axiom,
% 0.48/0.69    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.48/0.69     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.48/0.69       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.48/0.69  thf('6', plain,
% 0.48/0.69      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.48/0.69         ((k4_enumset1 @ X14 @ X14 @ X15 @ X16 @ X17 @ X18)
% 0.48/0.69           = (k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18))),
% 0.48/0.69      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.48/0.69  thf(t74_enumset1, axiom,
% 0.48/0.69    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.48/0.69     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.48/0.69       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.48/0.69  thf('7', plain,
% 0.48/0.69      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.48/0.69         ((k5_enumset1 @ X19 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24)
% 0.48/0.69           = (k4_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24))),
% 0.48/0.69      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.48/0.69  thf(t75_enumset1, axiom,
% 0.48/0.69    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.48/0.69     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.48/0.69       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.48/0.69  thf('8', plain,
% 0.48/0.69      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.48/0.69         ((k6_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31)
% 0.48/0.69           = (k5_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31))),
% 0.48/0.69      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.48/0.69  thf(d6_enumset1, axiom,
% 0.48/0.69    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.48/0.69     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 0.48/0.69       ( ![J:$i]:
% 0.48/0.69         ( ( r2_hidden @ J @ I ) <=>
% 0.48/0.69           ( ~( ( ( J ) != ( H ) ) & ( ( J ) != ( G ) ) & ( ( J ) != ( F ) ) & 
% 0.48/0.69                ( ( J ) != ( E ) ) & ( ( J ) != ( D ) ) & ( ( J ) != ( C ) ) & 
% 0.48/0.69                ( ( J ) != ( B ) ) & ( ( J ) != ( A ) ) ) ) ) ) ))).
% 0.48/0.69  thf(zf_stmt_0, type, zip_tseitin_0 :
% 0.48/0.69      $i > $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 0.48/0.69  thf(zf_stmt_1, axiom,
% 0.48/0.69    (![J:$i,H:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.48/0.69     ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) <=>
% 0.48/0.69       ( ( ( J ) != ( A ) ) & ( ( J ) != ( B ) ) & ( ( J ) != ( C ) ) & 
% 0.48/0.69         ( ( J ) != ( D ) ) & ( ( J ) != ( E ) ) & ( ( J ) != ( F ) ) & 
% 0.48/0.69         ( ( J ) != ( G ) ) & ( ( J ) != ( H ) ) ) ))).
% 0.48/0.69  thf(zf_stmt_2, axiom,
% 0.48/0.69    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.48/0.69     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 0.48/0.69       ( ![J:$i]:
% 0.48/0.69         ( ( r2_hidden @ J @ I ) <=>
% 0.48/0.69           ( ~( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.48/0.69  thf('9', plain,
% 0.48/0.69      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, 
% 0.48/0.69         X49 : $i, X50 : $i, X51 : $i]:
% 0.48/0.69         ((zip_tseitin_0 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50)
% 0.48/0.69          | (r2_hidden @ X42 @ X51)
% 0.48/0.69          | ((X51)
% 0.48/0.69              != (k6_enumset1 @ X50 @ X49 @ X48 @ X47 @ X46 @ X45 @ X44 @ X43)))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.48/0.69  thf('10', plain,
% 0.48/0.69      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, 
% 0.48/0.69         X49 : $i, X50 : $i]:
% 0.48/0.69         ((r2_hidden @ X42 @ 
% 0.48/0.69           (k6_enumset1 @ X50 @ X49 @ X48 @ X47 @ X46 @ X45 @ X44 @ X43))
% 0.48/0.69          | (zip_tseitin_0 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ 
% 0.48/0.69             X50))),
% 0.48/0.69      inference('simplify', [status(thm)], ['9'])).
% 0.48/0.69  thf('11', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.48/0.69         ((r2_hidden @ X7 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.48/0.69          | (zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6))),
% 0.48/0.69      inference('sup+', [status(thm)], ['8', '10'])).
% 0.48/0.69  thf('12', plain,
% 0.48/0.69      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, 
% 0.48/0.69         X39 : $i, X40 : $i]:
% 0.48/0.69         (((X33) != (X34))
% 0.48/0.69          | ~ (zip_tseitin_0 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ 
% 0.48/0.69               X32))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.48/0.69  thf('13', plain,
% 0.48/0.69      (![X32 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, 
% 0.48/0.69         X40 : $i]:
% 0.48/0.69         ~ (zip_tseitin_0 @ X34 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X32)),
% 0.48/0.69      inference('simplify', [status(thm)], ['12'])).
% 0.48/0.69  thf('14', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.48/0.69         (r2_hidden @ X6 @ (k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6))),
% 0.48/0.69      inference('sup-', [status(thm)], ['11', '13'])).
% 0.48/0.69  thf('15', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.48/0.69         (r2_hidden @ X0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.48/0.69      inference('sup+', [status(thm)], ['7', '14'])).
% 0.48/0.69  thf('16', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.48/0.69         (r2_hidden @ X0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.48/0.69      inference('sup+', [status(thm)], ['6', '15'])).
% 0.48/0.69  thf('17', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.48/0.69         (r2_hidden @ X0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.48/0.69      inference('sup+', [status(thm)], ['5', '16'])).
% 0.48/0.69  thf('18', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.69         (r2_hidden @ X0 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.48/0.69      inference('sup+', [status(thm)], ['4', '17'])).
% 0.48/0.69  thf('19', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 0.48/0.69      inference('sup+', [status(thm)], ['3', '18'])).
% 0.48/0.69  thf(t4_setfam_1, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 0.48/0.69  thf('20', plain,
% 0.48/0.69      (![X56 : $i, X57 : $i]:
% 0.48/0.69         ((r1_tarski @ (k1_setfam_1 @ X56) @ X57) | ~ (r2_hidden @ X57 @ X56))),
% 0.48/0.69      inference('cnf', [status(esa)], [t4_setfam_1])).
% 0.48/0.69  thf('21', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 0.48/0.69      inference('sup-', [status(thm)], ['19', '20'])).
% 0.48/0.69  thf(t25_relat_1, axiom,
% 0.48/0.69    (![A:$i]:
% 0.48/0.69     ( ( v1_relat_1 @ A ) =>
% 0.48/0.69       ( ![B:$i]:
% 0.48/0.69         ( ( v1_relat_1 @ B ) =>
% 0.48/0.69           ( ( r1_tarski @ A @ B ) =>
% 0.48/0.69             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.48/0.69               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.48/0.69  thf('22', plain,
% 0.48/0.69      (![X60 : $i, X61 : $i]:
% 0.48/0.69         (~ (v1_relat_1 @ X60)
% 0.48/0.69          | (r1_tarski @ (k2_relat_1 @ X61) @ (k2_relat_1 @ X60))
% 0.48/0.69          | ~ (r1_tarski @ X61 @ X60)
% 0.48/0.69          | ~ (v1_relat_1 @ X61))),
% 0.48/0.69      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.48/0.69  thf('23', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 0.48/0.69          | (r1_tarski @ 
% 0.48/0.69             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.48/0.69             (k2_relat_1 @ X0))
% 0.48/0.69          | ~ (v1_relat_1 @ X0))),
% 0.48/0.69      inference('sup-', [status(thm)], ['21', '22'])).
% 0.48/0.69  thf('24', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         (~ (v1_relat_1 @ X1)
% 0.48/0.69          | ~ (v1_relat_1 @ X0)
% 0.48/0.69          | (r1_tarski @ 
% 0.48/0.69             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.48/0.69             (k2_relat_1 @ X0)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['2', '23'])).
% 0.48/0.69  thf(t17_xboole_1, axiom,
% 0.48/0.69    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.48/0.69  thf('25', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.48/0.69      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.48/0.69  thf('26', plain,
% 0.48/0.69      (![X54 : $i, X55 : $i]:
% 0.48/0.69         ((k1_setfam_1 @ (k2_tarski @ X54 @ X55)) = (k3_xboole_0 @ X54 @ X55))),
% 0.48/0.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.48/0.69  thf('27', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0)),
% 0.48/0.69      inference('demod', [status(thm)], ['25', '26'])).
% 0.48/0.69  thf('28', plain,
% 0.48/0.69      (![X60 : $i, X61 : $i]:
% 0.48/0.69         (~ (v1_relat_1 @ X60)
% 0.48/0.69          | (r1_tarski @ (k2_relat_1 @ X61) @ (k2_relat_1 @ X60))
% 0.48/0.69          | ~ (r1_tarski @ X61 @ X60)
% 0.48/0.69          | ~ (v1_relat_1 @ X61))),
% 0.48/0.69      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.48/0.69  thf('29', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 0.48/0.69          | (r1_tarski @ 
% 0.48/0.69             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.48/0.69             (k2_relat_1 @ X0))
% 0.48/0.69          | ~ (v1_relat_1 @ X0))),
% 0.48/0.69      inference('sup-', [status(thm)], ['27', '28'])).
% 0.48/0.69  thf('30', plain,
% 0.48/0.69      (![X58 : $i, X59 : $i]:
% 0.48/0.69         (~ (v1_relat_1 @ X58)
% 0.48/0.69          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X58 @ X59))))),
% 0.48/0.69      inference('demod', [status(thm)], ['0', '1'])).
% 0.48/0.69  thf('31', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         (~ (v1_relat_1 @ X0)
% 0.48/0.69          | (r1_tarski @ 
% 0.48/0.69             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.48/0.69             (k2_relat_1 @ X0)))),
% 0.48/0.69      inference('clc', [status(thm)], ['29', '30'])).
% 0.48/0.69  thf(t19_xboole_1, axiom,
% 0.48/0.69    (![A:$i,B:$i,C:$i]:
% 0.48/0.69     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.48/0.69       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.48/0.69  thf('32', plain,
% 0.48/0.69      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.48/0.69         (~ (r1_tarski @ X2 @ X3)
% 0.48/0.69          | ~ (r1_tarski @ X2 @ X4)
% 0.48/0.69          | (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.48/0.69      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.48/0.69  thf('33', plain,
% 0.48/0.69      (![X54 : $i, X55 : $i]:
% 0.48/0.69         ((k1_setfam_1 @ (k2_tarski @ X54 @ X55)) = (k3_xboole_0 @ X54 @ X55))),
% 0.48/0.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.48/0.69  thf('34', plain,
% 0.48/0.69      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.48/0.69         (~ (r1_tarski @ X2 @ X3)
% 0.48/0.69          | ~ (r1_tarski @ X2 @ X4)
% 0.48/0.69          | (r1_tarski @ X2 @ (k1_setfam_1 @ (k2_tarski @ X3 @ X4))))),
% 0.48/0.69      inference('demod', [status(thm)], ['32', '33'])).
% 0.48/0.69  thf('35', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.69         (~ (v1_relat_1 @ X0)
% 0.48/0.69          | (r1_tarski @ 
% 0.48/0.69             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.48/0.69             (k1_setfam_1 @ (k2_tarski @ (k2_relat_1 @ X0) @ X2)))
% 0.48/0.69          | ~ (r1_tarski @ 
% 0.48/0.69               (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ X2))),
% 0.48/0.69      inference('sup-', [status(thm)], ['31', '34'])).
% 0.48/0.69  thf('36', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         (~ (v1_relat_1 @ X0)
% 0.48/0.69          | ~ (v1_relat_1 @ X1)
% 0.48/0.69          | (r1_tarski @ 
% 0.48/0.69             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.48/0.69             (k1_setfam_1 @ (k2_tarski @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0))))
% 0.48/0.69          | ~ (v1_relat_1 @ X1))),
% 0.48/0.69      inference('sup-', [status(thm)], ['24', '35'])).
% 0.48/0.69  thf('37', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         ((r1_tarski @ (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.48/0.69           (k1_setfam_1 @ (k2_tarski @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0))))
% 0.48/0.69          | ~ (v1_relat_1 @ X1)
% 0.48/0.69          | ~ (v1_relat_1 @ X0))),
% 0.48/0.69      inference('simplify', [status(thm)], ['36'])).
% 0.48/0.69  thf(t27_relat_1, conjecture,
% 0.48/0.69    (![A:$i]:
% 0.48/0.69     ( ( v1_relat_1 @ A ) =>
% 0.48/0.69       ( ![B:$i]:
% 0.48/0.69         ( ( v1_relat_1 @ B ) =>
% 0.48/0.69           ( r1_tarski @
% 0.48/0.69             ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.48/0.69             ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 0.48/0.69  thf(zf_stmt_3, negated_conjecture,
% 0.48/0.69    (~( ![A:$i]:
% 0.48/0.69        ( ( v1_relat_1 @ A ) =>
% 0.48/0.69          ( ![B:$i]:
% 0.48/0.69            ( ( v1_relat_1 @ B ) =>
% 0.48/0.69              ( r1_tarski @
% 0.48/0.69                ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.48/0.69                ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )),
% 0.48/0.69    inference('cnf.neg', [status(esa)], [t27_relat_1])).
% 0.48/0.69  thf('38', plain,
% 0.48/0.69      (~ (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 0.48/0.69          (k3_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.48/0.69  thf('39', plain,
% 0.48/0.69      (![X54 : $i, X55 : $i]:
% 0.48/0.69         ((k1_setfam_1 @ (k2_tarski @ X54 @ X55)) = (k3_xboole_0 @ X54 @ X55))),
% 0.48/0.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.48/0.69  thf('40', plain,
% 0.48/0.69      (![X54 : $i, X55 : $i]:
% 0.48/0.69         ((k1_setfam_1 @ (k2_tarski @ X54 @ X55)) = (k3_xboole_0 @ X54 @ X55))),
% 0.48/0.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.48/0.69  thf('41', plain,
% 0.48/0.69      (~ (r1_tarski @ 
% 0.48/0.69          (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))) @ 
% 0.48/0.69          (k1_setfam_1 @ 
% 0.48/0.69           (k2_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))))),
% 0.48/0.69      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.48/0.69  thf('42', plain, ((~ (v1_relat_1 @ sk_B) | ~ (v1_relat_1 @ sk_A))),
% 0.48/0.69      inference('sup-', [status(thm)], ['37', '41'])).
% 0.48/0.69  thf('43', plain, ((v1_relat_1 @ sk_B)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.48/0.69  thf('44', plain, ((v1_relat_1 @ sk_A)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.48/0.69  thf('45', plain, ($false),
% 0.48/0.69      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.48/0.69  
% 0.48/0.69  % SZS output end Refutation
% 0.48/0.69  
% 0.48/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
