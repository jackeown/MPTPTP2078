%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ygZbkg92Xl

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:57 EST 2020

% Result     : Theorem 4.08s
% Output     : Refutation 4.08s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 168 expanded)
%              Number of leaves         :   40 (  67 expanded)
%              Depth                    :   19
%              Number of atoms          :  842 (1537 expanded)
%              Number of equality atoms :   52 (  85 expanded)
%              Maximal formula depth    :   23 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t31_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_tarski @ A @ B )
             => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X65: $i] :
      ( ( ( k3_relat_1 @ X65 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X65 ) @ ( k2_relat_1 @ X65 ) ) )
      | ~ ( v1_relat_1 @ X65 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('2',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X66: $i,X67: $i] :
      ( ~ ( v1_relat_1 @ X66 )
      | ( r1_tarski @ ( k2_relat_1 @ X67 ) @ ( k2_relat_1 @ X66 ) )
      | ~ ( r1_tarski @ X67 @ X66 )
      | ~ ( v1_relat_1 @ X67 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,
    ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    = ( k2_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X65: $i] :
      ( ( ( k3_relat_1 @ X65 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X65 ) @ ( k2_relat_1 @ X65 ) ) )
      | ~ ( v1_relat_1 @ X65 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_tarski @ X8 @ X7 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X36 @ X37 ) )
      = ( k2_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X36 @ X37 ) )
      = ( k2_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','17'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_enumset1 @ X9 @ X9 @ X10 )
      = ( k2_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('20',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X11 @ X11 @ X12 @ X13 )
      = ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('21',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k3_enumset1 @ X14 @ X14 @ X15 @ X16 @ X17 )
      = ( k2_enumset1 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('22',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k4_enumset1 @ X18 @ X18 @ X19 @ X20 @ X21 @ X22 )
      = ( k3_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('23',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k5_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 )
      = ( k4_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('24',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k6_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 )
      = ( k5_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 ) ) ),
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

thf('25',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( zip_tseitin_0 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 )
      | ( r2_hidden @ X48 @ X57 )
      | ( X57
       != ( k6_enumset1 @ X56 @ X55 @ X54 @ X53 @ X52 @ X51 @ X50 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('26',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( r2_hidden @ X48 @ ( k6_enumset1 @ X56 @ X55 @ X54 @ X53 @ X52 @ X51 @ X50 @ X49 ) )
      | ( zip_tseitin_0 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6 ) ) ),
    inference('sup+',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( X39 != X38 )
      | ~ ( zip_tseitin_0 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('29',plain,(
    ! [X38: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ~ ( zip_tseitin_0 @ X38 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X38 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( r2_hidden @ X0 @ ( k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( r2_hidden @ X5 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X4 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','34'])).

thf(t8_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ) )).

thf('36',plain,(
    ! [X62: $i,X63: $i,X64: $i] :
      ( ~ ( r2_hidden @ X62 @ X63 )
      | ~ ( r1_tarski @ X62 @ X64 )
      | ( r1_tarski @ ( k1_setfam_1 @ X63 ) @ X64 ) ) ),
    inference(cnf,[status(esa)],[t8_setfam_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_tarski @ X8 @ X7 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('39',plain,(
    ! [X60: $i,X61: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X60 @ X61 ) )
      = ( k3_xboole_0 @ X60 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','41'])).

thf('43',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X66: $i,X67: $i] :
      ( ~ ( v1_relat_1 @ X66 )
      | ( r1_tarski @ ( k1_relat_1 @ X67 ) @ ( k1_relat_1 @ X66 ) )
      | ~ ( r1_tarski @ X67 @ X66 )
      | ~ ( v1_relat_1 @ X67 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('53',plain,
    ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X65: $i] :
      ( ( ( k3_relat_1 @ X65 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X65 ) @ ( k2_relat_1 @ X65 ) ) )
      | ~ ( v1_relat_1 @ X65 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('55',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['53','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['59','60'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('62',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X6 @ X5 )
      | ( r1_tarski @ ( k2_xboole_0 @ X4 @ X6 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k3_relat_1 @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['45','63'])).

thf('65',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    $false ),
    inference(demod,[status(thm)],['0','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ygZbkg92Xl
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:28:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 4.08/4.29  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.08/4.29  % Solved by: fo/fo7.sh
% 4.08/4.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.08/4.29  % done 7604 iterations in 3.815s
% 4.08/4.29  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.08/4.29  % SZS output start Refutation
% 4.08/4.29  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.08/4.29  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 4.08/4.29  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.08/4.29  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 4.08/4.29  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 4.08/4.29  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.08/4.29  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 4.08/4.29                                               $i > $i > $i > $o).
% 4.08/4.29  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.08/4.29  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.08/4.29  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 4.08/4.29  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.08/4.29  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 4.08/4.29  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 4.08/4.29  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 4.08/4.29  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 4.08/4.29                                           $i > $i).
% 4.08/4.29  thf(sk_A_type, type, sk_A: $i).
% 4.08/4.29  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.08/4.29  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 4.08/4.29  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 4.08/4.29  thf(sk_B_type, type, sk_B: $i).
% 4.08/4.29  thf(t31_relat_1, conjecture,
% 4.08/4.29    (![A:$i]:
% 4.08/4.29     ( ( v1_relat_1 @ A ) =>
% 4.08/4.29       ( ![B:$i]:
% 4.08/4.29         ( ( v1_relat_1 @ B ) =>
% 4.08/4.29           ( ( r1_tarski @ A @ B ) =>
% 4.08/4.29             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 4.08/4.29  thf(zf_stmt_0, negated_conjecture,
% 4.08/4.29    (~( ![A:$i]:
% 4.08/4.29        ( ( v1_relat_1 @ A ) =>
% 4.08/4.29          ( ![B:$i]:
% 4.08/4.29            ( ( v1_relat_1 @ B ) =>
% 4.08/4.29              ( ( r1_tarski @ A @ B ) =>
% 4.08/4.29                ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 4.08/4.29    inference('cnf.neg', [status(esa)], [t31_relat_1])).
% 4.08/4.29  thf('0', plain, (~ (r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 4.08/4.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.08/4.29  thf(d6_relat_1, axiom,
% 4.08/4.29    (![A:$i]:
% 4.08/4.29     ( ( v1_relat_1 @ A ) =>
% 4.08/4.29       ( ( k3_relat_1 @ A ) =
% 4.08/4.29         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 4.08/4.29  thf('1', plain,
% 4.08/4.29      (![X65 : $i]:
% 4.08/4.29         (((k3_relat_1 @ X65)
% 4.08/4.29            = (k2_xboole_0 @ (k1_relat_1 @ X65) @ (k2_relat_1 @ X65)))
% 4.08/4.29          | ~ (v1_relat_1 @ X65))),
% 4.08/4.29      inference('cnf', [status(esa)], [d6_relat_1])).
% 4.08/4.29  thf('2', plain, ((r1_tarski @ sk_A @ sk_B)),
% 4.08/4.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.08/4.29  thf(t25_relat_1, axiom,
% 4.08/4.29    (![A:$i]:
% 4.08/4.29     ( ( v1_relat_1 @ A ) =>
% 4.08/4.29       ( ![B:$i]:
% 4.08/4.29         ( ( v1_relat_1 @ B ) =>
% 4.08/4.29           ( ( r1_tarski @ A @ B ) =>
% 4.08/4.29             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 4.08/4.29               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 4.08/4.29  thf('3', plain,
% 4.08/4.29      (![X66 : $i, X67 : $i]:
% 4.08/4.29         (~ (v1_relat_1 @ X66)
% 4.08/4.29          | (r1_tarski @ (k2_relat_1 @ X67) @ (k2_relat_1 @ X66))
% 4.08/4.29          | ~ (r1_tarski @ X67 @ X66)
% 4.08/4.29          | ~ (v1_relat_1 @ X67))),
% 4.08/4.29      inference('cnf', [status(esa)], [t25_relat_1])).
% 4.08/4.29  thf('4', plain,
% 4.08/4.29      ((~ (v1_relat_1 @ sk_A)
% 4.08/4.29        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))
% 4.08/4.29        | ~ (v1_relat_1 @ sk_B))),
% 4.08/4.29      inference('sup-', [status(thm)], ['2', '3'])).
% 4.08/4.29  thf('5', plain, ((v1_relat_1 @ sk_A)),
% 4.08/4.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.08/4.29  thf('6', plain, ((v1_relat_1 @ sk_B)),
% 4.08/4.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.08/4.29  thf('7', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))),
% 4.08/4.29      inference('demod', [status(thm)], ['4', '5', '6'])).
% 4.08/4.29  thf(t28_xboole_1, axiom,
% 4.08/4.29    (![A:$i,B:$i]:
% 4.08/4.29     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 4.08/4.29  thf('8', plain,
% 4.08/4.29      (![X0 : $i, X1 : $i]:
% 4.08/4.29         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 4.08/4.29      inference('cnf', [status(esa)], [t28_xboole_1])).
% 4.08/4.29  thf('9', plain,
% 4.08/4.29      (((k3_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))
% 4.08/4.29         = (k2_relat_1 @ sk_A))),
% 4.08/4.29      inference('sup-', [status(thm)], ['7', '8'])).
% 4.08/4.29  thf('10', plain,
% 4.08/4.29      (![X65 : $i]:
% 4.08/4.29         (((k3_relat_1 @ X65)
% 4.08/4.29            = (k2_xboole_0 @ (k1_relat_1 @ X65) @ (k2_relat_1 @ X65)))
% 4.08/4.29          | ~ (v1_relat_1 @ X65))),
% 4.08/4.29      inference('cnf', [status(esa)], [d6_relat_1])).
% 4.08/4.29  thf(commutativity_k2_tarski, axiom,
% 4.08/4.29    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 4.08/4.29  thf('11', plain,
% 4.08/4.29      (![X7 : $i, X8 : $i]: ((k2_tarski @ X8 @ X7) = (k2_tarski @ X7 @ X8))),
% 4.08/4.29      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 4.08/4.29  thf(l51_zfmisc_1, axiom,
% 4.08/4.29    (![A:$i,B:$i]:
% 4.08/4.29     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 4.08/4.29  thf('12', plain,
% 4.08/4.29      (![X36 : $i, X37 : $i]:
% 4.08/4.29         ((k3_tarski @ (k2_tarski @ X36 @ X37)) = (k2_xboole_0 @ X36 @ X37))),
% 4.08/4.29      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 4.08/4.29  thf('13', plain,
% 4.08/4.29      (![X0 : $i, X1 : $i]:
% 4.08/4.29         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 4.08/4.29      inference('sup+', [status(thm)], ['11', '12'])).
% 4.08/4.29  thf('14', plain,
% 4.08/4.29      (![X36 : $i, X37 : $i]:
% 4.08/4.29         ((k3_tarski @ (k2_tarski @ X36 @ X37)) = (k2_xboole_0 @ X36 @ X37))),
% 4.08/4.29      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 4.08/4.29  thf('15', plain,
% 4.08/4.29      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.08/4.29      inference('sup+', [status(thm)], ['13', '14'])).
% 4.08/4.29  thf(t7_xboole_1, axiom,
% 4.08/4.29    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 4.08/4.29  thf('16', plain,
% 4.08/4.29      (![X2 : $i, X3 : $i]: (r1_tarski @ X2 @ (k2_xboole_0 @ X2 @ X3))),
% 4.08/4.29      inference('cnf', [status(esa)], [t7_xboole_1])).
% 4.08/4.29  thf('17', plain,
% 4.08/4.29      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 4.08/4.29      inference('sup+', [status(thm)], ['15', '16'])).
% 4.08/4.29  thf('18', plain,
% 4.08/4.29      (![X0 : $i]:
% 4.08/4.29         ((r1_tarski @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 4.08/4.29          | ~ (v1_relat_1 @ X0))),
% 4.08/4.29      inference('sup+', [status(thm)], ['10', '17'])).
% 4.08/4.29  thf(t70_enumset1, axiom,
% 4.08/4.29    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 4.08/4.29  thf('19', plain,
% 4.08/4.29      (![X9 : $i, X10 : $i]:
% 4.08/4.29         ((k1_enumset1 @ X9 @ X9 @ X10) = (k2_tarski @ X9 @ X10))),
% 4.08/4.29      inference('cnf', [status(esa)], [t70_enumset1])).
% 4.08/4.29  thf(t71_enumset1, axiom,
% 4.08/4.29    (![A:$i,B:$i,C:$i]:
% 4.08/4.29     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 4.08/4.29  thf('20', plain,
% 4.08/4.29      (![X11 : $i, X12 : $i, X13 : $i]:
% 4.08/4.29         ((k2_enumset1 @ X11 @ X11 @ X12 @ X13)
% 4.08/4.29           = (k1_enumset1 @ X11 @ X12 @ X13))),
% 4.08/4.29      inference('cnf', [status(esa)], [t71_enumset1])).
% 4.08/4.29  thf(t72_enumset1, axiom,
% 4.08/4.29    (![A:$i,B:$i,C:$i,D:$i]:
% 4.08/4.29     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 4.08/4.29  thf('21', plain,
% 4.08/4.29      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 4.08/4.29         ((k3_enumset1 @ X14 @ X14 @ X15 @ X16 @ X17)
% 4.08/4.29           = (k2_enumset1 @ X14 @ X15 @ X16 @ X17))),
% 4.08/4.29      inference('cnf', [status(esa)], [t72_enumset1])).
% 4.08/4.29  thf(t73_enumset1, axiom,
% 4.08/4.29    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 4.08/4.29     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 4.08/4.29       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 4.08/4.29  thf('22', plain,
% 4.08/4.29      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 4.08/4.29         ((k4_enumset1 @ X18 @ X18 @ X19 @ X20 @ X21 @ X22)
% 4.08/4.29           = (k3_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22))),
% 4.08/4.29      inference('cnf', [status(esa)], [t73_enumset1])).
% 4.08/4.29  thf(t74_enumset1, axiom,
% 4.08/4.29    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.08/4.29     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 4.08/4.29       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 4.08/4.29  thf('23', plain,
% 4.08/4.29      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 4.08/4.29         ((k5_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28)
% 4.08/4.29           = (k4_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28))),
% 4.08/4.29      inference('cnf', [status(esa)], [t74_enumset1])).
% 4.08/4.29  thf(t75_enumset1, axiom,
% 4.08/4.29    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 4.08/4.29     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 4.08/4.29       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 4.08/4.29  thf('24', plain,
% 4.08/4.29      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 4.08/4.29         ((k6_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35)
% 4.08/4.29           = (k5_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35))),
% 4.08/4.29      inference('cnf', [status(esa)], [t75_enumset1])).
% 4.08/4.29  thf(d6_enumset1, axiom,
% 4.08/4.29    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 4.08/4.29     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 4.08/4.29       ( ![J:$i]:
% 4.08/4.29         ( ( r2_hidden @ J @ I ) <=>
% 4.08/4.29           ( ~( ( ( J ) != ( H ) ) & ( ( J ) != ( G ) ) & ( ( J ) != ( F ) ) & 
% 4.08/4.29                ( ( J ) != ( E ) ) & ( ( J ) != ( D ) ) & ( ( J ) != ( C ) ) & 
% 4.08/4.29                ( ( J ) != ( B ) ) & ( ( J ) != ( A ) ) ) ) ) ) ))).
% 4.08/4.29  thf(zf_stmt_1, type, zip_tseitin_0 :
% 4.08/4.29      $i > $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 4.08/4.29  thf(zf_stmt_2, axiom,
% 4.08/4.29    (![J:$i,H:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 4.08/4.29     ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) <=>
% 4.08/4.29       ( ( ( J ) != ( A ) ) & ( ( J ) != ( B ) ) & ( ( J ) != ( C ) ) & 
% 4.08/4.29         ( ( J ) != ( D ) ) & ( ( J ) != ( E ) ) & ( ( J ) != ( F ) ) & 
% 4.08/4.29         ( ( J ) != ( G ) ) & ( ( J ) != ( H ) ) ) ))).
% 4.08/4.29  thf(zf_stmt_3, axiom,
% 4.08/4.29    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 4.08/4.29     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 4.08/4.29       ( ![J:$i]:
% 4.08/4.29         ( ( r2_hidden @ J @ I ) <=>
% 4.08/4.29           ( ~( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 4.08/4.29  thf('25', plain,
% 4.08/4.29      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, 
% 4.08/4.29         X55 : $i, X56 : $i, X57 : $i]:
% 4.08/4.29         ((zip_tseitin_0 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56)
% 4.08/4.29          | (r2_hidden @ X48 @ X57)
% 4.08/4.29          | ((X57)
% 4.08/4.29              != (k6_enumset1 @ X56 @ X55 @ X54 @ X53 @ X52 @ X51 @ X50 @ X49)))),
% 4.08/4.29      inference('cnf', [status(esa)], [zf_stmt_3])).
% 4.08/4.29  thf('26', plain,
% 4.08/4.29      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, 
% 4.08/4.29         X55 : $i, X56 : $i]:
% 4.08/4.29         ((r2_hidden @ X48 @ 
% 4.08/4.29           (k6_enumset1 @ X56 @ X55 @ X54 @ X53 @ X52 @ X51 @ X50 @ X49))
% 4.08/4.29          | (zip_tseitin_0 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ 
% 4.08/4.29             X56))),
% 4.08/4.29      inference('simplify', [status(thm)], ['25'])).
% 4.08/4.29  thf('27', plain,
% 4.08/4.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 4.08/4.29         ((r2_hidden @ X7 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 4.08/4.29          | (zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6))),
% 4.08/4.29      inference('sup+', [status(thm)], ['24', '26'])).
% 4.08/4.29  thf('28', plain,
% 4.08/4.29      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, 
% 4.08/4.29         X45 : $i, X46 : $i]:
% 4.08/4.29         (((X39) != (X38))
% 4.08/4.29          | ~ (zip_tseitin_0 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ 
% 4.08/4.29               X38))),
% 4.08/4.29      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.08/4.29  thf('29', plain,
% 4.08/4.29      (![X38 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, 
% 4.08/4.29         X46 : $i]:
% 4.08/4.29         ~ (zip_tseitin_0 @ X38 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X38)),
% 4.08/4.29      inference('simplify', [status(thm)], ['28'])).
% 4.08/4.29  thf('30', plain,
% 4.08/4.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 4.08/4.29         (r2_hidden @ X0 @ (k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6))),
% 4.08/4.29      inference('sup-', [status(thm)], ['27', '29'])).
% 4.08/4.29  thf('31', plain,
% 4.08/4.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 4.08/4.29         (r2_hidden @ X5 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 4.08/4.29      inference('sup+', [status(thm)], ['23', '30'])).
% 4.08/4.29  thf('32', plain,
% 4.08/4.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.08/4.29         (r2_hidden @ X4 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 4.08/4.29      inference('sup+', [status(thm)], ['22', '31'])).
% 4.08/4.29  thf('33', plain,
% 4.08/4.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.08/4.29         (r2_hidden @ X3 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 4.08/4.29      inference('sup+', [status(thm)], ['21', '32'])).
% 4.08/4.29  thf('34', plain,
% 4.08/4.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.08/4.29         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 4.08/4.29      inference('sup+', [status(thm)], ['20', '33'])).
% 4.08/4.29  thf('35', plain,
% 4.08/4.29      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 4.08/4.29      inference('sup+', [status(thm)], ['19', '34'])).
% 4.08/4.29  thf(t8_setfam_1, axiom,
% 4.08/4.29    (![A:$i,B:$i,C:$i]:
% 4.08/4.29     ( ( ( r2_hidden @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 4.08/4.29       ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ))).
% 4.08/4.29  thf('36', plain,
% 4.08/4.29      (![X62 : $i, X63 : $i, X64 : $i]:
% 4.08/4.29         (~ (r2_hidden @ X62 @ X63)
% 4.08/4.29          | ~ (r1_tarski @ X62 @ X64)
% 4.08/4.29          | (r1_tarski @ (k1_setfam_1 @ X63) @ X64))),
% 4.08/4.29      inference('cnf', [status(esa)], [t8_setfam_1])).
% 4.08/4.29  thf('37', plain,
% 4.08/4.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.08/4.29         ((r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X2)
% 4.08/4.29          | ~ (r1_tarski @ X1 @ X2))),
% 4.08/4.29      inference('sup-', [status(thm)], ['35', '36'])).
% 4.08/4.29  thf('38', plain,
% 4.08/4.29      (![X7 : $i, X8 : $i]: ((k2_tarski @ X8 @ X7) = (k2_tarski @ X7 @ X8))),
% 4.08/4.29      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 4.08/4.29  thf(t12_setfam_1, axiom,
% 4.08/4.29    (![A:$i,B:$i]:
% 4.08/4.29     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 4.08/4.29  thf('39', plain,
% 4.08/4.29      (![X60 : $i, X61 : $i]:
% 4.08/4.29         ((k1_setfam_1 @ (k2_tarski @ X60 @ X61)) = (k3_xboole_0 @ X60 @ X61))),
% 4.08/4.29      inference('cnf', [status(esa)], [t12_setfam_1])).
% 4.08/4.29  thf('40', plain,
% 4.08/4.29      (![X0 : $i, X1 : $i]:
% 4.08/4.29         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 4.08/4.29      inference('sup+', [status(thm)], ['38', '39'])).
% 4.08/4.29  thf('41', plain,
% 4.08/4.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.08/4.29         ((r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X1 @ X2))),
% 4.08/4.29      inference('demod', [status(thm)], ['37', '40'])).
% 4.08/4.29  thf('42', plain,
% 4.08/4.29      (![X0 : $i, X1 : $i]:
% 4.08/4.29         (~ (v1_relat_1 @ X0)
% 4.08/4.29          | (r1_tarski @ (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0)) @ 
% 4.08/4.29             (k3_relat_1 @ X0)))),
% 4.08/4.29      inference('sup-', [status(thm)], ['18', '41'])).
% 4.08/4.29  thf('43', plain,
% 4.08/4.29      (((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 4.08/4.29        | ~ (v1_relat_1 @ sk_B))),
% 4.08/4.29      inference('sup+', [status(thm)], ['9', '42'])).
% 4.08/4.29  thf('44', plain, ((v1_relat_1 @ sk_B)),
% 4.08/4.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.08/4.29  thf('45', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 4.08/4.29      inference('demod', [status(thm)], ['43', '44'])).
% 4.08/4.29  thf('46', plain, ((r1_tarski @ sk_A @ sk_B)),
% 4.08/4.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.08/4.29  thf('47', plain,
% 4.08/4.29      (![X66 : $i, X67 : $i]:
% 4.08/4.29         (~ (v1_relat_1 @ X66)
% 4.08/4.29          | (r1_tarski @ (k1_relat_1 @ X67) @ (k1_relat_1 @ X66))
% 4.08/4.29          | ~ (r1_tarski @ X67 @ X66)
% 4.08/4.29          | ~ (v1_relat_1 @ X67))),
% 4.08/4.29      inference('cnf', [status(esa)], [t25_relat_1])).
% 4.08/4.29  thf('48', plain,
% 4.08/4.29      ((~ (v1_relat_1 @ sk_A)
% 4.08/4.29        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 4.08/4.29        | ~ (v1_relat_1 @ sk_B))),
% 4.08/4.29      inference('sup-', [status(thm)], ['46', '47'])).
% 4.08/4.29  thf('49', plain, ((v1_relat_1 @ sk_A)),
% 4.08/4.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.08/4.29  thf('50', plain, ((v1_relat_1 @ sk_B)),
% 4.08/4.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.08/4.29  thf('51', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))),
% 4.08/4.29      inference('demod', [status(thm)], ['48', '49', '50'])).
% 4.08/4.29  thf('52', plain,
% 4.08/4.29      (![X0 : $i, X1 : $i]:
% 4.08/4.29         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 4.08/4.29      inference('cnf', [status(esa)], [t28_xboole_1])).
% 4.08/4.29  thf('53', plain,
% 4.08/4.29      (((k3_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 4.08/4.29         = (k1_relat_1 @ sk_A))),
% 4.08/4.29      inference('sup-', [status(thm)], ['51', '52'])).
% 4.08/4.29  thf('54', plain,
% 4.08/4.29      (![X65 : $i]:
% 4.08/4.29         (((k3_relat_1 @ X65)
% 4.08/4.29            = (k2_xboole_0 @ (k1_relat_1 @ X65) @ (k2_relat_1 @ X65)))
% 4.08/4.29          | ~ (v1_relat_1 @ X65))),
% 4.08/4.29      inference('cnf', [status(esa)], [d6_relat_1])).
% 4.08/4.29  thf('55', plain,
% 4.08/4.29      (![X2 : $i, X3 : $i]: (r1_tarski @ X2 @ (k2_xboole_0 @ X2 @ X3))),
% 4.08/4.29      inference('cnf', [status(esa)], [t7_xboole_1])).
% 4.08/4.29  thf('56', plain,
% 4.08/4.29      (![X0 : $i]:
% 4.08/4.29         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 4.08/4.29          | ~ (v1_relat_1 @ X0))),
% 4.08/4.29      inference('sup+', [status(thm)], ['54', '55'])).
% 4.08/4.29  thf('57', plain,
% 4.08/4.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.08/4.29         ((r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X1 @ X2))),
% 4.08/4.29      inference('demod', [status(thm)], ['37', '40'])).
% 4.08/4.29  thf('58', plain,
% 4.08/4.29      (![X0 : $i, X1 : $i]:
% 4.08/4.29         (~ (v1_relat_1 @ X0)
% 4.08/4.29          | (r1_tarski @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)) @ 
% 4.08/4.29             (k3_relat_1 @ X0)))),
% 4.08/4.29      inference('sup-', [status(thm)], ['56', '57'])).
% 4.08/4.29  thf('59', plain,
% 4.08/4.29      (((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 4.08/4.29        | ~ (v1_relat_1 @ sk_B))),
% 4.08/4.29      inference('sup+', [status(thm)], ['53', '58'])).
% 4.08/4.29  thf('60', plain, ((v1_relat_1 @ sk_B)),
% 4.08/4.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.08/4.29  thf('61', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 4.08/4.29      inference('demod', [status(thm)], ['59', '60'])).
% 4.08/4.29  thf(t8_xboole_1, axiom,
% 4.08/4.29    (![A:$i,B:$i,C:$i]:
% 4.08/4.29     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 4.08/4.29       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 4.08/4.29  thf('62', plain,
% 4.08/4.29      (![X4 : $i, X5 : $i, X6 : $i]:
% 4.08/4.29         (~ (r1_tarski @ X4 @ X5)
% 4.08/4.29          | ~ (r1_tarski @ X6 @ X5)
% 4.08/4.29          | (r1_tarski @ (k2_xboole_0 @ X4 @ X6) @ X5))),
% 4.08/4.29      inference('cnf', [status(esa)], [t8_xboole_1])).
% 4.08/4.29  thf('63', plain,
% 4.08/4.29      (![X0 : $i]:
% 4.08/4.29         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 4.08/4.29           (k3_relat_1 @ sk_B))
% 4.08/4.29          | ~ (r1_tarski @ X0 @ (k3_relat_1 @ sk_B)))),
% 4.08/4.29      inference('sup-', [status(thm)], ['61', '62'])).
% 4.08/4.29  thf('64', plain,
% 4.08/4.29      ((r1_tarski @ 
% 4.08/4.29        (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) @ 
% 4.08/4.29        (k3_relat_1 @ sk_B))),
% 4.08/4.29      inference('sup-', [status(thm)], ['45', '63'])).
% 4.08/4.29  thf('65', plain,
% 4.08/4.29      (((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 4.08/4.29        | ~ (v1_relat_1 @ sk_A))),
% 4.08/4.29      inference('sup+', [status(thm)], ['1', '64'])).
% 4.08/4.29  thf('66', plain, ((v1_relat_1 @ sk_A)),
% 4.08/4.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.08/4.29  thf('67', plain, ((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 4.08/4.29      inference('demod', [status(thm)], ['65', '66'])).
% 4.08/4.29  thf('68', plain, ($false), inference('demod', [status(thm)], ['0', '67'])).
% 4.08/4.29  
% 4.08/4.29  % SZS output end Refutation
% 4.08/4.29  
% 4.08/4.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
