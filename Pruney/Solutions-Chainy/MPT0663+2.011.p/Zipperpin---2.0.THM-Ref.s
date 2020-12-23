%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wormkOkUka

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:49 EST 2020

% Result     : Theorem 12.15s
% Output     : Refutation 12.15s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 872 expanded)
%              Number of leaves         :   43 ( 304 expanded)
%              Depth                    :   19
%              Number of atoms          : 1570 (11295 expanded)
%              Number of equality atoms :  122 ( 848 expanded)
%              Maximal formula depth    :   23 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X21 @ X21 @ X22 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('1',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k3_enumset1 @ X26 @ X26 @ X27 @ X28 @ X29 )
      = ( k2_enumset1 @ X26 @ X27 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k2_enumset1 @ X23 @ X23 @ X24 @ X25 )
      = ( k1_enumset1 @ X23 @ X24 @ X25 ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( k5_enumset1 @ X35 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 )
      = ( k4_enumset1 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('5',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k4_enumset1 @ X30 @ X30 @ X31 @ X32 @ X33 @ X34 )
      = ( k3_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 ) ) ),
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
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( k6_enumset1 @ X41 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 )
      = ( k5_enumset1 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 ) ) ),
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
    ! [X63: $i,X64: $i,X65: $i,X66: $i,X67: $i,X68: $i,X69: $i,X70: $i,X71: $i,X72: $i] :
      ( ( zip_tseitin_0 @ X63 @ X64 @ X65 @ X66 @ X67 @ X68 @ X69 @ X70 @ X71 )
      | ( r2_hidden @ X63 @ X72 )
      | ( X72
       != ( k6_enumset1 @ X71 @ X70 @ X69 @ X68 @ X67 @ X66 @ X65 @ X64 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('9',plain,(
    ! [X63: $i,X64: $i,X65: $i,X66: $i,X67: $i,X68: $i,X69: $i,X70: $i,X71: $i] :
      ( ( r2_hidden @ X63 @ ( k6_enumset1 @ X71 @ X70 @ X69 @ X68 @ X67 @ X66 @ X65 @ X64 ) )
      | ( zip_tseitin_0 @ X63 @ X64 @ X65 @ X66 @ X67 @ X68 @ X69 @ X70 @ X71 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6 ) ) ),
    inference('sup+',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i,X57: $i,X58: $i,X59: $i,X60: $i,X61: $i] :
      ( ( X54 != X53 )
      | ~ ( zip_tseitin_0 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 @ X61 @ X53 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('12',plain,(
    ! [X53: $i,X55: $i,X56: $i,X57: $i,X58: $i,X59: $i,X60: $i,X61: $i] :
      ~ ( zip_tseitin_0 @ X53 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 @ X61 @ X53 ) ),
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

thf(t71_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) )
       => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k1_funct_1 @ C @ A ) ) ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) )
         => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
            = ( k1_funct_1 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t71_funct_1])).

thf('17',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X82: $i,X83: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X82 @ X83 ) )
      = ( k3_xboole_0 @ X82 @ X83 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf(d1_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( A = k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ( B = k1_xboole_0 ) ) )
      & ( ( A != k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ! [D: $i] :
                  ( ( r2_hidden @ D @ A )
                 => ( r2_hidden @ C @ D ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X75: $i,X76: $i,X78: $i,X79: $i] :
      ( ( X75
       != ( k1_setfam_1 @ X76 ) )
      | ~ ( r2_hidden @ X78 @ X76 )
      | ( r2_hidden @ X79 @ X78 )
      | ~ ( r2_hidden @ X79 @ X75 )
      | ( X76 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('20',plain,(
    ! [X76: $i,X78: $i,X79: $i] :
      ( ( X76 = k1_xboole_0 )
      | ~ ( r2_hidden @ X79 @ ( k1_setfam_1 @ X76 ) )
      | ( r2_hidden @ X79 @ X78 )
      | ~ ( r2_hidden @ X78 @ X76 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X3 @ ( k2_tarski @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X3 )
      | ( ( k2_tarski @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t50_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
     != k1_xboole_0 ) )).

thf('23',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X50 @ X51 ) @ X52 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t50_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X3 @ ( k2_tarski @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X3 ) ) ),
    inference('simplify_reflect-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k2_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','25'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('27',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('28',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X21 @ X21 @ X22 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('29',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('32',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k4_enumset1 @ X30 @ X30 @ X31 @ X32 @ X33 @ X34 )
      = ( k3_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t67_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ) )).

thf('33',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k6_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 ) @ ( k2_tarski @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t67_enumset1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X6 @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( k6_enumset1 @ X41 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 )
      = ( k5_enumset1 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X6 @ X5 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X2 @ X1 @ X0 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['30','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','42'])).

thf('44',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k2_enumset1 @ X23 @ X23 @ X24 @ X25 )
      = ( k1_enumset1 @ X23 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t125_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ D @ C @ B @ A ) ) )).

thf('45',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 )
      = ( k2_enumset1 @ X1 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X2 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k2_enumset1 @ X23 @ X23 @ X24 @ X25 )
      = ( k1_enumset1 @ X23 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','42'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('53',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k3_enumset1 @ X26 @ X26 @ X27 @ X28 @ X29 )
      = ( k2_enumset1 @ X26 @ X27 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('54',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 )
      = ( k2_enumset1 @ X1 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 )
      = ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k4_enumset1 @ X30 @ X30 @ X31 @ X32 @ X33 @ X34 )
      = ( k3_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t61_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ) )).

thf('57',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k5_enumset1 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 ) @ ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t61_enumset1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X0 @ X0 @ X0 @ X1 @ X2 @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k3_enumset1 @ X26 @ X26 @ X27 @ X28 @ X29 )
      = ( k2_enumset1 @ X26 @ X27 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X1 @ X2 @ X3 @ X4 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X1 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 )
      = ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('71',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k3_enumset1 @ X26 @ X26 @ X27 @ X28 @ X29 )
      = ( k2_enumset1 @ X26 @ X27 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X1 @ X2 @ X3 )
      = ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X0 @ X0 @ X0 @ X1 @ X2 @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X0 @ X1 @ X1 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['69','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X1 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['52','79'])).

thf('81',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X21 @ X21 @ X22 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['51','82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['26','84'])).

thf('86',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['16','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','48'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X1 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','14'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['26','84'])).

thf('93',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf(t86_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('94',plain,(
    ! [X84: $i,X85: $i,X86: $i] :
      ( ~ ( r2_hidden @ X84 @ X85 )
      | ~ ( r2_hidden @ X84 @ ( k1_relat_1 @ X86 ) )
      | ( r2_hidden @ X84 @ ( k1_relat_1 @ ( k7_relat_1 @ X86 @ X85 ) ) )
      | ~ ( v1_relat_1 @ X86 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C_1 @ X0 ) ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C_1 @ X0 ) ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['86','97'])).

thf(t70_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
       => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k1_funct_1 @ C @ A ) ) ) ) )).

thf('99',plain,(
    ! [X87: $i,X88: $i,X89: $i] :
      ( ~ ( r2_hidden @ X87 @ ( k1_relat_1 @ ( k7_relat_1 @ X88 @ X89 ) ) )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X88 @ X89 ) @ X87 )
        = ( k1_funct_1 @ X88 @ X87 ) )
      | ~ ( v1_funct_1 @ X88 )
      | ~ ( v1_relat_1 @ X88 ) ) ),
    inference(cnf,[status(esa)],[t70_funct_1])).

thf('100',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k1_funct_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) @ sk_A )
      = ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('102',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('103',plain,
    ( ( k1_funct_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) @ sk_A )
    = ( k1_funct_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,(
    ( k1_funct_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) @ sk_A )
 != ( k1_funct_1 @ sk_C_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('105',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['103','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wormkOkUka
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:04:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 12.15/12.32  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 12.15/12.32  % Solved by: fo/fo7.sh
% 12.15/12.32  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 12.15/12.32  % done 7697 iterations in 11.870s
% 12.15/12.32  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 12.15/12.32  % SZS output start Refutation
% 12.15/12.32  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 12.15/12.32                                               $i > $i > $i > $o).
% 12.15/12.32  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 12.15/12.32  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 12.15/12.32  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 12.15/12.32  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 12.15/12.32                                           $i > $i).
% 12.15/12.32  thf(sk_A_type, type, sk_A: $i).
% 12.15/12.32  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 12.15/12.32  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 12.15/12.32  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 12.15/12.32  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 12.15/12.32  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 12.15/12.32  thf(sk_C_1_type, type, sk_C_1: $i).
% 12.15/12.32  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 12.15/12.32  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 12.15/12.32  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 12.15/12.32  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 12.15/12.32  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 12.15/12.32  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 12.15/12.32  thf(sk_B_type, type, sk_B: $i).
% 12.15/12.32  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 12.15/12.32  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 12.15/12.32  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 12.15/12.32  thf(t70_enumset1, axiom,
% 12.15/12.32    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 12.15/12.32  thf('0', plain,
% 12.15/12.32      (![X21 : $i, X22 : $i]:
% 12.15/12.32         ((k1_enumset1 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 12.15/12.32      inference('cnf', [status(esa)], [t70_enumset1])).
% 12.15/12.32  thf(t72_enumset1, axiom,
% 12.15/12.32    (![A:$i,B:$i,C:$i,D:$i]:
% 12.15/12.32     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 12.15/12.32  thf('1', plain,
% 12.15/12.32      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 12.15/12.32         ((k3_enumset1 @ X26 @ X26 @ X27 @ X28 @ X29)
% 12.15/12.32           = (k2_enumset1 @ X26 @ X27 @ X28 @ X29))),
% 12.15/12.32      inference('cnf', [status(esa)], [t72_enumset1])).
% 12.15/12.32  thf(t71_enumset1, axiom,
% 12.15/12.32    (![A:$i,B:$i,C:$i]:
% 12.15/12.32     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 12.15/12.32  thf('2', plain,
% 12.15/12.32      (![X23 : $i, X24 : $i, X25 : $i]:
% 12.15/12.32         ((k2_enumset1 @ X23 @ X23 @ X24 @ X25)
% 12.15/12.32           = (k1_enumset1 @ X23 @ X24 @ X25))),
% 12.15/12.32      inference('cnf', [status(esa)], [t71_enumset1])).
% 12.15/12.32  thf('3', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.15/12.32         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 12.15/12.32      inference('sup+', [status(thm)], ['1', '2'])).
% 12.15/12.32  thf(t74_enumset1, axiom,
% 12.15/12.32    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 12.15/12.32     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 12.15/12.32       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 12.15/12.32  thf('4', plain,
% 12.15/12.32      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 12.15/12.32         ((k5_enumset1 @ X35 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40)
% 12.15/12.32           = (k4_enumset1 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40))),
% 12.15/12.32      inference('cnf', [status(esa)], [t74_enumset1])).
% 12.15/12.32  thf(t73_enumset1, axiom,
% 12.15/12.32    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 12.15/12.32     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 12.15/12.32       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 12.15/12.32  thf('5', plain,
% 12.15/12.32      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 12.15/12.32         ((k4_enumset1 @ X30 @ X30 @ X31 @ X32 @ X33 @ X34)
% 12.15/12.32           = (k3_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34))),
% 12.15/12.32      inference('cnf', [status(esa)], [t73_enumset1])).
% 12.15/12.32  thf('6', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 12.15/12.32         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 12.15/12.32           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 12.15/12.32      inference('sup+', [status(thm)], ['4', '5'])).
% 12.15/12.32  thf(t75_enumset1, axiom,
% 12.15/12.32    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 12.15/12.32     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 12.15/12.32       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 12.15/12.32  thf('7', plain,
% 12.15/12.32      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 12.15/12.32         ((k6_enumset1 @ X41 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47)
% 12.15/12.32           = (k5_enumset1 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47))),
% 12.15/12.32      inference('cnf', [status(esa)], [t75_enumset1])).
% 12.15/12.32  thf(d6_enumset1, axiom,
% 12.15/12.32    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 12.15/12.32     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 12.15/12.32       ( ![J:$i]:
% 12.15/12.32         ( ( r2_hidden @ J @ I ) <=>
% 12.15/12.32           ( ~( ( ( J ) != ( H ) ) & ( ( J ) != ( G ) ) & ( ( J ) != ( F ) ) & 
% 12.15/12.32                ( ( J ) != ( E ) ) & ( ( J ) != ( D ) ) & ( ( J ) != ( C ) ) & 
% 12.15/12.32                ( ( J ) != ( B ) ) & ( ( J ) != ( A ) ) ) ) ) ) ))).
% 12.15/12.32  thf(zf_stmt_0, type, zip_tseitin_0 :
% 12.15/12.32      $i > $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 12.15/12.32  thf(zf_stmt_1, axiom,
% 12.15/12.32    (![J:$i,H:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 12.15/12.32     ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) <=>
% 12.15/12.32       ( ( ( J ) != ( A ) ) & ( ( J ) != ( B ) ) & ( ( J ) != ( C ) ) & 
% 12.15/12.32         ( ( J ) != ( D ) ) & ( ( J ) != ( E ) ) & ( ( J ) != ( F ) ) & 
% 12.15/12.32         ( ( J ) != ( G ) ) & ( ( J ) != ( H ) ) ) ))).
% 12.15/12.32  thf(zf_stmt_2, axiom,
% 12.15/12.32    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 12.15/12.32     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 12.15/12.32       ( ![J:$i]:
% 12.15/12.32         ( ( r2_hidden @ J @ I ) <=>
% 12.15/12.32           ( ~( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 12.15/12.32  thf('8', plain,
% 12.15/12.32      (![X63 : $i, X64 : $i, X65 : $i, X66 : $i, X67 : $i, X68 : $i, X69 : $i, 
% 12.15/12.32         X70 : $i, X71 : $i, X72 : $i]:
% 12.15/12.32         ((zip_tseitin_0 @ X63 @ X64 @ X65 @ X66 @ X67 @ X68 @ X69 @ X70 @ X71)
% 12.15/12.32          | (r2_hidden @ X63 @ X72)
% 12.15/12.32          | ((X72)
% 12.15/12.32              != (k6_enumset1 @ X71 @ X70 @ X69 @ X68 @ X67 @ X66 @ X65 @ X64)))),
% 12.15/12.32      inference('cnf', [status(esa)], [zf_stmt_2])).
% 12.15/12.32  thf('9', plain,
% 12.15/12.32      (![X63 : $i, X64 : $i, X65 : $i, X66 : $i, X67 : $i, X68 : $i, X69 : $i, 
% 12.15/12.32         X70 : $i, X71 : $i]:
% 12.15/12.32         ((r2_hidden @ X63 @ 
% 12.15/12.32           (k6_enumset1 @ X71 @ X70 @ X69 @ X68 @ X67 @ X66 @ X65 @ X64))
% 12.15/12.32          | (zip_tseitin_0 @ X63 @ X64 @ X65 @ X66 @ X67 @ X68 @ X69 @ X70 @ 
% 12.15/12.32             X71))),
% 12.15/12.32      inference('simplify', [status(thm)], ['8'])).
% 12.15/12.32  thf('10', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 12.15/12.32         ((r2_hidden @ X7 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 12.15/12.32          | (zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6))),
% 12.15/12.32      inference('sup+', [status(thm)], ['7', '9'])).
% 12.15/12.32  thf('11', plain,
% 12.15/12.32      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i, X58 : $i, X59 : $i, 
% 12.15/12.32         X60 : $i, X61 : $i]:
% 12.15/12.32         (((X54) != (X53))
% 12.15/12.32          | ~ (zip_tseitin_0 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 @ X61 @ 
% 12.15/12.32               X53))),
% 12.15/12.32      inference('cnf', [status(esa)], [zf_stmt_1])).
% 12.15/12.32  thf('12', plain,
% 12.15/12.32      (![X53 : $i, X55 : $i, X56 : $i, X57 : $i, X58 : $i, X59 : $i, X60 : $i, 
% 12.15/12.32         X61 : $i]:
% 12.15/12.32         ~ (zip_tseitin_0 @ X53 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 @ X61 @ X53)),
% 12.15/12.32      inference('simplify', [status(thm)], ['11'])).
% 12.15/12.32  thf('13', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 12.15/12.32         (r2_hidden @ X0 @ (k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6))),
% 12.15/12.32      inference('sup-', [status(thm)], ['10', '12'])).
% 12.15/12.32  thf('14', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 12.15/12.32         (r2_hidden @ X4 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 12.15/12.32      inference('sup+', [status(thm)], ['6', '13'])).
% 12.15/12.32  thf('15', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.15/12.32         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 12.15/12.32      inference('sup+', [status(thm)], ['3', '14'])).
% 12.15/12.32  thf('16', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 12.15/12.32      inference('sup+', [status(thm)], ['0', '15'])).
% 12.15/12.32  thf(t71_funct_1, conjecture,
% 12.15/12.32    (![A:$i,B:$i,C:$i]:
% 12.15/12.32     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 12.15/12.32       ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 12.15/12.32         ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k1_funct_1 @ C @ A ) ) ) ))).
% 12.15/12.32  thf(zf_stmt_3, negated_conjecture,
% 12.15/12.32    (~( ![A:$i,B:$i,C:$i]:
% 12.15/12.32        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 12.15/12.32          ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 12.15/12.32            ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) =
% 12.15/12.32              ( k1_funct_1 @ C @ A ) ) ) ) )),
% 12.15/12.32    inference('cnf.neg', [status(esa)], [t71_funct_1])).
% 12.15/12.32  thf('17', plain,
% 12.15/12.32      ((r2_hidden @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_C_1) @ sk_B))),
% 12.15/12.32      inference('cnf', [status(esa)], [zf_stmt_3])).
% 12.15/12.32  thf(t12_setfam_1, axiom,
% 12.15/12.32    (![A:$i,B:$i]:
% 12.15/12.32     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 12.15/12.32  thf('18', plain,
% 12.15/12.32      (![X82 : $i, X83 : $i]:
% 12.15/12.32         ((k1_setfam_1 @ (k2_tarski @ X82 @ X83)) = (k3_xboole_0 @ X82 @ X83))),
% 12.15/12.32      inference('cnf', [status(esa)], [t12_setfam_1])).
% 12.15/12.32  thf(d1_setfam_1, axiom,
% 12.15/12.32    (![A:$i,B:$i]:
% 12.15/12.32     ( ( ( ( A ) = ( k1_xboole_0 ) ) =>
% 12.15/12.32         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=> ( ( B ) = ( k1_xboole_0 ) ) ) ) & 
% 12.15/12.32       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 12.15/12.32         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=>
% 12.15/12.32           ( ![C:$i]:
% 12.15/12.32             ( ( r2_hidden @ C @ B ) <=>
% 12.15/12.32               ( ![D:$i]: ( ( r2_hidden @ D @ A ) => ( r2_hidden @ C @ D ) ) ) ) ) ) ) ))).
% 12.15/12.32  thf('19', plain,
% 12.15/12.32      (![X75 : $i, X76 : $i, X78 : $i, X79 : $i]:
% 12.15/12.32         (((X75) != (k1_setfam_1 @ X76))
% 12.15/12.32          | ~ (r2_hidden @ X78 @ X76)
% 12.15/12.32          | (r2_hidden @ X79 @ X78)
% 12.15/12.32          | ~ (r2_hidden @ X79 @ X75)
% 12.15/12.32          | ((X76) = (k1_xboole_0)))),
% 12.15/12.32      inference('cnf', [status(esa)], [d1_setfam_1])).
% 12.15/12.32  thf('20', plain,
% 12.15/12.32      (![X76 : $i, X78 : $i, X79 : $i]:
% 12.15/12.32         (((X76) = (k1_xboole_0))
% 12.15/12.32          | ~ (r2_hidden @ X79 @ (k1_setfam_1 @ X76))
% 12.15/12.32          | (r2_hidden @ X79 @ X78)
% 12.15/12.32          | ~ (r2_hidden @ X78 @ X76))),
% 12.15/12.32      inference('simplify', [status(thm)], ['19'])).
% 12.15/12.32  thf('21', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.15/12.32         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 12.15/12.32          | ~ (r2_hidden @ X3 @ (k2_tarski @ X1 @ X0))
% 12.15/12.32          | (r2_hidden @ X2 @ X3)
% 12.15/12.32          | ((k2_tarski @ X1 @ X0) = (k1_xboole_0)))),
% 12.15/12.32      inference('sup-', [status(thm)], ['18', '20'])).
% 12.15/12.32  thf(idempotence_k2_xboole_0, axiom,
% 12.15/12.32    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 12.15/12.32  thf('22', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 12.15/12.32      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 12.15/12.32  thf(t50_zfmisc_1, axiom,
% 12.15/12.32    (![A:$i,B:$i,C:$i]:
% 12.15/12.32     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 12.15/12.32  thf('23', plain,
% 12.15/12.32      (![X50 : $i, X51 : $i, X52 : $i]:
% 12.15/12.32         ((k2_xboole_0 @ (k2_tarski @ X50 @ X51) @ X52) != (k1_xboole_0))),
% 12.15/12.32      inference('cnf', [status(esa)], [t50_zfmisc_1])).
% 12.15/12.32  thf('24', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) != (k1_xboole_0))),
% 12.15/12.32      inference('sup-', [status(thm)], ['22', '23'])).
% 12.15/12.32  thf('25', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.15/12.32         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 12.15/12.32          | ~ (r2_hidden @ X3 @ (k2_tarski @ X1 @ X0))
% 12.15/12.32          | (r2_hidden @ X2 @ X3))),
% 12.15/12.32      inference('simplify_reflect-', [status(thm)], ['21', '24'])).
% 12.15/12.32  thf('26', plain,
% 12.15/12.32      (![X0 : $i]:
% 12.15/12.32         ((r2_hidden @ sk_A @ X0)
% 12.15/12.32          | ~ (r2_hidden @ X0 @ (k2_tarski @ (k1_relat_1 @ sk_C_1) @ sk_B)))),
% 12.15/12.32      inference('sup-', [status(thm)], ['17', '25'])).
% 12.15/12.32  thf(t69_enumset1, axiom,
% 12.15/12.32    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 12.15/12.32  thf('27', plain,
% 12.15/12.32      (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 12.15/12.32      inference('cnf', [status(esa)], [t69_enumset1])).
% 12.15/12.32  thf('28', plain,
% 12.15/12.32      (![X21 : $i, X22 : $i]:
% 12.15/12.32         ((k1_enumset1 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 12.15/12.32      inference('cnf', [status(esa)], [t70_enumset1])).
% 12.15/12.32  thf('29', plain,
% 12.15/12.32      (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 12.15/12.32      inference('cnf', [status(esa)], [t69_enumset1])).
% 12.15/12.32  thf('30', plain,
% 12.15/12.32      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 12.15/12.32      inference('sup+', [status(thm)], ['28', '29'])).
% 12.15/12.32  thf('31', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.15/12.32         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 12.15/12.32      inference('sup+', [status(thm)], ['1', '2'])).
% 12.15/12.32  thf('32', plain,
% 12.15/12.32      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 12.15/12.32         ((k4_enumset1 @ X30 @ X30 @ X31 @ X32 @ X33 @ X34)
% 12.15/12.32           = (k3_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34))),
% 12.15/12.32      inference('cnf', [status(esa)], [t73_enumset1])).
% 12.15/12.32  thf(t67_enumset1, axiom,
% 12.15/12.32    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 12.15/12.32     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 12.15/12.32       ( k2_xboole_0 @
% 12.15/12.32         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ))).
% 12.15/12.32  thf('33', plain,
% 12.15/12.32      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, 
% 12.15/12.32         X19 : $i]:
% 12.15/12.32         ((k6_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19)
% 12.15/12.32           = (k2_xboole_0 @ 
% 12.15/12.32              (k4_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17) @ 
% 12.15/12.32              (k2_tarski @ X18 @ X19)))),
% 12.15/12.32      inference('cnf', [status(esa)], [t67_enumset1])).
% 12.15/12.32  thf('34', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 12.15/12.32         ((k6_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5)
% 12.15/12.32           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 12.15/12.32              (k2_tarski @ X6 @ X5)))),
% 12.15/12.32      inference('sup+', [status(thm)], ['32', '33'])).
% 12.15/12.32  thf('35', plain,
% 12.15/12.32      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 12.15/12.32         ((k6_enumset1 @ X41 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47)
% 12.15/12.32           = (k5_enumset1 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47))),
% 12.15/12.32      inference('cnf', [status(esa)], [t75_enumset1])).
% 12.15/12.32  thf('36', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 12.15/12.32         ((k5_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5)
% 12.15/12.32           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 12.15/12.32              (k2_tarski @ X6 @ X5)))),
% 12.15/12.32      inference('demod', [status(thm)], ['34', '35'])).
% 12.15/12.32  thf('37', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 12.15/12.32         ((k5_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 @ X4 @ X3)
% 12.15/12.32           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 12.15/12.32              (k2_tarski @ X4 @ X3)))),
% 12.15/12.32      inference('sup+', [status(thm)], ['31', '36'])).
% 12.15/12.32  thf('38', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 12.15/12.32         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 12.15/12.32           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 12.15/12.32      inference('sup+', [status(thm)], ['4', '5'])).
% 12.15/12.32  thf('39', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 12.15/12.32         ((k3_enumset1 @ X2 @ X1 @ X0 @ X4 @ X3)
% 12.15/12.32           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 12.15/12.32              (k2_tarski @ X4 @ X3)))),
% 12.15/12.32      inference('demod', [status(thm)], ['37', '38'])).
% 12.15/12.32  thf('40', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.15/12.32         ((k3_enumset1 @ X0 @ X0 @ X0 @ X2 @ X1)
% 12.15/12.32           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 12.15/12.32      inference('sup+', [status(thm)], ['30', '39'])).
% 12.15/12.32  thf('41', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.15/12.32         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 12.15/12.32      inference('sup+', [status(thm)], ['1', '2'])).
% 12.15/12.32  thf('42', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.15/12.32         ((k1_enumset1 @ X0 @ X2 @ X1)
% 12.15/12.32           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 12.15/12.32      inference('demod', [status(thm)], ['40', '41'])).
% 12.15/12.32  thf('43', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i]:
% 12.15/12.32         ((k1_enumset1 @ X1 @ X0 @ X0)
% 12.15/12.32           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 12.15/12.32      inference('sup+', [status(thm)], ['27', '42'])).
% 12.15/12.32  thf('44', plain,
% 12.15/12.32      (![X23 : $i, X24 : $i, X25 : $i]:
% 12.15/12.32         ((k2_enumset1 @ X23 @ X23 @ X24 @ X25)
% 12.15/12.32           = (k1_enumset1 @ X23 @ X24 @ X25))),
% 12.15/12.32      inference('cnf', [status(esa)], [t71_enumset1])).
% 12.15/12.32  thf(t125_enumset1, axiom,
% 12.15/12.32    (![A:$i,B:$i,C:$i,D:$i]:
% 12.15/12.32     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ C @ B @ A ) ))).
% 12.15/12.32  thf('45', plain,
% 12.15/12.32      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 12.15/12.32         ((k2_enumset1 @ X4 @ X3 @ X2 @ X1) = (k2_enumset1 @ X1 @ X2 @ X3 @ X4))),
% 12.15/12.32      inference('cnf', [status(esa)], [t125_enumset1])).
% 12.15/12.32  thf('46', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.15/12.32         ((k2_enumset1 @ X0 @ X1 @ X2 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 12.15/12.32      inference('sup+', [status(thm)], ['44', '45'])).
% 12.15/12.32  thf('47', plain,
% 12.15/12.32      (![X23 : $i, X24 : $i, X25 : $i]:
% 12.15/12.32         ((k2_enumset1 @ X23 @ X23 @ X24 @ X25)
% 12.15/12.32           = (k1_enumset1 @ X23 @ X24 @ X25))),
% 12.15/12.32      inference('cnf', [status(esa)], [t71_enumset1])).
% 12.15/12.32  thf('48', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i]:
% 12.15/12.32         ((k1_enumset1 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X1))),
% 12.15/12.32      inference('sup+', [status(thm)], ['46', '47'])).
% 12.15/12.32  thf('49', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i]:
% 12.15/12.32         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 12.15/12.32           = (k1_enumset1 @ X0 @ X1 @ X1))),
% 12.15/12.32      inference('sup+', [status(thm)], ['43', '48'])).
% 12.15/12.32  thf('50', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i]:
% 12.15/12.32         ((k1_enumset1 @ X1 @ X0 @ X0)
% 12.15/12.32           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 12.15/12.32      inference('sup+', [status(thm)], ['27', '42'])).
% 12.15/12.32  thf('51', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i]:
% 12.15/12.32         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 12.15/12.32           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 12.15/12.32      inference('sup+', [status(thm)], ['49', '50'])).
% 12.15/12.32  thf('52', plain,
% 12.15/12.32      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 12.15/12.32      inference('sup+', [status(thm)], ['28', '29'])).
% 12.15/12.32  thf('53', plain,
% 12.15/12.32      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 12.15/12.32         ((k3_enumset1 @ X26 @ X26 @ X27 @ X28 @ X29)
% 12.15/12.32           = (k2_enumset1 @ X26 @ X27 @ X28 @ X29))),
% 12.15/12.32      inference('cnf', [status(esa)], [t72_enumset1])).
% 12.15/12.32  thf('54', plain,
% 12.15/12.32      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 12.15/12.32         ((k2_enumset1 @ X4 @ X3 @ X2 @ X1) = (k2_enumset1 @ X1 @ X2 @ X3 @ X4))),
% 12.15/12.32      inference('cnf', [status(esa)], [t125_enumset1])).
% 12.15/12.32  thf('55', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.15/12.32         ((k2_enumset1 @ X0 @ X1 @ X2 @ X3)
% 12.15/12.32           = (k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0))),
% 12.15/12.32      inference('sup+', [status(thm)], ['53', '54'])).
% 12.15/12.32  thf('56', plain,
% 12.15/12.32      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 12.15/12.32         ((k4_enumset1 @ X30 @ X30 @ X31 @ X32 @ X33 @ X34)
% 12.15/12.32           = (k3_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34))),
% 12.15/12.32      inference('cnf', [status(esa)], [t73_enumset1])).
% 12.15/12.32  thf(t61_enumset1, axiom,
% 12.15/12.32    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 12.15/12.32     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 12.15/12.32       ( k2_xboole_0 @
% 12.15/12.32         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ))).
% 12.15/12.32  thf('57', plain,
% 12.15/12.32      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 12.15/12.32         ((k5_enumset1 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11)
% 12.15/12.32           = (k2_xboole_0 @ (k4_enumset1 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10) @ 
% 12.15/12.32              (k1_tarski @ X11)))),
% 12.15/12.32      inference('cnf', [status(esa)], [t61_enumset1])).
% 12.15/12.32  thf('58', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 12.15/12.32         ((k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5)
% 12.15/12.32           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 12.15/12.32              (k1_tarski @ X5)))),
% 12.15/12.32      inference('sup+', [status(thm)], ['56', '57'])).
% 12.15/12.32  thf('59', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 12.15/12.32         ((k5_enumset1 @ X0 @ X0 @ X0 @ X1 @ X2 @ X3 @ X4)
% 12.15/12.32           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 12.15/12.32              (k1_tarski @ X4)))),
% 12.15/12.32      inference('sup+', [status(thm)], ['55', '58'])).
% 12.15/12.32  thf('60', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 12.15/12.32         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 12.15/12.32           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 12.15/12.32      inference('sup+', [status(thm)], ['4', '5'])).
% 12.15/12.32  thf('61', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 12.15/12.32         ((k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4)
% 12.15/12.32           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 12.15/12.32              (k1_tarski @ X4)))),
% 12.15/12.32      inference('demod', [status(thm)], ['59', '60'])).
% 12.15/12.32  thf('62', plain,
% 12.15/12.32      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 12.15/12.32         ((k3_enumset1 @ X26 @ X26 @ X27 @ X28 @ X29)
% 12.15/12.32           = (k2_enumset1 @ X26 @ X27 @ X28 @ X29))),
% 12.15/12.32      inference('cnf', [status(esa)], [t72_enumset1])).
% 12.15/12.32  thf('63', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 12.15/12.32         ((k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5)
% 12.15/12.32           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 12.15/12.32              (k1_tarski @ X5)))),
% 12.15/12.32      inference('sup+', [status(thm)], ['56', '57'])).
% 12.15/12.32  thf('64', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 12.15/12.32         ((k5_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4)
% 12.15/12.32           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 12.15/12.32              (k1_tarski @ X4)))),
% 12.15/12.32      inference('sup+', [status(thm)], ['62', '63'])).
% 12.15/12.32  thf('65', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 12.15/12.32         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 12.15/12.32           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 12.15/12.32      inference('sup+', [status(thm)], ['4', '5'])).
% 12.15/12.32  thf('66', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 12.15/12.32         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 12.15/12.32           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 12.15/12.32              (k1_tarski @ X4)))),
% 12.15/12.32      inference('demod', [status(thm)], ['64', '65'])).
% 12.15/12.32  thf('67', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 12.15/12.32         ((k3_enumset1 @ X1 @ X2 @ X3 @ X4 @ X0)
% 12.15/12.32           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 12.15/12.32      inference('sup+', [status(thm)], ['61', '66'])).
% 12.15/12.32  thf('68', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.15/12.32         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 12.15/12.32      inference('sup+', [status(thm)], ['1', '2'])).
% 12.15/12.32  thf('69', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.15/12.32         ((k3_enumset1 @ X2 @ X1 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 12.15/12.32      inference('sup+', [status(thm)], ['67', '68'])).
% 12.15/12.32  thf('70', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.15/12.32         ((k2_enumset1 @ X0 @ X1 @ X2 @ X3)
% 12.15/12.32           = (k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0))),
% 12.15/12.32      inference('sup+', [status(thm)], ['53', '54'])).
% 12.15/12.32  thf('71', plain,
% 12.15/12.32      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 12.15/12.32         ((k3_enumset1 @ X26 @ X26 @ X27 @ X28 @ X29)
% 12.15/12.32           = (k2_enumset1 @ X26 @ X27 @ X28 @ X29))),
% 12.15/12.32      inference('cnf', [status(esa)], [t72_enumset1])).
% 12.15/12.32  thf('72', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.15/12.32         ((k3_enumset1 @ X0 @ X0 @ X1 @ X2 @ X3)
% 12.15/12.32           = (k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0))),
% 12.15/12.32      inference('sup+', [status(thm)], ['70', '71'])).
% 12.15/12.32  thf('73', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 12.15/12.32         ((k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5)
% 12.15/12.32           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 12.15/12.32              (k1_tarski @ X5)))),
% 12.15/12.32      inference('sup+', [status(thm)], ['56', '57'])).
% 12.15/12.32  thf('74', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 12.15/12.32         ((k5_enumset1 @ X0 @ X0 @ X0 @ X1 @ X2 @ X3 @ X4)
% 12.15/12.32           = (k2_xboole_0 @ (k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0) @ 
% 12.15/12.32              (k1_tarski @ X4)))),
% 12.15/12.32      inference('sup+', [status(thm)], ['72', '73'])).
% 12.15/12.32  thf('75', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 12.15/12.32         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 12.15/12.32           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 12.15/12.32      inference('sup+', [status(thm)], ['4', '5'])).
% 12.15/12.32  thf('76', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 12.15/12.32         ((k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4)
% 12.15/12.32           = (k2_xboole_0 @ (k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0) @ 
% 12.15/12.32              (k1_tarski @ X4)))),
% 12.15/12.32      inference('demod', [status(thm)], ['74', '75'])).
% 12.15/12.32  thf('77', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.15/12.32         ((k3_enumset1 @ X0 @ X1 @ X1 @ X1 @ X2)
% 12.15/12.32           = (k2_xboole_0 @ (k1_enumset1 @ X1 @ X1 @ X0) @ (k1_tarski @ X2)))),
% 12.15/12.32      inference('sup+', [status(thm)], ['69', '76'])).
% 12.15/12.32  thf('78', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.15/12.32         ((k3_enumset1 @ X2 @ X1 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 12.15/12.32      inference('sup+', [status(thm)], ['67', '68'])).
% 12.15/12.32  thf('79', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.15/12.32         ((k1_enumset1 @ X1 @ X0 @ X2)
% 12.15/12.32           = (k2_xboole_0 @ (k1_enumset1 @ X1 @ X1 @ X0) @ (k1_tarski @ X2)))),
% 12.15/12.32      inference('demod', [status(thm)], ['77', '78'])).
% 12.15/12.32  thf('80', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i]:
% 12.15/12.32         ((k1_enumset1 @ X0 @ X0 @ X1)
% 12.15/12.32           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 12.15/12.32      inference('sup+', [status(thm)], ['52', '79'])).
% 12.15/12.32  thf('81', plain,
% 12.15/12.32      (![X21 : $i, X22 : $i]:
% 12.15/12.32         ((k1_enumset1 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 12.15/12.32      inference('cnf', [status(esa)], [t70_enumset1])).
% 12.15/12.32  thf('82', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i]:
% 12.15/12.32         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 12.15/12.32           = (k2_tarski @ X1 @ X0))),
% 12.15/12.32      inference('sup+', [status(thm)], ['80', '81'])).
% 12.15/12.32  thf('83', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i]:
% 12.15/12.32         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 12.15/12.32           = (k2_tarski @ X1 @ X0))),
% 12.15/12.32      inference('sup+', [status(thm)], ['80', '81'])).
% 12.15/12.32  thf('84', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 12.15/12.32      inference('demod', [status(thm)], ['51', '82', '83'])).
% 12.15/12.32  thf('85', plain,
% 12.15/12.32      (![X0 : $i]:
% 12.15/12.32         ((r2_hidden @ sk_A @ X0)
% 12.15/12.32          | ~ (r2_hidden @ X0 @ (k2_tarski @ sk_B @ (k1_relat_1 @ sk_C_1))))),
% 12.15/12.32      inference('demod', [status(thm)], ['26', '84'])).
% 12.15/12.32  thf('86', plain, ((r2_hidden @ sk_A @ sk_B)),
% 12.15/12.32      inference('sup-', [status(thm)], ['16', '85'])).
% 12.15/12.32  thf('87', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i]:
% 12.15/12.32         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 12.15/12.32           = (k1_enumset1 @ X0 @ X1 @ X1))),
% 12.15/12.32      inference('sup+', [status(thm)], ['43', '48'])).
% 12.15/12.32  thf('88', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i]:
% 12.15/12.32         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 12.15/12.32           = (k2_tarski @ X1 @ X0))),
% 12.15/12.32      inference('sup+', [status(thm)], ['80', '81'])).
% 12.15/12.32  thf('89', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i]:
% 12.15/12.32         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X1))),
% 12.15/12.32      inference('demod', [status(thm)], ['87', '88'])).
% 12.15/12.32  thf('90', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.15/12.32         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 12.15/12.32      inference('sup+', [status(thm)], ['3', '14'])).
% 12.15/12.32  thf('91', plain,
% 12.15/12.32      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 12.15/12.32      inference('sup+', [status(thm)], ['89', '90'])).
% 12.15/12.32  thf('92', plain,
% 12.15/12.32      (![X0 : $i]:
% 12.15/12.32         ((r2_hidden @ sk_A @ X0)
% 12.15/12.32          | ~ (r2_hidden @ X0 @ (k2_tarski @ sk_B @ (k1_relat_1 @ sk_C_1))))),
% 12.15/12.32      inference('demod', [status(thm)], ['26', '84'])).
% 12.15/12.32  thf('93', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))),
% 12.15/12.32      inference('sup-', [status(thm)], ['91', '92'])).
% 12.15/12.32  thf(t86_relat_1, axiom,
% 12.15/12.32    (![A:$i,B:$i,C:$i]:
% 12.15/12.32     ( ( v1_relat_1 @ C ) =>
% 12.15/12.32       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 12.15/12.32         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 12.15/12.32  thf('94', plain,
% 12.15/12.32      (![X84 : $i, X85 : $i, X86 : $i]:
% 12.15/12.32         (~ (r2_hidden @ X84 @ X85)
% 12.15/12.32          | ~ (r2_hidden @ X84 @ (k1_relat_1 @ X86))
% 12.15/12.32          | (r2_hidden @ X84 @ (k1_relat_1 @ (k7_relat_1 @ X86 @ X85)))
% 12.15/12.32          | ~ (v1_relat_1 @ X86))),
% 12.15/12.32      inference('cnf', [status(esa)], [t86_relat_1])).
% 12.15/12.32  thf('95', plain,
% 12.15/12.32      (![X0 : $i]:
% 12.15/12.32         (~ (v1_relat_1 @ sk_C_1)
% 12.15/12.32          | (r2_hidden @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_C_1 @ X0)))
% 12.15/12.32          | ~ (r2_hidden @ sk_A @ X0))),
% 12.15/12.32      inference('sup-', [status(thm)], ['93', '94'])).
% 12.15/12.32  thf('96', plain, ((v1_relat_1 @ sk_C_1)),
% 12.15/12.32      inference('cnf', [status(esa)], [zf_stmt_3])).
% 12.15/12.32  thf('97', plain,
% 12.15/12.32      (![X0 : $i]:
% 12.15/12.32         ((r2_hidden @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_C_1 @ X0)))
% 12.15/12.32          | ~ (r2_hidden @ sk_A @ X0))),
% 12.15/12.32      inference('demod', [status(thm)], ['95', '96'])).
% 12.15/12.32  thf('98', plain,
% 12.15/12.32      ((r2_hidden @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_C_1 @ sk_B)))),
% 12.15/12.32      inference('sup-', [status(thm)], ['86', '97'])).
% 12.15/12.32  thf(t70_funct_1, axiom,
% 12.15/12.32    (![A:$i,B:$i,C:$i]:
% 12.15/12.32     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 12.15/12.32       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) =>
% 12.15/12.32         ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k1_funct_1 @ C @ A ) ) ) ))).
% 12.15/12.32  thf('99', plain,
% 12.15/12.32      (![X87 : $i, X88 : $i, X89 : $i]:
% 12.15/12.32         (~ (r2_hidden @ X87 @ (k1_relat_1 @ (k7_relat_1 @ X88 @ X89)))
% 12.15/12.32          | ((k1_funct_1 @ (k7_relat_1 @ X88 @ X89) @ X87)
% 12.15/12.32              = (k1_funct_1 @ X88 @ X87))
% 12.15/12.32          | ~ (v1_funct_1 @ X88)
% 12.15/12.32          | ~ (v1_relat_1 @ X88))),
% 12.15/12.32      inference('cnf', [status(esa)], [t70_funct_1])).
% 12.15/12.32  thf('100', plain,
% 12.15/12.32      ((~ (v1_relat_1 @ sk_C_1)
% 12.15/12.32        | ~ (v1_funct_1 @ sk_C_1)
% 12.15/12.32        | ((k1_funct_1 @ (k7_relat_1 @ sk_C_1 @ sk_B) @ sk_A)
% 12.15/12.32            = (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 12.15/12.32      inference('sup-', [status(thm)], ['98', '99'])).
% 12.15/12.32  thf('101', plain, ((v1_relat_1 @ sk_C_1)),
% 12.15/12.32      inference('cnf', [status(esa)], [zf_stmt_3])).
% 12.15/12.32  thf('102', plain, ((v1_funct_1 @ sk_C_1)),
% 12.15/12.32      inference('cnf', [status(esa)], [zf_stmt_3])).
% 12.15/12.32  thf('103', plain,
% 12.15/12.32      (((k1_funct_1 @ (k7_relat_1 @ sk_C_1 @ sk_B) @ sk_A)
% 12.15/12.32         = (k1_funct_1 @ sk_C_1 @ sk_A))),
% 12.15/12.32      inference('demod', [status(thm)], ['100', '101', '102'])).
% 12.15/12.32  thf('104', plain,
% 12.15/12.32      (((k1_funct_1 @ (k7_relat_1 @ sk_C_1 @ sk_B) @ sk_A)
% 12.15/12.32         != (k1_funct_1 @ sk_C_1 @ sk_A))),
% 12.15/12.32      inference('cnf', [status(esa)], [zf_stmt_3])).
% 12.15/12.32  thf('105', plain, ($false),
% 12.15/12.32      inference('simplify_reflect-', [status(thm)], ['103', '104'])).
% 12.15/12.32  
% 12.15/12.32  % SZS output end Refutation
% 12.15/12.32  
% 12.15/12.33  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
