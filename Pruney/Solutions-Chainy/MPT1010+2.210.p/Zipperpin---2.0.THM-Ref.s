%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WKAyJoDzSS

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:42 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   86 (  95 expanded)
%              Number of leaves         :   43 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :  784 ( 966 expanded)
%              Number of equality atoms :   76 (  85 expanded)
%              Maximal formula depth    :   23 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(zf_stmt_0,axiom,(
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

thf('0',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 )
      | ( X35 = X36 )
      | ( X35 = X37 )
      | ( X35 = X38 )
      | ( X35 = X39 )
      | ( X35 = X40 )
      | ( X35 = X41 )
      | ( X35 = X42 )
      | ( X35 = X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( k1_funct_1 @ D @ C )
          = B ) ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ D @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_funct_2])).

thf('1',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('3',plain,(
    ! [X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ~ ( r2_hidden @ X59 @ X60 )
      | ( X61 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X62 )
      | ~ ( v1_funct_2 @ X62 @ X60 @ X61 )
      | ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X61 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X62 @ X59 ) @ X61 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('8',plain,(
    ! [X31: $i,X32: $i] :
      ( ( X32 != X31 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X32 ) @ ( k1_tarski @ X31 ) )
       != ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('9',plain,(
    ! [X31: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X31 ) @ ( k1_tarski @ X31 ) )
     != ( k1_tarski @ X31 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('10',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('11',plain,(
    ! [X56: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X56 ) )
      = X56 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X57: $i,X58: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X57 @ X58 ) )
      = ( k3_xboole_0 @ X57 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('17',plain,(
    ! [X2: $i] :
      ( ( k5_xboole_0 @ X2 @ X2 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('18',plain,(
    ! [X31: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X31 ) ) ),
    inference(demod,[status(thm)],['9','16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['7','18'])).

thf('20',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['1','19'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k1_enumset1 @ X4 @ X4 @ X5 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('22',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('24',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k2_enumset1 @ X6 @ X6 @ X7 @ X8 )
      = ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('25',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k3_enumset1 @ X9 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_enumset1 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('26',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k4_enumset1 @ X13 @ X13 @ X14 @ X15 @ X16 @ X17 )
      = ( k3_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('27',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k5_enumset1 @ X18 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 )
      = ( k4_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('28',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k6_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 )
      = ( k5_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( I
        = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) )
    <=> ! [J: $i] :
          ( ( r2_hidden @ J @ I )
        <=> ~ ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ~ ( r2_hidden @ X54 @ X53 )
      | ~ ( zip_tseitin_0 @ X54 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 )
      | ( X53
       != ( k6_enumset1 @ X52 @ X51 @ X50 @ X49 @ X48 @ X47 @ X46 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('30',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X54: $i] :
      ( ~ ( zip_tseitin_0 @ X54 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 )
      | ~ ( r2_hidden @ X54 @ ( k6_enumset1 @ X52 @ X51 @ X50 @ X49 @ X48 @ X47 @ X46 @ X45 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X6 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X5 @ X5 ) ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 @ X4 @ X4 ) ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 @ X3 @ X3 @ X3 ) ) ),
    inference('sup-',[status(thm)],['25','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2 @ X2 @ X2 @ X2 ) ) ),
    inference('sup-',[status(thm)],['24','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','35'])).

thf('37',plain,(
    ~ ( zip_tseitin_0 @ ( k1_funct_1 @ sk_D @ sk_C ) @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['20','36'])).

thf('38',plain,
    ( ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B ) ),
    inference('sup-',[status(thm)],['0','37'])).

thf('39',plain,
    ( ( k1_funct_1 @ sk_D @ sk_C )
    = sk_B ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ( k1_funct_1 @ sk_D @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('41',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['39','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WKAyJoDzSS
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:55:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.36/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.54  % Solved by: fo/fo7.sh
% 0.36/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.54  % done 96 iterations in 0.061s
% 0.36/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.54  % SZS output start Refutation
% 0.36/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.54  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.36/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.54  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.36/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.54  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.36/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.54  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.36/0.54  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.36/0.54  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.36/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 0.36/0.54                                               $i > $i > $i > $o).
% 0.36/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.36/0.54  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.36/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.54  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.36/0.54                                           $i > $i).
% 0.36/0.54  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.36/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.54  thf(d6_enumset1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.36/0.54     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 0.36/0.54       ( ![J:$i]:
% 0.36/0.54         ( ( r2_hidden @ J @ I ) <=>
% 0.36/0.54           ( ~( ( ( J ) != ( H ) ) & ( ( J ) != ( G ) ) & ( ( J ) != ( F ) ) & 
% 0.36/0.54                ( ( J ) != ( E ) ) & ( ( J ) != ( D ) ) & ( ( J ) != ( C ) ) & 
% 0.36/0.54                ( ( J ) != ( B ) ) & ( ( J ) != ( A ) ) ) ) ) ) ))).
% 0.36/0.54  thf(zf_stmt_0, axiom,
% 0.36/0.54    (![J:$i,H:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.36/0.54     ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) <=>
% 0.36/0.54       ( ( ( J ) != ( A ) ) & ( ( J ) != ( B ) ) & ( ( J ) != ( C ) ) & 
% 0.36/0.54         ( ( J ) != ( D ) ) & ( ( J ) != ( E ) ) & ( ( J ) != ( F ) ) & 
% 0.36/0.54         ( ( J ) != ( G ) ) & ( ( J ) != ( H ) ) ) ))).
% 0.36/0.54  thf('0', plain,
% 0.36/0.54      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, 
% 0.36/0.54         X42 : $i, X43 : $i]:
% 0.36/0.54         ((zip_tseitin_0 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43)
% 0.36/0.54          | ((X35) = (X36))
% 0.36/0.54          | ((X35) = (X37))
% 0.36/0.54          | ((X35) = (X38))
% 0.36/0.54          | ((X35) = (X39))
% 0.36/0.54          | ((X35) = (X40))
% 0.36/0.54          | ((X35) = (X41))
% 0.36/0.54          | ((X35) = (X42))
% 0.36/0.54          | ((X35) = (X43)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(t65_funct_2, conjecture,
% 0.36/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.54     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.36/0.54         ( m1_subset_1 @
% 0.36/0.54           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.36/0.54       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.36/0.54  thf(zf_stmt_1, negated_conjecture,
% 0.36/0.54    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.54        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.36/0.54            ( m1_subset_1 @
% 0.36/0.54              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.36/0.54          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.36/0.54    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.36/0.54  thf('1', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.36/0.54  thf('2', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_D @ 
% 0.36/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.36/0.54  thf(t7_funct_2, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.54     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.36/0.54         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.54       ( ( r2_hidden @ C @ A ) =>
% 0.36/0.54         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.36/0.54           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.36/0.54  thf('3', plain,
% 0.36/0.54      (![X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X59 @ X60)
% 0.36/0.54          | ((X61) = (k1_xboole_0))
% 0.36/0.54          | ~ (v1_funct_1 @ X62)
% 0.36/0.54          | ~ (v1_funct_2 @ X62 @ X60 @ X61)
% 0.36/0.54          | ~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X61)))
% 0.36/0.54          | (r2_hidden @ (k1_funct_1 @ X62 @ X59) @ X61))),
% 0.36/0.54      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.36/0.54  thf('4', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.36/0.54          | ~ (v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))
% 0.36/0.54          | ~ (v1_funct_1 @ sk_D)
% 0.36/0.54          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.36/0.54          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.54  thf('5', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.36/0.54  thf('6', plain, ((v1_funct_1 @ sk_D)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.36/0.54  thf('7', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.36/0.54          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.36/0.54          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.36/0.54  thf(t20_zfmisc_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.36/0.54         ( k1_tarski @ A ) ) <=>
% 0.36/0.54       ( ( A ) != ( B ) ) ))).
% 0.36/0.54  thf('8', plain,
% 0.36/0.54      (![X31 : $i, X32 : $i]:
% 0.36/0.54         (((X32) != (X31))
% 0.36/0.54          | ((k4_xboole_0 @ (k1_tarski @ X32) @ (k1_tarski @ X31))
% 0.36/0.54              != (k1_tarski @ X32)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.36/0.54  thf('9', plain,
% 0.36/0.54      (![X31 : $i]:
% 0.36/0.54         ((k4_xboole_0 @ (k1_tarski @ X31) @ (k1_tarski @ X31))
% 0.36/0.54           != (k1_tarski @ X31))),
% 0.36/0.54      inference('simplify', [status(thm)], ['8'])).
% 0.36/0.54  thf(t69_enumset1, axiom,
% 0.36/0.54    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.36/0.54  thf('10', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.36/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.55  thf(t11_setfam_1, axiom,
% 0.36/0.55    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.36/0.55  thf('11', plain, (![X56 : $i]: ((k1_setfam_1 @ (k1_tarski @ X56)) = (X56))),
% 0.36/0.55      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.36/0.55  thf('12', plain,
% 0.36/0.55      (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.36/0.55      inference('sup+', [status(thm)], ['10', '11'])).
% 0.36/0.55  thf(t12_setfam_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.36/0.55  thf('13', plain,
% 0.36/0.55      (![X57 : $i, X58 : $i]:
% 0.36/0.55         ((k1_setfam_1 @ (k2_tarski @ X57 @ X58)) = (k3_xboole_0 @ X57 @ X58))),
% 0.36/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.36/0.55  thf('14', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.36/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.36/0.55  thf(t100_xboole_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.36/0.55  thf('15', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((k4_xboole_0 @ X0 @ X1)
% 0.36/0.55           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.55  thf('16', plain,
% 0.36/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.36/0.55      inference('sup+', [status(thm)], ['14', '15'])).
% 0.36/0.55  thf(t92_xboole_1, axiom,
% 0.36/0.55    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.36/0.55  thf('17', plain, (![X2 : $i]: ((k5_xboole_0 @ X2 @ X2) = (k1_xboole_0))),
% 0.36/0.55      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.36/0.55  thf('18', plain, (![X31 : $i]: ((k1_xboole_0) != (k1_tarski @ X31))),
% 0.36/0.55      inference('demod', [status(thm)], ['9', '16', '17'])).
% 0.36/0.55  thf('19', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X0 @ sk_A)
% 0.36/0.55          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B)))),
% 0.36/0.55      inference('clc', [status(thm)], ['7', '18'])).
% 0.36/0.55  thf('20', plain,
% 0.36/0.55      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ (k1_tarski @ sk_B))),
% 0.36/0.55      inference('sup-', [status(thm)], ['1', '19'])).
% 0.36/0.55  thf(t70_enumset1, axiom,
% 0.36/0.55    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.36/0.55  thf('21', plain,
% 0.36/0.55      (![X4 : $i, X5 : $i]:
% 0.36/0.55         ((k1_enumset1 @ X4 @ X4 @ X5) = (k2_tarski @ X4 @ X5))),
% 0.36/0.55      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.36/0.55  thf('22', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.36/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.55  thf('23', plain,
% 0.36/0.55      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.36/0.55      inference('sup+', [status(thm)], ['21', '22'])).
% 0.36/0.55  thf(t71_enumset1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.36/0.55  thf('24', plain,
% 0.36/0.55      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.55         ((k2_enumset1 @ X6 @ X6 @ X7 @ X8) = (k1_enumset1 @ X6 @ X7 @ X8))),
% 0.36/0.55      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.36/0.55  thf(t72_enumset1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.55     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.36/0.55  thf('25', plain,
% 0.36/0.55      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.55         ((k3_enumset1 @ X9 @ X9 @ X10 @ X11 @ X12)
% 0.36/0.55           = (k2_enumset1 @ X9 @ X10 @ X11 @ X12))),
% 0.36/0.55      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.36/0.55  thf(t73_enumset1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.36/0.55     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.36/0.55       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.36/0.55  thf('26', plain,
% 0.36/0.55      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.36/0.55         ((k4_enumset1 @ X13 @ X13 @ X14 @ X15 @ X16 @ X17)
% 0.36/0.55           = (k3_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17))),
% 0.36/0.55      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.36/0.55  thf(t74_enumset1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.36/0.55     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.36/0.55       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.36/0.55  thf('27', plain,
% 0.36/0.55      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.36/0.55         ((k5_enumset1 @ X18 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23)
% 0.36/0.55           = (k4_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23))),
% 0.36/0.55      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.36/0.55  thf(t75_enumset1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.36/0.55     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.36/0.55       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.36/0.55  thf('28', plain,
% 0.36/0.55      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.36/0.55         ((k6_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30)
% 0.36/0.55           = (k5_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30))),
% 0.36/0.55      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.36/0.55  thf(zf_stmt_2, type, zip_tseitin_0 :
% 0.36/0.55      $i > $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 0.36/0.55  thf(zf_stmt_3, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.36/0.55     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 0.36/0.55       ( ![J:$i]:
% 0.36/0.55         ( ( r2_hidden @ J @ I ) <=>
% 0.36/0.55           ( ~( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.36/0.55  thf('29', plain,
% 0.36/0.55      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, 
% 0.36/0.55         X52 : $i, X53 : $i, X54 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X54 @ X53)
% 0.36/0.55          | ~ (zip_tseitin_0 @ X54 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ 
% 0.36/0.55               X52)
% 0.36/0.55          | ((X53)
% 0.36/0.55              != (k6_enumset1 @ X52 @ X51 @ X50 @ X49 @ X48 @ X47 @ X46 @ X45)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.36/0.55  thf('30', plain,
% 0.36/0.55      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, 
% 0.36/0.55         X52 : $i, X54 : $i]:
% 0.36/0.55         (~ (zip_tseitin_0 @ X54 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ 
% 0.36/0.55             X52)
% 0.36/0.55          | ~ (r2_hidden @ X54 @ 
% 0.36/0.55               (k6_enumset1 @ X52 @ X51 @ X50 @ X49 @ X48 @ X47 @ X46 @ X45)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['29'])).
% 0.36/0.55  thf('31', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X7 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.36/0.55          | ~ (zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6))),
% 0.36/0.55      inference('sup-', [status(thm)], ['28', '30'])).
% 0.36/0.55  thf('32', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X6 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.36/0.55          | ~ (zip_tseitin_0 @ X6 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X5 @ X5))),
% 0.36/0.55      inference('sup-', [status(thm)], ['27', '31'])).
% 0.36/0.55  thf('33', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X5 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.36/0.55          | ~ (zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 @ X4 @ X4))),
% 0.36/0.55      inference('sup-', [status(thm)], ['26', '32'])).
% 0.36/0.55  thf('34', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X4 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.36/0.55          | ~ (zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 @ X3 @ X3 @ X3))),
% 0.36/0.55      inference('sup-', [status(thm)], ['25', '33'])).
% 0.36/0.55  thf('35', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.36/0.55          | ~ (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2 @ X2 @ X2 @ X2))),
% 0.36/0.55      inference('sup-', [status(thm)], ['24', '34'])).
% 0.36/0.55  thf('36', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.36/0.55          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['23', '35'])).
% 0.36/0.55  thf('37', plain,
% 0.36/0.55      (~ (zip_tseitin_0 @ (k1_funct_1 @ sk_D @ sk_C) @ sk_B @ sk_B @ sk_B @ 
% 0.36/0.55          sk_B @ sk_B @ sk_B @ sk_B @ sk_B)),
% 0.36/0.55      inference('sup-', [status(thm)], ['20', '36'])).
% 0.36/0.55  thf('38', plain,
% 0.36/0.55      ((((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.36/0.55        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.36/0.55        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.36/0.55        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.36/0.55        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.36/0.55        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.36/0.55        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.36/0.55        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['0', '37'])).
% 0.36/0.55  thf('39', plain, (((k1_funct_1 @ sk_D @ sk_C) = (sk_B))),
% 0.36/0.55      inference('simplify', [status(thm)], ['38'])).
% 0.36/0.55  thf('40', plain, (((k1_funct_1 @ sk_D @ sk_C) != (sk_B))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.36/0.55  thf('41', plain, ($false),
% 0.36/0.55      inference('simplify_reflect-', [status(thm)], ['39', '40'])).
% 0.36/0.55  
% 0.36/0.55  % SZS output end Refutation
% 0.36/0.55  
% 0.36/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
