%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MJcQfN3oUF

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:47 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 155 expanded)
%              Number of leaves         :   52 (  70 expanded)
%              Depth                    :   17
%              Number of atoms          :  876 (1735 expanded)
%              Number of equality atoms :   74 ( 136 expanded)
%              Maximal formula depth    :   23 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('0',plain,(
    ! [X54: $i] :
      ( ( ( k7_relat_1 @ X54 @ ( k1_relat_1 @ X54 ) )
        = X54 )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf(t62_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
          = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
            = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_funct_2])).

thf('1',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('3',plain,(
    ! [X60: $i,X61: $i,X62: $i] :
      ( ( ( k2_relset_1 @ X61 @ X62 @ X60 )
        = ( k2_relat_1 @ X60 ) )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X61 @ X62 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('4',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','4'])).

thf('6',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('7',plain,(
    ! [X65: $i,X66: $i,X67: $i] :
      ( ~ ( v1_funct_2 @ X67 @ X65 @ X66 )
      | ( X65
        = ( k1_relset_1 @ X65 @ X66 @ X67 ) )
      | ~ ( zip_tseitin_2 @ X67 @ X66 @ X65 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('8',plain,
    ( ~ ( zip_tseitin_2 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf('9',plain,(
    ! [X63: $i,X64: $i] :
      ( ( zip_tseitin_1 @ X63 @ X64 )
      | ( X63 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_1 @ B @ A )
         => ( zip_tseitin_2 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X68: $i,X69: $i,X70: $i] :
      ( ~ ( zip_tseitin_1 @ X68 @ X69 )
      | ( zip_tseitin_2 @ X70 @ X68 @ X69 )
      | ~ ( m1_subset_1 @ X70 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X69 @ X68 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('12',plain,
    ( ( zip_tseitin_2 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    zip_tseitin_2 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('17',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( ( k1_relset_1 @ X58 @ X59 @ X57 )
        = ( k1_relat_1 @ X57 ) )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X59 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('18',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['8','15','18'])).

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

thf(zf_stmt_6,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_7,axiom,(
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

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( I
        = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) )
    <=> ! [J: $i] :
          ( ( r2_hidden @ J @ I )
        <=> ~ ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 )
      | ( r2_hidden @ X38 @ X47 )
      | ( X47
       != ( k6_enumset1 @ X46 @ X45 @ X44 @ X43 @ X42 @ X41 @ X40 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('28',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( r2_hidden @ X38 @ ( k6_enumset1 @ X46 @ X45 @ X44 @ X43 @ X42 @ X41 @ X40 @ X39 ) )
      | ( zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6 ) ) ),
    inference('sup+',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( X29 != X28 )
      | ~ ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('31',plain,(
    ! [X28: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ~ ( zip_tseitin_0 @ X28 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X28 ) ),
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
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','37'])).

thf('39',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['19','38'])).

thf(t168_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('40',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( r2_hidden @ X55 @ ( k1_relat_1 @ X56 ) )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X56 @ ( k1_tarski @ X55 ) ) )
        = ( k1_tarski @ ( k1_funct_1 @ X56 @ X55 ) ) )
      | ~ ( v1_funct_1 @ X56 )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t168_funct_1])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('43',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X51 ) )
      | ( v1_relat_1 @ X50 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('45',plain,(
    ! [X52: $i,X53: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('46',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['8','15','18'])).

thf('49',plain,
    ( ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
    = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','46','47','48'])).

thf('50',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['5','49'])).

thf('51',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['44','45'])).

thf('53',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    $false ),
    inference(simplify,[status(thm)],['53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MJcQfN3oUF
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:55:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.45/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.71  % Solved by: fo/fo7.sh
% 0.45/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.71  % done 154 iterations in 0.257s
% 0.45/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.71  % SZS output start Refutation
% 0.45/0.71  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.45/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.71  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.71  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.45/0.71  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.71  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 0.45/0.71                                               $i > $i > $i > $o).
% 0.45/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.71  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.45/0.71  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.45/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.71  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.45/0.71  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.45/0.71  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.71  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.45/0.71                                           $i > $i).
% 0.45/0.71  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.71  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.71  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.45/0.71  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.45/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.71  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.71  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.71  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.45/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.71  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.45/0.71  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.45/0.71  thf(t98_relat_1, axiom,
% 0.45/0.71    (![A:$i]:
% 0.45/0.71     ( ( v1_relat_1 @ A ) =>
% 0.45/0.71       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.45/0.71  thf('0', plain,
% 0.45/0.71      (![X54 : $i]:
% 0.45/0.71         (((k7_relat_1 @ X54 @ (k1_relat_1 @ X54)) = (X54))
% 0.45/0.71          | ~ (v1_relat_1 @ X54))),
% 0.45/0.71      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.45/0.71  thf(t62_funct_2, conjecture,
% 0.45/0.71    (![A:$i,B:$i,C:$i]:
% 0.45/0.71     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.45/0.71         ( m1_subset_1 @
% 0.45/0.71           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.45/0.71       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.45/0.71         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.45/0.71           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.45/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.71    (~( ![A:$i,B:$i,C:$i]:
% 0.45/0.71        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.45/0.71            ( m1_subset_1 @
% 0.45/0.71              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.45/0.71          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.45/0.71            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.45/0.71              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.45/0.71    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.45/0.71  thf('1', plain,
% 0.45/0.71      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)
% 0.45/0.71         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('2', plain,
% 0.45/0.71      ((m1_subset_1 @ sk_C @ 
% 0.45/0.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf(redefinition_k2_relset_1, axiom,
% 0.45/0.71    (![A:$i,B:$i,C:$i]:
% 0.45/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.71       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.45/0.71  thf('3', plain,
% 0.45/0.71      (![X60 : $i, X61 : $i, X62 : $i]:
% 0.45/0.71         (((k2_relset_1 @ X61 @ X62 @ X60) = (k2_relat_1 @ X60))
% 0.45/0.71          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X61 @ X62))))),
% 0.45/0.71      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.71  thf('4', plain,
% 0.45/0.71      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.45/0.71      inference('sup-', [status(thm)], ['2', '3'])).
% 0.45/0.71  thf('5', plain,
% 0.45/0.71      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.45/0.71      inference('demod', [status(thm)], ['1', '4'])).
% 0.45/0.71  thf('6', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B)),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf(d1_funct_2, axiom,
% 0.45/0.71    (![A:$i,B:$i,C:$i]:
% 0.45/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.71       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.71           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.45/0.71             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.45/0.71         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.71           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.45/0.71             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.45/0.71  thf(zf_stmt_1, axiom,
% 0.45/0.71    (![C:$i,B:$i,A:$i]:
% 0.45/0.71     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.45/0.71       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.45/0.71  thf('7', plain,
% 0.45/0.71      (![X65 : $i, X66 : $i, X67 : $i]:
% 0.45/0.71         (~ (v1_funct_2 @ X67 @ X65 @ X66)
% 0.45/0.71          | ((X65) = (k1_relset_1 @ X65 @ X66 @ X67))
% 0.45/0.71          | ~ (zip_tseitin_2 @ X67 @ X66 @ X65))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.71  thf('8', plain,
% 0.45/0.71      ((~ (zip_tseitin_2 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.45/0.71        | ((k1_tarski @ sk_A)
% 0.45/0.71            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)))),
% 0.45/0.71      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.71  thf(zf_stmt_2, axiom,
% 0.45/0.71    (![B:$i,A:$i]:
% 0.45/0.71     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.71       ( zip_tseitin_1 @ B @ A ) ))).
% 0.45/0.71  thf('9', plain,
% 0.45/0.71      (![X63 : $i, X64 : $i]:
% 0.45/0.71         ((zip_tseitin_1 @ X63 @ X64) | ((X63) = (k1_xboole_0)))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.71  thf('10', plain,
% 0.45/0.71      ((m1_subset_1 @ sk_C @ 
% 0.45/0.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.45/0.71  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $o).
% 0.45/0.71  thf(zf_stmt_5, axiom,
% 0.45/0.71    (![A:$i,B:$i,C:$i]:
% 0.45/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.71       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.45/0.71         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.71           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.45/0.71             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.45/0.71  thf('11', plain,
% 0.45/0.71      (![X68 : $i, X69 : $i, X70 : $i]:
% 0.45/0.71         (~ (zip_tseitin_1 @ X68 @ X69)
% 0.45/0.71          | (zip_tseitin_2 @ X70 @ X68 @ X69)
% 0.45/0.71          | ~ (m1_subset_1 @ X70 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X69 @ X68))))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.45/0.71  thf('12', plain,
% 0.45/0.71      (((zip_tseitin_2 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.45/0.71        | ~ (zip_tseitin_1 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.45/0.71      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.71  thf('13', plain,
% 0.45/0.71      ((((sk_B) = (k1_xboole_0))
% 0.45/0.71        | (zip_tseitin_2 @ sk_C @ sk_B @ (k1_tarski @ sk_A)))),
% 0.45/0.71      inference('sup-', [status(thm)], ['9', '12'])).
% 0.45/0.71  thf('14', plain, (((sk_B) != (k1_xboole_0))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('15', plain, ((zip_tseitin_2 @ sk_C @ sk_B @ (k1_tarski @ sk_A))),
% 0.45/0.71      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.45/0.71  thf('16', plain,
% 0.45/0.71      ((m1_subset_1 @ sk_C @ 
% 0.45/0.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf(redefinition_k1_relset_1, axiom,
% 0.45/0.71    (![A:$i,B:$i,C:$i]:
% 0.45/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.71       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.45/0.71  thf('17', plain,
% 0.45/0.71      (![X57 : $i, X58 : $i, X59 : $i]:
% 0.45/0.71         (((k1_relset_1 @ X58 @ X59 @ X57) = (k1_relat_1 @ X57))
% 0.45/0.71          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X59))))),
% 0.45/0.71      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.45/0.71  thf('18', plain,
% 0.45/0.71      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.45/0.71      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.71  thf('19', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.45/0.71      inference('demod', [status(thm)], ['8', '15', '18'])).
% 0.45/0.71  thf(t69_enumset1, axiom,
% 0.45/0.71    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.45/0.71  thf('20', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.45/0.71      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.71  thf(t70_enumset1, axiom,
% 0.45/0.71    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.45/0.71  thf('21', plain,
% 0.45/0.71      (![X1 : $i, X2 : $i]:
% 0.45/0.71         ((k1_enumset1 @ X1 @ X1 @ X2) = (k2_tarski @ X1 @ X2))),
% 0.45/0.71      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.45/0.71  thf(t71_enumset1, axiom,
% 0.45/0.71    (![A:$i,B:$i,C:$i]:
% 0.45/0.71     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.45/0.71  thf('22', plain,
% 0.45/0.71      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.45/0.71         ((k2_enumset1 @ X3 @ X3 @ X4 @ X5) = (k1_enumset1 @ X3 @ X4 @ X5))),
% 0.45/0.71      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.45/0.71  thf(t72_enumset1, axiom,
% 0.45/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.71     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.45/0.71  thf('23', plain,
% 0.45/0.71      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.45/0.71         ((k3_enumset1 @ X6 @ X6 @ X7 @ X8 @ X9)
% 0.45/0.71           = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 0.45/0.71      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.45/0.71  thf(t73_enumset1, axiom,
% 0.45/0.71    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.45/0.71     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.45/0.71       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.45/0.71  thf('24', plain,
% 0.45/0.71      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.45/0.71         ((k4_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 @ X14)
% 0.45/0.71           = (k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14))),
% 0.45/0.71      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.45/0.71  thf(t74_enumset1, axiom,
% 0.45/0.71    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.45/0.71     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.45/0.71       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.45/0.71  thf('25', plain,
% 0.45/0.71      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.71         ((k5_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20)
% 0.45/0.71           = (k4_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20))),
% 0.45/0.71      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.45/0.71  thf(t75_enumset1, axiom,
% 0.45/0.71    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.45/0.71     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.45/0.71       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.45/0.71  thf('26', plain,
% 0.45/0.71      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.45/0.71         ((k6_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27)
% 0.45/0.71           = (k5_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27))),
% 0.45/0.71      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.45/0.71  thf(d6_enumset1, axiom,
% 0.45/0.71    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.45/0.71     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 0.45/0.71       ( ![J:$i]:
% 0.45/0.71         ( ( r2_hidden @ J @ I ) <=>
% 0.45/0.71           ( ~( ( ( J ) != ( H ) ) & ( ( J ) != ( G ) ) & ( ( J ) != ( F ) ) & 
% 0.45/0.71                ( ( J ) != ( E ) ) & ( ( J ) != ( D ) ) & ( ( J ) != ( C ) ) & 
% 0.45/0.71                ( ( J ) != ( B ) ) & ( ( J ) != ( A ) ) ) ) ) ) ))).
% 0.45/0.71  thf(zf_stmt_6, type, zip_tseitin_0 :
% 0.45/0.71      $i > $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 0.45/0.71  thf(zf_stmt_7, axiom,
% 0.45/0.71    (![J:$i,H:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.45/0.71     ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) <=>
% 0.45/0.71       ( ( ( J ) != ( A ) ) & ( ( J ) != ( B ) ) & ( ( J ) != ( C ) ) & 
% 0.45/0.71         ( ( J ) != ( D ) ) & ( ( J ) != ( E ) ) & ( ( J ) != ( F ) ) & 
% 0.45/0.71         ( ( J ) != ( G ) ) & ( ( J ) != ( H ) ) ) ))).
% 0.45/0.71  thf(zf_stmt_8, axiom,
% 0.45/0.71    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.45/0.71     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 0.45/0.71       ( ![J:$i]:
% 0.45/0.71         ( ( r2_hidden @ J @ I ) <=>
% 0.45/0.71           ( ~( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.45/0.71  thf('27', plain,
% 0.45/0.71      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, 
% 0.45/0.71         X45 : $i, X46 : $i, X47 : $i]:
% 0.45/0.71         ((zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46)
% 0.45/0.71          | (r2_hidden @ X38 @ X47)
% 0.45/0.71          | ((X47)
% 0.45/0.71              != (k6_enumset1 @ X46 @ X45 @ X44 @ X43 @ X42 @ X41 @ X40 @ X39)))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.45/0.71  thf('28', plain,
% 0.45/0.71      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, 
% 0.45/0.71         X45 : $i, X46 : $i]:
% 0.45/0.71         ((r2_hidden @ X38 @ 
% 0.45/0.71           (k6_enumset1 @ X46 @ X45 @ X44 @ X43 @ X42 @ X41 @ X40 @ X39))
% 0.45/0.71          | (zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ 
% 0.45/0.71             X46))),
% 0.45/0.71      inference('simplify', [status(thm)], ['27'])).
% 0.45/0.71  thf('29', plain,
% 0.45/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.71         ((r2_hidden @ X7 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.45/0.71          | (zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6))),
% 0.45/0.71      inference('sup+', [status(thm)], ['26', '28'])).
% 0.45/0.71  thf('30', plain,
% 0.45/0.71      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, 
% 0.45/0.71         X35 : $i, X36 : $i]:
% 0.45/0.71         (((X29) != (X28))
% 0.45/0.71          | ~ (zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ 
% 0.45/0.71               X28))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.45/0.71  thf('31', plain,
% 0.45/0.71      (![X28 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, 
% 0.45/0.71         X36 : $i]:
% 0.45/0.71         ~ (zip_tseitin_0 @ X28 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X28)),
% 0.45/0.71      inference('simplify', [status(thm)], ['30'])).
% 0.45/0.71  thf('32', plain,
% 0.45/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.45/0.71         (r2_hidden @ X0 @ (k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6))),
% 0.45/0.71      inference('sup-', [status(thm)], ['29', '31'])).
% 0.45/0.71  thf('33', plain,
% 0.45/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.45/0.71         (r2_hidden @ X5 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.45/0.71      inference('sup+', [status(thm)], ['25', '32'])).
% 0.45/0.71  thf('34', plain,
% 0.45/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.45/0.71         (r2_hidden @ X4 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.45/0.71      inference('sup+', [status(thm)], ['24', '33'])).
% 0.45/0.71  thf('35', plain,
% 0.45/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.71         (r2_hidden @ X3 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.45/0.71      inference('sup+', [status(thm)], ['23', '34'])).
% 0.45/0.71  thf('36', plain,
% 0.45/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.71         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.45/0.71      inference('sup+', [status(thm)], ['22', '35'])).
% 0.45/0.71  thf('37', plain,
% 0.45/0.71      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.45/0.71      inference('sup+', [status(thm)], ['21', '36'])).
% 0.45/0.71  thf('38', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.45/0.71      inference('sup+', [status(thm)], ['20', '37'])).
% 0.45/0.71  thf('39', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.45/0.71      inference('sup+', [status(thm)], ['19', '38'])).
% 0.45/0.71  thf(t168_funct_1, axiom,
% 0.45/0.71    (![A:$i,B:$i]:
% 0.45/0.71     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.45/0.71       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.45/0.71         ( ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) =
% 0.45/0.71           ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.45/0.71  thf('40', plain,
% 0.45/0.71      (![X55 : $i, X56 : $i]:
% 0.45/0.71         (~ (r2_hidden @ X55 @ (k1_relat_1 @ X56))
% 0.45/0.71          | ((k2_relat_1 @ (k7_relat_1 @ X56 @ (k1_tarski @ X55)))
% 0.45/0.71              = (k1_tarski @ (k1_funct_1 @ X56 @ X55)))
% 0.45/0.71          | ~ (v1_funct_1 @ X56)
% 0.45/0.71          | ~ (v1_relat_1 @ X56))),
% 0.45/0.71      inference('cnf', [status(esa)], [t168_funct_1])).
% 0.45/0.71  thf('41', plain,
% 0.45/0.71      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.71        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.71        | ((k2_relat_1 @ (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)))
% 0.45/0.71            = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A))))),
% 0.45/0.71      inference('sup-', [status(thm)], ['39', '40'])).
% 0.45/0.71  thf('42', plain,
% 0.45/0.71      ((m1_subset_1 @ sk_C @ 
% 0.45/0.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf(cc2_relat_1, axiom,
% 0.45/0.71    (![A:$i]:
% 0.45/0.71     ( ( v1_relat_1 @ A ) =>
% 0.45/0.71       ( ![B:$i]:
% 0.45/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.45/0.71  thf('43', plain,
% 0.45/0.71      (![X50 : $i, X51 : $i]:
% 0.45/0.71         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X51))
% 0.45/0.71          | (v1_relat_1 @ X50)
% 0.45/0.71          | ~ (v1_relat_1 @ X51))),
% 0.45/0.71      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.45/0.71  thf('44', plain,
% 0.45/0.71      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.45/0.71        | (v1_relat_1 @ sk_C))),
% 0.45/0.71      inference('sup-', [status(thm)], ['42', '43'])).
% 0.45/0.71  thf(fc6_relat_1, axiom,
% 0.45/0.71    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.45/0.71  thf('45', plain,
% 0.45/0.71      (![X52 : $i, X53 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X52 @ X53))),
% 0.45/0.71      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.45/0.71  thf('46', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.71      inference('demod', [status(thm)], ['44', '45'])).
% 0.45/0.71  thf('47', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('48', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.45/0.71      inference('demod', [status(thm)], ['8', '15', '18'])).
% 0.45/0.71  thf('49', plain,
% 0.45/0.71      (((k2_relat_1 @ (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))
% 0.45/0.71         = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.45/0.71      inference('demod', [status(thm)], ['41', '46', '47', '48'])).
% 0.45/0.71  thf('50', plain,
% 0.45/0.71      (((k2_relat_1 @ sk_C)
% 0.45/0.71         != (k2_relat_1 @ (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))))),
% 0.45/0.71      inference('demod', [status(thm)], ['5', '49'])).
% 0.45/0.71  thf('51', plain,
% 0.45/0.71      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)) | ~ (v1_relat_1 @ sk_C))),
% 0.45/0.71      inference('sup-', [status(thm)], ['0', '50'])).
% 0.45/0.71  thf('52', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.71      inference('demod', [status(thm)], ['44', '45'])).
% 0.45/0.71  thf('53', plain, (((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))),
% 0.45/0.71      inference('demod', [status(thm)], ['51', '52'])).
% 0.45/0.71  thf('54', plain, ($false), inference('simplify', [status(thm)], ['53'])).
% 0.45/0.71  
% 0.45/0.71  % SZS output end Refutation
% 0.45/0.71  
% 0.45/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
