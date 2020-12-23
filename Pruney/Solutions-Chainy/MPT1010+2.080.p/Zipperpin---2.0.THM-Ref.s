%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QbmtodM8kb

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:24 EST 2020

% Result     : Theorem 20.74s
% Output     : Refutation 20.74s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 190 expanded)
%              Number of leaves         :   56 (  81 expanded)
%              Depth                    :   20
%              Number of atoms          : 1145 (2064 expanded)
%              Number of equality atoms :  110 ( 165 expanded)
%              Maximal formula depth    :   23 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(t65_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( k1_funct_1 @ D @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ D @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k1_enumset1 @ X4 @ X4 @ X5 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k2_enumset1 @ X6 @ X6 @ X7 @ X8 )
      = ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k3_enumset1 @ X9 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_enumset1 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k4_enumset1 @ X13 @ X13 @ X14 @ X15 @ X16 @ X17 )
      = ( k3_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k5_enumset1 @ X18 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 )
      = ( k4_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('7',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k6_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 )
      = ( k5_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 ) ) ),
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

thf('8',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( zip_tseitin_0 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 )
      | ( r2_hidden @ X44 @ X53 )
      | ( X53
       != ( k6_enumset1 @ X52 @ X51 @ X50 @ X49 @ X48 @ X47 @ X46 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('9',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ( r2_hidden @ X44 @ ( k6_enumset1 @ X52 @ X51 @ X50 @ X49 @ X48 @ X47 @ X46 @ X45 ) )
      | ( zip_tseitin_0 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6 ) ) ),
    inference('sup+',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( X35 != X34 )
      | ~ ( zip_tseitin_0 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('12',plain,(
    ! [X34: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ~ ( zip_tseitin_0 @ X34 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X34 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( r2_hidden @ X0 @ ( k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( r2_hidden @ X5 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X4 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','14'])).

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

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf('16',plain,(
    ! [X74: $i,X75: $i] :
      ( ( zip_tseitin_1 @ X74 @ X75 )
      | ( X74 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_5,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_7,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_1 @ B @ A )
         => ( zip_tseitin_2 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('18',plain,(
    ! [X79: $i,X80: $i,X81: $i] :
      ( ~ ( zip_tseitin_1 @ X79 @ X80 )
      | ( zip_tseitin_2 @ X81 @ X79 @ X80 )
      | ~ ( m1_subset_1 @ X81 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X80 @ X79 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('19',plain,
    ( ( zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_1 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X76: $i,X77: $i,X78: $i] :
      ( ~ ( v1_funct_2 @ X78 @ X76 @ X77 )
      | ( X76
        = ( k1_relset_1 @ X76 @ X77 @ X78 ) )
      | ~ ( zip_tseitin_2 @ X78 @ X77 @ X76 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('23',plain,
    ( ~ ( zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('25',plain,(
    ! [X65: $i,X66: $i,X67: $i] :
      ( ( ( k1_relset_1 @ X66 @ X67 @ X65 )
        = ( k1_relat_1 @ X65 ) )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X66 @ X67 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('26',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['20','27'])).

thf('29',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['20','27'])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('30',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X31 @ X32 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X31 ) @ X32 )
       != ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
       != ( k1_tarski @ sk_B ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_xboole_0 @ k1_xboole_0 @ ( k3_enumset1 @ sk_B @ X3 @ X2 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['15','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ k1_xboole_0 @ ( k2_enumset1 @ sk_B @ X2 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['4','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ k1_xboole_0 @ ( k1_enumset1 @ sk_B @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['3','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_B @ X0 ) )
       != k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['2','36'])).

thf('38',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_B ) )
     != k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','37'])).

thf('39',plain,(
    ! [X74: $i,X75: $i] :
      ( ( zip_tseitin_1 @ X74 @ X75 )
      | ( X74 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('40',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = X1 )
      | ( zip_tseitin_1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_1 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_B ) )
        = X0 )
      | ( zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_B ) )
        = X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['38','45'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('47',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ~ ( r2_hidden @ X59 @ ( k1_relat_1 @ X60 ) )
      | ( X61
       != ( k1_funct_1 @ X60 @ X59 ) )
      | ( r2_hidden @ ( k4_tarski @ X59 @ X61 ) @ X60 )
      | ~ ( v1_funct_1 @ X60 )
      | ~ ( v1_relat_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('48',plain,(
    ! [X59: $i,X60: $i] :
      ( ~ ( v1_relat_1 @ X60 )
      | ~ ( v1_funct_1 @ X60 )
      | ( r2_hidden @ ( k4_tarski @ X59 @ ( k1_funct_1 @ X60 @ X59 ) ) @ X60 )
      | ~ ( r2_hidden @ X59 @ ( k1_relat_1 @ X60 ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_D @ X0 ) ) @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('52',plain,(
    ! [X62: $i,X63: $i,X64: $i] :
      ( ( v1_relat_1 @ X62 )
      | ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X63 @ X64 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('53',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_D @ X0 ) ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['49','50','53'])).

thf('55',plain,(
    r2_hidden @ ( k4_tarski @ sk_C @ ( k1_funct_1 @ sk_D @ sk_C ) ) @ sk_D ),
    inference('sup-',[status(thm)],['0','54'])).

thf('56',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('57',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('58',plain,(
    ! [X31: $i,X33: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X31 ) @ X33 )
        = ( k1_tarski @ X31 ) )
      | ( r2_hidden @ X31 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('61',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ~ ( r2_hidden @ X56 @ X57 )
      | ( r2_hidden @ X56 @ X58 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ sk_D )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ sk_D )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['56','63'])).

thf(t13_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( ( k2_mcart_1 @ A )
          = C ) ) ) )).

thf('65',plain,(
    ! [X68: $i,X69: $i,X70: $i] :
      ( ( ( k2_mcart_1 @ X68 )
        = X70 )
      | ~ ( r2_hidden @ X68 @ ( k2_zfmisc_1 @ X69 @ ( k1_tarski @ X70 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_mcart_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ sk_D )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_mcart_1 @ X0 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X31 @ X32 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X31 ) @ X32 )
       != ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( ( k2_mcart_1 @ X0 )
        = sk_B )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_D )
      | ( ( k2_mcart_1 @ X0 )
        = sk_B ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( k2_mcart_1 @ ( k4_tarski @ sk_C @ ( k1_funct_1 @ sk_D @ sk_C ) ) )
    = sk_B ),
    inference('sup-',[status(thm)],['55','69'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('71',plain,(
    ! [X71: $i,X73: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X71 @ X73 ) )
      = X73 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('72',plain,
    ( ( k1_funct_1 @ sk_D @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ( k1_funct_1 @ sk_D @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['72','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QbmtodM8kb
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:27:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 20.74/20.99  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 20.74/20.99  % Solved by: fo/fo7.sh
% 20.74/20.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 20.74/20.99  % done 8836 iterations in 20.540s
% 20.74/20.99  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 20.74/20.99  % SZS output start Refutation
% 20.74/20.99  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 20.74/20.99  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 20.74/20.99  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 20.74/20.99  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 20.74/20.99  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 20.74/20.99  thf(sk_C_type, type, sk_C: $i).
% 20.74/20.99  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 20.74/20.99  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 20.74/20.99  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 20.74/20.99  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 20.74/20.99  thf(sk_B_type, type, sk_B: $i).
% 20.74/20.99  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 20.74/20.99  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 20.74/20.99  thf(sk_D_type, type, sk_D: $i).
% 20.74/20.99  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 20.74/20.99  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 20.74/20.99  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 20.74/20.99  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 20.74/20.99  thf(sk_A_type, type, sk_A: $i).
% 20.74/20.99  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 20.74/20.99  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 20.74/20.99  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 20.74/20.99  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 20.74/20.99  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 20.74/20.99  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 20.74/20.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 20.74/20.99  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 20.74/20.99  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 20.74/20.99                                           $i > $i).
% 20.74/20.99  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 20.74/20.99  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 20.74/20.99                                               $i > $i > $i > $o).
% 20.74/20.99  thf(t65_funct_2, conjecture,
% 20.74/20.99    (![A:$i,B:$i,C:$i,D:$i]:
% 20.74/20.99     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 20.74/20.99         ( m1_subset_1 @
% 20.74/20.99           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 20.74/20.99       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 20.74/20.99  thf(zf_stmt_0, negated_conjecture,
% 20.74/20.99    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 20.74/20.99        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 20.74/20.99            ( m1_subset_1 @
% 20.74/20.99              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 20.74/20.99          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 20.74/20.99    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 20.74/20.99  thf('0', plain, ((r2_hidden @ sk_C @ sk_A)),
% 20.74/20.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.74/20.99  thf(t69_enumset1, axiom,
% 20.74/20.99    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 20.74/20.99  thf('1', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 20.74/20.99      inference('cnf', [status(esa)], [t69_enumset1])).
% 20.74/20.99  thf(t70_enumset1, axiom,
% 20.74/20.99    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 20.74/20.99  thf('2', plain,
% 20.74/20.99      (![X4 : $i, X5 : $i]:
% 20.74/20.99         ((k1_enumset1 @ X4 @ X4 @ X5) = (k2_tarski @ X4 @ X5))),
% 20.74/20.99      inference('cnf', [status(esa)], [t70_enumset1])).
% 20.74/20.99  thf(t71_enumset1, axiom,
% 20.74/20.99    (![A:$i,B:$i,C:$i]:
% 20.74/20.99     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 20.74/20.99  thf('3', plain,
% 20.74/20.99      (![X6 : $i, X7 : $i, X8 : $i]:
% 20.74/20.99         ((k2_enumset1 @ X6 @ X6 @ X7 @ X8) = (k1_enumset1 @ X6 @ X7 @ X8))),
% 20.74/20.99      inference('cnf', [status(esa)], [t71_enumset1])).
% 20.74/20.99  thf(t72_enumset1, axiom,
% 20.74/20.99    (![A:$i,B:$i,C:$i,D:$i]:
% 20.74/20.99     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 20.74/20.99  thf('4', plain,
% 20.74/20.99      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 20.74/20.99         ((k3_enumset1 @ X9 @ X9 @ X10 @ X11 @ X12)
% 20.74/20.99           = (k2_enumset1 @ X9 @ X10 @ X11 @ X12))),
% 20.74/20.99      inference('cnf', [status(esa)], [t72_enumset1])).
% 20.74/20.99  thf(t73_enumset1, axiom,
% 20.74/20.99    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 20.74/20.99     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 20.74/20.99       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 20.74/20.99  thf('5', plain,
% 20.74/20.99      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 20.74/20.99         ((k4_enumset1 @ X13 @ X13 @ X14 @ X15 @ X16 @ X17)
% 20.74/20.99           = (k3_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17))),
% 20.74/20.99      inference('cnf', [status(esa)], [t73_enumset1])).
% 20.74/20.99  thf(t74_enumset1, axiom,
% 20.74/20.99    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 20.74/20.99     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 20.74/20.99       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 20.74/20.99  thf('6', plain,
% 20.74/20.99      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 20.74/20.99         ((k5_enumset1 @ X18 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23)
% 20.74/20.99           = (k4_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23))),
% 20.74/20.99      inference('cnf', [status(esa)], [t74_enumset1])).
% 20.74/20.99  thf(t75_enumset1, axiom,
% 20.74/20.99    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 20.74/20.99     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 20.74/20.99       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 20.74/20.99  thf('7', plain,
% 20.74/20.99      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 20.74/20.99         ((k6_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30)
% 20.74/20.99           = (k5_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30))),
% 20.74/20.99      inference('cnf', [status(esa)], [t75_enumset1])).
% 20.74/20.99  thf(d6_enumset1, axiom,
% 20.74/20.99    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 20.74/20.99     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 20.74/20.99       ( ![J:$i]:
% 20.74/20.99         ( ( r2_hidden @ J @ I ) <=>
% 20.74/20.99           ( ~( ( ( J ) != ( H ) ) & ( ( J ) != ( G ) ) & ( ( J ) != ( F ) ) & 
% 20.74/20.99                ( ( J ) != ( E ) ) & ( ( J ) != ( D ) ) & ( ( J ) != ( C ) ) & 
% 20.74/20.99                ( ( J ) != ( B ) ) & ( ( J ) != ( A ) ) ) ) ) ) ))).
% 20.74/20.99  thf(zf_stmt_1, type, zip_tseitin_0 :
% 20.74/20.99      $i > $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 20.74/20.99  thf(zf_stmt_2, axiom,
% 20.74/20.99    (![J:$i,H:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 20.74/20.99     ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) <=>
% 20.74/20.99       ( ( ( J ) != ( A ) ) & ( ( J ) != ( B ) ) & ( ( J ) != ( C ) ) & 
% 20.74/20.99         ( ( J ) != ( D ) ) & ( ( J ) != ( E ) ) & ( ( J ) != ( F ) ) & 
% 20.74/20.99         ( ( J ) != ( G ) ) & ( ( J ) != ( H ) ) ) ))).
% 20.74/20.99  thf(zf_stmt_3, axiom,
% 20.74/20.99    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 20.74/20.99     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 20.74/20.99       ( ![J:$i]:
% 20.74/20.99         ( ( r2_hidden @ J @ I ) <=>
% 20.74/20.99           ( ~( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 20.74/20.99  thf('8', plain,
% 20.74/20.99      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, 
% 20.74/20.99         X51 : $i, X52 : $i, X53 : $i]:
% 20.74/20.99         ((zip_tseitin_0 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52)
% 20.74/20.99          | (r2_hidden @ X44 @ X53)
% 20.74/20.99          | ((X53)
% 20.74/20.99              != (k6_enumset1 @ X52 @ X51 @ X50 @ X49 @ X48 @ X47 @ X46 @ X45)))),
% 20.74/20.99      inference('cnf', [status(esa)], [zf_stmt_3])).
% 20.74/20.99  thf('9', plain,
% 20.74/20.99      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, 
% 20.74/20.99         X51 : $i, X52 : $i]:
% 20.74/20.99         ((r2_hidden @ X44 @ 
% 20.74/20.99           (k6_enumset1 @ X52 @ X51 @ X50 @ X49 @ X48 @ X47 @ X46 @ X45))
% 20.74/20.99          | (zip_tseitin_0 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ 
% 20.74/20.99             X52))),
% 20.74/20.99      inference('simplify', [status(thm)], ['8'])).
% 20.74/20.99  thf('10', plain,
% 20.74/20.99      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 20.74/20.99         ((r2_hidden @ X7 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 20.74/20.99          | (zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6))),
% 20.74/20.99      inference('sup+', [status(thm)], ['7', '9'])).
% 20.74/20.99  thf('11', plain,
% 20.74/20.99      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, 
% 20.74/20.99         X41 : $i, X42 : $i]:
% 20.74/20.99         (((X35) != (X34))
% 20.74/20.99          | ~ (zip_tseitin_0 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ 
% 20.74/20.99               X34))),
% 20.74/20.99      inference('cnf', [status(esa)], [zf_stmt_2])).
% 20.74/20.99  thf('12', plain,
% 20.74/20.99      (![X34 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, 
% 20.74/20.99         X42 : $i]:
% 20.74/20.99         ~ (zip_tseitin_0 @ X34 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X34)),
% 20.74/20.99      inference('simplify', [status(thm)], ['11'])).
% 20.74/20.99  thf('13', plain,
% 20.74/20.99      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 20.74/20.99         (r2_hidden @ X0 @ (k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6))),
% 20.74/20.99      inference('sup-', [status(thm)], ['10', '12'])).
% 20.74/20.99  thf('14', plain,
% 20.74/20.99      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 20.74/20.99         (r2_hidden @ X5 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 20.74/20.99      inference('sup+', [status(thm)], ['6', '13'])).
% 20.74/20.99  thf('15', plain,
% 20.74/20.99      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 20.74/20.99         (r2_hidden @ X4 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 20.74/20.99      inference('sup+', [status(thm)], ['5', '14'])).
% 20.74/20.99  thf(d1_funct_2, axiom,
% 20.74/20.99    (![A:$i,B:$i,C:$i]:
% 20.74/20.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 20.74/20.99       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 20.74/20.99           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 20.74/20.99             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 20.74/20.99         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 20.74/20.99           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 20.74/20.99             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 20.74/20.99  thf(zf_stmt_4, axiom,
% 20.74/20.99    (![B:$i,A:$i]:
% 20.74/20.99     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 20.74/20.99       ( zip_tseitin_1 @ B @ A ) ))).
% 20.74/20.99  thf('16', plain,
% 20.74/20.99      (![X74 : $i, X75 : $i]:
% 20.74/20.99         ((zip_tseitin_1 @ X74 @ X75) | ((X74) = (k1_xboole_0)))),
% 20.74/20.99      inference('cnf', [status(esa)], [zf_stmt_4])).
% 20.74/20.99  thf('17', plain,
% 20.74/20.99      ((m1_subset_1 @ sk_D @ 
% 20.74/20.99        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 20.74/20.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.74/20.99  thf(zf_stmt_5, type, zip_tseitin_2 : $i > $i > $i > $o).
% 20.74/20.99  thf(zf_stmt_6, axiom,
% 20.74/20.99    (![C:$i,B:$i,A:$i]:
% 20.74/20.99     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 20.74/20.99       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 20.74/20.99  thf(zf_stmt_7, type, zip_tseitin_1 : $i > $i > $o).
% 20.74/20.99  thf(zf_stmt_8, axiom,
% 20.74/20.99    (![A:$i,B:$i,C:$i]:
% 20.74/20.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 20.74/20.99       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 20.74/20.99         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 20.74/20.99           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 20.74/20.99             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 20.74/20.99  thf('18', plain,
% 20.74/20.99      (![X79 : $i, X80 : $i, X81 : $i]:
% 20.74/20.99         (~ (zip_tseitin_1 @ X79 @ X80)
% 20.74/20.99          | (zip_tseitin_2 @ X81 @ X79 @ X80)
% 20.74/20.99          | ~ (m1_subset_1 @ X81 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X80 @ X79))))),
% 20.74/20.99      inference('cnf', [status(esa)], [zf_stmt_8])).
% 20.74/20.99  thf('19', plain,
% 20.74/20.99      (((zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 20.74/20.99        | ~ (zip_tseitin_1 @ (k1_tarski @ sk_B) @ sk_A))),
% 20.74/20.99      inference('sup-', [status(thm)], ['17', '18'])).
% 20.74/20.99  thf('20', plain,
% 20.74/20.99      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 20.74/20.99        | (zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A))),
% 20.74/20.99      inference('sup-', [status(thm)], ['16', '19'])).
% 20.74/20.99  thf('21', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 20.74/20.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.74/20.99  thf('22', plain,
% 20.74/20.99      (![X76 : $i, X77 : $i, X78 : $i]:
% 20.74/20.99         (~ (v1_funct_2 @ X78 @ X76 @ X77)
% 20.74/20.99          | ((X76) = (k1_relset_1 @ X76 @ X77 @ X78))
% 20.74/20.99          | ~ (zip_tseitin_2 @ X78 @ X77 @ X76))),
% 20.74/20.99      inference('cnf', [status(esa)], [zf_stmt_6])).
% 20.74/20.99  thf('23', plain,
% 20.74/20.99      ((~ (zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 20.74/20.99        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D)))),
% 20.74/20.99      inference('sup-', [status(thm)], ['21', '22'])).
% 20.74/20.99  thf('24', plain,
% 20.74/20.99      ((m1_subset_1 @ sk_D @ 
% 20.74/20.99        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 20.74/20.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.74/20.99  thf(redefinition_k1_relset_1, axiom,
% 20.74/20.99    (![A:$i,B:$i,C:$i]:
% 20.74/20.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 20.74/20.99       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 20.74/20.99  thf('25', plain,
% 20.74/20.99      (![X65 : $i, X66 : $i, X67 : $i]:
% 20.74/20.99         (((k1_relset_1 @ X66 @ X67 @ X65) = (k1_relat_1 @ X65))
% 20.74/20.99          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X66 @ X67))))),
% 20.74/20.99      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 20.74/20.99  thf('26', plain,
% 20.74/20.99      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D) = (k1_relat_1 @ sk_D))),
% 20.74/20.99      inference('sup-', [status(thm)], ['24', '25'])).
% 20.74/20.99  thf('27', plain,
% 20.74/20.99      ((~ (zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 20.74/20.99        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 20.74/20.99      inference('demod', [status(thm)], ['23', '26'])).
% 20.74/20.99  thf('28', plain,
% 20.74/20.99      ((((k1_tarski @ sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 20.74/20.99      inference('sup-', [status(thm)], ['20', '27'])).
% 20.74/20.99  thf('29', plain,
% 20.74/20.99      ((((k1_tarski @ sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 20.74/20.99      inference('sup-', [status(thm)], ['20', '27'])).
% 20.74/20.99  thf(l33_zfmisc_1, axiom,
% 20.74/20.99    (![A:$i,B:$i]:
% 20.74/20.99     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 20.74/20.99       ( ~( r2_hidden @ A @ B ) ) ))).
% 20.74/20.99  thf('30', plain,
% 20.74/20.99      (![X31 : $i, X32 : $i]:
% 20.74/20.99         (~ (r2_hidden @ X31 @ X32)
% 20.74/20.99          | ((k4_xboole_0 @ (k1_tarski @ X31) @ X32) != (k1_tarski @ X31)))),
% 20.74/20.99      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 20.74/20.99  thf('31', plain,
% 20.74/20.99      (![X0 : $i]:
% 20.74/20.99         (((k4_xboole_0 @ k1_xboole_0 @ X0) != (k1_tarski @ sk_B))
% 20.74/20.99          | ((sk_A) = (k1_relat_1 @ sk_D))
% 20.74/20.99          | ~ (r2_hidden @ sk_B @ X0))),
% 20.74/20.99      inference('sup-', [status(thm)], ['29', '30'])).
% 20.74/20.99  thf('32', plain,
% 20.74/20.99      (![X0 : $i]:
% 20.74/20.99         (((k4_xboole_0 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 20.74/20.99          | ((sk_A) = (k1_relat_1 @ sk_D))
% 20.74/20.99          | ~ (r2_hidden @ sk_B @ X0)
% 20.74/20.99          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 20.74/20.99      inference('sup-', [status(thm)], ['28', '31'])).
% 20.74/20.99  thf('33', plain,
% 20.74/20.99      (![X0 : $i]:
% 20.74/20.99         (~ (r2_hidden @ sk_B @ X0)
% 20.74/20.99          | ((sk_A) = (k1_relat_1 @ sk_D))
% 20.74/20.99          | ((k4_xboole_0 @ k1_xboole_0 @ X0) != (k1_xboole_0)))),
% 20.74/20.99      inference('simplify', [status(thm)], ['32'])).
% 20.74/20.99  thf('34', plain,
% 20.74/20.99      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 20.74/20.99         (((k4_xboole_0 @ k1_xboole_0 @ 
% 20.74/20.99            (k3_enumset1 @ sk_B @ X3 @ X2 @ X1 @ X0)) != (k1_xboole_0))
% 20.74/20.99          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 20.74/20.99      inference('sup-', [status(thm)], ['15', '33'])).
% 20.74/20.99  thf('35', plain,
% 20.74/20.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 20.74/20.99         (((k4_xboole_0 @ k1_xboole_0 @ (k2_enumset1 @ sk_B @ X2 @ X1 @ X0))
% 20.74/20.99            != (k1_xboole_0))
% 20.74/20.99          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 20.74/20.99      inference('sup-', [status(thm)], ['4', '34'])).
% 20.74/20.99  thf('36', plain,
% 20.74/20.99      (![X0 : $i, X1 : $i]:
% 20.74/20.99         (((k4_xboole_0 @ k1_xboole_0 @ (k1_enumset1 @ sk_B @ X1 @ X0))
% 20.74/20.99            != (k1_xboole_0))
% 20.74/20.99          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 20.74/20.99      inference('sup-', [status(thm)], ['3', '35'])).
% 20.74/20.99  thf('37', plain,
% 20.74/20.99      (![X0 : $i]:
% 20.74/20.99         (((k4_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_B @ X0))
% 20.74/20.99            != (k1_xboole_0))
% 20.74/20.99          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 20.74/20.99      inference('sup-', [status(thm)], ['2', '36'])).
% 20.74/20.99  thf('38', plain,
% 20.74/20.99      ((((k4_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_B)) != (k1_xboole_0))
% 20.74/20.99        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 20.74/20.99      inference('sup-', [status(thm)], ['1', '37'])).
% 20.74/20.99  thf('39', plain,
% 20.74/20.99      (![X74 : $i, X75 : $i]:
% 20.74/20.99         ((zip_tseitin_1 @ X74 @ X75) | ((X74) = (k1_xboole_0)))),
% 20.74/20.99      inference('cnf', [status(esa)], [zf_stmt_4])).
% 20.74/20.99  thf(t3_boole, axiom,
% 20.74/20.99    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 20.74/20.99  thf('40', plain, (![X2 : $i]: ((k4_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 20.74/20.99      inference('cnf', [status(esa)], [t3_boole])).
% 20.74/20.99  thf('41', plain,
% 20.74/20.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 20.74/20.99         (((k4_xboole_0 @ X1 @ X0) = (X1)) | (zip_tseitin_1 @ X0 @ X2))),
% 20.74/20.99      inference('sup+', [status(thm)], ['39', '40'])).
% 20.74/20.99  thf('42', plain,
% 20.74/20.99      (((zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 20.74/20.99        | ~ (zip_tseitin_1 @ (k1_tarski @ sk_B) @ sk_A))),
% 20.74/20.99      inference('sup-', [status(thm)], ['17', '18'])).
% 20.74/20.99  thf('43', plain,
% 20.74/20.99      (![X0 : $i]:
% 20.74/20.99         (((k4_xboole_0 @ X0 @ (k1_tarski @ sk_B)) = (X0))
% 20.74/20.99          | (zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A))),
% 20.74/20.99      inference('sup-', [status(thm)], ['41', '42'])).
% 20.74/20.99  thf('44', plain,
% 20.74/20.99      ((~ (zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 20.74/20.99        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 20.74/20.99      inference('demod', [status(thm)], ['23', '26'])).
% 20.74/20.99  thf('45', plain,
% 20.74/20.99      (![X0 : $i]:
% 20.74/20.99         (((k4_xboole_0 @ X0 @ (k1_tarski @ sk_B)) = (X0))
% 20.74/20.99          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 20.74/20.99      inference('sup-', [status(thm)], ['43', '44'])).
% 20.74/20.99  thf('46', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 20.74/20.99      inference('clc', [status(thm)], ['38', '45'])).
% 20.74/20.99  thf(t8_funct_1, axiom,
% 20.74/20.99    (![A:$i,B:$i,C:$i]:
% 20.74/20.99     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 20.74/20.99       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 20.74/20.99         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 20.74/20.99           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 20.74/20.99  thf('47', plain,
% 20.74/20.99      (![X59 : $i, X60 : $i, X61 : $i]:
% 20.74/20.99         (~ (r2_hidden @ X59 @ (k1_relat_1 @ X60))
% 20.74/20.99          | ((X61) != (k1_funct_1 @ X60 @ X59))
% 20.74/20.99          | (r2_hidden @ (k4_tarski @ X59 @ X61) @ X60)
% 20.74/20.99          | ~ (v1_funct_1 @ X60)
% 20.74/20.99          | ~ (v1_relat_1 @ X60))),
% 20.74/20.99      inference('cnf', [status(esa)], [t8_funct_1])).
% 20.74/20.99  thf('48', plain,
% 20.74/20.99      (![X59 : $i, X60 : $i]:
% 20.74/20.99         (~ (v1_relat_1 @ X60)
% 20.74/20.99          | ~ (v1_funct_1 @ X60)
% 20.74/20.99          | (r2_hidden @ (k4_tarski @ X59 @ (k1_funct_1 @ X60 @ X59)) @ X60)
% 20.74/20.99          | ~ (r2_hidden @ X59 @ (k1_relat_1 @ X60)))),
% 20.74/20.99      inference('simplify', [status(thm)], ['47'])).
% 20.74/20.99  thf('49', plain,
% 20.74/20.99      (![X0 : $i]:
% 20.74/20.99         (~ (r2_hidden @ X0 @ sk_A)
% 20.74/20.99          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D @ X0)) @ sk_D)
% 20.74/20.99          | ~ (v1_funct_1 @ sk_D)
% 20.74/20.99          | ~ (v1_relat_1 @ sk_D))),
% 20.74/20.99      inference('sup-', [status(thm)], ['46', '48'])).
% 20.74/20.99  thf('50', plain, ((v1_funct_1 @ sk_D)),
% 20.74/20.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.74/20.99  thf('51', plain,
% 20.74/20.99      ((m1_subset_1 @ sk_D @ 
% 20.74/20.99        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 20.74/20.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.74/20.99  thf(cc1_relset_1, axiom,
% 20.74/20.99    (![A:$i,B:$i,C:$i]:
% 20.74/20.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 20.74/20.99       ( v1_relat_1 @ C ) ))).
% 20.74/20.99  thf('52', plain,
% 20.74/20.99      (![X62 : $i, X63 : $i, X64 : $i]:
% 20.74/20.99         ((v1_relat_1 @ X62)
% 20.74/20.99          | ~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X63 @ X64))))),
% 20.74/20.99      inference('cnf', [status(esa)], [cc1_relset_1])).
% 20.74/20.99  thf('53', plain, ((v1_relat_1 @ sk_D)),
% 20.74/20.99      inference('sup-', [status(thm)], ['51', '52'])).
% 20.74/20.99  thf('54', plain,
% 20.74/20.99      (![X0 : $i]:
% 20.74/20.99         (~ (r2_hidden @ X0 @ sk_A)
% 20.74/20.99          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D @ X0)) @ sk_D))),
% 20.74/20.99      inference('demod', [status(thm)], ['49', '50', '53'])).
% 20.74/20.99  thf('55', plain,
% 20.74/20.99      ((r2_hidden @ (k4_tarski @ sk_C @ (k1_funct_1 @ sk_D @ sk_C)) @ sk_D)),
% 20.74/20.99      inference('sup-', [status(thm)], ['0', '54'])).
% 20.74/20.99  thf('56', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 20.74/20.99      inference('cnf', [status(esa)], [t69_enumset1])).
% 20.74/20.99  thf('57', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 20.74/20.99      inference('cnf', [status(esa)], [t69_enumset1])).
% 20.74/20.99  thf('58', plain,
% 20.74/20.99      (![X31 : $i, X33 : $i]:
% 20.74/20.99         (((k4_xboole_0 @ (k1_tarski @ X31) @ X33) = (k1_tarski @ X31))
% 20.74/20.99          | (r2_hidden @ X31 @ X33))),
% 20.74/20.99      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 20.74/20.99  thf('59', plain,
% 20.74/20.99      (![X0 : $i, X1 : $i]:
% 20.74/20.99         (((k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1) = (k1_tarski @ X0))
% 20.74/20.99          | (r2_hidden @ X0 @ X1))),
% 20.74/20.99      inference('sup+', [status(thm)], ['57', '58'])).
% 20.74/20.99  thf('60', plain,
% 20.74/20.99      ((m1_subset_1 @ sk_D @ 
% 20.74/20.99        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 20.74/20.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.74/20.99  thf(l3_subset_1, axiom,
% 20.74/20.99    (![A:$i,B:$i]:
% 20.74/20.99     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 20.74/20.99       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 20.74/20.99  thf('61', plain,
% 20.74/20.99      (![X56 : $i, X57 : $i, X58 : $i]:
% 20.74/20.99         (~ (r2_hidden @ X56 @ X57)
% 20.74/20.99          | (r2_hidden @ X56 @ X58)
% 20.74/20.99          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ X58)))),
% 20.74/20.99      inference('cnf', [status(esa)], [l3_subset_1])).
% 20.74/20.99  thf('62', plain,
% 20.74/20.99      (![X0 : $i]:
% 20.74/20.99         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))
% 20.74/20.99          | ~ (r2_hidden @ X0 @ sk_D))),
% 20.74/20.99      inference('sup-', [status(thm)], ['60', '61'])).
% 20.74/20.99  thf('63', plain,
% 20.74/20.99      (![X0 : $i]:
% 20.74/20.99         (((k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ sk_D) = (k1_tarski @ X0))
% 20.74/20.99          | (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 20.74/20.99      inference('sup-', [status(thm)], ['59', '62'])).
% 20.74/20.99  thf('64', plain,
% 20.74/20.99      (![X0 : $i]:
% 20.74/20.99         (((k4_xboole_0 @ (k1_tarski @ X0) @ sk_D) = (k1_tarski @ X0))
% 20.74/20.99          | (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 20.74/20.99      inference('sup+', [status(thm)], ['56', '63'])).
% 20.74/20.99  thf(t13_mcart_1, axiom,
% 20.74/20.99    (![A:$i,B:$i,C:$i]:
% 20.74/20.99     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) ) =>
% 20.74/20.99       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 20.74/20.99         ( ( k2_mcart_1 @ A ) = ( C ) ) ) ))).
% 20.74/20.99  thf('65', plain,
% 20.74/20.99      (![X68 : $i, X69 : $i, X70 : $i]:
% 20.74/20.99         (((k2_mcart_1 @ X68) = (X70))
% 20.74/20.99          | ~ (r2_hidden @ X68 @ (k2_zfmisc_1 @ X69 @ (k1_tarski @ X70))))),
% 20.74/20.99      inference('cnf', [status(esa)], [t13_mcart_1])).
% 20.74/20.99  thf('66', plain,
% 20.74/20.99      (![X0 : $i]:
% 20.74/20.99         (((k4_xboole_0 @ (k1_tarski @ X0) @ sk_D) = (k1_tarski @ X0))
% 20.74/20.99          | ((k2_mcart_1 @ X0) = (sk_B)))),
% 20.74/20.99      inference('sup-', [status(thm)], ['64', '65'])).
% 20.74/20.99  thf('67', plain,
% 20.74/20.99      (![X31 : $i, X32 : $i]:
% 20.74/20.99         (~ (r2_hidden @ X31 @ X32)
% 20.74/20.99          | ((k4_xboole_0 @ (k1_tarski @ X31) @ X32) != (k1_tarski @ X31)))),
% 20.74/20.99      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 20.74/20.99  thf('68', plain,
% 20.74/20.99      (![X0 : $i]:
% 20.74/20.99         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 20.74/20.99          | ((k2_mcart_1 @ X0) = (sk_B))
% 20.74/20.99          | ~ (r2_hidden @ X0 @ sk_D))),
% 20.74/20.99      inference('sup-', [status(thm)], ['66', '67'])).
% 20.74/20.99  thf('69', plain,
% 20.74/20.99      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_D) | ((k2_mcart_1 @ X0) = (sk_B)))),
% 20.74/20.99      inference('simplify', [status(thm)], ['68'])).
% 20.74/20.99  thf('70', plain,
% 20.74/20.99      (((k2_mcart_1 @ (k4_tarski @ sk_C @ (k1_funct_1 @ sk_D @ sk_C))) = (sk_B))),
% 20.74/20.99      inference('sup-', [status(thm)], ['55', '69'])).
% 20.74/20.99  thf(t7_mcart_1, axiom,
% 20.74/20.99    (![A:$i,B:$i]:
% 20.74/20.99     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 20.74/20.99       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 20.74/20.99  thf('71', plain,
% 20.74/20.99      (![X71 : $i, X73 : $i]: ((k2_mcart_1 @ (k4_tarski @ X71 @ X73)) = (X73))),
% 20.74/20.99      inference('cnf', [status(esa)], [t7_mcart_1])).
% 20.74/20.99  thf('72', plain, (((k1_funct_1 @ sk_D @ sk_C) = (sk_B))),
% 20.74/20.99      inference('demod', [status(thm)], ['70', '71'])).
% 20.74/20.99  thf('73', plain, (((k1_funct_1 @ sk_D @ sk_C) != (sk_B))),
% 20.74/20.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.74/20.99  thf('74', plain, ($false),
% 20.74/20.99      inference('simplify_reflect-', [status(thm)], ['72', '73'])).
% 20.74/20.99  
% 20.74/20.99  % SZS output end Refutation
% 20.74/20.99  
% 20.74/21.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
