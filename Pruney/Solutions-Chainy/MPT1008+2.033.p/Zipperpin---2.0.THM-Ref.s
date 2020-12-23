%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LLdkponkc0

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:35 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 152 expanded)
%              Number of leaves         :   58 (  72 expanded)
%              Depth                    :   14
%              Number of atoms          :  951 (1614 expanded)
%              Number of equality atoms :   80 ( 124 expanded)
%              Maximal formula depth    :   23 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

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

thf('0',plain,(
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

thf('1',plain,(
    ! [X72: $i,X73: $i,X74: $i] :
      ( ~ ( v1_funct_2 @ X74 @ X72 @ X73 )
      | ( X72
        = ( k1_relset_1 @ X72 @ X73 @ X74 ) )
      | ~ ( zip_tseitin_2 @ X74 @ X73 @ X72 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,
    ( ~ ( zip_tseitin_2 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf('3',plain,(
    ! [X70: $i,X71: $i] :
      ( ( zip_tseitin_1 @ X70 @ X71 )
      | ( X70 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X75: $i,X76: $i,X77: $i] :
      ( ~ ( zip_tseitin_1 @ X75 @ X76 )
      | ( zip_tseitin_2 @ X77 @ X75 @ X76 )
      | ~ ( m1_subset_1 @ X77 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X76 @ X75 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_2 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    zip_tseitin_2 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X64: $i,X65: $i,X66: $i] :
      ( ( ( k1_relset_1 @ X65 @ X66 @ X64 )
        = ( k1_relat_1 @ X64 ) )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X65 @ X66 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X2 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('16',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X3 @ X3 @ X4 @ X5 )
      = ( k1_enumset1 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k3_enumset1 @ X6 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('18',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k4_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 @ X14 )
      = ( k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('19',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k5_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k4_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('20',plain,(
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

thf('21',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 )
      | ( r2_hidden @ X38 @ X47 )
      | ( X47
       != ( k6_enumset1 @ X46 @ X45 @ X44 @ X43 @ X42 @ X41 @ X40 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('22',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( r2_hidden @ X38 @ ( k6_enumset1 @ X46 @ X45 @ X44 @ X43 @ X42 @ X41 @ X40 @ X39 ) )
      | ( zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6 ) ) ),
    inference('sup+',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( X29 != X28 )
      | ~ ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('25',plain,(
    ! [X28: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ~ ( zip_tseitin_0 @ X28 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X28 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( r2_hidden @ X0 @ ( k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( r2_hidden @ X5 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X4 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','31'])).

thf('33',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['13','32'])).

thf(t117_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('34',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( r2_hidden @ X56 @ ( k1_relat_1 @ X57 ) )
      | ( ( k11_relat_1 @ X57 @ X56 )
        = ( k1_tarski @ ( k1_funct_1 @ X57 @ X56 ) ) )
      | ~ ( v1_funct_1 @ X57 )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k11_relat_1 @ sk_C @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('37',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ( v1_relat_1 @ X58 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X60 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('38',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('40',plain,(
    ! [X50: $i,X51: $i] :
      ( ( ( k11_relat_1 @ X50 @ X51 )
        = ( k9_relat_1 @ X50 @ ( k1_tarski @ X51 ) ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('42',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ( v4_relat_1 @ X61 @ X62 )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X62 @ X63 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('43',plain,(
    v4_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('44',plain,(
    ! [X54: $i,X55: $i] :
      ( ( X54
        = ( k7_relat_1 @ X54 @ X55 ) )
      | ~ ( v4_relat_1 @ X54 @ X55 )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['36','37'])).

thf('47',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('48',plain,(
    ! [X52: $i,X53: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X52 @ X53 ) )
        = ( k9_relat_1 @ X52 @ X53 ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('49',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['36','37'])).

thf('51',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k11_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['40','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['36','37'])).

thf('54',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k11_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','38','39','54'])).

thf('56',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('58',plain,(
    ! [X67: $i,X68: $i,X69: $i] :
      ( ( ( k2_relset_1 @ X68 @ X69 @ X67 )
        = ( k2_relat_1 @ X67 ) )
      | ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X68 @ X69 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('59',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('61',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['55','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LLdkponkc0
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:03:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.51/0.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.51/0.74  % Solved by: fo/fo7.sh
% 0.51/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.74  % done 183 iterations in 0.284s
% 0.51/0.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.51/0.74  % SZS output start Refutation
% 0.51/0.74  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.51/0.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.51/0.74  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.51/0.74  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.51/0.74  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.51/0.74  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.51/0.74  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.51/0.74  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.51/0.74                                           $i > $i).
% 0.51/0.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.51/0.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.51/0.74  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.51/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.51/0.74  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.51/0.74  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.51/0.74  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.51/0.74  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.51/0.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.51/0.74  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.51/0.74  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.51/0.74  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.51/0.74  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.51/0.74  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.51/0.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.51/0.74  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.51/0.74  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.51/0.74  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.51/0.74  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.51/0.74  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.51/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.51/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.74  thf(sk_C_type, type, sk_C: $i).
% 0.51/0.74  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 0.51/0.74                                               $i > $i > $i > $o).
% 0.51/0.74  thf(t62_funct_2, conjecture,
% 0.51/0.74    (![A:$i,B:$i,C:$i]:
% 0.51/0.74     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.51/0.74         ( m1_subset_1 @
% 0.51/0.74           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.51/0.74       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.51/0.74         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.51/0.74           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.51/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.74    (~( ![A:$i,B:$i,C:$i]:
% 0.51/0.74        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.51/0.74            ( m1_subset_1 @
% 0.51/0.74              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.51/0.74          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.51/0.74            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.51/0.74              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.51/0.74    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.51/0.74  thf('0', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf(d1_funct_2, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i]:
% 0.51/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.74       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.51/0.74           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.51/0.74             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.51/0.74         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.51/0.74           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.51/0.74             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.51/0.74  thf(zf_stmt_1, axiom,
% 0.51/0.74    (![C:$i,B:$i,A:$i]:
% 0.51/0.74     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.51/0.74       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.51/0.74  thf('1', plain,
% 0.51/0.74      (![X72 : $i, X73 : $i, X74 : $i]:
% 0.51/0.74         (~ (v1_funct_2 @ X74 @ X72 @ X73)
% 0.51/0.74          | ((X72) = (k1_relset_1 @ X72 @ X73 @ X74))
% 0.51/0.74          | ~ (zip_tseitin_2 @ X74 @ X73 @ X72))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.51/0.74  thf('2', plain,
% 0.51/0.74      ((~ (zip_tseitin_2 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.51/0.74        | ((k1_tarski @ sk_A)
% 0.51/0.74            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['0', '1'])).
% 0.51/0.74  thf(zf_stmt_2, axiom,
% 0.51/0.74    (![B:$i,A:$i]:
% 0.51/0.74     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.51/0.74       ( zip_tseitin_1 @ B @ A ) ))).
% 0.51/0.74  thf('3', plain,
% 0.51/0.74      (![X70 : $i, X71 : $i]:
% 0.51/0.74         ((zip_tseitin_1 @ X70 @ X71) | ((X70) = (k1_xboole_0)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.51/0.74  thf('4', plain,
% 0.51/0.74      ((m1_subset_1 @ sk_C @ 
% 0.51/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.51/0.74  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $o).
% 0.51/0.74  thf(zf_stmt_5, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i]:
% 0.51/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.74       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.51/0.74         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.51/0.74           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.51/0.74             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.51/0.74  thf('5', plain,
% 0.51/0.74      (![X75 : $i, X76 : $i, X77 : $i]:
% 0.51/0.74         (~ (zip_tseitin_1 @ X75 @ X76)
% 0.51/0.74          | (zip_tseitin_2 @ X77 @ X75 @ X76)
% 0.51/0.74          | ~ (m1_subset_1 @ X77 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X76 @ X75))))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.51/0.74  thf('6', plain,
% 0.51/0.74      (((zip_tseitin_2 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.51/0.74        | ~ (zip_tseitin_1 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['4', '5'])).
% 0.51/0.74  thf('7', plain,
% 0.51/0.74      ((((sk_B) = (k1_xboole_0))
% 0.51/0.74        | (zip_tseitin_2 @ sk_C @ sk_B @ (k1_tarski @ sk_A)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['3', '6'])).
% 0.51/0.74  thf('8', plain, (((sk_B) != (k1_xboole_0))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('9', plain, ((zip_tseitin_2 @ sk_C @ sk_B @ (k1_tarski @ sk_A))),
% 0.51/0.74      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.51/0.74  thf('10', plain,
% 0.51/0.74      ((m1_subset_1 @ sk_C @ 
% 0.51/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf(redefinition_k1_relset_1, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i]:
% 0.51/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.74       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.51/0.74  thf('11', plain,
% 0.51/0.74      (![X64 : $i, X65 : $i, X66 : $i]:
% 0.51/0.74         (((k1_relset_1 @ X65 @ X66 @ X64) = (k1_relat_1 @ X64))
% 0.51/0.74          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X65 @ X66))))),
% 0.51/0.74      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.51/0.74  thf('12', plain,
% 0.51/0.74      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.51/0.74      inference('sup-', [status(thm)], ['10', '11'])).
% 0.51/0.74  thf('13', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.51/0.74      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.51/0.74  thf(t69_enumset1, axiom,
% 0.51/0.74    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.51/0.74  thf('14', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.51/0.74      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.51/0.74  thf(t70_enumset1, axiom,
% 0.51/0.74    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.51/0.74  thf('15', plain,
% 0.51/0.74      (![X1 : $i, X2 : $i]:
% 0.51/0.74         ((k1_enumset1 @ X1 @ X1 @ X2) = (k2_tarski @ X1 @ X2))),
% 0.51/0.74      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.51/0.74  thf(t71_enumset1, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i]:
% 0.51/0.74     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.51/0.74  thf('16', plain,
% 0.51/0.74      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.51/0.74         ((k2_enumset1 @ X3 @ X3 @ X4 @ X5) = (k1_enumset1 @ X3 @ X4 @ X5))),
% 0.51/0.74      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.51/0.74  thf(t72_enumset1, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.51/0.74     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.51/0.74  thf('17', plain,
% 0.51/0.74      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.51/0.74         ((k3_enumset1 @ X6 @ X6 @ X7 @ X8 @ X9)
% 0.51/0.74           = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 0.51/0.74      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.51/0.74  thf(t73_enumset1, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.51/0.74     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.51/0.74       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.51/0.74  thf('18', plain,
% 0.51/0.74      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.51/0.74         ((k4_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 @ X14)
% 0.51/0.74           = (k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14))),
% 0.51/0.74      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.51/0.74  thf(t74_enumset1, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.51/0.74     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.51/0.74       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.51/0.74  thf('19', plain,
% 0.51/0.74      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.51/0.74         ((k5_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20)
% 0.51/0.74           = (k4_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20))),
% 0.51/0.74      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.51/0.74  thf(t75_enumset1, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.51/0.74     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.51/0.74       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.51/0.74  thf('20', plain,
% 0.51/0.74      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.51/0.74         ((k6_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27)
% 0.51/0.74           = (k5_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27))),
% 0.51/0.74      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.51/0.74  thf(d6_enumset1, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.51/0.74     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 0.51/0.74       ( ![J:$i]:
% 0.51/0.74         ( ( r2_hidden @ J @ I ) <=>
% 0.51/0.74           ( ~( ( ( J ) != ( H ) ) & ( ( J ) != ( G ) ) & ( ( J ) != ( F ) ) & 
% 0.51/0.74                ( ( J ) != ( E ) ) & ( ( J ) != ( D ) ) & ( ( J ) != ( C ) ) & 
% 0.51/0.74                ( ( J ) != ( B ) ) & ( ( J ) != ( A ) ) ) ) ) ) ))).
% 0.51/0.74  thf(zf_stmt_6, type, zip_tseitin_0 :
% 0.51/0.74      $i > $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 0.51/0.74  thf(zf_stmt_7, axiom,
% 0.51/0.74    (![J:$i,H:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.51/0.74     ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) <=>
% 0.51/0.74       ( ( ( J ) != ( A ) ) & ( ( J ) != ( B ) ) & ( ( J ) != ( C ) ) & 
% 0.51/0.74         ( ( J ) != ( D ) ) & ( ( J ) != ( E ) ) & ( ( J ) != ( F ) ) & 
% 0.51/0.74         ( ( J ) != ( G ) ) & ( ( J ) != ( H ) ) ) ))).
% 0.51/0.74  thf(zf_stmt_8, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.51/0.74     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 0.51/0.74       ( ![J:$i]:
% 0.51/0.74         ( ( r2_hidden @ J @ I ) <=>
% 0.51/0.74           ( ~( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.51/0.74  thf('21', plain,
% 0.51/0.74      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, 
% 0.51/0.74         X45 : $i, X46 : $i, X47 : $i]:
% 0.51/0.74         ((zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46)
% 0.51/0.74          | (r2_hidden @ X38 @ X47)
% 0.51/0.74          | ((X47)
% 0.51/0.74              != (k6_enumset1 @ X46 @ X45 @ X44 @ X43 @ X42 @ X41 @ X40 @ X39)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.51/0.74  thf('22', plain,
% 0.51/0.74      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, 
% 0.51/0.74         X45 : $i, X46 : $i]:
% 0.51/0.74         ((r2_hidden @ X38 @ 
% 0.51/0.74           (k6_enumset1 @ X46 @ X45 @ X44 @ X43 @ X42 @ X41 @ X40 @ X39))
% 0.51/0.74          | (zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ 
% 0.51/0.74             X46))),
% 0.51/0.74      inference('simplify', [status(thm)], ['21'])).
% 0.51/0.74  thf('23', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.51/0.74         ((r2_hidden @ X7 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.51/0.74          | (zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6))),
% 0.51/0.74      inference('sup+', [status(thm)], ['20', '22'])).
% 0.51/0.74  thf('24', plain,
% 0.51/0.74      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, 
% 0.51/0.74         X35 : $i, X36 : $i]:
% 0.51/0.74         (((X29) != (X28))
% 0.51/0.74          | ~ (zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ 
% 0.51/0.74               X28))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.51/0.74  thf('25', plain,
% 0.51/0.74      (![X28 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, 
% 0.51/0.74         X36 : $i]:
% 0.51/0.74         ~ (zip_tseitin_0 @ X28 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X28)),
% 0.51/0.74      inference('simplify', [status(thm)], ['24'])).
% 0.51/0.74  thf('26', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.51/0.74         (r2_hidden @ X0 @ (k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6))),
% 0.51/0.74      inference('sup-', [status(thm)], ['23', '25'])).
% 0.51/0.74  thf('27', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.51/0.74         (r2_hidden @ X5 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['19', '26'])).
% 0.51/0.74  thf('28', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.51/0.74         (r2_hidden @ X4 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['18', '27'])).
% 0.51/0.74  thf('29', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.51/0.74         (r2_hidden @ X3 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['17', '28'])).
% 0.51/0.74  thf('30', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.74         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['16', '29'])).
% 0.51/0.74  thf('31', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['15', '30'])).
% 0.51/0.74  thf('32', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['14', '31'])).
% 0.51/0.74  thf('33', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.51/0.74      inference('sup+', [status(thm)], ['13', '32'])).
% 0.51/0.74  thf(t117_funct_1, axiom,
% 0.51/0.74    (![A:$i,B:$i]:
% 0.51/0.74     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.51/0.74       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.51/0.74         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.51/0.74  thf('34', plain,
% 0.51/0.74      (![X56 : $i, X57 : $i]:
% 0.51/0.74         (~ (r2_hidden @ X56 @ (k1_relat_1 @ X57))
% 0.51/0.74          | ((k11_relat_1 @ X57 @ X56) = (k1_tarski @ (k1_funct_1 @ X57 @ X56)))
% 0.51/0.74          | ~ (v1_funct_1 @ X57)
% 0.51/0.74          | ~ (v1_relat_1 @ X57))),
% 0.51/0.74      inference('cnf', [status(esa)], [t117_funct_1])).
% 0.51/0.74  thf('35', plain,
% 0.51/0.74      ((~ (v1_relat_1 @ sk_C)
% 0.51/0.74        | ~ (v1_funct_1 @ sk_C)
% 0.51/0.74        | ((k11_relat_1 @ sk_C @ sk_A)
% 0.51/0.74            = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['33', '34'])).
% 0.51/0.74  thf('36', plain,
% 0.51/0.74      ((m1_subset_1 @ sk_C @ 
% 0.51/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf(cc1_relset_1, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i]:
% 0.51/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.74       ( v1_relat_1 @ C ) ))).
% 0.51/0.74  thf('37', plain,
% 0.51/0.74      (![X58 : $i, X59 : $i, X60 : $i]:
% 0.51/0.74         ((v1_relat_1 @ X58)
% 0.51/0.74          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X60))))),
% 0.51/0.74      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.51/0.74  thf('38', plain, ((v1_relat_1 @ sk_C)),
% 0.51/0.74      inference('sup-', [status(thm)], ['36', '37'])).
% 0.51/0.74  thf('39', plain, ((v1_funct_1 @ sk_C)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf(d16_relat_1, axiom,
% 0.51/0.74    (![A:$i]:
% 0.51/0.74     ( ( v1_relat_1 @ A ) =>
% 0.51/0.74       ( ![B:$i]:
% 0.51/0.74         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.51/0.74  thf('40', plain,
% 0.51/0.74      (![X50 : $i, X51 : $i]:
% 0.51/0.74         (((k11_relat_1 @ X50 @ X51) = (k9_relat_1 @ X50 @ (k1_tarski @ X51)))
% 0.51/0.74          | ~ (v1_relat_1 @ X50))),
% 0.51/0.74      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.51/0.74  thf('41', plain,
% 0.51/0.74      ((m1_subset_1 @ sk_C @ 
% 0.51/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf(cc2_relset_1, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i]:
% 0.51/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.74       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.51/0.74  thf('42', plain,
% 0.51/0.74      (![X61 : $i, X62 : $i, X63 : $i]:
% 0.51/0.74         ((v4_relat_1 @ X61 @ X62)
% 0.51/0.74          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X62 @ X63))))),
% 0.51/0.74      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.51/0.74  thf('43', plain, ((v4_relat_1 @ sk_C @ (k1_tarski @ sk_A))),
% 0.51/0.74      inference('sup-', [status(thm)], ['41', '42'])).
% 0.51/0.74  thf(t209_relat_1, axiom,
% 0.51/0.74    (![A:$i,B:$i]:
% 0.51/0.74     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.51/0.74       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.51/0.74  thf('44', plain,
% 0.51/0.74      (![X54 : $i, X55 : $i]:
% 0.51/0.74         (((X54) = (k7_relat_1 @ X54 @ X55))
% 0.51/0.74          | ~ (v4_relat_1 @ X54 @ X55)
% 0.51/0.74          | ~ (v1_relat_1 @ X54))),
% 0.51/0.74      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.51/0.74  thf('45', plain,
% 0.51/0.74      ((~ (v1_relat_1 @ sk_C)
% 0.51/0.74        | ((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['43', '44'])).
% 0.51/0.74  thf('46', plain, ((v1_relat_1 @ sk_C)),
% 0.51/0.74      inference('sup-', [status(thm)], ['36', '37'])).
% 0.51/0.74  thf('47', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.51/0.74      inference('demod', [status(thm)], ['45', '46'])).
% 0.51/0.74  thf(t148_relat_1, axiom,
% 0.51/0.74    (![A:$i,B:$i]:
% 0.51/0.74     ( ( v1_relat_1 @ B ) =>
% 0.51/0.74       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.51/0.74  thf('48', plain,
% 0.51/0.74      (![X52 : $i, X53 : $i]:
% 0.51/0.74         (((k2_relat_1 @ (k7_relat_1 @ X52 @ X53)) = (k9_relat_1 @ X52 @ X53))
% 0.51/0.74          | ~ (v1_relat_1 @ X52))),
% 0.51/0.74      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.51/0.74  thf('49', plain,
% 0.51/0.74      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_tarski @ sk_A)))
% 0.51/0.74        | ~ (v1_relat_1 @ sk_C))),
% 0.51/0.74      inference('sup+', [status(thm)], ['47', '48'])).
% 0.51/0.74  thf('50', plain, ((v1_relat_1 @ sk_C)),
% 0.51/0.74      inference('sup-', [status(thm)], ['36', '37'])).
% 0.51/0.74  thf('51', plain,
% 0.51/0.74      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.51/0.74      inference('demod', [status(thm)], ['49', '50'])).
% 0.51/0.74  thf('52', plain,
% 0.51/0.74      ((((k2_relat_1 @ sk_C) = (k11_relat_1 @ sk_C @ sk_A))
% 0.51/0.74        | ~ (v1_relat_1 @ sk_C))),
% 0.51/0.74      inference('sup+', [status(thm)], ['40', '51'])).
% 0.51/0.74  thf('53', plain, ((v1_relat_1 @ sk_C)),
% 0.51/0.74      inference('sup-', [status(thm)], ['36', '37'])).
% 0.51/0.74  thf('54', plain, (((k2_relat_1 @ sk_C) = (k11_relat_1 @ sk_C @ sk_A))),
% 0.51/0.74      inference('demod', [status(thm)], ['52', '53'])).
% 0.51/0.74  thf('55', plain,
% 0.51/0.74      (((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.51/0.74      inference('demod', [status(thm)], ['35', '38', '39', '54'])).
% 0.51/0.74  thf('56', plain,
% 0.51/0.74      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)
% 0.51/0.74         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('57', plain,
% 0.51/0.74      ((m1_subset_1 @ sk_C @ 
% 0.51/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf(redefinition_k2_relset_1, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i]:
% 0.51/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.74       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.51/0.74  thf('58', plain,
% 0.51/0.74      (![X67 : $i, X68 : $i, X69 : $i]:
% 0.51/0.74         (((k2_relset_1 @ X68 @ X69 @ X67) = (k2_relat_1 @ X67))
% 0.51/0.74          | ~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X68 @ X69))))),
% 0.51/0.74      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.51/0.74  thf('59', plain,
% 0.51/0.74      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.51/0.74      inference('sup-', [status(thm)], ['57', '58'])).
% 0.51/0.74  thf('60', plain,
% 0.51/0.74      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.51/0.74      inference('demod', [status(thm)], ['56', '59'])).
% 0.51/0.74  thf('61', plain, ($false),
% 0.51/0.74      inference('simplify_reflect-', [status(thm)], ['55', '60'])).
% 0.51/0.74  
% 0.51/0.74  % SZS output end Refutation
% 0.51/0.74  
% 0.51/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
