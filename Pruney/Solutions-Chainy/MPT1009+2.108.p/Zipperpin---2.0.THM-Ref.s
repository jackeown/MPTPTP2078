%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jnbB45fQHL

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:04 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 978 expanded)
%              Number of leaves         :   60 ( 326 expanded)
%              Depth                    :   16
%              Number of atoms          : 1146 (11007 expanded)
%              Number of equality atoms :   89 ( 514 expanded)
%              Maximal formula depth    :   23 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(t64_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X83: $i,X84: $i,X85: $i,X86: $i] :
      ( ~ ( m1_subset_1 @ X83 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X84 @ X85 ) ) )
      | ( ( k7_relset_1 @ X84 @ X85 @ X83 @ X86 )
        = ( k9_relat_1 @ X83 @ X86 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('8',plain,(
    ! [X87: $i,X88: $i,X89: $i,X90: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X87 ) @ X88 )
      | ( m1_subset_1 @ X87 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X88 @ X89 ) ) )
      | ~ ( m1_subset_1 @ X87 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X90 @ X89 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X60: $i,X61: $i] :
      ( ( r1_tarski @ X60 @ X61 )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ X61 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) @ sk_D )
    | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B )
      = sk_D ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('15',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X5 @ X5 @ X6 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('17',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X7 @ X7 @ X8 @ X9 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('18',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k3_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('19',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k4_enumset1 @ X14 @ X14 @ X15 @ X16 @ X17 @ X18 )
      = ( k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('20',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( k5_enumset1 @ X19 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 )
      = ( k4_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('21',plain,(
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

thf('22',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( zip_tseitin_0 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 )
      | ( r2_hidden @ X48 @ X57 )
      | ( X57
       != ( k6_enumset1 @ X56 @ X55 @ X54 @ X53 @ X52 @ X51 @ X50 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('23',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( r2_hidden @ X48 @ ( k6_enumset1 @ X56 @ X55 @ X54 @ X53 @ X52 @ X51 @ X50 @ X49 ) )
      | ( zip_tseitin_0 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6 ) ) ),
    inference('sup+',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( X39 != X38 )
      | ~ ( zip_tseitin_0 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('26',plain,(
    ! [X38: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ~ ( zip_tseitin_0 @ X38 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X38 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( r2_hidden @ X0 @ ( k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( r2_hidden @ X5 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X4 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('35',plain,(
    ! [X80: $i,X81: $i,X82: $i] :
      ( ( v4_relat_1 @ X80 @ X81 )
      | ~ ( m1_subset_1 @ X80 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X81 @ X82 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('36',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('37',plain,(
    ! [X67: $i,X68: $i] :
      ( ~ ( v4_relat_1 @ X67 @ X68 )
      | ( r1_tarski @ ( k1_relat_1 @ X67 ) @ X68 )
      | ~ ( v1_relat_1 @ X67 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('40',plain,(
    ! [X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ X64 ) )
      | ( v1_relat_1 @ X63 )
      | ~ ( v1_relat_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('42',plain,(
    ! [X69: $i,X70: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X69 @ X70 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('43',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['38','43'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('45',plain,(
    ! [X32: $i,X33: $i] :
      ( ( X33
        = ( k1_tarski @ X32 ) )
      | ( X33 = k1_xboole_0 )
      | ~ ( r1_tarski @ X33 @ ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('46',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(t117_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('47',plain,(
    ! [X78: $i,X79: $i] :
      ( ~ ( r2_hidden @ X78 @ ( k1_relat_1 @ X79 ) )
      | ( ( k11_relat_1 @ X79 @ X78 )
        = ( k1_tarski @ ( k1_funct_1 @ X79 @ X78 ) ) )
      | ~ ( v1_funct_1 @ X79 )
      | ~ ( v1_relat_1 @ X79 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k11_relat_1 @ sk_D @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ sk_D @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['41','42'])).

thf('50',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ( ( k11_relat_1 @ sk_D @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ sk_D @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ( ( k11_relat_1 @ sk_D @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','51'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('53',plain,(
    ! [X65: $i,X66: $i] :
      ( ( ( k11_relat_1 @ X65 @ X66 )
        = ( k9_relat_1 @ X65 @ ( k1_tarski @ X66 ) ) )
      | ~ ( v1_relat_1 @ X65 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('54',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('55',plain,(
    ! [X76: $i,X77: $i] :
      ( ( X76
        = ( k7_relat_1 @ X76 @ X77 ) )
      | ~ ( v4_relat_1 @ X76 @ X77 )
      | ~ ( v1_relat_1 @ X76 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('56',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['41','42'])).

thf('58',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('59',plain,(
    ! [X73: $i,X74: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X73 @ X74 ) )
        = ( k9_relat_1 @ X73 @ X74 ) )
      | ~ ( v1_relat_1 @ X73 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('60',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k9_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['41','42'])).

thf('62',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k9_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k11_relat_1 @ sk_D @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['53','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['41','42'])).

thf('65',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k11_relat_1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','65'])).

thf('67',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('68',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('70',plain,(
    ! [X73: $i,X74: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X73 @ X74 ) )
        = ( k9_relat_1 @ X73 @ X74 ) )
      | ~ ( v1_relat_1 @ X73 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('71',plain,(
    ! [X71: $i,X72: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X71 @ X72 ) @ ( k2_relat_1 @ X71 ) )
      | ~ ( v1_relat_1 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_D )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) @ X0 ) @ ( k9_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['41','42'])).

thf('75',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['41','42'])).

thf('76',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('77',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k9_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('78',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['73','74','75','76','77'])).

thf('79',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['68','78'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('80',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k2_zfmisc_1 @ X36 @ X37 )
        = k1_xboole_0 )
      | ( X36 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('81',plain,(
    ! [X37: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X37 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['80'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('82',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('83',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['68','78'])).

thf('84',plain,(
    ! [X37: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X37 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['80'])).

thf('85',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['14','79','81','82','83','84'])).

thf(t150_relat_1,axiom,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('86',plain,(
    ! [X75: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X75 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t150_relat_1])).

thf('87',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['14','79','81','82','83','84'])).

thf('88',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('89',plain,(
    $false ),
    inference(demod,[status(thm)],['4','85','86','87','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jnbB45fQHL
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:32:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.42/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.60  % Solved by: fo/fo7.sh
% 0.42/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.60  % done 352 iterations in 0.137s
% 0.42/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.60  % SZS output start Refutation
% 0.42/0.60  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.42/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.60  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.42/0.60  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.42/0.60  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.42/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.42/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.42/0.60  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.42/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.42/0.60  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.42/0.60  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.42/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.60  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.42/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.42/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.60  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.42/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.42/0.60  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.42/0.60  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.42/0.60                                           $i > $i).
% 0.42/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.42/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.42/0.60  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.42/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.42/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.42/0.60  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.42/0.60  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 0.42/0.60                                               $i > $i > $i > $o).
% 0.42/0.60  thf(t64_funct_2, conjecture,
% 0.42/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.60     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.42/0.60         ( m1_subset_1 @
% 0.42/0.60           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.42/0.60       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.42/0.60         ( r1_tarski @
% 0.42/0.60           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.42/0.60           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.42/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.60    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.60        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.42/0.60            ( m1_subset_1 @
% 0.42/0.60              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.42/0.60          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.42/0.60            ( r1_tarski @
% 0.42/0.60              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.42/0.60              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.42/0.60    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.42/0.60  thf('0', plain,
% 0.42/0.60      (~ (r1_tarski @ 
% 0.42/0.60          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.42/0.60          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('1', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_D @ 
% 0.42/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(redefinition_k7_relset_1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.60       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.42/0.60  thf('2', plain,
% 0.42/0.60      (![X83 : $i, X84 : $i, X85 : $i, X86 : $i]:
% 0.42/0.60         (~ (m1_subset_1 @ X83 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X84 @ X85)))
% 0.42/0.60          | ((k7_relset_1 @ X84 @ X85 @ X83 @ X86) = (k9_relat_1 @ X83 @ X86)))),
% 0.42/0.60      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.42/0.60  thf('3', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.42/0.60           = (k9_relat_1 @ sk_D @ X0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.42/0.60  thf('4', plain,
% 0.42/0.60      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.42/0.60          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.42/0.60      inference('demod', [status(thm)], ['0', '3'])).
% 0.42/0.60  thf(d10_xboole_0, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.42/0.60  thf('5', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.42/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.42/0.60  thf('6', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.42/0.60      inference('simplify', [status(thm)], ['5'])).
% 0.42/0.60  thf('7', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_D @ 
% 0.42/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(t13_relset_1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.60     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.42/0.60       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 0.42/0.60         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 0.42/0.60  thf('8', plain,
% 0.42/0.60      (![X87 : $i, X88 : $i, X89 : $i, X90 : $i]:
% 0.42/0.60         (~ (r1_tarski @ (k1_relat_1 @ X87) @ X88)
% 0.42/0.60          | (m1_subset_1 @ X87 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X88 @ X89)))
% 0.42/0.60          | ~ (m1_subset_1 @ X87 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X90 @ X89))))),
% 0.42/0.60      inference('cnf', [status(esa)], [t13_relset_1])).
% 0.42/0.60  thf('9', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.42/0.60          | ~ (r1_tarski @ (k1_relat_1 @ sk_D) @ X0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['7', '8'])).
% 0.42/0.60  thf('10', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_D @ 
% 0.42/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['6', '9'])).
% 0.42/0.60  thf(t3_subset, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.42/0.60  thf('11', plain,
% 0.42/0.60      (![X60 : $i, X61 : $i]:
% 0.42/0.60         ((r1_tarski @ X60 @ X61) | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ X61)))),
% 0.42/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.42/0.60  thf('12', plain,
% 0.42/0.60      ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B))),
% 0.42/0.60      inference('sup-', [status(thm)], ['10', '11'])).
% 0.42/0.60  thf('13', plain,
% 0.42/0.60      (![X0 : $i, X2 : $i]:
% 0.42/0.60         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.42/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.42/0.60  thf('14', plain,
% 0.42/0.60      ((~ (r1_tarski @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B) @ sk_D)
% 0.42/0.60        | ((k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B) = (sk_D)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['12', '13'])).
% 0.42/0.60  thf(t69_enumset1, axiom,
% 0.42/0.60    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.42/0.60  thf('15', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.42/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.42/0.60  thf(t70_enumset1, axiom,
% 0.42/0.60    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.42/0.60  thf('16', plain,
% 0.42/0.60      (![X5 : $i, X6 : $i]:
% 0.42/0.60         ((k1_enumset1 @ X5 @ X5 @ X6) = (k2_tarski @ X5 @ X6))),
% 0.42/0.60      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.42/0.60  thf(t71_enumset1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.42/0.60  thf('17', plain,
% 0.42/0.60      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.42/0.60         ((k2_enumset1 @ X7 @ X7 @ X8 @ X9) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 0.42/0.60      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.42/0.60  thf(t72_enumset1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.60     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.42/0.60  thf('18', plain,
% 0.42/0.60      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.42/0.60         ((k3_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13)
% 0.42/0.60           = (k2_enumset1 @ X10 @ X11 @ X12 @ X13))),
% 0.42/0.60      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.42/0.60  thf(t73_enumset1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.42/0.60     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.42/0.60       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.42/0.60  thf('19', plain,
% 0.42/0.60      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.42/0.60         ((k4_enumset1 @ X14 @ X14 @ X15 @ X16 @ X17 @ X18)
% 0.42/0.60           = (k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18))),
% 0.42/0.60      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.42/0.60  thf(t74_enumset1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.42/0.60     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.42/0.60       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.42/0.60  thf('20', plain,
% 0.42/0.60      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.42/0.60         ((k5_enumset1 @ X19 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24)
% 0.42/0.60           = (k4_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24))),
% 0.42/0.60      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.42/0.60  thf(t75_enumset1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.42/0.60     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.42/0.60       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.42/0.60  thf('21', plain,
% 0.42/0.60      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.42/0.60         ((k6_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31)
% 0.42/0.60           = (k5_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31))),
% 0.42/0.60      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.42/0.60  thf(d6_enumset1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.42/0.60     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 0.42/0.60       ( ![J:$i]:
% 0.42/0.60         ( ( r2_hidden @ J @ I ) <=>
% 0.42/0.60           ( ~( ( ( J ) != ( H ) ) & ( ( J ) != ( G ) ) & ( ( J ) != ( F ) ) & 
% 0.42/0.60                ( ( J ) != ( E ) ) & ( ( J ) != ( D ) ) & ( ( J ) != ( C ) ) & 
% 0.42/0.60                ( ( J ) != ( B ) ) & ( ( J ) != ( A ) ) ) ) ) ) ))).
% 0.42/0.60  thf(zf_stmt_1, type, zip_tseitin_0 :
% 0.42/0.60      $i > $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 0.42/0.60  thf(zf_stmt_2, axiom,
% 0.42/0.60    (![J:$i,H:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.42/0.60     ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) <=>
% 0.42/0.60       ( ( ( J ) != ( A ) ) & ( ( J ) != ( B ) ) & ( ( J ) != ( C ) ) & 
% 0.42/0.60         ( ( J ) != ( D ) ) & ( ( J ) != ( E ) ) & ( ( J ) != ( F ) ) & 
% 0.42/0.60         ( ( J ) != ( G ) ) & ( ( J ) != ( H ) ) ) ))).
% 0.42/0.60  thf(zf_stmt_3, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.42/0.60     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 0.42/0.60       ( ![J:$i]:
% 0.42/0.60         ( ( r2_hidden @ J @ I ) <=>
% 0.42/0.60           ( ~( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.42/0.60  thf('22', plain,
% 0.42/0.60      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, 
% 0.42/0.60         X55 : $i, X56 : $i, X57 : $i]:
% 0.42/0.60         ((zip_tseitin_0 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56)
% 0.42/0.60          | (r2_hidden @ X48 @ X57)
% 0.42/0.60          | ((X57)
% 0.42/0.60              != (k6_enumset1 @ X56 @ X55 @ X54 @ X53 @ X52 @ X51 @ X50 @ X49)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.42/0.60  thf('23', plain,
% 0.42/0.60      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, 
% 0.42/0.60         X55 : $i, X56 : $i]:
% 0.42/0.60         ((r2_hidden @ X48 @ 
% 0.42/0.60           (k6_enumset1 @ X56 @ X55 @ X54 @ X53 @ X52 @ X51 @ X50 @ X49))
% 0.42/0.60          | (zip_tseitin_0 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ 
% 0.42/0.60             X56))),
% 0.42/0.60      inference('simplify', [status(thm)], ['22'])).
% 0.42/0.60  thf('24', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.42/0.60         ((r2_hidden @ X7 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.42/0.60          | (zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6))),
% 0.42/0.60      inference('sup+', [status(thm)], ['21', '23'])).
% 0.42/0.60  thf('25', plain,
% 0.42/0.60      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, 
% 0.42/0.60         X45 : $i, X46 : $i]:
% 0.42/0.60         (((X39) != (X38))
% 0.42/0.60          | ~ (zip_tseitin_0 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ 
% 0.42/0.60               X38))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.42/0.60  thf('26', plain,
% 0.42/0.60      (![X38 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, 
% 0.42/0.60         X46 : $i]:
% 0.42/0.60         ~ (zip_tseitin_0 @ X38 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X38)),
% 0.42/0.60      inference('simplify', [status(thm)], ['25'])).
% 0.42/0.60  thf('27', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.42/0.60         (r2_hidden @ X0 @ (k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6))),
% 0.42/0.60      inference('sup-', [status(thm)], ['24', '26'])).
% 0.42/0.60  thf('28', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.42/0.60         (r2_hidden @ X5 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.42/0.60      inference('sup+', [status(thm)], ['20', '27'])).
% 0.42/0.60  thf('29', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.42/0.60         (r2_hidden @ X4 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.42/0.60      inference('sup+', [status(thm)], ['19', '28'])).
% 0.42/0.60  thf('30', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.42/0.60         (r2_hidden @ X3 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.42/0.60      inference('sup+', [status(thm)], ['18', '29'])).
% 0.42/0.60  thf('31', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.60         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.42/0.60      inference('sup+', [status(thm)], ['17', '30'])).
% 0.42/0.60  thf('32', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.42/0.60      inference('sup+', [status(thm)], ['16', '31'])).
% 0.42/0.60  thf('33', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.42/0.60      inference('sup+', [status(thm)], ['15', '32'])).
% 0.42/0.60  thf('34', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_D @ 
% 0.42/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(cc2_relset_1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.60       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.42/0.60  thf('35', plain,
% 0.42/0.60      (![X80 : $i, X81 : $i, X82 : $i]:
% 0.42/0.60         ((v4_relat_1 @ X80 @ X81)
% 0.42/0.60          | ~ (m1_subset_1 @ X80 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X81 @ X82))))),
% 0.42/0.60      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.42/0.60  thf('36', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.42/0.60      inference('sup-', [status(thm)], ['34', '35'])).
% 0.42/0.60  thf(d18_relat_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( v1_relat_1 @ B ) =>
% 0.42/0.60       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.42/0.60  thf('37', plain,
% 0.42/0.60      (![X67 : $i, X68 : $i]:
% 0.42/0.60         (~ (v4_relat_1 @ X67 @ X68)
% 0.42/0.60          | (r1_tarski @ (k1_relat_1 @ X67) @ X68)
% 0.42/0.60          | ~ (v1_relat_1 @ X67))),
% 0.42/0.60      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.42/0.60  thf('38', plain,
% 0.42/0.60      ((~ (v1_relat_1 @ sk_D)
% 0.42/0.60        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['36', '37'])).
% 0.42/0.60  thf('39', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_D @ 
% 0.42/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(cc2_relat_1, axiom,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( v1_relat_1 @ A ) =>
% 0.42/0.60       ( ![B:$i]:
% 0.42/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.42/0.60  thf('40', plain,
% 0.42/0.60      (![X63 : $i, X64 : $i]:
% 0.42/0.60         (~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ X64))
% 0.42/0.60          | (v1_relat_1 @ X63)
% 0.42/0.60          | ~ (v1_relat_1 @ X64))),
% 0.42/0.60      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.42/0.60  thf('41', plain,
% 0.42/0.60      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.42/0.60        | (v1_relat_1 @ sk_D))),
% 0.42/0.60      inference('sup-', [status(thm)], ['39', '40'])).
% 0.42/0.60  thf(fc6_relat_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.42/0.60  thf('42', plain,
% 0.42/0.60      (![X69 : $i, X70 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X69 @ X70))),
% 0.42/0.60      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.42/0.60  thf('43', plain, ((v1_relat_1 @ sk_D)),
% 0.42/0.60      inference('demod', [status(thm)], ['41', '42'])).
% 0.42/0.60  thf('44', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.42/0.60      inference('demod', [status(thm)], ['38', '43'])).
% 0.42/0.60  thf(l3_zfmisc_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.42/0.60       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.42/0.60  thf('45', plain,
% 0.42/0.60      (![X32 : $i, X33 : $i]:
% 0.42/0.60         (((X33) = (k1_tarski @ X32))
% 0.42/0.60          | ((X33) = (k1_xboole_0))
% 0.42/0.60          | ~ (r1_tarski @ X33 @ (k1_tarski @ X32)))),
% 0.42/0.60      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.42/0.60  thf('46', plain,
% 0.42/0.60      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.42/0.60        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['44', '45'])).
% 0.42/0.60  thf(t117_funct_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.42/0.60       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.42/0.60         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.42/0.60  thf('47', plain,
% 0.42/0.60      (![X78 : $i, X79 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X78 @ (k1_relat_1 @ X79))
% 0.42/0.60          | ((k11_relat_1 @ X79 @ X78) = (k1_tarski @ (k1_funct_1 @ X79 @ X78)))
% 0.42/0.60          | ~ (v1_funct_1 @ X79)
% 0.42/0.60          | ~ (v1_relat_1 @ X79))),
% 0.42/0.60      inference('cnf', [status(esa)], [t117_funct_1])).
% 0.42/0.60  thf('48', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.42/0.60          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.42/0.60          | ~ (v1_relat_1 @ sk_D)
% 0.42/0.60          | ~ (v1_funct_1 @ sk_D)
% 0.42/0.60          | ((k11_relat_1 @ sk_D @ X0) = (k1_tarski @ (k1_funct_1 @ sk_D @ X0))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['46', '47'])).
% 0.42/0.60  thf('49', plain, ((v1_relat_1 @ sk_D)),
% 0.42/0.60      inference('demod', [status(thm)], ['41', '42'])).
% 0.42/0.60  thf('50', plain, ((v1_funct_1 @ sk_D)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('51', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.42/0.60          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.42/0.60          | ((k11_relat_1 @ sk_D @ X0) = (k1_tarski @ (k1_funct_1 @ sk_D @ X0))))),
% 0.42/0.60      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.42/0.60  thf('52', plain,
% 0.42/0.60      ((((k11_relat_1 @ sk_D @ sk_A) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.42/0.60        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['33', '51'])).
% 0.42/0.60  thf(d16_relat_1, axiom,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( v1_relat_1 @ A ) =>
% 0.42/0.60       ( ![B:$i]:
% 0.42/0.60         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.42/0.60  thf('53', plain,
% 0.42/0.60      (![X65 : $i, X66 : $i]:
% 0.42/0.60         (((k11_relat_1 @ X65 @ X66) = (k9_relat_1 @ X65 @ (k1_tarski @ X66)))
% 0.42/0.60          | ~ (v1_relat_1 @ X65))),
% 0.42/0.60      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.42/0.60  thf('54', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.42/0.60      inference('sup-', [status(thm)], ['34', '35'])).
% 0.42/0.60  thf(t209_relat_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.42/0.60       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.42/0.60  thf('55', plain,
% 0.42/0.60      (![X76 : $i, X77 : $i]:
% 0.42/0.60         (((X76) = (k7_relat_1 @ X76 @ X77))
% 0.42/0.60          | ~ (v4_relat_1 @ X76 @ X77)
% 0.42/0.60          | ~ (v1_relat_1 @ X76))),
% 0.42/0.60      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.42/0.60  thf('56', plain,
% 0.42/0.60      ((~ (v1_relat_1 @ sk_D)
% 0.42/0.60        | ((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['54', '55'])).
% 0.42/0.60  thf('57', plain, ((v1_relat_1 @ sk_D)),
% 0.42/0.60      inference('demod', [status(thm)], ['41', '42'])).
% 0.42/0.60  thf('58', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 0.42/0.60      inference('demod', [status(thm)], ['56', '57'])).
% 0.42/0.60  thf(t148_relat_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( v1_relat_1 @ B ) =>
% 0.42/0.60       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.42/0.60  thf('59', plain,
% 0.42/0.60      (![X73 : $i, X74 : $i]:
% 0.42/0.60         (((k2_relat_1 @ (k7_relat_1 @ X73 @ X74)) = (k9_relat_1 @ X73 @ X74))
% 0.42/0.60          | ~ (v1_relat_1 @ X73))),
% 0.42/0.60      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.42/0.60  thf('60', plain,
% 0.42/0.60      ((((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ (k1_tarski @ sk_A)))
% 0.42/0.60        | ~ (v1_relat_1 @ sk_D))),
% 0.42/0.60      inference('sup+', [status(thm)], ['58', '59'])).
% 0.42/0.60  thf('61', plain, ((v1_relat_1 @ sk_D)),
% 0.42/0.60      inference('demod', [status(thm)], ['41', '42'])).
% 0.42/0.60  thf('62', plain,
% 0.42/0.60      (((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 0.42/0.60      inference('demod', [status(thm)], ['60', '61'])).
% 0.42/0.60  thf('63', plain,
% 0.42/0.60      ((((k2_relat_1 @ sk_D) = (k11_relat_1 @ sk_D @ sk_A))
% 0.42/0.60        | ~ (v1_relat_1 @ sk_D))),
% 0.42/0.60      inference('sup+', [status(thm)], ['53', '62'])).
% 0.42/0.60  thf('64', plain, ((v1_relat_1 @ sk_D)),
% 0.42/0.60      inference('demod', [status(thm)], ['41', '42'])).
% 0.42/0.60  thf('65', plain, (((k2_relat_1 @ sk_D) = (k11_relat_1 @ sk_D @ sk_A))),
% 0.42/0.60      inference('demod', [status(thm)], ['63', '64'])).
% 0.42/0.60  thf('66', plain,
% 0.42/0.60      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.42/0.60        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.42/0.60      inference('demod', [status(thm)], ['52', '65'])).
% 0.42/0.60  thf('67', plain,
% 0.42/0.60      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.42/0.60          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.42/0.60      inference('demod', [status(thm)], ['0', '3'])).
% 0.42/0.60  thf('68', plain,
% 0.42/0.60      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.42/0.60        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['66', '67'])).
% 0.42/0.60  thf('69', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 0.42/0.60      inference('demod', [status(thm)], ['56', '57'])).
% 0.42/0.60  thf('70', plain,
% 0.42/0.60      (![X73 : $i, X74 : $i]:
% 0.42/0.60         (((k2_relat_1 @ (k7_relat_1 @ X73 @ X74)) = (k9_relat_1 @ X73 @ X74))
% 0.42/0.60          | ~ (v1_relat_1 @ X73))),
% 0.42/0.60      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.42/0.60  thf(t144_relat_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( v1_relat_1 @ B ) =>
% 0.42/0.60       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.42/0.60  thf('71', plain,
% 0.42/0.60      (![X71 : $i, X72 : $i]:
% 0.42/0.60         ((r1_tarski @ (k9_relat_1 @ X71 @ X72) @ (k2_relat_1 @ X71))
% 0.42/0.60          | ~ (v1_relat_1 @ X71))),
% 0.42/0.60      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.42/0.60  thf('72', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.60         ((r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 0.42/0.60           (k9_relat_1 @ X1 @ X0))
% 0.42/0.60          | ~ (v1_relat_1 @ X1)
% 0.42/0.60          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.42/0.60      inference('sup+', [status(thm)], ['70', '71'])).
% 0.42/0.60  thf('73', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (v1_relat_1 @ sk_D)
% 0.42/0.60          | ~ (v1_relat_1 @ sk_D)
% 0.42/0.60          | (r1_tarski @ 
% 0.42/0.60             (k9_relat_1 @ (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A)) @ X0) @ 
% 0.42/0.60             (k9_relat_1 @ sk_D @ (k1_tarski @ sk_A))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['69', '72'])).
% 0.42/0.60  thf('74', plain, ((v1_relat_1 @ sk_D)),
% 0.42/0.60      inference('demod', [status(thm)], ['41', '42'])).
% 0.42/0.60  thf('75', plain, ((v1_relat_1 @ sk_D)),
% 0.42/0.60      inference('demod', [status(thm)], ['41', '42'])).
% 0.42/0.60  thf('76', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 0.42/0.60      inference('demod', [status(thm)], ['56', '57'])).
% 0.42/0.60  thf('77', plain,
% 0.42/0.60      (((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 0.42/0.60      inference('demod', [status(thm)], ['60', '61'])).
% 0.42/0.60  thf('78', plain,
% 0.42/0.60      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D))),
% 0.42/0.60      inference('demod', [status(thm)], ['73', '74', '75', '76', '77'])).
% 0.42/0.60  thf('79', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.42/0.60      inference('demod', [status(thm)], ['68', '78'])).
% 0.42/0.60  thf(t113_zfmisc_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.42/0.60       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.42/0.60  thf('80', plain,
% 0.42/0.60      (![X36 : $i, X37 : $i]:
% 0.42/0.60         (((k2_zfmisc_1 @ X36 @ X37) = (k1_xboole_0))
% 0.42/0.60          | ((X36) != (k1_xboole_0)))),
% 0.42/0.60      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.42/0.60  thf('81', plain,
% 0.42/0.60      (![X37 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X37) = (k1_xboole_0))),
% 0.42/0.60      inference('simplify', [status(thm)], ['80'])).
% 0.42/0.60  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.42/0.60  thf('82', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.42/0.60      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.42/0.60  thf('83', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.42/0.60      inference('demod', [status(thm)], ['68', '78'])).
% 0.42/0.60  thf('84', plain,
% 0.42/0.60      (![X37 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X37) = (k1_xboole_0))),
% 0.42/0.60      inference('simplify', [status(thm)], ['80'])).
% 0.42/0.60  thf('85', plain, (((k1_xboole_0) = (sk_D))),
% 0.42/0.60      inference('demod', [status(thm)], ['14', '79', '81', '82', '83', '84'])).
% 0.42/0.60  thf(t150_relat_1, axiom,
% 0.42/0.60    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.42/0.60  thf('86', plain,
% 0.42/0.60      (![X75 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X75) = (k1_xboole_0))),
% 0.42/0.60      inference('cnf', [status(esa)], [t150_relat_1])).
% 0.42/0.60  thf('87', plain, (((k1_xboole_0) = (sk_D))),
% 0.42/0.60      inference('demod', [status(thm)], ['14', '79', '81', '82', '83', '84'])).
% 0.42/0.60  thf('88', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.42/0.60      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.42/0.60  thf('89', plain, ($false),
% 0.42/0.60      inference('demod', [status(thm)], ['4', '85', '86', '87', '88'])).
% 0.42/0.60  
% 0.42/0.60  % SZS output end Refutation
% 0.42/0.60  
% 0.42/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
