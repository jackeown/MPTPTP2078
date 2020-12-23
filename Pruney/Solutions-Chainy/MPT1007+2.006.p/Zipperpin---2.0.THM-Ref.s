%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WUZT8pPQYB

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 318 expanded)
%              Number of leaves         :   46 ( 115 expanded)
%              Depth                    :   22
%              Number of atoms          :  909 (3513 expanded)
%              Number of equality atoms :   55 ( 222 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(t61_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_funct_2])).

thf('0',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
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
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( v1_funct_2 @ X47 @ X45 @ X46 )
      | ( X45
        = ( k1_relset_1 @ X45 @ X46 @ X47 ) )
      | ~ ( zip_tseitin_2 @ X47 @ X46 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,
    ( ~ ( zip_tseitin_2 @ sk_C @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf('3',plain,(
    ! [X43: $i,X44: $i] :
      ( ( zip_tseitin_1 @ X43 @ X44 )
      | ( X43 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
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
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( zip_tseitin_1 @ X48 @ X49 )
      | ( zip_tseitin_2 @ X50 @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_2 @ sk_C @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_C @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    zip_tseitin_2 @ sk_C @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( ( k1_relset_1 @ X41 @ X42 @ X40 )
        = ( k1_relat_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
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
    ! [X15: $i] :
      ( ( k2_tarski @ X15 @ X15 )
      = ( k1_tarski @ X15 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_enumset1 @ X16 @ X16 @ X17 )
      = ( k2_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X11 )
      | ( r2_hidden @ X8 @ X12 )
      | ( X12
       != ( k1_enumset1 @ X11 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('17',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X8 @ ( k1_enumset1 @ X11 @ X10 @ X9 ) )
      | ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X11 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 )
      | ~ ( v1_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
      | ( zip_tseitin_0 @ X0 @ sk_A @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','21'])).

thf('23',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('24',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( zip_tseitin_0 @ X4 @ X5 @ X6 @ X7 )
      | ( X4 = X5 )
      | ( X4 = X6 )
      | ( X4 = X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('25',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('26',plain,(
    ! [X15: $i] :
      ( ( k2_tarski @ X15 @ X15 )
      = ( k1_tarski @ X15 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('27',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_enumset1 @ X16 @ X16 @ X17 )
      = ( k2_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('28',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( zip_tseitin_0 @ X13 @ X9 @ X10 @ X11 )
      | ( X12
       != ( k1_enumset1 @ X11 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('29',plain,(
    ! [X9: $i,X10: $i,X11: $i,X13: $i] :
      ( ~ ( zip_tseitin_0 @ X13 @ X9 @ X10 @ X11 )
      | ~ ( r2_hidden @ X13 @ ( k1_enumset1 @ X11 @ X10 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( sk_B @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( ( sk_B @ ( k1_relat_1 @ sk_C ) )
      = sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['23','34'])).

thf('36',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('37',plain,
    ( ( ( sk_B @ ( k1_relat_1 @ sk_C ) )
      = sk_A )
    | ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('39',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('41',plain,(
    ! [X24: $i,X25: $i,X27: $i] :
      ( ~ ( r2_hidden @ X24 @ ( k1_relat_1 @ X25 ) )
      | ( r2_hidden @ ( k4_tarski @ X24 @ X27 ) @ X25 )
      | ( X27
       != ( k1_funct_1 @ X25 @ X24 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('42',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_funct_1 @ X25 )
      | ( r2_hidden @ ( k4_tarski @ X24 @ ( k1_funct_1 @ X25 @ X24 ) ) @ X25 )
      | ~ ( r2_hidden @ X24 @ ( k1_relat_1 @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('46',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v1_relat_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('47',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['43','44','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('50',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('52',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_xboole_0 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X37 ) ) )
      | ( v1_xboole_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('53',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('55',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v5_relat_1 @ X34 @ X36 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('56',plain,(
    v5_relat_1 @ sk_C @ sk_B_1 ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf(t176_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v5_relat_1 @ C @ A )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) )
       => ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ) )).

thf('58',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X28 @ ( k1_relat_1 @ X29 ) )
      | ( m1_subset_1 @ ( k1_funct_1 @ X29 @ X28 ) @ X30 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v5_relat_1 @ X29 @ X30 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t176_funct_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v5_relat_1 @ sk_C @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( m1_subset_1 @ ( k1_funct_1 @ sk_C @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('61',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
      | ~ ( v5_relat_1 @ sk_C @ X0 )
      | ( m1_subset_1 @ ( k1_funct_1 @ sk_C @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( m1_subset_1 @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_1 )
    | ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('64',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r2_hidden @ X21 @ X22 )
      | ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('65',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
      | ( zip_tseitin_0 @ X0 @ sk_A @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','21'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( zip_tseitin_0 @ X0 @ sk_A @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X4 != X3 )
      | ~ ( zip_tseitin_0 @ X4 @ X5 @ X6 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('71',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ~ ( zip_tseitin_0 @ X3 @ X5 @ X6 @ X3 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['69','71'])).

thf('73',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['53','72'])).

thf('74',plain,(
    v1_xboole_0 @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['50','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ sk_A @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['22','74'])).

thf('76',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ~ ( zip_tseitin_0 @ X3 @ X5 @ X6 @ X3 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('77',plain,(
    $false ),
    inference('sup-',[status(thm)],['75','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WUZT8pPQYB
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:17:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 156 iterations in 0.102s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.55  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.55  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.55  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.20/0.55  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.55  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.55  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.55  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.20/0.55  thf(t61_funct_2, conjecture,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.20/0.55         ( m1_subset_1 @
% 0.20/0.55           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.20/0.55       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.55         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.55        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.20/0.55            ( m1_subset_1 @
% 0.20/0.55              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.20/0.55          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.55            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.20/0.55  thf('0', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(d1_funct_2, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.55       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.55           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.20/0.55             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.55         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.55           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.20/0.55             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_1, axiom,
% 0.20/0.55    (![C:$i,B:$i,A:$i]:
% 0.20/0.55     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.20/0.55       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.20/0.55         (~ (v1_funct_2 @ X47 @ X45 @ X46)
% 0.20/0.55          | ((X45) = (k1_relset_1 @ X45 @ X46 @ X47))
% 0.20/0.55          | ~ (zip_tseitin_2 @ X47 @ X46 @ X45))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      ((~ (zip_tseitin_2 @ sk_C @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.20/0.55        | ((k1_tarski @ sk_A)
% 0.20/0.55            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.55  thf(zf_stmt_2, axiom,
% 0.20/0.55    (![B:$i,A:$i]:
% 0.20/0.55     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.55       ( zip_tseitin_1 @ B @ A ) ))).
% 0.20/0.55  thf('3', plain,
% 0.20/0.55      (![X43 : $i, X44 : $i]:
% 0.20/0.55         ((zip_tseitin_1 @ X43 @ X44) | ((X43) = (k1_xboole_0)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.55  thf('4', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ 
% 0.20/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.20/0.55  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $o).
% 0.20/0.55  thf(zf_stmt_5, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.55       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.20/0.55         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.55           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.55             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.20/0.55  thf('5', plain,
% 0.20/0.55      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.20/0.55         (~ (zip_tseitin_1 @ X48 @ X49)
% 0.20/0.55          | (zip_tseitin_2 @ X50 @ X48 @ X49)
% 0.20/0.55          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.55  thf('6', plain,
% 0.20/0.55      (((zip_tseitin_2 @ sk_C @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.20/0.55        | ~ (zip_tseitin_1 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.55  thf('7', plain,
% 0.20/0.55      ((((sk_B_1) = (k1_xboole_0))
% 0.20/0.55        | (zip_tseitin_2 @ sk_C @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['3', '6'])).
% 0.20/0.55  thf('8', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('9', plain, ((zip_tseitin_2 @ sk_C @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.20/0.55  thf('10', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ 
% 0.20/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.55       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.55  thf('11', plain,
% 0.20/0.55      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.20/0.55         (((k1_relset_1 @ X41 @ X42 @ X40) = (k1_relat_1 @ X40))
% 0.20/0.55          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 0.20/0.55      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.55  thf('12', plain,
% 0.20/0.55      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.55         = (k1_relat_1 @ sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.55  thf('13', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.20/0.55      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.20/0.55  thf(t69_enumset1, axiom,
% 0.20/0.55    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.55  thf('14', plain,
% 0.20/0.55      (![X15 : $i]: ((k2_tarski @ X15 @ X15) = (k1_tarski @ X15))),
% 0.20/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.55  thf(t70_enumset1, axiom,
% 0.20/0.55    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.55  thf('15', plain,
% 0.20/0.55      (![X16 : $i, X17 : $i]:
% 0.20/0.55         ((k1_enumset1 @ X16 @ X16 @ X17) = (k2_tarski @ X16 @ X17))),
% 0.20/0.55      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.55  thf(d1_enumset1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.55     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.55       ( ![E:$i]:
% 0.20/0.55         ( ( r2_hidden @ E @ D ) <=>
% 0.20/0.55           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.55  thf(zf_stmt_7, axiom,
% 0.20/0.55    (![E:$i,C:$i,B:$i,A:$i]:
% 0.20/0.55     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.20/0.55       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_8, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.55     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.55       ( ![E:$i]:
% 0.20/0.55         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.55         ((zip_tseitin_0 @ X8 @ X9 @ X10 @ X11)
% 0.20/0.55          | (r2_hidden @ X8 @ X12)
% 0.20/0.55          | ((X12) != (k1_enumset1 @ X11 @ X10 @ X9)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.20/0.55  thf('17', plain,
% 0.20/0.55      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.55         ((r2_hidden @ X8 @ (k1_enumset1 @ X11 @ X10 @ X9))
% 0.20/0.55          | (zip_tseitin_0 @ X8 @ X9 @ X10 @ X11))),
% 0.20/0.55      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.55  thf(d1_xboole_0, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.55  thf('18', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.55  thf('19', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.55         ((zip_tseitin_0 @ X3 @ X0 @ X1 @ X2)
% 0.20/0.55          | ~ (v1_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.55  thf('20', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         (~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))
% 0.20/0.55          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['15', '19'])).
% 0.20/0.55  thf('21', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (v1_xboole_0 @ (k1_tarski @ X0))
% 0.20/0.55          | (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['14', '20'])).
% 0.20/0.55  thf('22', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.20/0.55          | (zip_tseitin_0 @ X0 @ sk_A @ sk_A @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['13', '21'])).
% 0.20/0.55  thf('23', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.20/0.55      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.20/0.55  thf('24', plain,
% 0.20/0.55      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.55         ((zip_tseitin_0 @ X4 @ X5 @ X6 @ X7)
% 0.20/0.55          | ((X4) = (X5))
% 0.20/0.55          | ((X4) = (X6))
% 0.20/0.55          | ((X4) = (X7)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.20/0.55  thf('25', plain,
% 0.20/0.55      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.55  thf('26', plain,
% 0.20/0.55      (![X15 : $i]: ((k2_tarski @ X15 @ X15) = (k1_tarski @ X15))),
% 0.20/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.55  thf('27', plain,
% 0.20/0.55      (![X16 : $i, X17 : $i]:
% 0.20/0.55         ((k1_enumset1 @ X16 @ X16 @ X17) = (k2_tarski @ X16 @ X17))),
% 0.20/0.55      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.55  thf('28', plain,
% 0.20/0.55      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X13 @ X12)
% 0.20/0.55          | ~ (zip_tseitin_0 @ X13 @ X9 @ X10 @ X11)
% 0.20/0.55          | ((X12) != (k1_enumset1 @ X11 @ X10 @ X9)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.20/0.55  thf('29', plain,
% 0.20/0.55      (![X9 : $i, X10 : $i, X11 : $i, X13 : $i]:
% 0.20/0.55         (~ (zip_tseitin_0 @ X13 @ X9 @ X10 @ X11)
% 0.20/0.55          | ~ (r2_hidden @ X13 @ (k1_enumset1 @ X11 @ X10 @ X9)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.55  thf('30', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.20/0.55          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['27', '29'])).
% 0.20/0.55  thf('31', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.20/0.55          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['26', '30'])).
% 0.20/0.55  thf('32', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v1_xboole_0 @ (k1_tarski @ X0))
% 0.20/0.55          | ~ (zip_tseitin_0 @ (sk_B @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['25', '31'])).
% 0.20/0.55  thf('33', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((sk_B @ (k1_tarski @ X0)) = (X0))
% 0.20/0.55          | ((sk_B @ (k1_tarski @ X0)) = (X0))
% 0.20/0.55          | ((sk_B @ (k1_tarski @ X0)) = (X0))
% 0.20/0.55          | (v1_xboole_0 @ (k1_tarski @ X0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['24', '32'])).
% 0.20/0.55  thf('34', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v1_xboole_0 @ (k1_tarski @ X0)) | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['33'])).
% 0.20/0.55  thf('35', plain,
% 0.20/0.55      ((((sk_B @ (k1_relat_1 @ sk_C)) = (sk_A))
% 0.20/0.55        | (v1_xboole_0 @ (k1_tarski @ sk_A)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['23', '34'])).
% 0.20/0.55  thf('36', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.20/0.55      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.20/0.55  thf('37', plain,
% 0.20/0.55      ((((sk_B @ (k1_relat_1 @ sk_C)) = (sk_A))
% 0.20/0.55        | (v1_xboole_0 @ (k1_relat_1 @ sk_C)))),
% 0.20/0.55      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.55  thf('38', plain,
% 0.20/0.55      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.55  thf('39', plain,
% 0.20/0.55      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))
% 0.20/0.55        | (v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.20/0.55        | (v1_xboole_0 @ (k1_relat_1 @ sk_C)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['37', '38'])).
% 0.20/0.55  thf('40', plain,
% 0.20/0.55      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.20/0.55        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['39'])).
% 0.20/0.55  thf(d4_funct_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.55       ( ![B:$i,C:$i]:
% 0.20/0.55         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.20/0.55             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.20/0.55               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.55           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.20/0.55             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.20/0.55               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.20/0.55  thf('41', plain,
% 0.20/0.55      (![X24 : $i, X25 : $i, X27 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X24 @ (k1_relat_1 @ X25))
% 0.20/0.55          | (r2_hidden @ (k4_tarski @ X24 @ X27) @ X25)
% 0.20/0.55          | ((X27) != (k1_funct_1 @ X25 @ X24))
% 0.20/0.55          | ~ (v1_funct_1 @ X25)
% 0.20/0.55          | ~ (v1_relat_1 @ X25))),
% 0.20/0.55      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.20/0.55  thf('42', plain,
% 0.20/0.55      (![X24 : $i, X25 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X25)
% 0.20/0.55          | ~ (v1_funct_1 @ X25)
% 0.20/0.55          | (r2_hidden @ (k4_tarski @ X24 @ (k1_funct_1 @ X25 @ X24)) @ X25)
% 0.20/0.55          | ~ (r2_hidden @ X24 @ (k1_relat_1 @ X25)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['41'])).
% 0.20/0.55  thf('43', plain,
% 0.20/0.55      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.20/0.55        | (r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C @ sk_A)) @ sk_C)
% 0.20/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.55        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['40', '42'])).
% 0.20/0.55  thf('44', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('45', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ 
% 0.20/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(cc1_relset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.55       ( v1_relat_1 @ C ) ))).
% 0.20/0.55  thf('46', plain,
% 0.20/0.55      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.20/0.55         ((v1_relat_1 @ X31)
% 0.20/0.55          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.20/0.55      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.55  thf('47', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.55      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.55  thf('48', plain,
% 0.20/0.55      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.20/0.55        | (r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C @ sk_A)) @ sk_C))),
% 0.20/0.55      inference('demod', [status(thm)], ['43', '44', '47'])).
% 0.20/0.55  thf('49', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.55  thf('50', plain,
% 0.20/0.55      (((v1_xboole_0 @ (k1_relat_1 @ sk_C)) | ~ (v1_xboole_0 @ sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.55  thf('51', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ 
% 0.20/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(cc4_relset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( v1_xboole_0 @ A ) =>
% 0.20/0.55       ( ![C:$i]:
% 0.20/0.55         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.20/0.55           ( v1_xboole_0 @ C ) ) ) ))).
% 0.20/0.55  thf('52', plain,
% 0.20/0.55      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.20/0.55         (~ (v1_xboole_0 @ X37)
% 0.20/0.55          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X37)))
% 0.20/0.55          | (v1_xboole_0 @ X38))),
% 0.20/0.55      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.20/0.55  thf('53', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.55  thf('54', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ 
% 0.20/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(cc2_relset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.55       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.55  thf('55', plain,
% 0.20/0.55      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.20/0.55         ((v5_relat_1 @ X34 @ X36)
% 0.20/0.55          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.20/0.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.55  thf('56', plain, ((v5_relat_1 @ sk_C @ sk_B_1)),
% 0.20/0.55      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.55  thf('57', plain,
% 0.20/0.55      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.20/0.55        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['39'])).
% 0.20/0.55  thf(t176_funct_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.55       ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) =>
% 0.20/0.55         ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ))).
% 0.20/0.55  thf('58', plain,
% 0.20/0.55      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X28 @ (k1_relat_1 @ X29))
% 0.20/0.55          | (m1_subset_1 @ (k1_funct_1 @ X29 @ X28) @ X30)
% 0.20/0.55          | ~ (v1_funct_1 @ X29)
% 0.20/0.55          | ~ (v5_relat_1 @ X29 @ X30)
% 0.20/0.55          | ~ (v1_relat_1 @ X29))),
% 0.20/0.55      inference('cnf', [status(esa)], [t176_funct_1])).
% 0.20/0.55  thf('59', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.20/0.55          | ~ (v1_relat_1 @ sk_C)
% 0.20/0.55          | ~ (v5_relat_1 @ sk_C @ X0)
% 0.20/0.55          | ~ (v1_funct_1 @ sk_C)
% 0.20/0.55          | (m1_subset_1 @ (k1_funct_1 @ sk_C @ sk_A) @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['57', '58'])).
% 0.20/0.55  thf('60', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.55      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.55  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('62', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.20/0.55          | ~ (v5_relat_1 @ sk_C @ X0)
% 0.20/0.55          | (m1_subset_1 @ (k1_funct_1 @ sk_C @ sk_A) @ X0))),
% 0.20/0.55      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.20/0.55  thf('63', plain,
% 0.20/0.55      (((m1_subset_1 @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_1)
% 0.20/0.55        | (v1_xboole_0 @ (k1_relat_1 @ sk_C)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['56', '62'])).
% 0.20/0.55  thf(t2_subset, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.55       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.55  thf('64', plain,
% 0.20/0.55      (![X21 : $i, X22 : $i]:
% 0.20/0.55         ((r2_hidden @ X21 @ X22)
% 0.20/0.55          | (v1_xboole_0 @ X22)
% 0.20/0.55          | ~ (m1_subset_1 @ X21 @ X22))),
% 0.20/0.55      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.55  thf('65', plain,
% 0.20/0.55      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.20/0.55        | (v1_xboole_0 @ sk_B_1)
% 0.20/0.55        | (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.55  thf('66', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('67', plain,
% 0.20/0.55      (((v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ (k1_relat_1 @ sk_C)))),
% 0.20/0.55      inference('clc', [status(thm)], ['65', '66'])).
% 0.20/0.55  thf('68', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.20/0.55          | (zip_tseitin_0 @ X0 @ sk_A @ sk_A @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['13', '21'])).
% 0.20/0.55  thf('69', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v1_xboole_0 @ sk_B_1) | (zip_tseitin_0 @ X0 @ sk_A @ sk_A @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['67', '68'])).
% 0.20/0.55  thf('70', plain,
% 0.20/0.55      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.55         (((X4) != (X3)) | ~ (zip_tseitin_0 @ X4 @ X5 @ X6 @ X3))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.20/0.55  thf('71', plain,
% 0.20/0.55      (![X3 : $i, X5 : $i, X6 : $i]: ~ (zip_tseitin_0 @ X3 @ X5 @ X6 @ X3)),
% 0.20/0.55      inference('simplify', [status(thm)], ['70'])).
% 0.20/0.55  thf('72', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.20/0.55      inference('sup-', [status(thm)], ['69', '71'])).
% 0.20/0.55  thf('73', plain, ((v1_xboole_0 @ sk_C)),
% 0.20/0.55      inference('demod', [status(thm)], ['53', '72'])).
% 0.20/0.55  thf('74', plain, ((v1_xboole_0 @ (k1_relat_1 @ sk_C))),
% 0.20/0.55      inference('demod', [status(thm)], ['50', '73'])).
% 0.20/0.55  thf('75', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ sk_A @ sk_A @ sk_A)),
% 0.20/0.55      inference('demod', [status(thm)], ['22', '74'])).
% 0.20/0.55  thf('76', plain,
% 0.20/0.55      (![X3 : $i, X5 : $i, X6 : $i]: ~ (zip_tseitin_0 @ X3 @ X5 @ X6 @ X3)),
% 0.20/0.55      inference('simplify', [status(thm)], ['70'])).
% 0.20/0.55  thf('77', plain, ($false), inference('sup-', [status(thm)], ['75', '76'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
