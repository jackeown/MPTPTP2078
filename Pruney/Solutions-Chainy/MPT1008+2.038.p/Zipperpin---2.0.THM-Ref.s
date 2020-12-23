%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DEi1SsREnz

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:36 EST 2020

% Result     : Theorem 1.76s
% Output     : Refutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 229 expanded)
%              Number of leaves         :   48 (  92 expanded)
%              Depth                    :   15
%              Number of atoms          : 1001 (2699 expanded)
%              Number of equality atoms :  118 ( 283 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X2 != X1 )
      | ( r2_hidden @ X2 @ X3 )
      | ( X3
       != ( k2_tarski @ X4 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('2',plain,(
    ! [X1: $i,X4: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X4 @ X1 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

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

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t22_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) )
      <=> ( ( k1_relset_1 @ B @ A @ C )
          = B ) ) ) )).

thf('5',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( ( k1_relset_1 @ X38 @ X39 @ X40 )
       != X38 )
      | ~ ( r2_hidden @ X41 @ X38 )
      | ( r2_hidden @ ( k4_tarski @ X41 @ ( sk_E @ X41 @ X40 ) ) @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[t22_relset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_C ) ) @ sk_C )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
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
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('8',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( v1_funct_2 @ X47 @ X45 @ X46 )
      | ( X45
        = ( k1_relset_1 @ X45 @ X46 @ X47 ) )
      | ~ ( zip_tseitin_1 @ X47 @ X46 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('9',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X43: $i,X44: $i] :
      ( ( zip_tseitin_0 @ X43 @ X44 )
      | ( X43 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( zip_tseitin_0 @ X48 @ X49 )
      | ( zip_tseitin_1 @ X50 @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('13',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['9','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_C ) ) @ sk_C )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['6','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_C ) ) @ sk_C ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( sk_E @ sk_A @ sk_C ) ) @ sk_C ),
    inference('sup-',[status(thm)],['3','19'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('21',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ~ ( r1_tarski @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('22',plain,(
    ~ ( r1_tarski @ sk_C @ ( k4_tarski @ sk_A @ ( sk_E @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('24',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v4_relat_1 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('25',plain,(
    v4_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('26',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v4_relat_1 @ X22 @ X23 )
      | ( r1_tarski @ ( k1_relat_1 @ X22 ) @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('29',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v1_relat_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('30',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['27','30'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('32',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k2_enumset1 @ X10 @ X10 @ X11 @ X12 )
      = ( k1_enumset1 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('33',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X8 @ X8 @ X9 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k2_enumset1 @ X10 @ X10 @ X11 @ X12 )
      = ( k1_enumset1 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t142_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) )
    <=> ~ ( ( D != k1_xboole_0 )
          & ( D
           != ( k1_tarski @ A ) )
          & ( D
           != ( k1_tarski @ B ) )
          & ( D
           != ( k1_tarski @ C ) )
          & ( D
           != ( k2_tarski @ A @ B ) )
          & ( D
           != ( k2_tarski @ B @ C ) )
          & ( D
           != ( k2_tarski @ A @ C ) )
          & ( D
           != ( k1_enumset1 @ A @ B @ C ) ) ) ) )).

thf('38',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X16
        = ( k1_enumset1 @ X13 @ X14 @ X15 ) )
      | ( X16
        = ( k2_tarski @ X13 @ X15 ) )
      | ( X16
        = ( k2_tarski @ X14 @ X15 ) )
      | ( X16
        = ( k2_tarski @ X13 @ X14 ) )
      | ( X16
        = ( k1_tarski @ X15 ) )
      | ( X16
        = ( k1_tarski @ X14 ) )
      | ( X16
        = ( k1_tarski @ X13 ) )
      | ( X16 = k1_xboole_0 )
      | ~ ( r1_tarski @ X16 @ ( k1_enumset1 @ X13 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t142_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X3
        = ( k1_tarski @ X2 ) )
      | ( X3
        = ( k1_tarski @ X1 ) )
      | ( X3
        = ( k1_tarski @ X0 ) )
      | ( X3
        = ( k2_tarski @ X2 @ X1 ) )
      | ( X3
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X3
        = ( k2_tarski @ X2 @ X0 ) )
      | ( X3
        = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_enumset1 @ X0 @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X8 @ X8 @ X9 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('42',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('43',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('44',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('45',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['40','41','42','43','44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','47'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('49',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k1_relat_1 @ X26 )
       != ( k1_tarski @ X25 ) )
      | ( ( k2_relat_1 @ X26 )
        = ( k1_tarski @ ( k1_funct_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C ) )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['50'])).

thf('52',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['28','29'])).

thf('54',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('57',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k2_relset_1 @ X36 @ X37 @ X35 )
        = ( k2_relat_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('58',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','58'])).

thf('60',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['54','59'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('61',plain,(
    ! [X24: $i] :
      ( ( ( k1_relat_1 @ X24 )
       != k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('62',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['28','29'])).

thf('64',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['64'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('67',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('68',plain,(
    $false ),
    inference(demod,[status(thm)],['22','65','66','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DEi1SsREnz
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:27:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.76/1.96  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.76/1.96  % Solved by: fo/fo7.sh
% 1.76/1.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.76/1.96  % done 1130 iterations in 1.489s
% 1.76/1.96  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.76/1.96  % SZS output start Refutation
% 1.76/1.96  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.76/1.96  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.76/1.96  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.76/1.96  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.76/1.96  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.76/1.96  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.76/1.96  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.76/1.96  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.76/1.96  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.76/1.96  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.76/1.96  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.76/1.96  thf(sk_C_type, type, sk_C: $i).
% 1.76/1.96  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.76/1.96  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.76/1.96  thf(sk_B_type, type, sk_B: $i).
% 1.76/1.96  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.76/1.96  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.76/1.96  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.76/1.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.76/1.96  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.76/1.96  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.76/1.96  thf(sk_E_type, type, sk_E: $i > $i > $i).
% 1.76/1.96  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.76/1.96  thf(sk_A_type, type, sk_A: $i).
% 1.76/1.96  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.76/1.96  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.76/1.96  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.76/1.96  thf(t69_enumset1, axiom,
% 1.76/1.96    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.76/1.96  thf('0', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 1.76/1.96      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.76/1.96  thf(d2_tarski, axiom,
% 1.76/1.96    (![A:$i,B:$i,C:$i]:
% 1.76/1.96     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 1.76/1.96       ( ![D:$i]:
% 1.76/1.96         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 1.76/1.96  thf('1', plain,
% 1.76/1.96      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.76/1.96         (((X2) != (X1))
% 1.76/1.96          | (r2_hidden @ X2 @ X3)
% 1.76/1.96          | ((X3) != (k2_tarski @ X4 @ X1)))),
% 1.76/1.96      inference('cnf', [status(esa)], [d2_tarski])).
% 1.76/1.96  thf('2', plain,
% 1.76/1.96      (![X1 : $i, X4 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X4 @ X1))),
% 1.76/1.96      inference('simplify', [status(thm)], ['1'])).
% 1.76/1.96  thf('3', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.76/1.96      inference('sup+', [status(thm)], ['0', '2'])).
% 1.76/1.96  thf(t62_funct_2, conjecture,
% 1.76/1.96    (![A:$i,B:$i,C:$i]:
% 1.76/1.96     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 1.76/1.96         ( m1_subset_1 @
% 1.76/1.96           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 1.76/1.96       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 1.76/1.96         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 1.76/1.96           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 1.76/1.96  thf(zf_stmt_0, negated_conjecture,
% 1.76/1.96    (~( ![A:$i,B:$i,C:$i]:
% 1.76/1.96        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 1.76/1.96            ( m1_subset_1 @
% 1.76/1.96              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 1.76/1.96          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 1.76/1.96            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 1.76/1.96              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 1.76/1.96    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 1.76/1.96  thf('4', plain,
% 1.76/1.96      ((m1_subset_1 @ sk_C @ 
% 1.76/1.96        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.76/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.96  thf(t22_relset_1, axiom,
% 1.76/1.96    (![A:$i,B:$i,C:$i]:
% 1.76/1.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 1.76/1.96       ( ( ![D:$i]:
% 1.76/1.96           ( ~( ( r2_hidden @ D @ B ) & 
% 1.76/1.96                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 1.76/1.96         ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ))).
% 1.76/1.96  thf('5', plain,
% 1.76/1.96      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 1.76/1.96         (((k1_relset_1 @ X38 @ X39 @ X40) != (X38))
% 1.76/1.96          | ~ (r2_hidden @ X41 @ X38)
% 1.76/1.96          | (r2_hidden @ (k4_tarski @ X41 @ (sk_E @ X41 @ X40)) @ X40)
% 1.76/1.96          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 1.76/1.96      inference('cnf', [status(esa)], [t22_relset_1])).
% 1.76/1.96  thf('6', plain,
% 1.76/1.96      (![X0 : $i]:
% 1.76/1.96         ((r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_C)) @ sk_C)
% 1.76/1.96          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 1.76/1.96          | ((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)
% 1.76/1.96              != (k1_tarski @ sk_A)))),
% 1.76/1.96      inference('sup-', [status(thm)], ['4', '5'])).
% 1.76/1.96  thf('7', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B)),
% 1.76/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.96  thf(d1_funct_2, axiom,
% 1.76/1.96    (![A:$i,B:$i,C:$i]:
% 1.76/1.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.76/1.96       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.76/1.96           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.76/1.96             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.76/1.96         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.76/1.96           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.76/1.96             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.76/1.96  thf(zf_stmt_1, axiom,
% 1.76/1.96    (![C:$i,B:$i,A:$i]:
% 1.76/1.96     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.76/1.96       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.76/1.96  thf('8', plain,
% 1.76/1.96      (![X45 : $i, X46 : $i, X47 : $i]:
% 1.76/1.96         (~ (v1_funct_2 @ X47 @ X45 @ X46)
% 1.76/1.96          | ((X45) = (k1_relset_1 @ X45 @ X46 @ X47))
% 1.76/1.96          | ~ (zip_tseitin_1 @ X47 @ X46 @ X45))),
% 1.76/1.96      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.76/1.96  thf('9', plain,
% 1.76/1.96      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 1.76/1.96        | ((k1_tarski @ sk_A)
% 1.76/1.96            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)))),
% 1.76/1.96      inference('sup-', [status(thm)], ['7', '8'])).
% 1.76/1.96  thf(zf_stmt_2, axiom,
% 1.76/1.96    (![B:$i,A:$i]:
% 1.76/1.96     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.76/1.96       ( zip_tseitin_0 @ B @ A ) ))).
% 1.76/1.96  thf('10', plain,
% 1.76/1.96      (![X43 : $i, X44 : $i]:
% 1.76/1.96         ((zip_tseitin_0 @ X43 @ X44) | ((X43) = (k1_xboole_0)))),
% 1.76/1.96      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.76/1.96  thf('11', plain,
% 1.76/1.96      ((m1_subset_1 @ sk_C @ 
% 1.76/1.96        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.76/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.96  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.76/1.96  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.76/1.96  thf(zf_stmt_5, axiom,
% 1.76/1.96    (![A:$i,B:$i,C:$i]:
% 1.76/1.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.76/1.96       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.76/1.96         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.76/1.96           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.76/1.96             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.76/1.96  thf('12', plain,
% 1.76/1.96      (![X48 : $i, X49 : $i, X50 : $i]:
% 1.76/1.96         (~ (zip_tseitin_0 @ X48 @ X49)
% 1.76/1.96          | (zip_tseitin_1 @ X50 @ X48 @ X49)
% 1.76/1.96          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48))))),
% 1.76/1.96      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.76/1.96  thf('13', plain,
% 1.76/1.96      (((zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 1.76/1.96        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 1.76/1.96      inference('sup-', [status(thm)], ['11', '12'])).
% 1.76/1.96  thf('14', plain,
% 1.76/1.96      ((((sk_B) = (k1_xboole_0))
% 1.76/1.96        | (zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A)))),
% 1.76/1.96      inference('sup-', [status(thm)], ['10', '13'])).
% 1.76/1.96  thf('15', plain, (((sk_B) != (k1_xboole_0))),
% 1.76/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.96  thf('16', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))),
% 1.76/1.96      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 1.76/1.96  thf('17', plain,
% 1.76/1.96      (((k1_tarski @ sk_A) = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C))),
% 1.76/1.96      inference('demod', [status(thm)], ['9', '16'])).
% 1.76/1.96  thf('18', plain,
% 1.76/1.96      (![X0 : $i]:
% 1.76/1.96         ((r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_C)) @ sk_C)
% 1.76/1.96          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 1.76/1.96          | ((k1_tarski @ sk_A) != (k1_tarski @ sk_A)))),
% 1.76/1.96      inference('demod', [status(thm)], ['6', '17'])).
% 1.76/1.96  thf('19', plain,
% 1.76/1.96      (![X0 : $i]:
% 1.76/1.96         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 1.76/1.96          | (r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_C)) @ sk_C))),
% 1.76/1.96      inference('simplify', [status(thm)], ['18'])).
% 1.76/1.96  thf('20', plain,
% 1.76/1.96      ((r2_hidden @ (k4_tarski @ sk_A @ (sk_E @ sk_A @ sk_C)) @ sk_C)),
% 1.76/1.96      inference('sup-', [status(thm)], ['3', '19'])).
% 1.76/1.96  thf(t7_ordinal1, axiom,
% 1.76/1.96    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.76/1.96  thf('21', plain,
% 1.76/1.96      (![X27 : $i, X28 : $i]:
% 1.76/1.96         (~ (r2_hidden @ X27 @ X28) | ~ (r1_tarski @ X28 @ X27))),
% 1.76/1.96      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.76/1.96  thf('22', plain,
% 1.76/1.96      (~ (r1_tarski @ sk_C @ (k4_tarski @ sk_A @ (sk_E @ sk_A @ sk_C)))),
% 1.76/1.96      inference('sup-', [status(thm)], ['20', '21'])).
% 1.76/1.96  thf('23', plain,
% 1.76/1.96      ((m1_subset_1 @ sk_C @ 
% 1.76/1.96        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.76/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.96  thf(cc2_relset_1, axiom,
% 1.76/1.96    (![A:$i,B:$i,C:$i]:
% 1.76/1.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.76/1.96       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.76/1.96  thf('24', plain,
% 1.76/1.96      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.76/1.96         ((v4_relat_1 @ X32 @ X33)
% 1.76/1.96          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 1.76/1.96      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.76/1.96  thf('25', plain, ((v4_relat_1 @ sk_C @ (k1_tarski @ sk_A))),
% 1.76/1.96      inference('sup-', [status(thm)], ['23', '24'])).
% 1.76/1.96  thf(d18_relat_1, axiom,
% 1.76/1.96    (![A:$i,B:$i]:
% 1.76/1.96     ( ( v1_relat_1 @ B ) =>
% 1.76/1.96       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.76/1.96  thf('26', plain,
% 1.76/1.96      (![X22 : $i, X23 : $i]:
% 1.76/1.96         (~ (v4_relat_1 @ X22 @ X23)
% 1.76/1.96          | (r1_tarski @ (k1_relat_1 @ X22) @ X23)
% 1.76/1.96          | ~ (v1_relat_1 @ X22))),
% 1.76/1.96      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.76/1.96  thf('27', plain,
% 1.76/1.96      ((~ (v1_relat_1 @ sk_C)
% 1.76/1.96        | (r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A)))),
% 1.76/1.96      inference('sup-', [status(thm)], ['25', '26'])).
% 1.76/1.96  thf('28', plain,
% 1.76/1.96      ((m1_subset_1 @ sk_C @ 
% 1.76/1.96        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.76/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.96  thf(cc1_relset_1, axiom,
% 1.76/1.96    (![A:$i,B:$i,C:$i]:
% 1.76/1.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.76/1.96       ( v1_relat_1 @ C ) ))).
% 1.76/1.96  thf('29', plain,
% 1.76/1.96      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.76/1.96         ((v1_relat_1 @ X29)
% 1.76/1.96          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 1.76/1.96      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.76/1.96  thf('30', plain, ((v1_relat_1 @ sk_C)),
% 1.76/1.96      inference('sup-', [status(thm)], ['28', '29'])).
% 1.76/1.96  thf('31', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A))),
% 1.76/1.96      inference('demod', [status(thm)], ['27', '30'])).
% 1.76/1.96  thf(t71_enumset1, axiom,
% 1.76/1.96    (![A:$i,B:$i,C:$i]:
% 1.76/1.96     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 1.76/1.96  thf('32', plain,
% 1.76/1.96      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.76/1.96         ((k2_enumset1 @ X10 @ X10 @ X11 @ X12)
% 1.76/1.96           = (k1_enumset1 @ X10 @ X11 @ X12))),
% 1.76/1.96      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.76/1.96  thf(t70_enumset1, axiom,
% 1.76/1.96    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.76/1.96  thf('33', plain,
% 1.76/1.96      (![X8 : $i, X9 : $i]:
% 1.76/1.96         ((k1_enumset1 @ X8 @ X8 @ X9) = (k2_tarski @ X8 @ X9))),
% 1.76/1.96      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.76/1.96  thf('34', plain,
% 1.76/1.96      (![X0 : $i, X1 : $i]:
% 1.76/1.96         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 1.76/1.96      inference('sup+', [status(thm)], ['32', '33'])).
% 1.76/1.96  thf('35', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 1.76/1.96      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.76/1.96  thf('36', plain,
% 1.76/1.96      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 1.76/1.96      inference('sup+', [status(thm)], ['34', '35'])).
% 1.76/1.96  thf('37', plain,
% 1.76/1.96      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.76/1.96         ((k2_enumset1 @ X10 @ X10 @ X11 @ X12)
% 1.76/1.96           = (k1_enumset1 @ X10 @ X11 @ X12))),
% 1.76/1.96      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.76/1.96  thf(t142_zfmisc_1, axiom,
% 1.76/1.96    (![A:$i,B:$i,C:$i,D:$i]:
% 1.76/1.96     ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.76/1.96       ( ~( ( ( D ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_tarski @ A ) ) & 
% 1.76/1.96            ( ( D ) != ( k1_tarski @ B ) ) & ( ( D ) != ( k1_tarski @ C ) ) & 
% 1.76/1.96            ( ( D ) != ( k2_tarski @ A @ B ) ) & 
% 1.76/1.96            ( ( D ) != ( k2_tarski @ B @ C ) ) & 
% 1.76/1.96            ( ( D ) != ( k2_tarski @ A @ C ) ) & 
% 1.76/1.96            ( ( D ) != ( k1_enumset1 @ A @ B @ C ) ) ) ) ))).
% 1.76/1.96  thf('38', plain,
% 1.76/1.96      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 1.76/1.96         (((X16) = (k1_enumset1 @ X13 @ X14 @ X15))
% 1.76/1.96          | ((X16) = (k2_tarski @ X13 @ X15))
% 1.76/1.96          | ((X16) = (k2_tarski @ X14 @ X15))
% 1.76/1.96          | ((X16) = (k2_tarski @ X13 @ X14))
% 1.76/1.96          | ((X16) = (k1_tarski @ X15))
% 1.76/1.96          | ((X16) = (k1_tarski @ X14))
% 1.76/1.96          | ((X16) = (k1_tarski @ X13))
% 1.76/1.96          | ((X16) = (k1_xboole_0))
% 1.76/1.96          | ~ (r1_tarski @ X16 @ (k1_enumset1 @ X13 @ X14 @ X15)))),
% 1.76/1.96      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 1.76/1.96  thf('39', plain,
% 1.76/1.96      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.76/1.96         (~ (r1_tarski @ X3 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0))
% 1.76/1.96          | ((X3) = (k1_xboole_0))
% 1.76/1.96          | ((X3) = (k1_tarski @ X2))
% 1.76/1.96          | ((X3) = (k1_tarski @ X1))
% 1.76/1.96          | ((X3) = (k1_tarski @ X0))
% 1.76/1.96          | ((X3) = (k2_tarski @ X2 @ X1))
% 1.76/1.96          | ((X3) = (k2_tarski @ X1 @ X0))
% 1.76/1.96          | ((X3) = (k2_tarski @ X2 @ X0))
% 1.76/1.96          | ((X3) = (k1_enumset1 @ X2 @ X1 @ X0)))),
% 1.76/1.96      inference('sup-', [status(thm)], ['37', '38'])).
% 1.76/1.96  thf('40', plain,
% 1.76/1.96      (![X0 : $i, X1 : $i]:
% 1.76/1.96         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 1.76/1.96          | ((X1) = (k1_enumset1 @ X0 @ X0 @ X0))
% 1.76/1.96          | ((X1) = (k2_tarski @ X0 @ X0))
% 1.76/1.96          | ((X1) = (k2_tarski @ X0 @ X0))
% 1.76/1.96          | ((X1) = (k2_tarski @ X0 @ X0))
% 1.76/1.96          | ((X1) = (k1_tarski @ X0))
% 1.76/1.96          | ((X1) = (k1_tarski @ X0))
% 1.76/1.96          | ((X1) = (k1_tarski @ X0))
% 1.76/1.96          | ((X1) = (k1_xboole_0)))),
% 1.76/1.96      inference('sup-', [status(thm)], ['36', '39'])).
% 1.76/1.96  thf('41', plain,
% 1.76/1.96      (![X8 : $i, X9 : $i]:
% 1.76/1.96         ((k1_enumset1 @ X8 @ X8 @ X9) = (k2_tarski @ X8 @ X9))),
% 1.76/1.96      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.76/1.96  thf('42', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 1.76/1.96      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.76/1.96  thf('43', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 1.76/1.96      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.76/1.96  thf('44', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 1.76/1.96      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.76/1.96  thf('45', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 1.76/1.96      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.76/1.96  thf('46', plain,
% 1.76/1.96      (![X0 : $i, X1 : $i]:
% 1.76/1.96         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 1.76/1.96          | ((X1) = (k1_tarski @ X0))
% 1.76/1.96          | ((X1) = (k1_tarski @ X0))
% 1.76/1.96          | ((X1) = (k1_tarski @ X0))
% 1.76/1.96          | ((X1) = (k1_tarski @ X0))
% 1.76/1.96          | ((X1) = (k1_tarski @ X0))
% 1.76/1.96          | ((X1) = (k1_tarski @ X0))
% 1.76/1.96          | ((X1) = (k1_tarski @ X0))
% 1.76/1.96          | ((X1) = (k1_xboole_0)))),
% 1.76/1.96      inference('demod', [status(thm)], ['40', '41', '42', '43', '44', '45'])).
% 1.76/1.96  thf('47', plain,
% 1.76/1.96      (![X0 : $i, X1 : $i]:
% 1.76/1.96         (((X1) = (k1_xboole_0))
% 1.76/1.96          | ((X1) = (k1_tarski @ X0))
% 1.76/1.96          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 1.76/1.96      inference('simplify', [status(thm)], ['46'])).
% 1.76/1.96  thf('48', plain,
% 1.76/1.96      ((((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 1.76/1.96        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 1.76/1.96      inference('sup-', [status(thm)], ['31', '47'])).
% 1.76/1.96  thf(t14_funct_1, axiom,
% 1.76/1.96    (![A:$i,B:$i]:
% 1.76/1.96     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.76/1.96       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 1.76/1.96         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 1.76/1.96  thf('49', plain,
% 1.76/1.96      (![X25 : $i, X26 : $i]:
% 1.76/1.96         (((k1_relat_1 @ X26) != (k1_tarski @ X25))
% 1.76/1.96          | ((k2_relat_1 @ X26) = (k1_tarski @ (k1_funct_1 @ X26 @ X25)))
% 1.76/1.96          | ~ (v1_funct_1 @ X26)
% 1.76/1.96          | ~ (v1_relat_1 @ X26))),
% 1.76/1.96      inference('cnf', [status(esa)], [t14_funct_1])).
% 1.76/1.96  thf('50', plain,
% 1.76/1.96      (![X0 : $i]:
% 1.76/1.96         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_C))
% 1.76/1.96          | ((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 1.76/1.96          | ~ (v1_relat_1 @ X0)
% 1.76/1.96          | ~ (v1_funct_1 @ X0)
% 1.76/1.96          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 1.76/1.96      inference('sup-', [status(thm)], ['48', '49'])).
% 1.76/1.96  thf('51', plain,
% 1.76/1.96      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 1.76/1.96        | ~ (v1_funct_1 @ sk_C)
% 1.76/1.96        | ~ (v1_relat_1 @ sk_C)
% 1.76/1.96        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 1.76/1.96      inference('eq_res', [status(thm)], ['50'])).
% 1.76/1.96  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 1.76/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.96  thf('53', plain, ((v1_relat_1 @ sk_C)),
% 1.76/1.96      inference('sup-', [status(thm)], ['28', '29'])).
% 1.76/1.96  thf('54', plain,
% 1.76/1.96      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 1.76/1.96        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 1.76/1.96      inference('demod', [status(thm)], ['51', '52', '53'])).
% 1.76/1.96  thf('55', plain,
% 1.76/1.96      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)
% 1.76/1.96         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 1.76/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.96  thf('56', plain,
% 1.76/1.96      ((m1_subset_1 @ sk_C @ 
% 1.76/1.96        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.76/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.96  thf(redefinition_k2_relset_1, axiom,
% 1.76/1.96    (![A:$i,B:$i,C:$i]:
% 1.76/1.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.76/1.96       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.76/1.96  thf('57', plain,
% 1.76/1.96      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.76/1.96         (((k2_relset_1 @ X36 @ X37 @ X35) = (k2_relat_1 @ X35))
% 1.76/1.96          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 1.76/1.96      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.76/1.96  thf('58', plain,
% 1.76/1.96      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.76/1.96      inference('sup-', [status(thm)], ['56', '57'])).
% 1.76/1.96  thf('59', plain,
% 1.76/1.96      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 1.76/1.96      inference('demod', [status(thm)], ['55', '58'])).
% 1.76/1.96  thf('60', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 1.76/1.96      inference('simplify_reflect-', [status(thm)], ['54', '59'])).
% 1.76/1.96  thf(t64_relat_1, axiom,
% 1.76/1.96    (![A:$i]:
% 1.76/1.96     ( ( v1_relat_1 @ A ) =>
% 1.76/1.96       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 1.76/1.96           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 1.76/1.96         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 1.76/1.96  thf('61', plain,
% 1.76/1.96      (![X24 : $i]:
% 1.76/1.96         (((k1_relat_1 @ X24) != (k1_xboole_0))
% 1.76/1.96          | ((X24) = (k1_xboole_0))
% 1.76/1.96          | ~ (v1_relat_1 @ X24))),
% 1.76/1.96      inference('cnf', [status(esa)], [t64_relat_1])).
% 1.76/1.96  thf('62', plain,
% 1.76/1.96      ((((k1_xboole_0) != (k1_xboole_0))
% 1.76/1.96        | ~ (v1_relat_1 @ sk_C)
% 1.76/1.96        | ((sk_C) = (k1_xboole_0)))),
% 1.76/1.96      inference('sup-', [status(thm)], ['60', '61'])).
% 1.76/1.96  thf('63', plain, ((v1_relat_1 @ sk_C)),
% 1.76/1.96      inference('sup-', [status(thm)], ['28', '29'])).
% 1.76/1.96  thf('64', plain,
% 1.76/1.96      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 1.76/1.96      inference('demod', [status(thm)], ['62', '63'])).
% 1.76/1.96  thf('65', plain, (((sk_C) = (k1_xboole_0))),
% 1.76/1.96      inference('simplify', [status(thm)], ['64'])).
% 1.76/1.96  thf('66', plain, (((sk_C) = (k1_xboole_0))),
% 1.76/1.96      inference('simplify', [status(thm)], ['64'])).
% 1.76/1.96  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.76/1.96  thf('67', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.76/1.96      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.76/1.96  thf('68', plain, ($false),
% 1.76/1.96      inference('demod', [status(thm)], ['22', '65', '66', '67'])).
% 1.76/1.96  
% 1.76/1.96  % SZS output end Refutation
% 1.76/1.96  
% 1.76/1.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
