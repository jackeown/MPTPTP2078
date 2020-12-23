%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FEHssGe9uo

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:03 EST 2020

% Result     : Theorem 8.77s
% Output     : Refutation 8.77s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 416 expanded)
%              Number of leaves         :   52 ( 145 expanded)
%              Depth                    :   34
%              Number of atoms          : 1388 (4626 expanded)
%              Number of equality atoms :   91 ( 242 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

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
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 @ sk_C_1 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X99: $i,X100: $i,X101: $i,X102: $i] :
      ( ~ ( m1_subset_1 @ X99 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X100 @ X101 ) ) )
      | ( ( k7_relset_1 @ X100 @ X101 @ X99 @ X102 )
        = ( k9_relat_1 @ X99 @ X102 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C_1 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('5',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k2_zfmisc_1 @ X37 @ X38 )
        = k1_xboole_0 )
      | ( X37 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('6',plain,(
    ! [X38: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X38 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(d3_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( F
        = ( k3_enumset1 @ A @ B @ C @ D @ E ) )
    <=> ! [G: $i] :
          ( ( r2_hidden @ G @ F )
        <=> ~ ( ( G != E )
              & ( G != D )
              & ( G != C )
              & ( G != B )
              & ( G != A ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [G: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A )
    <=> ( ( G != A )
        & ( G != B )
        & ( G != C )
        & ( G != D )
        & ( G != E ) ) ) )).

thf('7',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( zip_tseitin_0 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 )
      | ( X40 = X41 )
      | ( X40 = X42 )
      | ( X40 = X43 )
      | ( X40 = X44 )
      | ( X40 = X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X89: $i,X90: $i,X91: $i] :
      ( ( v4_relat_1 @ X89 @ X90 )
      | ~ ( m1_subset_1 @ X89 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X90 @ X91 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('11',plain,(
    v4_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('12',plain,(
    ! [X66: $i,X67: $i] :
      ( ~ ( v4_relat_1 @ X66 @ X67 )
      | ( r1_tarski @ ( k1_relat_1 @ X66 ) @ X67 )
      | ~ ( v1_relat_1 @ X66 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('15',plain,(
    ! [X64: $i,X65: $i] :
      ( ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ X65 ) )
      | ( v1_relat_1 @ X64 )
      | ~ ( v1_relat_1 @ X65 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('17',plain,(
    ! [X68: $i,X69: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('18',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','21'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('23',plain,(
    ! [X8: $i] :
      ( ( k2_tarski @ X8 @ X8 )
      = ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('24',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_enumset1 @ X9 @ X9 @ X10 )
      = ( k2_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('25',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X11 @ X11 @ X12 @ X13 )
      = ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('26',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k3_enumset1 @ X14 @ X14 @ X15 @ X16 @ X17 )
      = ( k2_enumset1 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( F
        = ( k3_enumset1 @ A @ B @ C @ D @ E ) )
    <=> ! [G: $i] :
          ( ( r2_hidden @ G @ F )
        <=> ~ ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ~ ( r2_hidden @ X53 @ X52 )
      | ~ ( zip_tseitin_0 @ X53 @ X47 @ X48 @ X49 @ X50 @ X51 )
      | ( X52
       != ( k3_enumset1 @ X51 @ X50 @ X49 @ X48 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('28',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X53: $i] :
      ( ~ ( zip_tseitin_0 @ X53 @ X47 @ X48 @ X49 @ X50 @ X51 )
      | ~ ( r2_hidden @ X53 @ ( k3_enumset1 @ X51 @ X50 @ X49 @ X48 @ X47 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2 ) ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ X0 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
        = sk_A )
      | ( ( sk_C @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
        = sk_A )
      | ( ( sk_C @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
        = sk_A )
      | ( ( sk_C @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
        = sk_A )
      | ( ( sk_C @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
        = sk_A )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ X0 )
      | ( ( sk_C @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
        = sk_A ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ X0 )
      | ( ( sk_C @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
        = sk_A ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('37',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('38',plain,(
    ! [X56: $i,X57: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X56 ) @ ( k1_zfmisc_1 @ X57 ) )
      | ~ ( r2_hidden @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('40',plain,(
    ! [X58: $i,X59: $i] :
      ( ( r1_tarski @ X58 @ X59 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ X59 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('42',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_tarski @ sk_A ) )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ X0 )
      | ( ( k1_relat_1 @ sk_D_1 )
        = ( k1_tarski @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','43'])).

thf('45',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['13','18'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ X0 )
      | ( ( k1_relat_1 @ sk_D_1 )
        = ( k1_tarski @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_D_1 )
        = ( k1_tarski @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_D_1 )
        = ( k1_tarski @ sk_A ) )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ X0 )
      | ( ( k1_relat_1 @ sk_D_1 )
        = ( k1_tarski @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('51',plain,(
    ! [X103: $i,X104: $i,X105: $i,X106: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X103 ) @ X104 )
      | ( m1_subset_1 @ X103 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X104 @ X105 ) ) )
      | ~ ( m1_subset_1 @ X103 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X106 @ X105 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_D_1 )
        = ( k1_tarski @ sk_A ) )
      | ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','53'])).

thf('55',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k2_zfmisc_1 @ X37 @ X38 )
        = k1_xboole_0 )
      | ( X38 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('56',plain,(
    ! [X37: $i] :
      ( ( k2_zfmisc_1 @ X37 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X99: $i,X100: $i,X101: $i,X102: $i] :
      ( ~ ( m1_subset_1 @ X99 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X100 @ X101 ) ) )
      | ( ( k7_relset_1 @ X100 @ X101 @ X99 @ X102 )
        = ( k9_relat_1 @ X99 @ X102 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k7_relset_1 @ X0 @ k1_xboole_0 @ X1 @ X2 )
        = ( k9_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ sk_D_1 )
        = ( k1_tarski @ sk_A ) )
      | ( ( k7_relset_1 @ X1 @ k1_xboole_0 @ sk_D_1 @ X0 )
        = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','58'])).

thf('60',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('61',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','53'])).

thf('62',plain,(
    ! [X58: $i,X59: $i] :
      ( ( r1_tarski @ X58 @ X59 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ X59 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('63',plain,
    ( ( ( k1_relat_1 @ sk_D_1 )
      = ( k1_tarski @ sk_A ) )
    | ( r1_tarski @ sk_D_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_D_1 )
        = ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_D_1 ) @ k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_D_1 )
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('67',plain,(
    ! [X87: $i,X88: $i] :
      ( ~ ( r2_hidden @ X87 @ X88 )
      | ~ ( r1_tarski @ X88 @ X87 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_D_1 )
        = ( k1_tarski @ sk_A ) )
      | ( r1_tarski @ sk_D_1 @ X0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ ( sk_C @ X0 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('69',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_D_1 )
        = ( k1_tarski @ sk_A ) )
      | ( r1_tarski @ sk_D_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X58: $i,X60: $i] :
      ( ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ X60 ) )
      | ~ ( r1_tarski @ X58 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_D_1 )
        = ( k1_tarski @ sk_A ) )
      | ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X37: $i] :
      ( ( k2_zfmisc_1 @ X37 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['55'])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('74',plain,(
    ! [X92: $i,X93: $i,X94: $i,X95: $i] :
      ( ~ ( m1_subset_1 @ X92 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X93 @ X94 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X93 @ X94 @ X92 @ X95 ) @ ( k1_zfmisc_1 @ X94 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X0 @ k1_xboole_0 @ X1 @ X2 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ sk_D_1 )
        = ( k1_tarski @ sk_A ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X1 @ k1_xboole_0 @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k9_relat_1 @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k1_relat_1 @ sk_D_1 )
        = ( k1_tarski @ sk_A ) )
      | ( ( k1_relat_1 @ sk_D_1 )
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['59','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_D_1 )
        = ( k1_tarski @ sk_A ) )
      | ( m1_subset_1 @ ( k9_relat_1 @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X58: $i,X59: $i] :
      ( ( r1_tarski @ X58 @ X59 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ X59 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_D_1 )
        = ( k1_tarski @ sk_A ) )
      | ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('82',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_D_1 )
        = ( k1_tarski @ sk_A ) )
      | ( ( k9_relat_1 @ sk_D_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C_1 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('86',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('88',plain,
    ( ( k1_relat_1 @ sk_D_1 )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['86','87'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('89',plain,(
    ! [X85: $i,X86: $i] :
      ( ( ( k1_relat_1 @ X86 )
       != ( k1_tarski @ X85 ) )
      | ( ( k2_relat_1 @ X86 )
        = ( k1_tarski @ ( k1_funct_1 @ X86 @ X85 ) ) )
      | ~ ( v1_funct_1 @ X86 )
      | ~ ( v1_relat_1 @ X86 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D_1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( k2_relat_1 @ sk_D_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference(eq_res,[status(thm)],['90'])).

thf('92',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['16','17'])).

thf('94',plain,
    ( ( k2_relat_1 @ sk_D_1 )
    = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('96',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t14_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) )).

thf('98',plain,(
    ! [X107: $i,X108: $i,X109: $i,X110: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X107 ) @ X108 )
      | ( m1_subset_1 @ X107 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X109 @ X108 ) ) )
      | ~ ( m1_subset_1 @ X107 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X109 @ X110 ) ) ) ) ),
    inference(cnf,[status(esa)],[t14_relset_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['96','99'])).

thf('101',plain,(
    ! [X92: $i,X93: $i,X94: $i,X95: $i] :
      ( ~ ( m1_subset_1 @ X92 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X93 @ X94 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X93 @ X94 @ X92 @ X95 ) @ ( k1_zfmisc_1 @ X94 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ ( k2_relat_1 @ sk_D_1 ) @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['96','99'])).

thf('104',plain,(
    ! [X99: $i,X100: $i,X101: $i,X102: $i] :
      ( ~ ( m1_subset_1 @ X99 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X100 @ X101 ) ) )
      | ( ( k7_relset_1 @ X100 @ X101 @ X99 @ X102 )
        = ( k9_relat_1 @ X99 @ X102 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ ( k2_relat_1 @ sk_D_1 ) @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_relat_1 @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['102','105'])).

thf('107',plain,(
    ! [X58: $i,X59: $i] :
      ( ( r1_tarski @ X58 @ X59 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ X59 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('108',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ X0 ) @ ( k2_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    $false ),
    inference(demod,[status(thm)],['4','94','108'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FEHssGe9uo
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:48:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 8.77/8.98  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 8.77/8.98  % Solved by: fo/fo7.sh
% 8.77/8.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.77/8.98  % done 12733 iterations in 8.554s
% 8.77/8.98  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 8.77/8.98  % SZS output start Refutation
% 8.77/8.98  thf(sk_B_type, type, sk_B: $i).
% 8.77/8.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.77/8.98  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 8.77/8.98  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 8.77/8.98  thf(sk_A_type, type, sk_A: $i).
% 8.77/8.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 8.77/8.98  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 8.77/8.98  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 8.77/8.98  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 8.77/8.98  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 8.77/8.98  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 8.77/8.98  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 8.77/8.98  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 8.77/8.98  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 8.77/8.98  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 8.77/8.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.77/8.98  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 8.77/8.98  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 8.77/8.98  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 8.77/8.98  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 8.77/8.98  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 8.77/8.98  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 8.77/8.98  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 8.77/8.98  thf(sk_D_1_type, type, sk_D_1: $i).
% 8.77/8.98  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 8.77/8.98  thf(sk_C_1_type, type, sk_C_1: $i).
% 8.77/8.98  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o).
% 8.77/8.98  thf(t64_funct_2, conjecture,
% 8.77/8.98    (![A:$i,B:$i,C:$i,D:$i]:
% 8.77/8.98     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 8.77/8.98         ( m1_subset_1 @
% 8.77/8.98           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 8.77/8.98       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 8.77/8.98         ( r1_tarski @
% 8.77/8.98           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 8.77/8.98           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 8.77/8.98  thf(zf_stmt_0, negated_conjecture,
% 8.77/8.98    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 8.77/8.98        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 8.77/8.98            ( m1_subset_1 @
% 8.77/8.98              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 8.77/8.98          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 8.77/8.98            ( r1_tarski @
% 8.77/8.98              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 8.77/8.98              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 8.77/8.98    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 8.77/8.98  thf('0', plain,
% 8.77/8.98      (~ (r1_tarski @ 
% 8.77/8.98          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ sk_C_1) @ 
% 8.77/8.98          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 8.77/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.77/8.98  thf('1', plain,
% 8.77/8.98      ((m1_subset_1 @ sk_D_1 @ 
% 8.77/8.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 8.77/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.77/8.98  thf(redefinition_k7_relset_1, axiom,
% 8.77/8.98    (![A:$i,B:$i,C:$i,D:$i]:
% 8.77/8.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.77/8.98       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 8.77/8.98  thf('2', plain,
% 8.77/8.98      (![X99 : $i, X100 : $i, X101 : $i, X102 : $i]:
% 8.77/8.98         (~ (m1_subset_1 @ X99 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X100 @ X101)))
% 8.77/8.98          | ((k7_relset_1 @ X100 @ X101 @ X99 @ X102)
% 8.77/8.98              = (k9_relat_1 @ X99 @ X102)))),
% 8.77/8.98      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 8.77/8.98  thf('3', plain,
% 8.77/8.98      (![X0 : $i]:
% 8.77/8.98         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ X0)
% 8.77/8.98           = (k9_relat_1 @ sk_D_1 @ X0))),
% 8.77/8.98      inference('sup-', [status(thm)], ['1', '2'])).
% 8.77/8.98  thf('4', plain,
% 8.77/8.98      (~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C_1) @ 
% 8.77/8.98          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 8.77/8.98      inference('demod', [status(thm)], ['0', '3'])).
% 8.77/8.98  thf(t113_zfmisc_1, axiom,
% 8.77/8.98    (![A:$i,B:$i]:
% 8.77/8.98     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 8.77/8.98       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 8.77/8.98  thf('5', plain,
% 8.77/8.98      (![X37 : $i, X38 : $i]:
% 8.77/8.98         (((k2_zfmisc_1 @ X37 @ X38) = (k1_xboole_0))
% 8.77/8.98          | ((X37) != (k1_xboole_0)))),
% 8.77/8.98      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 8.77/8.98  thf('6', plain,
% 8.77/8.98      (![X38 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X38) = (k1_xboole_0))),
% 8.77/8.98      inference('simplify', [status(thm)], ['5'])).
% 8.77/8.98  thf(d3_enumset1, axiom,
% 8.77/8.98    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 8.77/8.98     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 8.77/8.98       ( ![G:$i]:
% 8.77/8.98         ( ( r2_hidden @ G @ F ) <=>
% 8.77/8.98           ( ~( ( ( G ) != ( E ) ) & ( ( G ) != ( D ) ) & ( ( G ) != ( C ) ) & 
% 8.77/8.98                ( ( G ) != ( B ) ) & ( ( G ) != ( A ) ) ) ) ) ) ))).
% 8.77/8.98  thf(zf_stmt_1, axiom,
% 8.77/8.98    (![G:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 8.77/8.98     ( ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) <=>
% 8.77/8.98       ( ( ( G ) != ( A ) ) & ( ( G ) != ( B ) ) & ( ( G ) != ( C ) ) & 
% 8.77/8.98         ( ( G ) != ( D ) ) & ( ( G ) != ( E ) ) ) ))).
% 8.77/8.98  thf('7', plain,
% 8.77/8.98      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 8.77/8.98         ((zip_tseitin_0 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45)
% 8.77/8.98          | ((X40) = (X41))
% 8.77/8.98          | ((X40) = (X42))
% 8.77/8.98          | ((X40) = (X43))
% 8.77/8.98          | ((X40) = (X44))
% 8.77/8.98          | ((X40) = (X45)))),
% 8.77/8.98      inference('cnf', [status(esa)], [zf_stmt_1])).
% 8.77/8.98  thf(d3_tarski, axiom,
% 8.77/8.98    (![A:$i,B:$i]:
% 8.77/8.98     ( ( r1_tarski @ A @ B ) <=>
% 8.77/8.98       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 8.77/8.98  thf('8', plain,
% 8.77/8.98      (![X1 : $i, X3 : $i]:
% 8.77/8.98         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 8.77/8.98      inference('cnf', [status(esa)], [d3_tarski])).
% 8.77/8.98  thf('9', plain,
% 8.77/8.98      ((m1_subset_1 @ sk_D_1 @ 
% 8.77/8.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 8.77/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.77/8.98  thf(cc2_relset_1, axiom,
% 8.77/8.98    (![A:$i,B:$i,C:$i]:
% 8.77/8.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.77/8.98       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 8.77/8.98  thf('10', plain,
% 8.77/8.98      (![X89 : $i, X90 : $i, X91 : $i]:
% 8.77/8.98         ((v4_relat_1 @ X89 @ X90)
% 8.77/8.98          | ~ (m1_subset_1 @ X89 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X90 @ X91))))),
% 8.77/8.98      inference('cnf', [status(esa)], [cc2_relset_1])).
% 8.77/8.98  thf('11', plain, ((v4_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A))),
% 8.77/8.98      inference('sup-', [status(thm)], ['9', '10'])).
% 8.77/8.98  thf(d18_relat_1, axiom,
% 8.77/8.98    (![A:$i,B:$i]:
% 8.77/8.98     ( ( v1_relat_1 @ B ) =>
% 8.77/8.98       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 8.77/8.98  thf('12', plain,
% 8.77/8.98      (![X66 : $i, X67 : $i]:
% 8.77/8.98         (~ (v4_relat_1 @ X66 @ X67)
% 8.77/8.98          | (r1_tarski @ (k1_relat_1 @ X66) @ X67)
% 8.77/8.98          | ~ (v1_relat_1 @ X66))),
% 8.77/8.98      inference('cnf', [status(esa)], [d18_relat_1])).
% 8.77/8.98  thf('13', plain,
% 8.77/8.98      ((~ (v1_relat_1 @ sk_D_1)
% 8.77/8.98        | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ (k1_tarski @ sk_A)))),
% 8.77/8.98      inference('sup-', [status(thm)], ['11', '12'])).
% 8.77/8.98  thf('14', plain,
% 8.77/8.98      ((m1_subset_1 @ sk_D_1 @ 
% 8.77/8.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 8.77/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.77/8.98  thf(cc2_relat_1, axiom,
% 8.77/8.98    (![A:$i]:
% 8.77/8.98     ( ( v1_relat_1 @ A ) =>
% 8.77/8.98       ( ![B:$i]:
% 8.77/8.98         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 8.77/8.98  thf('15', plain,
% 8.77/8.98      (![X64 : $i, X65 : $i]:
% 8.77/8.98         (~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ X65))
% 8.77/8.98          | (v1_relat_1 @ X64)
% 8.77/8.98          | ~ (v1_relat_1 @ X65))),
% 8.77/8.98      inference('cnf', [status(esa)], [cc2_relat_1])).
% 8.77/8.98  thf('16', plain,
% 8.77/8.98      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 8.77/8.98        | (v1_relat_1 @ sk_D_1))),
% 8.77/8.98      inference('sup-', [status(thm)], ['14', '15'])).
% 8.77/8.98  thf(fc6_relat_1, axiom,
% 8.77/8.98    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 8.77/8.98  thf('17', plain,
% 8.77/8.98      (![X68 : $i, X69 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X68 @ X69))),
% 8.77/8.98      inference('cnf', [status(esa)], [fc6_relat_1])).
% 8.77/8.98  thf('18', plain, ((v1_relat_1 @ sk_D_1)),
% 8.77/8.98      inference('demod', [status(thm)], ['16', '17'])).
% 8.77/8.98  thf('19', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ (k1_tarski @ sk_A))),
% 8.77/8.98      inference('demod', [status(thm)], ['13', '18'])).
% 8.77/8.98  thf('20', plain,
% 8.77/8.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.77/8.98         (~ (r2_hidden @ X0 @ X1)
% 8.77/8.98          | (r2_hidden @ X0 @ X2)
% 8.77/8.98          | ~ (r1_tarski @ X1 @ X2))),
% 8.77/8.98      inference('cnf', [status(esa)], [d3_tarski])).
% 8.77/8.98  thf('21', plain,
% 8.77/8.98      (![X0 : $i]:
% 8.77/8.98         ((r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 8.77/8.98          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_1)))),
% 8.77/8.98      inference('sup-', [status(thm)], ['19', '20'])).
% 8.77/8.98  thf('22', plain,
% 8.77/8.98      (![X0 : $i]:
% 8.77/8.98         ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ X0)
% 8.77/8.98          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ sk_D_1)) @ 
% 8.77/8.98             (k1_tarski @ sk_A)))),
% 8.77/8.98      inference('sup-', [status(thm)], ['8', '21'])).
% 8.77/8.98  thf(t69_enumset1, axiom,
% 8.77/8.98    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 8.77/8.98  thf('23', plain, (![X8 : $i]: ((k2_tarski @ X8 @ X8) = (k1_tarski @ X8))),
% 8.77/8.98      inference('cnf', [status(esa)], [t69_enumset1])).
% 8.77/8.98  thf(t70_enumset1, axiom,
% 8.77/8.98    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 8.77/8.98  thf('24', plain,
% 8.77/8.98      (![X9 : $i, X10 : $i]:
% 8.77/8.98         ((k1_enumset1 @ X9 @ X9 @ X10) = (k2_tarski @ X9 @ X10))),
% 8.77/8.98      inference('cnf', [status(esa)], [t70_enumset1])).
% 8.77/8.98  thf(t71_enumset1, axiom,
% 8.77/8.98    (![A:$i,B:$i,C:$i]:
% 8.77/8.98     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 8.77/8.98  thf('25', plain,
% 8.77/8.98      (![X11 : $i, X12 : $i, X13 : $i]:
% 8.77/8.98         ((k2_enumset1 @ X11 @ X11 @ X12 @ X13)
% 8.77/8.98           = (k1_enumset1 @ X11 @ X12 @ X13))),
% 8.77/8.98      inference('cnf', [status(esa)], [t71_enumset1])).
% 8.77/8.98  thf(t72_enumset1, axiom,
% 8.77/8.98    (![A:$i,B:$i,C:$i,D:$i]:
% 8.77/8.98     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 8.77/8.98  thf('26', plain,
% 8.77/8.98      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 8.77/8.98         ((k3_enumset1 @ X14 @ X14 @ X15 @ X16 @ X17)
% 8.77/8.98           = (k2_enumset1 @ X14 @ X15 @ X16 @ X17))),
% 8.77/8.98      inference('cnf', [status(esa)], [t72_enumset1])).
% 8.77/8.98  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $o).
% 8.77/8.98  thf(zf_stmt_3, axiom,
% 8.77/8.98    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 8.77/8.98     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 8.77/8.98       ( ![G:$i]:
% 8.77/8.98         ( ( r2_hidden @ G @ F ) <=>
% 8.77/8.98           ( ~( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) ) ) ) ))).
% 8.77/8.98  thf('27', plain,
% 8.77/8.98      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 8.77/8.98         (~ (r2_hidden @ X53 @ X52)
% 8.77/8.98          | ~ (zip_tseitin_0 @ X53 @ X47 @ X48 @ X49 @ X50 @ X51)
% 8.77/8.98          | ((X52) != (k3_enumset1 @ X51 @ X50 @ X49 @ X48 @ X47)))),
% 8.77/8.98      inference('cnf', [status(esa)], [zf_stmt_3])).
% 8.77/8.98  thf('28', plain,
% 8.77/8.98      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X53 : $i]:
% 8.77/8.98         (~ (zip_tseitin_0 @ X53 @ X47 @ X48 @ X49 @ X50 @ X51)
% 8.77/8.98          | ~ (r2_hidden @ X53 @ (k3_enumset1 @ X51 @ X50 @ X49 @ X48 @ X47)))),
% 8.77/8.98      inference('simplify', [status(thm)], ['27'])).
% 8.77/8.98  thf('29', plain,
% 8.77/8.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 8.77/8.98         (~ (r2_hidden @ X4 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 8.77/8.98          | ~ (zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3))),
% 8.77/8.98      inference('sup-', [status(thm)], ['26', '28'])).
% 8.77/8.98  thf('30', plain,
% 8.77/8.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.77/8.98         (~ (r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 8.77/8.98          | ~ (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2))),
% 8.77/8.98      inference('sup-', [status(thm)], ['25', '29'])).
% 8.77/8.98  thf('31', plain,
% 8.77/8.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.77/8.98         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 8.77/8.98          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 @ X1))),
% 8.77/8.98      inference('sup-', [status(thm)], ['24', '30'])).
% 8.77/8.98  thf('32', plain,
% 8.77/8.98      (![X0 : $i, X1 : $i]:
% 8.77/8.98         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 8.77/8.98          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0))),
% 8.77/8.98      inference('sup-', [status(thm)], ['23', '31'])).
% 8.77/8.98  thf('33', plain,
% 8.77/8.98      (![X0 : $i]:
% 8.77/8.98         ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ X0)
% 8.77/8.98          | ~ (zip_tseitin_0 @ (sk_C @ X0 @ (k1_relat_1 @ sk_D_1)) @ sk_A @ 
% 8.77/8.98               sk_A @ sk_A @ sk_A @ sk_A))),
% 8.77/8.98      inference('sup-', [status(thm)], ['22', '32'])).
% 8.77/8.98  thf('34', plain,
% 8.77/8.98      (![X0 : $i]:
% 8.77/8.98         (((sk_C @ X0 @ (k1_relat_1 @ sk_D_1)) = (sk_A))
% 8.77/8.98          | ((sk_C @ X0 @ (k1_relat_1 @ sk_D_1)) = (sk_A))
% 8.77/8.98          | ((sk_C @ X0 @ (k1_relat_1 @ sk_D_1)) = (sk_A))
% 8.77/8.98          | ((sk_C @ X0 @ (k1_relat_1 @ sk_D_1)) = (sk_A))
% 8.77/8.98          | ((sk_C @ X0 @ (k1_relat_1 @ sk_D_1)) = (sk_A))
% 8.77/8.98          | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ X0))),
% 8.77/8.98      inference('sup-', [status(thm)], ['7', '33'])).
% 8.77/8.98  thf('35', plain,
% 8.77/8.98      (![X0 : $i]:
% 8.77/8.98         ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ X0)
% 8.77/8.98          | ((sk_C @ X0 @ (k1_relat_1 @ sk_D_1)) = (sk_A)))),
% 8.77/8.98      inference('simplify', [status(thm)], ['34'])).
% 8.77/8.98  thf('36', plain,
% 8.77/8.98      (![X0 : $i]:
% 8.77/8.98         ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ X0)
% 8.77/8.98          | ((sk_C @ X0 @ (k1_relat_1 @ sk_D_1)) = (sk_A)))),
% 8.77/8.98      inference('simplify', [status(thm)], ['34'])).
% 8.77/8.98  thf('37', plain,
% 8.77/8.98      (![X1 : $i, X3 : $i]:
% 8.77/8.98         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 8.77/8.98      inference('cnf', [status(esa)], [d3_tarski])).
% 8.77/8.98  thf(t63_subset_1, axiom,
% 8.77/8.98    (![A:$i,B:$i]:
% 8.77/8.98     ( ( r2_hidden @ A @ B ) =>
% 8.77/8.98       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 8.77/8.98  thf('38', plain,
% 8.77/8.98      (![X56 : $i, X57 : $i]:
% 8.77/8.98         ((m1_subset_1 @ (k1_tarski @ X56) @ (k1_zfmisc_1 @ X57))
% 8.77/8.98          | ~ (r2_hidden @ X56 @ X57))),
% 8.77/8.98      inference('cnf', [status(esa)], [t63_subset_1])).
% 8.77/8.98  thf('39', plain,
% 8.77/8.98      (![X0 : $i, X1 : $i]:
% 8.77/8.98         ((r1_tarski @ X0 @ X1)
% 8.77/8.98          | (m1_subset_1 @ (k1_tarski @ (sk_C @ X1 @ X0)) @ (k1_zfmisc_1 @ X0)))),
% 8.77/8.98      inference('sup-', [status(thm)], ['37', '38'])).
% 8.77/8.98  thf(t3_subset, axiom,
% 8.77/8.98    (![A:$i,B:$i]:
% 8.77/8.98     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 8.77/8.98  thf('40', plain,
% 8.77/8.98      (![X58 : $i, X59 : $i]:
% 8.77/8.98         ((r1_tarski @ X58 @ X59) | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ X59)))),
% 8.77/8.98      inference('cnf', [status(esa)], [t3_subset])).
% 8.77/8.98  thf('41', plain,
% 8.77/8.98      (![X0 : $i, X1 : $i]:
% 8.77/8.98         ((r1_tarski @ X0 @ X1)
% 8.77/8.98          | (r1_tarski @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X0))),
% 8.77/8.98      inference('sup-', [status(thm)], ['39', '40'])).
% 8.77/8.98  thf(d10_xboole_0, axiom,
% 8.77/8.98    (![A:$i,B:$i]:
% 8.77/8.98     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 8.77/8.98  thf('42', plain,
% 8.77/8.98      (![X4 : $i, X6 : $i]:
% 8.77/8.98         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 8.77/8.98      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.77/8.98  thf('43', plain,
% 8.77/8.98      (![X0 : $i, X1 : $i]:
% 8.77/8.98         ((r1_tarski @ X0 @ X1)
% 8.77/8.98          | ~ (r1_tarski @ X0 @ (k1_tarski @ (sk_C @ X1 @ X0)))
% 8.77/8.98          | ((X0) = (k1_tarski @ (sk_C @ X1 @ X0))))),
% 8.77/8.98      inference('sup-', [status(thm)], ['41', '42'])).
% 8.77/8.98  thf('44', plain,
% 8.77/8.98      (![X0 : $i]:
% 8.77/8.98         (~ (r1_tarski @ (k1_relat_1 @ sk_D_1) @ (k1_tarski @ sk_A))
% 8.77/8.98          | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ X0)
% 8.77/8.98          | ((k1_relat_1 @ sk_D_1)
% 8.77/8.98              = (k1_tarski @ (sk_C @ X0 @ (k1_relat_1 @ sk_D_1))))
% 8.77/8.98          | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ X0))),
% 8.77/8.98      inference('sup-', [status(thm)], ['36', '43'])).
% 8.77/8.98  thf('45', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ (k1_tarski @ sk_A))),
% 8.77/8.98      inference('demod', [status(thm)], ['13', '18'])).
% 8.77/8.98  thf('46', plain,
% 8.77/8.98      (![X0 : $i]:
% 8.77/8.98         ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ X0)
% 8.77/8.98          | ((k1_relat_1 @ sk_D_1)
% 8.77/8.98              = (k1_tarski @ (sk_C @ X0 @ (k1_relat_1 @ sk_D_1))))
% 8.77/8.98          | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ X0))),
% 8.77/8.98      inference('demod', [status(thm)], ['44', '45'])).
% 8.77/8.98  thf('47', plain,
% 8.77/8.98      (![X0 : $i]:
% 8.77/8.98         (((k1_relat_1 @ sk_D_1)
% 8.77/8.98            = (k1_tarski @ (sk_C @ X0 @ (k1_relat_1 @ sk_D_1))))
% 8.77/8.98          | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ X0))),
% 8.77/8.98      inference('simplify', [status(thm)], ['46'])).
% 8.77/8.98  thf('48', plain,
% 8.77/8.98      (![X0 : $i]:
% 8.77/8.98         (((k1_relat_1 @ sk_D_1) = (k1_tarski @ sk_A))
% 8.77/8.98          | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ X0)
% 8.77/8.98          | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ X0))),
% 8.77/8.98      inference('sup+', [status(thm)], ['35', '47'])).
% 8.77/8.98  thf('49', plain,
% 8.77/8.98      (![X0 : $i]:
% 8.77/8.98         ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ X0)
% 8.77/8.98          | ((k1_relat_1 @ sk_D_1) = (k1_tarski @ sk_A)))),
% 8.77/8.98      inference('simplify', [status(thm)], ['48'])).
% 8.77/8.98  thf('50', plain,
% 8.77/8.98      ((m1_subset_1 @ sk_D_1 @ 
% 8.77/8.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 8.77/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.77/8.98  thf(t13_relset_1, axiom,
% 8.77/8.98    (![A:$i,B:$i,C:$i,D:$i]:
% 8.77/8.98     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 8.77/8.98       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 8.77/8.98         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 8.77/8.98  thf('51', plain,
% 8.77/8.98      (![X103 : $i, X104 : $i, X105 : $i, X106 : $i]:
% 8.77/8.98         (~ (r1_tarski @ (k1_relat_1 @ X103) @ X104)
% 8.77/8.98          | (m1_subset_1 @ X103 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X104 @ X105)))
% 8.77/8.98          | ~ (m1_subset_1 @ X103 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X106 @ X105))))),
% 8.77/8.98      inference('cnf', [status(esa)], [t13_relset_1])).
% 8.77/8.98  thf('52', plain,
% 8.77/8.98      (![X0 : $i]:
% 8.77/8.98         ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 8.77/8.98          | ~ (r1_tarski @ (k1_relat_1 @ sk_D_1) @ X0))),
% 8.77/8.98      inference('sup-', [status(thm)], ['50', '51'])).
% 8.77/8.98  thf('53', plain,
% 8.77/8.98      (![X0 : $i]:
% 8.77/8.98         (((k1_relat_1 @ sk_D_1) = (k1_tarski @ sk_A))
% 8.77/8.98          | (m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B))))),
% 8.77/8.98      inference('sup-', [status(thm)], ['49', '52'])).
% 8.77/8.98  thf('54', plain,
% 8.77/8.98      (((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 8.77/8.98        | ((k1_relat_1 @ sk_D_1) = (k1_tarski @ sk_A)))),
% 8.77/8.98      inference('sup+', [status(thm)], ['6', '53'])).
% 8.77/8.98  thf('55', plain,
% 8.77/8.98      (![X37 : $i, X38 : $i]:
% 8.77/8.98         (((k2_zfmisc_1 @ X37 @ X38) = (k1_xboole_0))
% 8.77/8.98          | ((X38) != (k1_xboole_0)))),
% 8.77/8.98      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 8.77/8.98  thf('56', plain,
% 8.77/8.98      (![X37 : $i]: ((k2_zfmisc_1 @ X37 @ k1_xboole_0) = (k1_xboole_0))),
% 8.77/8.98      inference('simplify', [status(thm)], ['55'])).
% 8.77/8.98  thf('57', plain,
% 8.77/8.98      (![X99 : $i, X100 : $i, X101 : $i, X102 : $i]:
% 8.77/8.98         (~ (m1_subset_1 @ X99 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X100 @ X101)))
% 8.77/8.98          | ((k7_relset_1 @ X100 @ X101 @ X99 @ X102)
% 8.77/8.98              = (k9_relat_1 @ X99 @ X102)))),
% 8.77/8.98      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 8.77/8.98  thf('58', plain,
% 8.77/8.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.77/8.98         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 8.77/8.98          | ((k7_relset_1 @ X0 @ k1_xboole_0 @ X1 @ X2)
% 8.77/8.98              = (k9_relat_1 @ X1 @ X2)))),
% 8.77/8.98      inference('sup-', [status(thm)], ['56', '57'])).
% 8.77/8.98  thf('59', plain,
% 8.77/8.98      (![X0 : $i, X1 : $i]:
% 8.77/8.98         (((k1_relat_1 @ sk_D_1) = (k1_tarski @ sk_A))
% 8.77/8.98          | ((k7_relset_1 @ X1 @ k1_xboole_0 @ sk_D_1 @ X0)
% 8.77/8.98              = (k9_relat_1 @ sk_D_1 @ X0)))),
% 8.77/8.98      inference('sup-', [status(thm)], ['54', '58'])).
% 8.77/8.98  thf('60', plain,
% 8.77/8.98      (![X1 : $i, X3 : $i]:
% 8.77/8.98         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 8.77/8.98      inference('cnf', [status(esa)], [d3_tarski])).
% 8.77/8.98  thf('61', plain,
% 8.77/8.98      (((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 8.77/8.98        | ((k1_relat_1 @ sk_D_1) = (k1_tarski @ sk_A)))),
% 8.77/8.98      inference('sup+', [status(thm)], ['6', '53'])).
% 8.77/8.98  thf('62', plain,
% 8.77/8.98      (![X58 : $i, X59 : $i]:
% 8.77/8.98         ((r1_tarski @ X58 @ X59) | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ X59)))),
% 8.77/8.98      inference('cnf', [status(esa)], [t3_subset])).
% 8.77/8.98  thf('63', plain,
% 8.77/8.98      ((((k1_relat_1 @ sk_D_1) = (k1_tarski @ sk_A))
% 8.77/8.98        | (r1_tarski @ sk_D_1 @ k1_xboole_0))),
% 8.77/8.98      inference('sup-', [status(thm)], ['61', '62'])).
% 8.77/8.98  thf('64', plain,
% 8.77/8.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.77/8.98         (~ (r2_hidden @ X0 @ X1)
% 8.77/8.98          | (r2_hidden @ X0 @ X2)
% 8.77/8.98          | ~ (r1_tarski @ X1 @ X2))),
% 8.77/8.98      inference('cnf', [status(esa)], [d3_tarski])).
% 8.77/8.98  thf('65', plain,
% 8.77/8.98      (![X0 : $i]:
% 8.77/8.98         (((k1_relat_1 @ sk_D_1) = (k1_tarski @ sk_A))
% 8.77/8.98          | (r2_hidden @ X0 @ k1_xboole_0)
% 8.77/8.98          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 8.77/8.98      inference('sup-', [status(thm)], ['63', '64'])).
% 8.77/8.98  thf('66', plain,
% 8.77/8.98      (![X0 : $i]:
% 8.77/8.98         ((r1_tarski @ sk_D_1 @ X0)
% 8.77/8.98          | (r2_hidden @ (sk_C @ X0 @ sk_D_1) @ k1_xboole_0)
% 8.77/8.98          | ((k1_relat_1 @ sk_D_1) = (k1_tarski @ sk_A)))),
% 8.77/8.98      inference('sup-', [status(thm)], ['60', '65'])).
% 8.77/8.98  thf(t7_ordinal1, axiom,
% 8.77/8.98    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 8.77/8.98  thf('67', plain,
% 8.77/8.98      (![X87 : $i, X88 : $i]:
% 8.77/8.98         (~ (r2_hidden @ X87 @ X88) | ~ (r1_tarski @ X88 @ X87))),
% 8.77/8.98      inference('cnf', [status(esa)], [t7_ordinal1])).
% 8.77/8.98  thf('68', plain,
% 8.77/8.98      (![X0 : $i]:
% 8.77/8.98         (((k1_relat_1 @ sk_D_1) = (k1_tarski @ sk_A))
% 8.77/8.98          | (r1_tarski @ sk_D_1 @ X0)
% 8.77/8.98          | ~ (r1_tarski @ k1_xboole_0 @ (sk_C @ X0 @ sk_D_1)))),
% 8.77/8.98      inference('sup-', [status(thm)], ['66', '67'])).
% 8.77/8.98  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 8.77/8.98  thf('69', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 8.77/8.98      inference('cnf', [status(esa)], [t2_xboole_1])).
% 8.77/8.98  thf('70', plain,
% 8.77/8.98      (![X0 : $i]:
% 8.77/8.98         (((k1_relat_1 @ sk_D_1) = (k1_tarski @ sk_A))
% 8.77/8.98          | (r1_tarski @ sk_D_1 @ X0))),
% 8.77/8.98      inference('demod', [status(thm)], ['68', '69'])).
% 8.77/8.98  thf('71', plain,
% 8.77/8.98      (![X58 : $i, X60 : $i]:
% 8.77/8.98         ((m1_subset_1 @ X58 @ (k1_zfmisc_1 @ X60)) | ~ (r1_tarski @ X58 @ X60))),
% 8.77/8.98      inference('cnf', [status(esa)], [t3_subset])).
% 8.77/8.98  thf('72', plain,
% 8.77/8.98      (![X0 : $i]:
% 8.77/8.98         (((k1_relat_1 @ sk_D_1) = (k1_tarski @ sk_A))
% 8.77/8.98          | (m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ X0)))),
% 8.77/8.98      inference('sup-', [status(thm)], ['70', '71'])).
% 8.77/8.98  thf('73', plain,
% 8.77/8.98      (![X37 : $i]: ((k2_zfmisc_1 @ X37 @ k1_xboole_0) = (k1_xboole_0))),
% 8.77/8.98      inference('simplify', [status(thm)], ['55'])).
% 8.77/8.98  thf(dt_k7_relset_1, axiom,
% 8.77/8.98    (![A:$i,B:$i,C:$i,D:$i]:
% 8.77/8.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.77/8.98       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 8.77/8.98  thf('74', plain,
% 8.77/8.98      (![X92 : $i, X93 : $i, X94 : $i, X95 : $i]:
% 8.77/8.98         (~ (m1_subset_1 @ X92 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X93 @ X94)))
% 8.77/8.98          | (m1_subset_1 @ (k7_relset_1 @ X93 @ X94 @ X92 @ X95) @ 
% 8.77/8.98             (k1_zfmisc_1 @ X94)))),
% 8.77/8.98      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 8.77/8.98  thf('75', plain,
% 8.77/8.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.77/8.98         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 8.77/8.98          | (m1_subset_1 @ (k7_relset_1 @ X0 @ k1_xboole_0 @ X1 @ X2) @ 
% 8.77/8.98             (k1_zfmisc_1 @ k1_xboole_0)))),
% 8.77/8.98      inference('sup-', [status(thm)], ['73', '74'])).
% 8.77/8.98  thf('76', plain,
% 8.77/8.98      (![X0 : $i, X1 : $i]:
% 8.77/8.98         (((k1_relat_1 @ sk_D_1) = (k1_tarski @ sk_A))
% 8.77/8.98          | (m1_subset_1 @ (k7_relset_1 @ X1 @ k1_xboole_0 @ sk_D_1 @ X0) @ 
% 8.77/8.98             (k1_zfmisc_1 @ k1_xboole_0)))),
% 8.77/8.98      inference('sup-', [status(thm)], ['72', '75'])).
% 8.77/8.98  thf('77', plain,
% 8.77/8.98      (![X0 : $i]:
% 8.77/8.98         ((m1_subset_1 @ (k9_relat_1 @ sk_D_1 @ X0) @ 
% 8.77/8.98           (k1_zfmisc_1 @ k1_xboole_0))
% 8.77/8.98          | ((k1_relat_1 @ sk_D_1) = (k1_tarski @ sk_A))
% 8.77/8.98          | ((k1_relat_1 @ sk_D_1) = (k1_tarski @ sk_A)))),
% 8.77/8.98      inference('sup+', [status(thm)], ['59', '76'])).
% 8.77/8.98  thf('78', plain,
% 8.77/8.98      (![X0 : $i]:
% 8.77/8.98         (((k1_relat_1 @ sk_D_1) = (k1_tarski @ sk_A))
% 8.77/8.98          | (m1_subset_1 @ (k9_relat_1 @ sk_D_1 @ X0) @ 
% 8.77/8.98             (k1_zfmisc_1 @ k1_xboole_0)))),
% 8.77/8.98      inference('simplify', [status(thm)], ['77'])).
% 8.77/8.98  thf('79', plain,
% 8.77/8.98      (![X58 : $i, X59 : $i]:
% 8.77/8.98         ((r1_tarski @ X58 @ X59) | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ X59)))),
% 8.77/8.98      inference('cnf', [status(esa)], [t3_subset])).
% 8.77/8.98  thf('80', plain,
% 8.77/8.98      (![X0 : $i]:
% 8.77/8.98         (((k1_relat_1 @ sk_D_1) = (k1_tarski @ sk_A))
% 8.77/8.98          | (r1_tarski @ (k9_relat_1 @ sk_D_1 @ X0) @ k1_xboole_0))),
% 8.77/8.98      inference('sup-', [status(thm)], ['78', '79'])).
% 8.77/8.98  thf('81', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 8.77/8.98      inference('cnf', [status(esa)], [t2_xboole_1])).
% 8.77/8.98  thf('82', plain,
% 8.77/8.98      (![X4 : $i, X6 : $i]:
% 8.77/8.98         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 8.77/8.98      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.77/8.98  thf('83', plain,
% 8.77/8.98      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 8.77/8.98      inference('sup-', [status(thm)], ['81', '82'])).
% 8.77/8.98  thf('84', plain,
% 8.77/8.98      (![X0 : $i]:
% 8.77/8.98         (((k1_relat_1 @ sk_D_1) = (k1_tarski @ sk_A))
% 8.77/8.98          | ((k9_relat_1 @ sk_D_1 @ X0) = (k1_xboole_0)))),
% 8.77/8.98      inference('sup-', [status(thm)], ['80', '83'])).
% 8.77/8.98  thf('85', plain,
% 8.77/8.98      (~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C_1) @ 
% 8.77/8.98          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 8.77/8.98      inference('demod', [status(thm)], ['0', '3'])).
% 8.77/8.98  thf('86', plain,
% 8.77/8.98      ((~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))
% 8.77/8.98        | ((k1_relat_1 @ sk_D_1) = (k1_tarski @ sk_A)))),
% 8.77/8.98      inference('sup-', [status(thm)], ['84', '85'])).
% 8.77/8.98  thf('87', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 8.77/8.98      inference('cnf', [status(esa)], [t2_xboole_1])).
% 8.77/8.98  thf('88', plain, (((k1_relat_1 @ sk_D_1) = (k1_tarski @ sk_A))),
% 8.77/8.98      inference('demod', [status(thm)], ['86', '87'])).
% 8.77/8.98  thf(t14_funct_1, axiom,
% 8.77/8.98    (![A:$i,B:$i]:
% 8.77/8.98     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 8.77/8.98       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 8.77/8.98         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 8.77/8.98  thf('89', plain,
% 8.77/8.98      (![X85 : $i, X86 : $i]:
% 8.77/8.98         (((k1_relat_1 @ X86) != (k1_tarski @ X85))
% 8.77/8.98          | ((k2_relat_1 @ X86) = (k1_tarski @ (k1_funct_1 @ X86 @ X85)))
% 8.77/8.98          | ~ (v1_funct_1 @ X86)
% 8.77/8.98          | ~ (v1_relat_1 @ X86))),
% 8.77/8.98      inference('cnf', [status(esa)], [t14_funct_1])).
% 8.77/8.98  thf('90', plain,
% 8.77/8.98      (![X0 : $i]:
% 8.77/8.98         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D_1))
% 8.77/8.98          | ~ (v1_relat_1 @ X0)
% 8.77/8.98          | ~ (v1_funct_1 @ X0)
% 8.77/8.98          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 8.77/8.98      inference('sup-', [status(thm)], ['88', '89'])).
% 8.77/8.98  thf('91', plain,
% 8.77/8.98      ((((k2_relat_1 @ sk_D_1) = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))
% 8.77/8.98        | ~ (v1_funct_1 @ sk_D_1)
% 8.77/8.98        | ~ (v1_relat_1 @ sk_D_1))),
% 8.77/8.98      inference('eq_res', [status(thm)], ['90'])).
% 8.77/8.98  thf('92', plain, ((v1_funct_1 @ sk_D_1)),
% 8.77/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.77/8.98  thf('93', plain, ((v1_relat_1 @ sk_D_1)),
% 8.77/8.98      inference('demod', [status(thm)], ['16', '17'])).
% 8.77/8.98  thf('94', plain,
% 8.77/8.98      (((k2_relat_1 @ sk_D_1) = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 8.77/8.98      inference('demod', [status(thm)], ['91', '92', '93'])).
% 8.77/8.98  thf('95', plain,
% 8.77/8.98      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 8.77/8.98      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.77/8.98  thf('96', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 8.77/8.98      inference('simplify', [status(thm)], ['95'])).
% 8.77/8.98  thf('97', plain,
% 8.77/8.98      ((m1_subset_1 @ sk_D_1 @ 
% 8.77/8.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 8.77/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.77/8.98  thf(t14_relset_1, axiom,
% 8.77/8.98    (![A:$i,B:$i,C:$i,D:$i]:
% 8.77/8.98     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 8.77/8.98       ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B ) =>
% 8.77/8.98         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ))).
% 8.77/8.98  thf('98', plain,
% 8.77/8.98      (![X107 : $i, X108 : $i, X109 : $i, X110 : $i]:
% 8.77/8.98         (~ (r1_tarski @ (k2_relat_1 @ X107) @ X108)
% 8.77/8.98          | (m1_subset_1 @ X107 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X109 @ X108)))
% 8.77/8.98          | ~ (m1_subset_1 @ X107 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X109 @ X110))))),
% 8.77/8.98      inference('cnf', [status(esa)], [t14_relset_1])).
% 8.77/8.98  thf('99', plain,
% 8.77/8.98      (![X0 : $i]:
% 8.77/8.98         ((m1_subset_1 @ sk_D_1 @ 
% 8.77/8.98           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ X0)))
% 8.77/8.98          | ~ (r1_tarski @ (k2_relat_1 @ sk_D_1) @ X0))),
% 8.77/8.98      inference('sup-', [status(thm)], ['97', '98'])).
% 8.77/8.98  thf('100', plain,
% 8.77/8.98      ((m1_subset_1 @ sk_D_1 @ 
% 8.77/8.98        (k1_zfmisc_1 @ 
% 8.77/8.98         (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_relat_1 @ sk_D_1))))),
% 8.77/8.98      inference('sup-', [status(thm)], ['96', '99'])).
% 8.77/8.98  thf('101', plain,
% 8.77/8.98      (![X92 : $i, X93 : $i, X94 : $i, X95 : $i]:
% 8.77/8.98         (~ (m1_subset_1 @ X92 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X93 @ X94)))
% 8.77/8.98          | (m1_subset_1 @ (k7_relset_1 @ X93 @ X94 @ X92 @ X95) @ 
% 8.77/8.98             (k1_zfmisc_1 @ X94)))),
% 8.77/8.98      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 8.77/8.98  thf('102', plain,
% 8.77/8.98      (![X0 : $i]:
% 8.77/8.98         (m1_subset_1 @ 
% 8.77/8.98          (k7_relset_1 @ (k1_tarski @ sk_A) @ (k2_relat_1 @ sk_D_1) @ sk_D_1 @ 
% 8.77/8.98           X0) @ 
% 8.77/8.98          (k1_zfmisc_1 @ (k2_relat_1 @ sk_D_1)))),
% 8.77/8.98      inference('sup-', [status(thm)], ['100', '101'])).
% 8.77/8.98  thf('103', plain,
% 8.77/8.98      ((m1_subset_1 @ sk_D_1 @ 
% 8.77/8.98        (k1_zfmisc_1 @ 
% 8.77/8.98         (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_relat_1 @ sk_D_1))))),
% 8.77/8.98      inference('sup-', [status(thm)], ['96', '99'])).
% 8.77/8.98  thf('104', plain,
% 8.77/8.98      (![X99 : $i, X100 : $i, X101 : $i, X102 : $i]:
% 8.77/8.98         (~ (m1_subset_1 @ X99 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X100 @ X101)))
% 8.77/8.98          | ((k7_relset_1 @ X100 @ X101 @ X99 @ X102)
% 8.77/8.98              = (k9_relat_1 @ X99 @ X102)))),
% 8.77/8.98      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 8.77/8.98  thf('105', plain,
% 8.77/8.98      (![X0 : $i]:
% 8.77/8.98         ((k7_relset_1 @ (k1_tarski @ sk_A) @ (k2_relat_1 @ sk_D_1) @ sk_D_1 @ 
% 8.77/8.98           X0) = (k9_relat_1 @ sk_D_1 @ X0))),
% 8.77/8.98      inference('sup-', [status(thm)], ['103', '104'])).
% 8.77/8.98  thf('106', plain,
% 8.77/8.98      (![X0 : $i]:
% 8.77/8.98         (m1_subset_1 @ (k9_relat_1 @ sk_D_1 @ X0) @ 
% 8.77/8.98          (k1_zfmisc_1 @ (k2_relat_1 @ sk_D_1)))),
% 8.77/8.98      inference('demod', [status(thm)], ['102', '105'])).
% 8.77/8.98  thf('107', plain,
% 8.77/8.98      (![X58 : $i, X59 : $i]:
% 8.77/8.98         ((r1_tarski @ X58 @ X59) | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ X59)))),
% 8.77/8.98      inference('cnf', [status(esa)], [t3_subset])).
% 8.77/8.98  thf('108', plain,
% 8.77/8.98      (![X0 : $i]:
% 8.77/8.98         (r1_tarski @ (k9_relat_1 @ sk_D_1 @ X0) @ (k2_relat_1 @ sk_D_1))),
% 8.77/8.98      inference('sup-', [status(thm)], ['106', '107'])).
% 8.77/8.98  thf('109', plain, ($false),
% 8.77/8.98      inference('demod', [status(thm)], ['4', '94', '108'])).
% 8.77/8.98  
% 8.77/8.98  % SZS output end Refutation
% 8.77/8.98  
% 8.77/8.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
