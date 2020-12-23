%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XnEjiYtMR2

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:53 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :  215 (12271 expanded)
%              Number of leaves         :   50 (3527 expanded)
%              Depth                    :   29
%              Number of atoms          : 1436 (132164 expanded)
%              Number of equality atoms :   41 (4910 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('6',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( v4_relat_1 @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v4_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('11',plain,(
    ! [X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X1 ) @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(clc,[status(thm)],['8','11'])).

thf(t5_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_relat_1 @ C ) )
     => ( ( ! [D: $i] :
              ( ( r2_hidden @ D @ A )
             => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
          & ( ( k1_relat_1 @ C )
            = A ) )
       => ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
          & ( v1_funct_2 @ C @ A @ B )
          & ( v1_funct_1 @ C ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( r2_hidden @ D @ A )
       => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
     => ( zip_tseitin_1 @ D @ C @ B @ A ) ) )).

thf('13',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ( zip_tseitin_1 @ X49 @ X50 @ X51 @ X52 )
      | ( r2_hidden @ X49 @ X52 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('14',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_1 @ X1 @ X3 @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( zip_tseitin_1 @ X0 @ X3 @ X2 @ ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf(zf_stmt_1,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( ( k1_relat_1 @ C )
            = A )
          & ! [D: $i] :
              ( zip_tseitin_1 @ D @ C @ B @ A ) )
       => ( zip_tseitin_2 @ C @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ( ( k1_relat_1 @ X57 )
       != X56 )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X57 @ X58 @ X56 ) @ X57 @ X58 @ X56 )
      | ( zip_tseitin_2 @ X57 @ X58 @ X56 )
      | ~ ( v1_funct_1 @ X57 )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('18',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( v1_relat_1 @ X57 )
      | ~ ( v1_funct_1 @ X57 )
      | ( zip_tseitin_2 @ X57 @ X58 @ ( k1_relat_1 @ X57 ) )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X57 @ X58 @ ( k1_relat_1 @ X57 ) ) @ X57 @ X58 @ ( k1_relat_1 @ X57 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_2 @ X0 @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( v1_funct_2 @ X53 @ X55 @ X54 )
      | ~ ( zip_tseitin_2 @ X53 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t121_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_5,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t121_funct_2])).

thf('22',plain,(
    r2_hidden @ sk_C_1 @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(d2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k1_funct_2 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i] :
              ( ( v1_relat_1 @ E )
              & ( v1_funct_1 @ E )
              & ( D = E )
              & ( ( k1_relat_1 @ E )
                = A )
              & ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B )
        & ( ( k1_relat_1 @ E )
          = A )
        & ( D = E )
        & ( v1_funct_1 @ E )
        & ( v1_relat_1 @ E ) ) ) )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k1_funct_2 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i] :
              ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( r2_hidden @ X45 @ X44 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X45 @ X42 @ X43 ) @ X45 @ X42 @ X43 )
      | ( X44
       != ( k1_funct_2 @ X43 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('24',plain,(
    ! [X42: $i,X43: $i,X45: $i] :
      ( ( zip_tseitin_0 @ ( sk_E_1 @ X45 @ X42 @ X43 ) @ X45 @ X42 @ X43 )
      | ~ ( r2_hidden @ X45 @ ( k1_funct_2 @ X43 @ X42 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_C_1 @ sk_B_1 @ sk_A ) @ sk_C_1 @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_C_1 @ sk_B_1 @ sk_A ) @ sk_C_1 @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['22','24'])).

thf('27',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( X37 = X35 )
      | ~ ( zip_tseitin_0 @ X35 @ X37 @ X36 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('28',plain,
    ( sk_C_1
    = ( sk_E_1 @ sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( ( k1_relat_1 @ X35 )
        = X38 )
      | ~ ( zip_tseitin_0 @ X35 @ X37 @ X36 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('31',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X48: $i] :
      ( ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X48 ) @ ( k2_relat_1 @ X48 ) ) ) )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('33',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['25','28'])).

thf('35',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( v1_relat_1 @ X35 )
      | ~ ( zip_tseitin_0 @ X35 @ X37 @ X36 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('36',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['25','28'])).

thf('38',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( v1_funct_1 @ X35 )
      | ~ ( zip_tseitin_0 @ X35 @ X37 @ X36 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('39',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['33','36','39'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('41',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( v1_partfun1 @ X32 @ X33 )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X34 )
      | ~ ( v1_funct_1 @ X32 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('44',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['29','30'])).

thf('45',plain,(
    ! [X48: $i] :
      ( ( v1_funct_2 @ X48 @ ( k1_relat_1 @ X48 ) @ ( k2_relat_1 @ X48 ) )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('46',plain,
    ( ( v1_funct_2 @ sk_C_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['34','35'])).

thf('48',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('49',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['42','43','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['33','36','39'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('52',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X23 ) ) )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('53',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['42','43','49'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('56',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('57',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('59',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X23 ) ) )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['33','36','39'])).

thf('63',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('64',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('66',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( sk_C_1
      = ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( sk_C_1
      = ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['61','68'])).

thf('70',plain,
    ( ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ( sk_C_1
      = ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['55','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('77',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( v4_relat_1 @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v4_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v4_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('82',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['80','83'])).

thf('85',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('86',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['75','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X1 ) @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(clc,[status(thm)],['8','11'])).

thf('95',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ ( k1_relat_1 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference('sup+',[status(thm)],['93','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(condensation,[status(thm)],['98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_partfun1 @ sk_C_1 @ sk_A )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['70','99'])).

thf('101',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['42','43','49'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ sk_C_1 @ sk_A )
      | ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('104',plain,(
    ! [X1: $i] :
      ( ( v1_partfun1 @ sk_C_1 @ sk_A )
      | ( v4_relat_1 @ sk_C_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v4_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ sk_C_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['34','35'])).

thf('108',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['29','30'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ sk_C_1 @ sk_A )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ sk_C_1 @ sk_A )
      | ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('111',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ sk_C_1 @ sk_A )
      | ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ sk_C_1 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( X0 = sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ( sk_A = sk_C_1 )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['109','114'])).

thf('116',plain,
    ( ( sk_A = sk_C_1 )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['25','28'])).

thf('118',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X35 ) @ X36 )
      | ~ ( zip_tseitin_0 @ X35 @ X37 @ X36 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('119',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['56'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('121',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X26 ) @ X27 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X26 ) @ X28 )
      | ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['119','122'])).

thf('124',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['29','30'])).

thf('125',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['34','35'])).

thf('126',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('127',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_partfun1 @ X29 @ X30 )
      | ( v1_funct_2 @ X29 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('128',plain,
    ( ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 )
    | ~ ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('130',plain,
    ( ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 )
    | ~ ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('132',plain,
    ( ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 )
   <= ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['131'])).

thf('133',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('134',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
   <= ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['131'])).

thf('135',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('137',plain,
    ( ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['131'])).

thf('138',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,
    ( ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['131'])).

thf('140',plain,(
    ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['135','138','139'])).

thf('141',plain,(
    ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['132','140'])).

thf('142',plain,(
    ~ ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference(clc,[status(thm)],['130','141'])).

thf('143',plain,(
    sk_A = sk_C_1 ),
    inference('sup-',[status(thm)],['116','142'])).

thf('144',plain,
    ( ( v1_partfun1 @ sk_C_1 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['54','143'])).

thf('145',plain,(
    ~ ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference(clc,[status(thm)],['130','141'])).

thf('146',plain,(
    sk_A = sk_C_1 ),
    inference('sup-',[status(thm)],['116','142'])).

thf('147',plain,(
    ~ ( v1_partfun1 @ sk_C_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,(
    v1_xboole_0 @ sk_C_1 ),
    inference(clc,[status(thm)],['144','147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_C_1 = X0 ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['132','140'])).

thf('152',plain,(
    sk_A = sk_C_1 ),
    inference('sup-',[status(thm)],['116','142'])).

thf('153',plain,(
    ~ ( v1_funct_2 @ sk_C_1 @ sk_C_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_2 @ sk_C_1 @ X0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['150','153'])).

thf('155',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['21','154'])).

thf('156',plain,(
    v1_xboole_0 @ sk_C_1 ),
    inference(clc,[status(thm)],['144','147'])).

thf('157',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('158',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['34','35'])).

thf('159',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['29','30'])).

thf('160',plain,(
    sk_A = sk_C_1 ),
    inference('sup-',[status(thm)],['116','142'])).

thf('161',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,(
    v1_xboole_0 @ sk_C_1 ),
    inference(clc,[status(thm)],['144','147'])).

thf('163',plain,(
    $false ),
    inference(demod,[status(thm)],['155','156','157','158','161','162'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XnEjiYtMR2
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:06:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.31/1.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.31/1.52  % Solved by: fo/fo7.sh
% 1.31/1.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.31/1.52  % done 1689 iterations in 1.060s
% 1.31/1.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.31/1.52  % SZS output start Refutation
% 1.31/1.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.31/1.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.31/1.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.31/1.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.31/1.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.31/1.52  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 1.31/1.52  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.31/1.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.31/1.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.31/1.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.31/1.52  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 1.31/1.52  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.31/1.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.31/1.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.31/1.52  thf(sk_B_type, type, sk_B: $i > $i).
% 1.31/1.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.31/1.52  thf(sk_A_type, type, sk_A: $i).
% 1.31/1.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.31/1.52  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 1.31/1.52  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 1.31/1.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.31/1.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.31/1.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.31/1.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.31/1.52  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 1.31/1.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.31/1.52  thf(d3_tarski, axiom,
% 1.31/1.52    (![A:$i,B:$i]:
% 1.31/1.52     ( ( r1_tarski @ A @ B ) <=>
% 1.31/1.52       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.31/1.52  thf('0', plain,
% 1.31/1.52      (![X4 : $i, X6 : $i]:
% 1.31/1.52         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.31/1.52      inference('cnf', [status(esa)], [d3_tarski])).
% 1.31/1.52  thf(d1_xboole_0, axiom,
% 1.31/1.52    (![A:$i]:
% 1.31/1.52     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.31/1.52  thf('1', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.31/1.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.31/1.52  thf('2', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.31/1.52      inference('sup-', [status(thm)], ['0', '1'])).
% 1.31/1.52  thf(t3_subset, axiom,
% 1.31/1.52    (![A:$i,B:$i]:
% 1.31/1.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.31/1.52  thf('3', plain,
% 1.31/1.52      (![X10 : $i, X12 : $i]:
% 1.31/1.52         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 1.31/1.52      inference('cnf', [status(esa)], [t3_subset])).
% 1.31/1.52  thf('4', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]:
% 1.31/1.52         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 1.31/1.52      inference('sup-', [status(thm)], ['2', '3'])).
% 1.31/1.52  thf(cc2_relset_1, axiom,
% 1.31/1.52    (![A:$i,B:$i,C:$i]:
% 1.31/1.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.31/1.52       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.31/1.52  thf('5', plain,
% 1.31/1.52      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.31/1.52         ((v4_relat_1 @ X20 @ X21)
% 1.31/1.52          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.31/1.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.31/1.52  thf('6', plain,
% 1.31/1.52      (![X1 : $i, X2 : $i]: (~ (v1_xboole_0 @ X2) | (v4_relat_1 @ X2 @ X1))),
% 1.31/1.52      inference('sup-', [status(thm)], ['4', '5'])).
% 1.31/1.52  thf(d18_relat_1, axiom,
% 1.31/1.52    (![A:$i,B:$i]:
% 1.31/1.52     ( ( v1_relat_1 @ B ) =>
% 1.31/1.52       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.31/1.52  thf('7', plain,
% 1.31/1.52      (![X13 : $i, X14 : $i]:
% 1.31/1.52         (~ (v4_relat_1 @ X13 @ X14)
% 1.31/1.52          | (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 1.31/1.52          | ~ (v1_relat_1 @ X13))),
% 1.31/1.52      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.31/1.52  thf('8', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]:
% 1.31/1.52         (~ (v1_xboole_0 @ X1)
% 1.31/1.52          | ~ (v1_relat_1 @ X1)
% 1.31/1.52          | (r1_tarski @ (k1_relat_1 @ X1) @ X0))),
% 1.31/1.52      inference('sup-', [status(thm)], ['6', '7'])).
% 1.31/1.52  thf('9', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]:
% 1.31/1.52         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 1.31/1.52      inference('sup-', [status(thm)], ['2', '3'])).
% 1.31/1.52  thf(cc1_relset_1, axiom,
% 1.31/1.52    (![A:$i,B:$i,C:$i]:
% 1.31/1.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.31/1.52       ( v1_relat_1 @ C ) ))).
% 1.31/1.52  thf('10', plain,
% 1.31/1.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.31/1.52         ((v1_relat_1 @ X17)
% 1.31/1.52          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.31/1.52      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.31/1.52  thf('11', plain, (![X2 : $i]: (~ (v1_xboole_0 @ X2) | (v1_relat_1 @ X2))),
% 1.31/1.52      inference('sup-', [status(thm)], ['9', '10'])).
% 1.31/1.52  thf('12', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]:
% 1.31/1.52         ((r1_tarski @ (k1_relat_1 @ X1) @ X0) | ~ (v1_xboole_0 @ X1))),
% 1.31/1.52      inference('clc', [status(thm)], ['8', '11'])).
% 1.31/1.52  thf(t5_funct_2, axiom,
% 1.31/1.52    (![A:$i,B:$i,C:$i]:
% 1.31/1.52     ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 1.31/1.52       ( ( ( ![D:$i]:
% 1.31/1.52             ( ( r2_hidden @ D @ A ) =>
% 1.31/1.52               ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) & 
% 1.31/1.52           ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 1.31/1.52         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.31/1.52           ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) ) ))).
% 1.31/1.52  thf(zf_stmt_0, axiom,
% 1.31/1.52    (![D:$i,C:$i,B:$i,A:$i]:
% 1.31/1.52     ( ( ( r2_hidden @ D @ A ) => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) =>
% 1.31/1.52       ( zip_tseitin_1 @ D @ C @ B @ A ) ))).
% 1.31/1.52  thf('13', plain,
% 1.31/1.52      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 1.31/1.52         ((zip_tseitin_1 @ X49 @ X50 @ X51 @ X52) | (r2_hidden @ X49 @ X52))),
% 1.31/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.52  thf(t7_ordinal1, axiom,
% 1.31/1.52    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.31/1.52  thf('14', plain,
% 1.31/1.52      (![X15 : $i, X16 : $i]:
% 1.31/1.52         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 1.31/1.52      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.31/1.52  thf('15', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.31/1.52         ((zip_tseitin_1 @ X1 @ X3 @ X2 @ X0) | ~ (r1_tarski @ X0 @ X1))),
% 1.31/1.52      inference('sup-', [status(thm)], ['13', '14'])).
% 1.31/1.52  thf('16', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.31/1.52         (~ (v1_xboole_0 @ X1)
% 1.31/1.52          | (zip_tseitin_1 @ X0 @ X3 @ X2 @ (k1_relat_1 @ X1)))),
% 1.31/1.52      inference('sup-', [status(thm)], ['12', '15'])).
% 1.31/1.52  thf(zf_stmt_1, type, zip_tseitin_2 : $i > $i > $i > $o).
% 1.31/1.52  thf(zf_stmt_2, axiom,
% 1.31/1.52    (![C:$i,B:$i,A:$i]:
% 1.31/1.52     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 1.31/1.52       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.31/1.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 1.31/1.52  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 1.31/1.52  thf(zf_stmt_4, axiom,
% 1.31/1.52    (![A:$i,B:$i,C:$i]:
% 1.31/1.52     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.31/1.52       ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 1.31/1.52           ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) =>
% 1.31/1.52         ( zip_tseitin_2 @ C @ B @ A ) ) ))).
% 1.31/1.52  thf('17', plain,
% 1.31/1.52      (![X56 : $i, X57 : $i, X58 : $i]:
% 1.31/1.52         (((k1_relat_1 @ X57) != (X56))
% 1.31/1.52          | ~ (zip_tseitin_1 @ (sk_D_1 @ X57 @ X58 @ X56) @ X57 @ X58 @ X56)
% 1.31/1.52          | (zip_tseitin_2 @ X57 @ X58 @ X56)
% 1.31/1.52          | ~ (v1_funct_1 @ X57)
% 1.31/1.52          | ~ (v1_relat_1 @ X57))),
% 1.31/1.52      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.31/1.52  thf('18', plain,
% 1.31/1.52      (![X57 : $i, X58 : $i]:
% 1.31/1.52         (~ (v1_relat_1 @ X57)
% 1.31/1.52          | ~ (v1_funct_1 @ X57)
% 1.31/1.52          | (zip_tseitin_2 @ X57 @ X58 @ (k1_relat_1 @ X57))
% 1.31/1.52          | ~ (zip_tseitin_1 @ (sk_D_1 @ X57 @ X58 @ (k1_relat_1 @ X57)) @ 
% 1.31/1.52               X57 @ X58 @ (k1_relat_1 @ X57)))),
% 1.31/1.52      inference('simplify', [status(thm)], ['17'])).
% 1.31/1.52  thf('19', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]:
% 1.31/1.52         (~ (v1_xboole_0 @ X0)
% 1.31/1.52          | (zip_tseitin_2 @ X0 @ X1 @ (k1_relat_1 @ X0))
% 1.31/1.52          | ~ (v1_funct_1 @ X0)
% 1.31/1.52          | ~ (v1_relat_1 @ X0))),
% 1.31/1.52      inference('sup-', [status(thm)], ['16', '18'])).
% 1.31/1.52  thf('20', plain,
% 1.31/1.52      (![X53 : $i, X54 : $i, X55 : $i]:
% 1.31/1.52         ((v1_funct_2 @ X53 @ X55 @ X54) | ~ (zip_tseitin_2 @ X53 @ X54 @ X55))),
% 1.31/1.52      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.31/1.52  thf('21', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]:
% 1.31/1.52         (~ (v1_relat_1 @ X0)
% 1.31/1.52          | ~ (v1_funct_1 @ X0)
% 1.31/1.52          | ~ (v1_xboole_0 @ X0)
% 1.31/1.52          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ X1))),
% 1.31/1.52      inference('sup-', [status(thm)], ['19', '20'])).
% 1.31/1.52  thf(t121_funct_2, conjecture,
% 1.31/1.52    (![A:$i,B:$i,C:$i]:
% 1.31/1.52     ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 1.31/1.52       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.31/1.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 1.31/1.52  thf(zf_stmt_5, negated_conjecture,
% 1.31/1.52    (~( ![A:$i,B:$i,C:$i]:
% 1.31/1.52        ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 1.31/1.52          ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.31/1.52            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )),
% 1.31/1.52    inference('cnf.neg', [status(esa)], [t121_funct_2])).
% 1.31/1.52  thf('22', plain, ((r2_hidden @ sk_C_1 @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 1.31/1.52      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.31/1.52  thf(d2_funct_2, axiom,
% 1.31/1.52    (![A:$i,B:$i,C:$i]:
% 1.31/1.52     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 1.31/1.52       ( ![D:$i]:
% 1.31/1.52         ( ( r2_hidden @ D @ C ) <=>
% 1.31/1.52           ( ?[E:$i]:
% 1.31/1.52             ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) & ( ( D ) = ( E ) ) & 
% 1.31/1.52               ( ( k1_relat_1 @ E ) = ( A ) ) & 
% 1.31/1.52               ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) ) ))).
% 1.31/1.52  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.31/1.52  thf(zf_stmt_7, axiom,
% 1.31/1.52    (![E:$i,D:$i,B:$i,A:$i]:
% 1.31/1.52     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 1.31/1.52       ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) & 
% 1.31/1.52         ( ( k1_relat_1 @ E ) = ( A ) ) & ( ( D ) = ( E ) ) & 
% 1.31/1.52         ( v1_funct_1 @ E ) & ( v1_relat_1 @ E ) ) ))).
% 1.31/1.52  thf(zf_stmt_8, axiom,
% 1.31/1.52    (![A:$i,B:$i,C:$i]:
% 1.31/1.52     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 1.31/1.52       ( ![D:$i]:
% 1.31/1.52         ( ( r2_hidden @ D @ C ) <=>
% 1.31/1.52           ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ))).
% 1.31/1.52  thf('23', plain,
% 1.31/1.52      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 1.31/1.52         (~ (r2_hidden @ X45 @ X44)
% 1.31/1.52          | (zip_tseitin_0 @ (sk_E_1 @ X45 @ X42 @ X43) @ X45 @ X42 @ X43)
% 1.31/1.52          | ((X44) != (k1_funct_2 @ X43 @ X42)))),
% 1.31/1.52      inference('cnf', [status(esa)], [zf_stmt_8])).
% 1.31/1.52  thf('24', plain,
% 1.31/1.52      (![X42 : $i, X43 : $i, X45 : $i]:
% 1.31/1.52         ((zip_tseitin_0 @ (sk_E_1 @ X45 @ X42 @ X43) @ X45 @ X42 @ X43)
% 1.31/1.52          | ~ (r2_hidden @ X45 @ (k1_funct_2 @ X43 @ X42)))),
% 1.31/1.52      inference('simplify', [status(thm)], ['23'])).
% 1.31/1.52  thf('25', plain,
% 1.31/1.52      ((zip_tseitin_0 @ (sk_E_1 @ sk_C_1 @ sk_B_1 @ sk_A) @ sk_C_1 @ sk_B_1 @ 
% 1.31/1.52        sk_A)),
% 1.31/1.52      inference('sup-', [status(thm)], ['22', '24'])).
% 1.31/1.52  thf('26', plain,
% 1.31/1.52      ((zip_tseitin_0 @ (sk_E_1 @ sk_C_1 @ sk_B_1 @ sk_A) @ sk_C_1 @ sk_B_1 @ 
% 1.31/1.52        sk_A)),
% 1.31/1.52      inference('sup-', [status(thm)], ['22', '24'])).
% 1.31/1.52  thf('27', plain,
% 1.31/1.52      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.31/1.52         (((X37) = (X35)) | ~ (zip_tseitin_0 @ X35 @ X37 @ X36 @ X38))),
% 1.31/1.52      inference('cnf', [status(esa)], [zf_stmt_7])).
% 1.31/1.52  thf('28', plain, (((sk_C_1) = (sk_E_1 @ sk_C_1 @ sk_B_1 @ sk_A))),
% 1.31/1.52      inference('sup-', [status(thm)], ['26', '27'])).
% 1.31/1.52  thf('29', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_1 @ sk_A)),
% 1.31/1.52      inference('demod', [status(thm)], ['25', '28'])).
% 1.31/1.52  thf('30', plain,
% 1.31/1.52      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.31/1.52         (((k1_relat_1 @ X35) = (X38))
% 1.31/1.52          | ~ (zip_tseitin_0 @ X35 @ X37 @ X36 @ X38))),
% 1.31/1.52      inference('cnf', [status(esa)], [zf_stmt_7])).
% 1.31/1.52  thf('31', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 1.31/1.52      inference('sup-', [status(thm)], ['29', '30'])).
% 1.31/1.52  thf(t3_funct_2, axiom,
% 1.31/1.52    (![A:$i]:
% 1.31/1.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.31/1.52       ( ( v1_funct_1 @ A ) & 
% 1.31/1.52         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.31/1.52         ( m1_subset_1 @
% 1.31/1.52           A @ 
% 1.31/1.52           ( k1_zfmisc_1 @
% 1.31/1.52             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.31/1.52  thf('32', plain,
% 1.31/1.52      (![X48 : $i]:
% 1.31/1.52         ((m1_subset_1 @ X48 @ 
% 1.31/1.52           (k1_zfmisc_1 @ 
% 1.31/1.52            (k2_zfmisc_1 @ (k1_relat_1 @ X48) @ (k2_relat_1 @ X48))))
% 1.31/1.52          | ~ (v1_funct_1 @ X48)
% 1.31/1.52          | ~ (v1_relat_1 @ X48))),
% 1.31/1.52      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.31/1.52  thf('33', plain,
% 1.31/1.52      (((m1_subset_1 @ sk_C_1 @ 
% 1.31/1.52         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))
% 1.31/1.52        | ~ (v1_relat_1 @ sk_C_1)
% 1.31/1.52        | ~ (v1_funct_1 @ sk_C_1))),
% 1.31/1.52      inference('sup+', [status(thm)], ['31', '32'])).
% 1.31/1.52  thf('34', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_1 @ sk_A)),
% 1.31/1.52      inference('demod', [status(thm)], ['25', '28'])).
% 1.31/1.52  thf('35', plain,
% 1.31/1.52      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.31/1.52         ((v1_relat_1 @ X35) | ~ (zip_tseitin_0 @ X35 @ X37 @ X36 @ X38))),
% 1.31/1.52      inference('cnf', [status(esa)], [zf_stmt_7])).
% 1.31/1.52  thf('36', plain, ((v1_relat_1 @ sk_C_1)),
% 1.31/1.52      inference('sup-', [status(thm)], ['34', '35'])).
% 1.31/1.52  thf('37', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_1 @ sk_A)),
% 1.31/1.52      inference('demod', [status(thm)], ['25', '28'])).
% 1.31/1.52  thf('38', plain,
% 1.31/1.52      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.31/1.52         ((v1_funct_1 @ X35) | ~ (zip_tseitin_0 @ X35 @ X37 @ X36 @ X38))),
% 1.31/1.52      inference('cnf', [status(esa)], [zf_stmt_7])).
% 1.31/1.52  thf('39', plain, ((v1_funct_1 @ sk_C_1)),
% 1.31/1.52      inference('sup-', [status(thm)], ['37', '38'])).
% 1.31/1.52  thf('40', plain,
% 1.31/1.52      ((m1_subset_1 @ sk_C_1 @ 
% 1.31/1.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))),
% 1.31/1.52      inference('demod', [status(thm)], ['33', '36', '39'])).
% 1.31/1.52  thf(cc5_funct_2, axiom,
% 1.31/1.52    (![A:$i,B:$i]:
% 1.31/1.52     ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.31/1.52       ( ![C:$i]:
% 1.31/1.52         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.31/1.52           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 1.31/1.52             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 1.31/1.52  thf('41', plain,
% 1.31/1.52      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.31/1.52         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 1.31/1.52          | (v1_partfun1 @ X32 @ X33)
% 1.31/1.52          | ~ (v1_funct_2 @ X32 @ X33 @ X34)
% 1.31/1.52          | ~ (v1_funct_1 @ X32)
% 1.31/1.52          | (v1_xboole_0 @ X34))),
% 1.31/1.52      inference('cnf', [status(esa)], [cc5_funct_2])).
% 1.31/1.52  thf('42', plain,
% 1.31/1.52      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1))
% 1.31/1.52        | ~ (v1_funct_1 @ sk_C_1)
% 1.31/1.52        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ (k2_relat_1 @ sk_C_1))
% 1.31/1.52        | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 1.31/1.52      inference('sup-', [status(thm)], ['40', '41'])).
% 1.31/1.52  thf('43', plain, ((v1_funct_1 @ sk_C_1)),
% 1.31/1.52      inference('sup-', [status(thm)], ['37', '38'])).
% 1.31/1.52  thf('44', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 1.31/1.52      inference('sup-', [status(thm)], ['29', '30'])).
% 1.31/1.52  thf('45', plain,
% 1.31/1.52      (![X48 : $i]:
% 1.31/1.52         ((v1_funct_2 @ X48 @ (k1_relat_1 @ X48) @ (k2_relat_1 @ X48))
% 1.31/1.52          | ~ (v1_funct_1 @ X48)
% 1.31/1.52          | ~ (v1_relat_1 @ X48))),
% 1.31/1.52      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.31/1.52  thf('46', plain,
% 1.31/1.52      (((v1_funct_2 @ sk_C_1 @ sk_A @ (k2_relat_1 @ sk_C_1))
% 1.31/1.52        | ~ (v1_relat_1 @ sk_C_1)
% 1.31/1.52        | ~ (v1_funct_1 @ sk_C_1))),
% 1.31/1.52      inference('sup+', [status(thm)], ['44', '45'])).
% 1.31/1.52  thf('47', plain, ((v1_relat_1 @ sk_C_1)),
% 1.31/1.52      inference('sup-', [status(thm)], ['34', '35'])).
% 1.31/1.52  thf('48', plain, ((v1_funct_1 @ sk_C_1)),
% 1.31/1.52      inference('sup-', [status(thm)], ['37', '38'])).
% 1.31/1.52  thf('49', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ (k2_relat_1 @ sk_C_1))),
% 1.31/1.52      inference('demod', [status(thm)], ['46', '47', '48'])).
% 1.31/1.52  thf('50', plain,
% 1.31/1.52      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1)) | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 1.31/1.52      inference('demod', [status(thm)], ['42', '43', '49'])).
% 1.31/1.52  thf('51', plain,
% 1.31/1.52      ((m1_subset_1 @ sk_C_1 @ 
% 1.31/1.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))),
% 1.31/1.52      inference('demod', [status(thm)], ['33', '36', '39'])).
% 1.31/1.52  thf(cc4_relset_1, axiom,
% 1.31/1.52    (![A:$i,B:$i]:
% 1.31/1.52     ( ( v1_xboole_0 @ A ) =>
% 1.31/1.52       ( ![C:$i]:
% 1.31/1.52         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 1.31/1.52           ( v1_xboole_0 @ C ) ) ) ))).
% 1.31/1.52  thf('52', plain,
% 1.31/1.52      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.31/1.52         (~ (v1_xboole_0 @ X23)
% 1.31/1.52          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X23)))
% 1.31/1.52          | (v1_xboole_0 @ X24))),
% 1.31/1.52      inference('cnf', [status(esa)], [cc4_relset_1])).
% 1.31/1.52  thf('53', plain,
% 1.31/1.52      (((v1_xboole_0 @ sk_C_1) | ~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_1)))),
% 1.31/1.52      inference('sup-', [status(thm)], ['51', '52'])).
% 1.31/1.52  thf('54', plain, (((v1_partfun1 @ sk_C_1 @ sk_A) | (v1_xboole_0 @ sk_C_1))),
% 1.31/1.52      inference('sup-', [status(thm)], ['50', '53'])).
% 1.31/1.52  thf('55', plain,
% 1.31/1.52      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1)) | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 1.31/1.52      inference('demod', [status(thm)], ['42', '43', '49'])).
% 1.31/1.52  thf(d10_xboole_0, axiom,
% 1.31/1.52    (![A:$i,B:$i]:
% 1.31/1.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.31/1.52  thf('56', plain,
% 1.31/1.52      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 1.31/1.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.31/1.52  thf('57', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 1.31/1.52      inference('simplify', [status(thm)], ['56'])).
% 1.31/1.52  thf('58', plain,
% 1.31/1.52      (![X10 : $i, X12 : $i]:
% 1.31/1.52         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 1.31/1.52      inference('cnf', [status(esa)], [t3_subset])).
% 1.31/1.52  thf('59', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.31/1.52      inference('sup-', [status(thm)], ['57', '58'])).
% 1.31/1.52  thf('60', plain,
% 1.31/1.52      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.31/1.52         (~ (v1_xboole_0 @ X23)
% 1.31/1.52          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X23)))
% 1.31/1.52          | (v1_xboole_0 @ X24))),
% 1.31/1.52      inference('cnf', [status(esa)], [cc4_relset_1])).
% 1.31/1.52  thf('61', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]:
% 1.31/1.52         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.31/1.52      inference('sup-', [status(thm)], ['59', '60'])).
% 1.31/1.52  thf('62', plain,
% 1.31/1.52      ((m1_subset_1 @ sk_C_1 @ 
% 1.31/1.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))),
% 1.31/1.52      inference('demod', [status(thm)], ['33', '36', '39'])).
% 1.31/1.52  thf('63', plain,
% 1.31/1.52      (![X10 : $i, X11 : $i]:
% 1.31/1.52         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 1.31/1.52      inference('cnf', [status(esa)], [t3_subset])).
% 1.31/1.52  thf('64', plain,
% 1.31/1.52      ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1)))),
% 1.31/1.52      inference('sup-', [status(thm)], ['62', '63'])).
% 1.31/1.52  thf('65', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.31/1.52      inference('sup-', [status(thm)], ['0', '1'])).
% 1.31/1.52  thf('66', plain,
% 1.31/1.52      (![X7 : $i, X9 : $i]:
% 1.31/1.52         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 1.31/1.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.31/1.52  thf('67', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]:
% 1.31/1.52         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 1.31/1.52      inference('sup-', [status(thm)], ['65', '66'])).
% 1.31/1.52  thf('68', plain,
% 1.31/1.52      ((((sk_C_1) = (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1)))
% 1.31/1.52        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))),
% 1.31/1.52      inference('sup-', [status(thm)], ['64', '67'])).
% 1.31/1.52  thf('69', plain,
% 1.31/1.52      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_1))
% 1.31/1.52        | ((sk_C_1) = (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))),
% 1.31/1.52      inference('sup-', [status(thm)], ['61', '68'])).
% 1.31/1.52  thf('70', plain,
% 1.31/1.52      (((v1_partfun1 @ sk_C_1 @ sk_A)
% 1.31/1.52        | ((sk_C_1) = (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))),
% 1.31/1.52      inference('sup-', [status(thm)], ['55', '69'])).
% 1.31/1.52  thf('71', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]:
% 1.31/1.52         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.31/1.52      inference('sup-', [status(thm)], ['59', '60'])).
% 1.31/1.52  thf('72', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.31/1.52      inference('sup-', [status(thm)], ['0', '1'])).
% 1.31/1.52  thf('73', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]:
% 1.31/1.52         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 1.31/1.52      inference('sup-', [status(thm)], ['65', '66'])).
% 1.31/1.52  thf('74', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]:
% 1.31/1.52         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.31/1.52      inference('sup-', [status(thm)], ['72', '73'])).
% 1.31/1.52  thf('75', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.31/1.52         (~ (v1_xboole_0 @ X0)
% 1.31/1.52          | ~ (v1_xboole_0 @ X2)
% 1.31/1.52          | ((k2_zfmisc_1 @ X1 @ X0) = (X2)))),
% 1.31/1.52      inference('sup-', [status(thm)], ['71', '74'])).
% 1.31/1.52  thf('76', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]:
% 1.31/1.52         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.31/1.52      inference('sup-', [status(thm)], ['59', '60'])).
% 1.31/1.52  thf('77', plain,
% 1.31/1.52      (![X1 : $i, X2 : $i]: (~ (v1_xboole_0 @ X2) | (v4_relat_1 @ X2 @ X1))),
% 1.31/1.52      inference('sup-', [status(thm)], ['4', '5'])).
% 1.31/1.52  thf('78', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.31/1.52         (~ (v1_xboole_0 @ X0) | (v4_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X2))),
% 1.31/1.52      inference('sup-', [status(thm)], ['76', '77'])).
% 1.31/1.52  thf('79', plain,
% 1.31/1.52      (![X13 : $i, X14 : $i]:
% 1.31/1.52         (~ (v4_relat_1 @ X13 @ X14)
% 1.31/1.52          | (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 1.31/1.52          | ~ (v1_relat_1 @ X13))),
% 1.31/1.52      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.31/1.52  thf('80', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.31/1.52         (~ (v1_xboole_0 @ X1)
% 1.31/1.52          | ~ (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X1))
% 1.31/1.52          | (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X2 @ X1)) @ X0))),
% 1.31/1.52      inference('sup-', [status(thm)], ['78', '79'])).
% 1.31/1.52  thf('81', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.31/1.52      inference('sup-', [status(thm)], ['57', '58'])).
% 1.31/1.52  thf('82', plain,
% 1.31/1.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.31/1.52         ((v1_relat_1 @ X17)
% 1.31/1.52          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.31/1.52      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.31/1.52  thf('83', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))),
% 1.31/1.52      inference('sup-', [status(thm)], ['81', '82'])).
% 1.31/1.52  thf('84', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.31/1.52         (~ (v1_xboole_0 @ X1)
% 1.31/1.52          | (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X2 @ X1)) @ X0))),
% 1.31/1.52      inference('demod', [status(thm)], ['80', '83'])).
% 1.31/1.52  thf('85', plain,
% 1.31/1.52      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.31/1.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.31/1.52  thf('86', plain,
% 1.31/1.52      (![X15 : $i, X16 : $i]:
% 1.31/1.52         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 1.31/1.52      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.31/1.52  thf('87', plain,
% 1.31/1.52      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 1.31/1.52      inference('sup-', [status(thm)], ['85', '86'])).
% 1.31/1.52  thf('88', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]:
% 1.31/1.52         (~ (v1_xboole_0 @ X0)
% 1.31/1.52          | (v1_xboole_0 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 1.31/1.52      inference('sup-', [status(thm)], ['84', '87'])).
% 1.31/1.52  thf('89', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]:
% 1.31/1.52         ((v1_xboole_0 @ (k1_relat_1 @ X0))
% 1.31/1.52          | ~ (v1_xboole_0 @ X0)
% 1.31/1.52          | ~ (v1_xboole_0 @ X1)
% 1.31/1.52          | ~ (v1_xboole_0 @ X1))),
% 1.31/1.52      inference('sup+', [status(thm)], ['75', '88'])).
% 1.31/1.52  thf('90', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]:
% 1.31/1.52         (~ (v1_xboole_0 @ X1)
% 1.31/1.52          | ~ (v1_xboole_0 @ X0)
% 1.31/1.52          | (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 1.31/1.52      inference('simplify', [status(thm)], ['89'])).
% 1.31/1.52  thf('91', plain,
% 1.31/1.52      (![X0 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.31/1.52      inference('condensation', [status(thm)], ['90'])).
% 1.31/1.52  thf('92', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.31/1.52         (~ (v1_xboole_0 @ X0)
% 1.31/1.52          | ~ (v1_xboole_0 @ X2)
% 1.31/1.52          | ((k2_zfmisc_1 @ X1 @ X0) = (X2)))),
% 1.31/1.52      inference('sup-', [status(thm)], ['71', '74'])).
% 1.31/1.52  thf('93', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.31/1.52         (~ (v1_xboole_0 @ X0)
% 1.31/1.52          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_relat_1 @ X0))
% 1.31/1.52          | ~ (v1_xboole_0 @ X1))),
% 1.31/1.52      inference('sup-', [status(thm)], ['91', '92'])).
% 1.31/1.52  thf('94', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]:
% 1.31/1.52         ((r1_tarski @ (k1_relat_1 @ X1) @ X0) | ~ (v1_xboole_0 @ X1))),
% 1.31/1.52      inference('clc', [status(thm)], ['8', '11'])).
% 1.31/1.52  thf('95', plain,
% 1.31/1.52      (![X10 : $i, X12 : $i]:
% 1.31/1.52         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 1.31/1.52      inference('cnf', [status(esa)], [t3_subset])).
% 1.31/1.52  thf('96', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]:
% 1.31/1.52         (~ (v1_xboole_0 @ X1)
% 1.31/1.52          | (m1_subset_1 @ (k1_relat_1 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 1.31/1.52      inference('sup-', [status(thm)], ['94', '95'])).
% 1.31/1.52  thf('97', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.31/1.52         ((m1_subset_1 @ (k2_zfmisc_1 @ X1 @ X0) @ (k1_zfmisc_1 @ X2))
% 1.31/1.52          | ~ (v1_xboole_0 @ X0)
% 1.31/1.52          | ~ (v1_xboole_0 @ X3)
% 1.31/1.52          | ~ (v1_xboole_0 @ X3))),
% 1.31/1.52      inference('sup+', [status(thm)], ['93', '96'])).
% 1.31/1.52  thf('98', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.31/1.52         (~ (v1_xboole_0 @ X3)
% 1.31/1.52          | ~ (v1_xboole_0 @ X0)
% 1.31/1.52          | (m1_subset_1 @ (k2_zfmisc_1 @ X1 @ X0) @ (k1_zfmisc_1 @ X2)))),
% 1.31/1.52      inference('simplify', [status(thm)], ['97'])).
% 1.31/1.52  thf('99', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.31/1.52         ((m1_subset_1 @ (k2_zfmisc_1 @ X2 @ X1) @ (k1_zfmisc_1 @ X0))
% 1.31/1.52          | ~ (v1_xboole_0 @ X1))),
% 1.31/1.52      inference('condensation', [status(thm)], ['98'])).
% 1.31/1.52  thf('100', plain,
% 1.31/1.52      (![X0 : $i]:
% 1.31/1.52         ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 1.31/1.52          | (v1_partfun1 @ sk_C_1 @ sk_A)
% 1.31/1.52          | ~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_1)))),
% 1.31/1.52      inference('sup+', [status(thm)], ['70', '99'])).
% 1.31/1.52  thf('101', plain,
% 1.31/1.52      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1)) | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 1.31/1.52      inference('demod', [status(thm)], ['42', '43', '49'])).
% 1.31/1.52  thf('102', plain,
% 1.31/1.52      (![X0 : $i]:
% 1.31/1.52         ((v1_partfun1 @ sk_C_1 @ sk_A)
% 1.31/1.52          | (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0)))),
% 1.31/1.52      inference('clc', [status(thm)], ['100', '101'])).
% 1.31/1.52  thf('103', plain,
% 1.31/1.52      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.31/1.52         ((v4_relat_1 @ X20 @ X21)
% 1.31/1.52          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.31/1.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.31/1.52  thf('104', plain,
% 1.31/1.52      (![X1 : $i]: ((v1_partfun1 @ sk_C_1 @ sk_A) | (v4_relat_1 @ sk_C_1 @ X1))),
% 1.31/1.52      inference('sup-', [status(thm)], ['102', '103'])).
% 1.31/1.52  thf('105', plain,
% 1.31/1.52      (![X13 : $i, X14 : $i]:
% 1.31/1.52         (~ (v4_relat_1 @ X13 @ X14)
% 1.31/1.52          | (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 1.31/1.52          | ~ (v1_relat_1 @ X13))),
% 1.31/1.52      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.31/1.52  thf('106', plain,
% 1.31/1.52      (![X0 : $i]:
% 1.31/1.52         ((v1_partfun1 @ sk_C_1 @ sk_A)
% 1.31/1.52          | ~ (v1_relat_1 @ sk_C_1)
% 1.31/1.52          | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ X0))),
% 1.31/1.52      inference('sup-', [status(thm)], ['104', '105'])).
% 1.31/1.52  thf('107', plain, ((v1_relat_1 @ sk_C_1)),
% 1.31/1.52      inference('sup-', [status(thm)], ['34', '35'])).
% 1.31/1.52  thf('108', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 1.31/1.52      inference('sup-', [status(thm)], ['29', '30'])).
% 1.31/1.52  thf('109', plain,
% 1.31/1.52      (![X0 : $i]: ((v1_partfun1 @ sk_C_1 @ sk_A) | (r1_tarski @ sk_A @ X0))),
% 1.31/1.52      inference('demod', [status(thm)], ['106', '107', '108'])).
% 1.31/1.52  thf('110', plain,
% 1.31/1.52      (![X0 : $i]:
% 1.31/1.52         ((v1_partfun1 @ sk_C_1 @ sk_A)
% 1.31/1.52          | (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0)))),
% 1.31/1.52      inference('clc', [status(thm)], ['100', '101'])).
% 1.31/1.52  thf('111', plain,
% 1.31/1.52      (![X10 : $i, X11 : $i]:
% 1.31/1.52         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 1.31/1.52      inference('cnf', [status(esa)], [t3_subset])).
% 1.31/1.52  thf('112', plain,
% 1.31/1.52      (![X0 : $i]: ((v1_partfun1 @ sk_C_1 @ sk_A) | (r1_tarski @ sk_C_1 @ X0))),
% 1.31/1.52      inference('sup-', [status(thm)], ['110', '111'])).
% 1.31/1.52  thf('113', plain,
% 1.31/1.52      (![X7 : $i, X9 : $i]:
% 1.31/1.52         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 1.31/1.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.31/1.52  thf('114', plain,
% 1.31/1.52      (![X0 : $i]:
% 1.31/1.52         ((v1_partfun1 @ sk_C_1 @ sk_A)
% 1.31/1.52          | ~ (r1_tarski @ X0 @ sk_C_1)
% 1.31/1.52          | ((X0) = (sk_C_1)))),
% 1.31/1.52      inference('sup-', [status(thm)], ['112', '113'])).
% 1.31/1.52  thf('115', plain,
% 1.31/1.52      (((v1_partfun1 @ sk_C_1 @ sk_A)
% 1.31/1.52        | ((sk_A) = (sk_C_1))
% 1.31/1.52        | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 1.31/1.52      inference('sup-', [status(thm)], ['109', '114'])).
% 1.31/1.52  thf('116', plain, ((((sk_A) = (sk_C_1)) | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 1.31/1.52      inference('simplify', [status(thm)], ['115'])).
% 1.31/1.52  thf('117', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_1 @ sk_A)),
% 1.31/1.52      inference('demod', [status(thm)], ['25', '28'])).
% 1.31/1.52  thf('118', plain,
% 1.31/1.52      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.31/1.52         ((r1_tarski @ (k2_relat_1 @ X35) @ X36)
% 1.31/1.52          | ~ (zip_tseitin_0 @ X35 @ X37 @ X36 @ X38))),
% 1.31/1.52      inference('cnf', [status(esa)], [zf_stmt_7])).
% 1.31/1.52  thf('119', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)),
% 1.31/1.52      inference('sup-', [status(thm)], ['117', '118'])).
% 1.31/1.52  thf('120', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 1.31/1.52      inference('simplify', [status(thm)], ['56'])).
% 1.31/1.52  thf(t11_relset_1, axiom,
% 1.31/1.52    (![A:$i,B:$i,C:$i]:
% 1.31/1.52     ( ( v1_relat_1 @ C ) =>
% 1.31/1.52       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 1.31/1.52           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 1.31/1.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 1.31/1.52  thf('121', plain,
% 1.31/1.52      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.31/1.52         (~ (r1_tarski @ (k1_relat_1 @ X26) @ X27)
% 1.31/1.52          | ~ (r1_tarski @ (k2_relat_1 @ X26) @ X28)
% 1.31/1.52          | (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 1.31/1.52          | ~ (v1_relat_1 @ X26))),
% 1.31/1.52      inference('cnf', [status(esa)], [t11_relset_1])).
% 1.31/1.52  thf('122', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]:
% 1.31/1.52         (~ (v1_relat_1 @ X0)
% 1.31/1.52          | (m1_subset_1 @ X0 @ 
% 1.31/1.52             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 1.31/1.52          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 1.31/1.52      inference('sup-', [status(thm)], ['120', '121'])).
% 1.31/1.52  thf('123', plain,
% 1.31/1.52      (((m1_subset_1 @ sk_C_1 @ 
% 1.31/1.52         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ sk_B_1)))
% 1.31/1.52        | ~ (v1_relat_1 @ sk_C_1))),
% 1.31/1.52      inference('sup-', [status(thm)], ['119', '122'])).
% 1.31/1.52  thf('124', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 1.31/1.52      inference('sup-', [status(thm)], ['29', '30'])).
% 1.31/1.52  thf('125', plain, ((v1_relat_1 @ sk_C_1)),
% 1.31/1.52      inference('sup-', [status(thm)], ['34', '35'])).
% 1.31/1.52  thf('126', plain,
% 1.31/1.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.31/1.52      inference('demod', [status(thm)], ['123', '124', '125'])).
% 1.31/1.52  thf(cc1_funct_2, axiom,
% 1.31/1.52    (![A:$i,B:$i,C:$i]:
% 1.31/1.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.31/1.52       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 1.31/1.52         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 1.31/1.52  thf('127', plain,
% 1.31/1.52      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.31/1.52         (~ (v1_funct_1 @ X29)
% 1.31/1.52          | ~ (v1_partfun1 @ X29 @ X30)
% 1.31/1.52          | (v1_funct_2 @ X29 @ X30 @ X31)
% 1.31/1.52          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 1.31/1.52      inference('cnf', [status(esa)], [cc1_funct_2])).
% 1.31/1.52  thf('128', plain,
% 1.31/1.52      (((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 1.31/1.52        | ~ (v1_partfun1 @ sk_C_1 @ sk_A)
% 1.31/1.52        | ~ (v1_funct_1 @ sk_C_1))),
% 1.31/1.52      inference('sup-', [status(thm)], ['126', '127'])).
% 1.31/1.52  thf('129', plain, ((v1_funct_1 @ sk_C_1)),
% 1.31/1.52      inference('sup-', [status(thm)], ['37', '38'])).
% 1.31/1.52  thf('130', plain,
% 1.31/1.52      (((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1) | ~ (v1_partfun1 @ sk_C_1 @ sk_A))),
% 1.31/1.52      inference('demod', [status(thm)], ['128', '129'])).
% 1.31/1.52  thf('131', plain,
% 1.31/1.52      ((~ (v1_funct_1 @ sk_C_1)
% 1.31/1.52        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 1.31/1.52        | ~ (m1_subset_1 @ sk_C_1 @ 
% 1.31/1.52             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))),
% 1.31/1.52      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.31/1.52  thf('132', plain,
% 1.31/1.52      ((~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1))
% 1.31/1.52         <= (~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)))),
% 1.31/1.52      inference('split', [status(esa)], ['131'])).
% 1.31/1.52  thf('133', plain, ((v1_funct_1 @ sk_C_1)),
% 1.31/1.52      inference('sup-', [status(thm)], ['37', '38'])).
% 1.31/1.52  thf('134', plain, ((~ (v1_funct_1 @ sk_C_1)) <= (~ ((v1_funct_1 @ sk_C_1)))),
% 1.31/1.52      inference('split', [status(esa)], ['131'])).
% 1.31/1.52  thf('135', plain, (((v1_funct_1 @ sk_C_1))),
% 1.31/1.52      inference('sup-', [status(thm)], ['133', '134'])).
% 1.31/1.52  thf('136', plain,
% 1.31/1.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.31/1.52      inference('demod', [status(thm)], ['123', '124', '125'])).
% 1.31/1.52  thf('137', plain,
% 1.31/1.52      ((~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))
% 1.31/1.52         <= (~
% 1.31/1.52             ((m1_subset_1 @ sk_C_1 @ 
% 1.31/1.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))))),
% 1.31/1.52      inference('split', [status(esa)], ['131'])).
% 1.31/1.52  thf('138', plain,
% 1.31/1.52      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))),
% 1.31/1.52      inference('sup-', [status(thm)], ['136', '137'])).
% 1.31/1.52  thf('139', plain,
% 1.31/1.52      (~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)) | 
% 1.31/1.52       ~
% 1.31/1.52       ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))) | 
% 1.31/1.52       ~ ((v1_funct_1 @ sk_C_1))),
% 1.31/1.52      inference('split', [status(esa)], ['131'])).
% 1.31/1.52  thf('140', plain, (~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1))),
% 1.31/1.52      inference('sat_resolution*', [status(thm)], ['135', '138', '139'])).
% 1.31/1.52  thf('141', plain, (~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 1.31/1.52      inference('simpl_trail', [status(thm)], ['132', '140'])).
% 1.31/1.52  thf('142', plain, (~ (v1_partfun1 @ sk_C_1 @ sk_A)),
% 1.31/1.52      inference('clc', [status(thm)], ['130', '141'])).
% 1.31/1.52  thf('143', plain, (((sk_A) = (sk_C_1))),
% 1.31/1.52      inference('sup-', [status(thm)], ['116', '142'])).
% 1.31/1.52  thf('144', plain,
% 1.31/1.52      (((v1_partfun1 @ sk_C_1 @ sk_C_1) | (v1_xboole_0 @ sk_C_1))),
% 1.31/1.52      inference('demod', [status(thm)], ['54', '143'])).
% 1.31/1.52  thf('145', plain, (~ (v1_partfun1 @ sk_C_1 @ sk_A)),
% 1.31/1.52      inference('clc', [status(thm)], ['130', '141'])).
% 1.31/1.52  thf('146', plain, (((sk_A) = (sk_C_1))),
% 1.31/1.52      inference('sup-', [status(thm)], ['116', '142'])).
% 1.31/1.52  thf('147', plain, (~ (v1_partfun1 @ sk_C_1 @ sk_C_1)),
% 1.31/1.52      inference('demod', [status(thm)], ['145', '146'])).
% 1.31/1.52  thf('148', plain, ((v1_xboole_0 @ sk_C_1)),
% 1.31/1.52      inference('clc', [status(thm)], ['144', '147'])).
% 1.31/1.52  thf('149', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]:
% 1.31/1.52         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.31/1.52      inference('sup-', [status(thm)], ['72', '73'])).
% 1.31/1.52  thf('150', plain, (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((sk_C_1) = (X0)))),
% 1.31/1.52      inference('sup-', [status(thm)], ['148', '149'])).
% 1.31/1.52  thf('151', plain, (~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 1.31/1.52      inference('simpl_trail', [status(thm)], ['132', '140'])).
% 1.31/1.52  thf('152', plain, (((sk_A) = (sk_C_1))),
% 1.31/1.52      inference('sup-', [status(thm)], ['116', '142'])).
% 1.31/1.52  thf('153', plain, (~ (v1_funct_2 @ sk_C_1 @ sk_C_1 @ sk_B_1)),
% 1.31/1.52      inference('demod', [status(thm)], ['151', '152'])).
% 1.31/1.52  thf('154', plain,
% 1.31/1.52      (![X0 : $i]:
% 1.31/1.52         (~ (v1_funct_2 @ sk_C_1 @ X0 @ sk_B_1) | ~ (v1_xboole_0 @ X0))),
% 1.31/1.52      inference('sup-', [status(thm)], ['150', '153'])).
% 1.31/1.52  thf('155', plain,
% 1.31/1.52      ((~ (v1_xboole_0 @ sk_C_1)
% 1.31/1.52        | ~ (v1_funct_1 @ sk_C_1)
% 1.31/1.52        | ~ (v1_relat_1 @ sk_C_1)
% 1.31/1.52        | ~ (v1_xboole_0 @ (k1_relat_1 @ sk_C_1)))),
% 1.31/1.52      inference('sup-', [status(thm)], ['21', '154'])).
% 1.31/1.52  thf('156', plain, ((v1_xboole_0 @ sk_C_1)),
% 1.31/1.52      inference('clc', [status(thm)], ['144', '147'])).
% 1.31/1.52  thf('157', plain, ((v1_funct_1 @ sk_C_1)),
% 1.31/1.52      inference('sup-', [status(thm)], ['37', '38'])).
% 1.31/1.52  thf('158', plain, ((v1_relat_1 @ sk_C_1)),
% 1.31/1.52      inference('sup-', [status(thm)], ['34', '35'])).
% 1.31/1.52  thf('159', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 1.31/1.52      inference('sup-', [status(thm)], ['29', '30'])).
% 1.31/1.52  thf('160', plain, (((sk_A) = (sk_C_1))),
% 1.31/1.52      inference('sup-', [status(thm)], ['116', '142'])).
% 1.31/1.52  thf('161', plain, (((k1_relat_1 @ sk_C_1) = (sk_C_1))),
% 1.31/1.52      inference('demod', [status(thm)], ['159', '160'])).
% 1.31/1.52  thf('162', plain, ((v1_xboole_0 @ sk_C_1)),
% 1.31/1.52      inference('clc', [status(thm)], ['144', '147'])).
% 1.31/1.52  thf('163', plain, ($false),
% 1.31/1.52      inference('demod', [status(thm)],
% 1.31/1.52                ['155', '156', '157', '158', '161', '162'])).
% 1.31/1.52  
% 1.31/1.52  % SZS output end Refutation
% 1.31/1.52  
% 1.31/1.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
