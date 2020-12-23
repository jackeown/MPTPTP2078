%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HFz8am39Ez

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:20 EST 2020

% Result     : Theorem 0.66s
% Output     : Refutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :  230 ( 797 expanded)
%              Number of leaves         :   50 ( 265 expanded)
%              Depth                    :   22
%              Number of atoms          : 1928 (16796 expanded)
%              Number of equality atoms :  140 (1155 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t36_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ C )
                = B )
              & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
              & ( v2_funct_1 @ C ) )
           => ( ( A = k1_xboole_0 )
              | ( B = k1_xboole_0 )
              | ( D
                = ( k2_funct_1 @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( ( ( k2_relset_1 @ A @ B @ C )
                  = B )
                & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
                & ( v2_funct_1 @ C ) )
             => ( ( A = k1_xboole_0 )
                | ( B = k1_xboole_0 )
                | ( D
                  = ( k2_funct_1 @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_funct_2])).

thf('0',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ X6 )
        = ( k4_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('2',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('5',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('7',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','7','8'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('10',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('11',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['5','6'])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['11','12','13','14'])).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('16',plain,(
    ! [X4: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X4 ) )
        = X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('17',plain,(
    ! [X5: $i] :
      ( ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['5','6'])).

thf('21',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
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

thf('23',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ( X34
        = ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('24',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('25',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('27',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('28',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('33',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('34',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['24','31','34'])).

thf('36',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['21','35'])).

thf('37',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('40',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ( ( k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45 )
        = ( k5_relat_1 @ X42 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['37','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( m1_subset_1 @ ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) )).

thf('50',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X14 @ X15 @ X17 @ X18 @ X13 @ X16 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relset_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('55',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k4_relset_1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 )
        = ( k5_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','57'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('59',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( X28 = X31 )
      | ~ ( r2_relset_1 @ X29 @ X30 @ X28 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','60'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('62',plain,(
    ! [X41: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('63',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62'])).

thf(l72_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ! [D: $i] :
              ( ( ( v1_relat_1 @ D )
                & ( v1_funct_1 @ D ) )
             => ( ( ( ( k2_relat_1 @ B )
                    = A )
                  & ( ( k5_relat_1 @ B @ C )
                    = ( k6_relat_1 @ ( k1_relat_1 @ D ) ) )
                  & ( ( k5_relat_1 @ C @ D )
                    = ( k6_relat_1 @ A ) ) )
               => ( D = B ) ) ) ) ) )).

thf('64',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( ( k2_relat_1 @ X10 )
       != X9 )
      | ( ( k5_relat_1 @ X10 @ X8 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X11 ) ) )
      | ( ( k5_relat_1 @ X8 @ X11 )
       != ( k6_relat_1 @ X9 ) )
      | ( X11 = X10 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l72_funct_1])).

thf('65',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X11 = X10 )
      | ( ( k5_relat_1 @ X8 @ X11 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X10 ) ) )
      | ( ( k5_relat_1 @ X10 @ X8 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('66',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('67',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('68',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X11 = X10 )
      | ( ( k5_relat_1 @ X8 @ X11 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X10 ) ) )
      | ( ( k5_relat_1 @ X10 @ X8 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ sk_A )
       != ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k5_relat_1 @ X0 @ sk_C )
       != ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) )
      | ( sk_D = X0 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['5','6'])).

thf('71',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ( X34
        = ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('74',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('76',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('78',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['79','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('84',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['74','81','84'])).

thf('86',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('89',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('91',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ sk_A )
       != ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ( ( k5_relat_1 @ X0 @ sk_C )
       != ( k6_partfun1 @ sk_B ) )
      | ( sk_D = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70','71','85','86','91'])).

thf('93',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ( sk_D
      = ( k4_relat_1 @ sk_C ) )
    | ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
     != ( k6_partfun1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','92'])).

thf('94',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['11','12','13','14'])).

thf('95',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','7','8'])).

thf('96',plain,(
    ! [X7: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('97',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['5','6'])).

thf('99',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['97','98','99','100'])).

thf('102',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','7','8'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('103',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X12 ) @ X12 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('104',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('105',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X12 ) @ X12 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['102','105'])).

thf('107',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['5','6'])).

thf('108',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['106','107','108','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf('112',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( v2_funct_1 @ X49 )
      | ( ( k2_relset_1 @ X51 @ X50 @ X49 )
       != X50 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X49 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X50 ) ) )
      | ~ ( v1_funct_2 @ X49 @ X51 @ X50 )
      | ~ ( v1_funct_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('113',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','7','8'])).

thf('117',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['113','114','115','116','117','118'])).

thf('120',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('122',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X4: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X4 ) )
        = X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('124',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['97','98','99','100'])).

thf('125',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ X6 )
        = ( k4_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('126',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ( ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) )
      = ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['11','12','13','14'])).

thf('128',plain,
    ( ( ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) )
      = ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','7','8'])).

thf('130',plain,(
    ! [X7: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('131',plain,
    ( ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['5','6'])).

thf('133',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['131','132','133','134'])).

thf('136',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['128','135'])).

thf('137',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('138',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['136','137'])).

thf('139',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['11','12','13','14'])).

thf('140',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['97','98','99','100'])).

thf('141',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['131','132','133','134'])).

thf('142',plain,(
    v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['138','139','140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('144',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['11','12','13','14'])).

thf('146',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['123','146'])).

thf('148',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['5','6'])).

thf('149',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['122','149'])).

thf('151',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( v2_funct_1 @ X49 )
      | ( ( k2_relset_1 @ X51 @ X50 @ X49 )
       != X50 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X49 ) @ X50 @ X51 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X50 ) ) )
      | ~ ( v1_funct_2 @ X49 @ X51 @ X50 )
      | ~ ( v1_funct_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('153',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','7','8'])).

thf('157',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['153','154','155','156','157','158'])).

thf('160',plain,(
    v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ( X34
        = ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('162',plain,
    ( ~ ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('164',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('165',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('166',plain,
    ( ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['163','166'])).

thf('168',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['167','168'])).

thf('170',plain,
    ( sk_B
    = ( k1_relset_1 @ sk_B @ sk_A @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['162','169'])).

thf('171',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['150','170'])).

thf('172',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['110','171'])).

thf('173',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ( sk_D
      = ( k4_relat_1 @ sk_C ) )
    | ( ( k6_partfun1 @ sk_B )
     != ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['93','94','101','172'])).

thf('174',plain,
    ( sk_D
    = ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','7','8'])).

thf('177',plain,(
    sk_D
 != ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('178',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['174','177'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HFz8am39Ez
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:53:17 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.66/0.85  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.66/0.85  % Solved by: fo/fo7.sh
% 0.66/0.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.66/0.85  % done 327 iterations in 0.386s
% 0.66/0.85  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.66/0.85  % SZS output start Refutation
% 0.66/0.85  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.66/0.85  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.66/0.85  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.66/0.85  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.66/0.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.66/0.85  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.66/0.85  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.66/0.85  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.66/0.85  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.66/0.85  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.66/0.85  thf(sk_D_type, type, sk_D: $i).
% 0.66/0.85  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.66/0.85  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.66/0.85  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.66/0.85  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.66/0.85  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.66/0.85  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.66/0.85  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.66/0.85  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.66/0.85  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.66/0.85  thf(sk_B_type, type, sk_B: $i).
% 0.66/0.85  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.66/0.85  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.66/0.85  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 0.66/0.85  thf(sk_A_type, type, sk_A: $i).
% 0.66/0.85  thf(sk_C_type, type, sk_C: $i).
% 0.66/0.85  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.66/0.85  thf(t36_funct_2, conjecture,
% 0.66/0.85    (![A:$i,B:$i,C:$i]:
% 0.66/0.85     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.66/0.85         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.66/0.85       ( ![D:$i]:
% 0.66/0.85         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.66/0.85             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.66/0.85           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.66/0.85               ( r2_relset_1 @
% 0.66/0.85                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.66/0.85                 ( k6_partfun1 @ A ) ) & 
% 0.66/0.85               ( v2_funct_1 @ C ) ) =>
% 0.66/0.85             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.66/0.85               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.66/0.85  thf(zf_stmt_0, negated_conjecture,
% 0.66/0.85    (~( ![A:$i,B:$i,C:$i]:
% 0.66/0.85        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.66/0.85            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.66/0.85          ( ![D:$i]:
% 0.66/0.85            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.66/0.85                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.66/0.85              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.66/0.85                  ( r2_relset_1 @
% 0.66/0.85                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.66/0.85                    ( k6_partfun1 @ A ) ) & 
% 0.66/0.85                  ( v2_funct_1 @ C ) ) =>
% 0.66/0.85                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.66/0.85                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.66/0.85    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.66/0.85  thf('0', plain, ((v1_funct_1 @ sk_C)),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf(d9_funct_1, axiom,
% 0.66/0.85    (![A:$i]:
% 0.66/0.85     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.66/0.85       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.66/0.85  thf('1', plain,
% 0.66/0.85      (![X6 : $i]:
% 0.66/0.85         (~ (v2_funct_1 @ X6)
% 0.66/0.85          | ((k2_funct_1 @ X6) = (k4_relat_1 @ X6))
% 0.66/0.85          | ~ (v1_funct_1 @ X6)
% 0.66/0.85          | ~ (v1_relat_1 @ X6))),
% 0.66/0.85      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.66/0.85  thf('2', plain,
% 0.66/0.85      ((~ (v1_relat_1 @ sk_C)
% 0.66/0.85        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 0.66/0.85        | ~ (v2_funct_1 @ sk_C))),
% 0.66/0.85      inference('sup-', [status(thm)], ['0', '1'])).
% 0.66/0.85  thf('3', plain,
% 0.66/0.85      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf(cc2_relat_1, axiom,
% 0.66/0.85    (![A:$i]:
% 0.66/0.85     ( ( v1_relat_1 @ A ) =>
% 0.66/0.85       ( ![B:$i]:
% 0.66/0.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.66/0.85  thf('4', plain,
% 0.66/0.85      (![X0 : $i, X1 : $i]:
% 0.66/0.85         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.66/0.85          | (v1_relat_1 @ X0)
% 0.66/0.85          | ~ (v1_relat_1 @ X1))),
% 0.66/0.85      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.66/0.85  thf('5', plain,
% 0.66/0.85      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.66/0.85      inference('sup-', [status(thm)], ['3', '4'])).
% 0.66/0.85  thf(fc6_relat_1, axiom,
% 0.66/0.85    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.66/0.85  thf('6', plain,
% 0.66/0.85      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.66/0.85      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.66/0.85  thf('7', plain, ((v1_relat_1 @ sk_C)),
% 0.66/0.85      inference('demod', [status(thm)], ['5', '6'])).
% 0.66/0.85  thf('8', plain, ((v2_funct_1 @ sk_C)),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('9', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.66/0.85      inference('demod', [status(thm)], ['2', '7', '8'])).
% 0.66/0.85  thf(fc6_funct_1, axiom,
% 0.66/0.85    (![A:$i]:
% 0.66/0.85     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.66/0.85       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.66/0.85         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.66/0.85         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.66/0.85  thf('10', plain,
% 0.66/0.85      (![X7 : $i]:
% 0.66/0.85         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 0.66/0.85          | ~ (v2_funct_1 @ X7)
% 0.66/0.85          | ~ (v1_funct_1 @ X7)
% 0.66/0.85          | ~ (v1_relat_1 @ X7))),
% 0.66/0.85      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.66/0.85  thf('11', plain,
% 0.66/0.85      (((v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.66/0.85        | ~ (v1_relat_1 @ sk_C)
% 0.66/0.85        | ~ (v1_funct_1 @ sk_C)
% 0.66/0.85        | ~ (v2_funct_1 @ sk_C))),
% 0.66/0.85      inference('sup+', [status(thm)], ['9', '10'])).
% 0.66/0.85  thf('12', plain, ((v1_relat_1 @ sk_C)),
% 0.66/0.85      inference('demod', [status(thm)], ['5', '6'])).
% 0.66/0.85  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('14', plain, ((v2_funct_1 @ sk_C)),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('15', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.66/0.85      inference('demod', [status(thm)], ['11', '12', '13', '14'])).
% 0.66/0.85  thf(involutiveness_k4_relat_1, axiom,
% 0.66/0.85    (![A:$i]:
% 0.66/0.85     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 0.66/0.85  thf('16', plain,
% 0.66/0.85      (![X4 : $i]:
% 0.66/0.85         (((k4_relat_1 @ (k4_relat_1 @ X4)) = (X4)) | ~ (v1_relat_1 @ X4))),
% 0.66/0.85      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 0.66/0.85  thf(t37_relat_1, axiom,
% 0.66/0.85    (![A:$i]:
% 0.66/0.85     ( ( v1_relat_1 @ A ) =>
% 0.66/0.85       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.66/0.85         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.66/0.85  thf('17', plain,
% 0.66/0.85      (![X5 : $i]:
% 0.66/0.85         (((k2_relat_1 @ X5) = (k1_relat_1 @ (k4_relat_1 @ X5)))
% 0.66/0.85          | ~ (v1_relat_1 @ X5))),
% 0.66/0.85      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.66/0.85  thf('18', plain,
% 0.66/0.85      (![X0 : $i]:
% 0.66/0.85         (((k2_relat_1 @ (k4_relat_1 @ X0)) = (k1_relat_1 @ X0))
% 0.66/0.85          | ~ (v1_relat_1 @ X0)
% 0.66/0.85          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.66/0.85      inference('sup+', [status(thm)], ['16', '17'])).
% 0.66/0.85  thf('19', plain,
% 0.66/0.85      ((~ (v1_relat_1 @ sk_C)
% 0.66/0.85        | ((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C)))),
% 0.66/0.85      inference('sup-', [status(thm)], ['15', '18'])).
% 0.66/0.85  thf('20', plain, ((v1_relat_1 @ sk_C)),
% 0.66/0.85      inference('demod', [status(thm)], ['5', '6'])).
% 0.66/0.85  thf('21', plain,
% 0.66/0.85      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.66/0.85      inference('demod', [status(thm)], ['19', '20'])).
% 0.66/0.85  thf('22', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf(d1_funct_2, axiom,
% 0.66/0.85    (![A:$i,B:$i,C:$i]:
% 0.66/0.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.66/0.85       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.66/0.85           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.66/0.85             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.66/0.85         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.66/0.85           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.66/0.85             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.66/0.85  thf(zf_stmt_1, axiom,
% 0.66/0.85    (![C:$i,B:$i,A:$i]:
% 0.66/0.85     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.66/0.85       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.66/0.85  thf('23', plain,
% 0.66/0.85      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.66/0.85         (~ (v1_funct_2 @ X36 @ X34 @ X35)
% 0.66/0.85          | ((X34) = (k1_relset_1 @ X34 @ X35 @ X36))
% 0.66/0.85          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.66/0.85  thf('24', plain,
% 0.66/0.85      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.66/0.85        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.66/0.85      inference('sup-', [status(thm)], ['22', '23'])).
% 0.66/0.85  thf(zf_stmt_2, axiom,
% 0.66/0.85    (![B:$i,A:$i]:
% 0.66/0.85     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.66/0.85       ( zip_tseitin_0 @ B @ A ) ))).
% 0.66/0.85  thf('25', plain,
% 0.66/0.85      (![X32 : $i, X33 : $i]:
% 0.66/0.85         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.66/0.85  thf('26', plain,
% 0.66/0.85      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.66/0.85  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.66/0.85  thf(zf_stmt_5, axiom,
% 0.66/0.85    (![A:$i,B:$i,C:$i]:
% 0.66/0.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.66/0.85       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.66/0.85         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.66/0.85           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.66/0.85             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.66/0.85  thf('27', plain,
% 0.66/0.85      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.66/0.85         (~ (zip_tseitin_0 @ X37 @ X38)
% 0.66/0.85          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 0.66/0.85          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.66/0.85  thf('28', plain,
% 0.66/0.85      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.66/0.85      inference('sup-', [status(thm)], ['26', '27'])).
% 0.66/0.85  thf('29', plain,
% 0.66/0.85      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.66/0.85      inference('sup-', [status(thm)], ['25', '28'])).
% 0.66/0.85  thf('30', plain, (((sk_B) != (k1_xboole_0))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('31', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.66/0.85      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.66/0.85  thf('32', plain,
% 0.66/0.85      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf(redefinition_k1_relset_1, axiom,
% 0.66/0.85    (![A:$i,B:$i,C:$i]:
% 0.66/0.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.66/0.85       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.66/0.85  thf('33', plain,
% 0.66/0.85      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.66/0.85         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 0.66/0.85          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.66/0.85      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.66/0.85  thf('34', plain,
% 0.66/0.85      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.66/0.85      inference('sup-', [status(thm)], ['32', '33'])).
% 0.66/0.85  thf('35', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.66/0.85      inference('demod', [status(thm)], ['24', '31', '34'])).
% 0.66/0.85  thf('36', plain, (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (sk_A))),
% 0.66/0.85      inference('demod', [status(thm)], ['21', '35'])).
% 0.66/0.85  thf('37', plain,
% 0.66/0.85      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.66/0.85        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.66/0.85        (k6_partfun1 @ sk_A))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('38', plain,
% 0.66/0.85      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('39', plain,
% 0.66/0.85      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf(redefinition_k1_partfun1, axiom,
% 0.66/0.85    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.66/0.85     ( ( ( v1_funct_1 @ E ) & 
% 0.66/0.85         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.66/0.85         ( v1_funct_1 @ F ) & 
% 0.66/0.85         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.66/0.85       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.66/0.85  thf('40', plain,
% 0.66/0.85      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.66/0.85         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 0.66/0.85          | ~ (v1_funct_1 @ X42)
% 0.66/0.85          | ~ (v1_funct_1 @ X45)
% 0.66/0.85          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 0.66/0.85          | ((k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45)
% 0.66/0.85              = (k5_relat_1 @ X42 @ X45)))),
% 0.66/0.85      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.66/0.85  thf('41', plain,
% 0.66/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.85         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.66/0.85            = (k5_relat_1 @ sk_C @ X0))
% 0.66/0.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.66/0.85          | ~ (v1_funct_1 @ X0)
% 0.66/0.85          | ~ (v1_funct_1 @ sk_C))),
% 0.66/0.85      inference('sup-', [status(thm)], ['39', '40'])).
% 0.66/0.85  thf('42', plain, ((v1_funct_1 @ sk_C)),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('43', plain,
% 0.66/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.85         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.66/0.85            = (k5_relat_1 @ sk_C @ X0))
% 0.66/0.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.66/0.85          | ~ (v1_funct_1 @ X0))),
% 0.66/0.85      inference('demod', [status(thm)], ['41', '42'])).
% 0.66/0.85  thf('44', plain,
% 0.66/0.85      ((~ (v1_funct_1 @ sk_D)
% 0.66/0.85        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.66/0.85            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.66/0.85      inference('sup-', [status(thm)], ['38', '43'])).
% 0.66/0.85  thf('45', plain, ((v1_funct_1 @ sk_D)),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('46', plain,
% 0.66/0.85      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.66/0.85         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.66/0.85      inference('demod', [status(thm)], ['44', '45'])).
% 0.66/0.85  thf('47', plain,
% 0.66/0.85      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.66/0.85        (k6_partfun1 @ sk_A))),
% 0.66/0.85      inference('demod', [status(thm)], ['37', '46'])).
% 0.66/0.85  thf('48', plain,
% 0.66/0.85      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('49', plain,
% 0.66/0.85      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf(dt_k4_relset_1, axiom,
% 0.66/0.85    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.66/0.85     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.66/0.85         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.66/0.85       ( m1_subset_1 @
% 0.66/0.85         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.66/0.85         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 0.66/0.85  thf('50', plain,
% 0.66/0.85      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.66/0.85         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.66/0.85          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.66/0.85          | (m1_subset_1 @ (k4_relset_1 @ X14 @ X15 @ X17 @ X18 @ X13 @ X16) @ 
% 0.66/0.85             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X18))))),
% 0.66/0.85      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 0.66/0.85  thf('51', plain,
% 0.66/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.85         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.66/0.85           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.66/0.85          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 0.66/0.85      inference('sup-', [status(thm)], ['49', '50'])).
% 0.66/0.85  thf('52', plain,
% 0.66/0.85      ((m1_subset_1 @ 
% 0.66/0.85        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.66/0.85        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.66/0.85      inference('sup-', [status(thm)], ['48', '51'])).
% 0.66/0.85  thf('53', plain,
% 0.66/0.85      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('54', plain,
% 0.66/0.85      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf(redefinition_k4_relset_1, axiom,
% 0.66/0.85    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.66/0.85     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.66/0.85         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.66/0.85       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.66/0.85  thf('55', plain,
% 0.66/0.85      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.66/0.85         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.66/0.85          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.66/0.85          | ((k4_relset_1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25)
% 0.66/0.85              = (k5_relat_1 @ X22 @ X25)))),
% 0.66/0.85      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 0.66/0.85  thf('56', plain,
% 0.66/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.85         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.66/0.85            = (k5_relat_1 @ sk_C @ X0))
% 0.66/0.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.66/0.85      inference('sup-', [status(thm)], ['54', '55'])).
% 0.66/0.85  thf('57', plain,
% 0.66/0.85      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.66/0.85         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.66/0.85      inference('sup-', [status(thm)], ['53', '56'])).
% 0.66/0.85  thf('58', plain,
% 0.66/0.85      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.66/0.85        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.66/0.85      inference('demod', [status(thm)], ['52', '57'])).
% 0.66/0.85  thf(redefinition_r2_relset_1, axiom,
% 0.66/0.85    (![A:$i,B:$i,C:$i,D:$i]:
% 0.66/0.85     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.66/0.85         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.66/0.85       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.66/0.85  thf('59', plain,
% 0.66/0.85      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.66/0.85         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.66/0.85          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.66/0.85          | ((X28) = (X31))
% 0.66/0.85          | ~ (r2_relset_1 @ X29 @ X30 @ X28 @ X31))),
% 0.66/0.85      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.66/0.85  thf('60', plain,
% 0.66/0.85      (![X0 : $i]:
% 0.66/0.85         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 0.66/0.85          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 0.66/0.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.66/0.85      inference('sup-', [status(thm)], ['58', '59'])).
% 0.66/0.85  thf('61', plain,
% 0.66/0.85      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.66/0.85           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.66/0.85        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 0.66/0.85      inference('sup-', [status(thm)], ['47', '60'])).
% 0.66/0.85  thf(dt_k6_partfun1, axiom,
% 0.66/0.85    (![A:$i]:
% 0.66/0.85     ( ( m1_subset_1 @
% 0.66/0.85         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.66/0.85       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.66/0.85  thf('62', plain,
% 0.66/0.85      (![X41 : $i]:
% 0.66/0.85         (m1_subset_1 @ (k6_partfun1 @ X41) @ 
% 0.66/0.85          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))),
% 0.66/0.85      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.66/0.85  thf('63', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.66/0.85      inference('demod', [status(thm)], ['61', '62'])).
% 0.66/0.85  thf(l72_funct_1, axiom,
% 0.66/0.85    (![A:$i,B:$i]:
% 0.66/0.85     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.66/0.85       ( ![C:$i]:
% 0.66/0.85         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.66/0.85           ( ![D:$i]:
% 0.66/0.85             ( ( ( v1_relat_1 @ D ) & ( v1_funct_1 @ D ) ) =>
% 0.66/0.85               ( ( ( ( k2_relat_1 @ B ) = ( A ) ) & 
% 0.66/0.85                   ( ( k5_relat_1 @ B @ C ) =
% 0.66/0.85                     ( k6_relat_1 @ ( k1_relat_1 @ D ) ) ) & 
% 0.66/0.85                   ( ( k5_relat_1 @ C @ D ) = ( k6_relat_1 @ A ) ) ) =>
% 0.66/0.85                 ( ( D ) = ( B ) ) ) ) ) ) ) ))).
% 0.66/0.85  thf('64', plain,
% 0.66/0.85      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.66/0.85         (~ (v1_relat_1 @ X8)
% 0.66/0.85          | ~ (v1_funct_1 @ X8)
% 0.66/0.85          | ((k2_relat_1 @ X10) != (X9))
% 0.66/0.85          | ((k5_relat_1 @ X10 @ X8) != (k6_relat_1 @ (k1_relat_1 @ X11)))
% 0.66/0.85          | ((k5_relat_1 @ X8 @ X11) != (k6_relat_1 @ X9))
% 0.66/0.85          | ((X11) = (X10))
% 0.66/0.85          | ~ (v1_funct_1 @ X11)
% 0.66/0.85          | ~ (v1_relat_1 @ X11)
% 0.66/0.85          | ~ (v1_funct_1 @ X10)
% 0.66/0.85          | ~ (v1_relat_1 @ X10))),
% 0.66/0.85      inference('cnf', [status(esa)], [l72_funct_1])).
% 0.66/0.85  thf('65', plain,
% 0.66/0.85      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.66/0.85         (~ (v1_relat_1 @ X10)
% 0.66/0.85          | ~ (v1_funct_1 @ X10)
% 0.66/0.85          | ~ (v1_relat_1 @ X11)
% 0.66/0.85          | ~ (v1_funct_1 @ X11)
% 0.66/0.85          | ((X11) = (X10))
% 0.66/0.85          | ((k5_relat_1 @ X8 @ X11) != (k6_relat_1 @ (k2_relat_1 @ X10)))
% 0.66/0.85          | ((k5_relat_1 @ X10 @ X8) != (k6_relat_1 @ (k1_relat_1 @ X11)))
% 0.66/0.85          | ~ (v1_funct_1 @ X8)
% 0.66/0.85          | ~ (v1_relat_1 @ X8))),
% 0.66/0.85      inference('simplify', [status(thm)], ['64'])).
% 0.66/0.85  thf(redefinition_k6_partfun1, axiom,
% 0.66/0.85    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.66/0.85  thf('66', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 0.66/0.85      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.66/0.85  thf('67', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 0.66/0.85      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.66/0.85  thf('68', plain,
% 0.66/0.85      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.66/0.85         (~ (v1_relat_1 @ X10)
% 0.66/0.85          | ~ (v1_funct_1 @ X10)
% 0.66/0.85          | ~ (v1_relat_1 @ X11)
% 0.66/0.85          | ~ (v1_funct_1 @ X11)
% 0.66/0.85          | ((X11) = (X10))
% 0.66/0.85          | ((k5_relat_1 @ X8 @ X11) != (k6_partfun1 @ (k2_relat_1 @ X10)))
% 0.66/0.85          | ((k5_relat_1 @ X10 @ X8) != (k6_partfun1 @ (k1_relat_1 @ X11)))
% 0.66/0.85          | ~ (v1_funct_1 @ X8)
% 0.66/0.85          | ~ (v1_relat_1 @ X8))),
% 0.66/0.85      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.66/0.85  thf('69', plain,
% 0.66/0.85      (![X0 : $i]:
% 0.66/0.85         (((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ X0)))
% 0.66/0.85          | ~ (v1_relat_1 @ sk_C)
% 0.66/0.85          | ~ (v1_funct_1 @ sk_C)
% 0.66/0.85          | ((k5_relat_1 @ X0 @ sk_C) != (k6_partfun1 @ (k1_relat_1 @ sk_D)))
% 0.66/0.85          | ((sk_D) = (X0))
% 0.66/0.85          | ~ (v1_funct_1 @ sk_D)
% 0.66/0.85          | ~ (v1_relat_1 @ sk_D)
% 0.66/0.85          | ~ (v1_funct_1 @ X0)
% 0.66/0.85          | ~ (v1_relat_1 @ X0))),
% 0.66/0.85      inference('sup-', [status(thm)], ['63', '68'])).
% 0.66/0.85  thf('70', plain, ((v1_relat_1 @ sk_C)),
% 0.66/0.85      inference('demod', [status(thm)], ['5', '6'])).
% 0.66/0.85  thf('71', plain, ((v1_funct_1 @ sk_C)),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('72', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('73', plain,
% 0.66/0.85      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.66/0.85         (~ (v1_funct_2 @ X36 @ X34 @ X35)
% 0.66/0.85          | ((X34) = (k1_relset_1 @ X34 @ X35 @ X36))
% 0.66/0.85          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.66/0.85  thf('74', plain,
% 0.66/0.85      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 0.66/0.85        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 0.66/0.85      inference('sup-', [status(thm)], ['72', '73'])).
% 0.66/0.85  thf('75', plain,
% 0.66/0.85      (![X32 : $i, X33 : $i]:
% 0.66/0.85         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.66/0.85  thf('76', plain,
% 0.66/0.85      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('77', plain,
% 0.66/0.85      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.66/0.85         (~ (zip_tseitin_0 @ X37 @ X38)
% 0.66/0.85          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 0.66/0.85          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.66/0.85  thf('78', plain,
% 0.66/0.85      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 0.66/0.85      inference('sup-', [status(thm)], ['76', '77'])).
% 0.66/0.85  thf('79', plain,
% 0.66/0.85      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 0.66/0.85      inference('sup-', [status(thm)], ['75', '78'])).
% 0.66/0.85  thf('80', plain, (((sk_A) != (k1_xboole_0))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('81', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 0.66/0.85      inference('simplify_reflect-', [status(thm)], ['79', '80'])).
% 0.66/0.85  thf('82', plain,
% 0.66/0.85      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('83', plain,
% 0.66/0.85      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.66/0.85         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 0.66/0.85          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.66/0.85      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.66/0.85  thf('84', plain,
% 0.66/0.85      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.66/0.85      inference('sup-', [status(thm)], ['82', '83'])).
% 0.66/0.85  thf('85', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.66/0.85      inference('demod', [status(thm)], ['74', '81', '84'])).
% 0.66/0.85  thf('86', plain, ((v1_funct_1 @ sk_D)),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('87', plain,
% 0.66/0.85      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('88', plain,
% 0.66/0.85      (![X0 : $i, X1 : $i]:
% 0.66/0.85         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.66/0.85          | (v1_relat_1 @ X0)
% 0.66/0.85          | ~ (v1_relat_1 @ X1))),
% 0.66/0.85      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.66/0.85  thf('89', plain,
% 0.66/0.85      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.66/0.85      inference('sup-', [status(thm)], ['87', '88'])).
% 0.66/0.85  thf('90', plain,
% 0.66/0.85      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.66/0.85      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.66/0.85  thf('91', plain, ((v1_relat_1 @ sk_D)),
% 0.66/0.85      inference('demod', [status(thm)], ['89', '90'])).
% 0.66/0.85  thf('92', plain,
% 0.66/0.85      (![X0 : $i]:
% 0.66/0.85         (((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ X0)))
% 0.66/0.85          | ((k5_relat_1 @ X0 @ sk_C) != (k6_partfun1 @ sk_B))
% 0.66/0.85          | ((sk_D) = (X0))
% 0.66/0.85          | ~ (v1_funct_1 @ X0)
% 0.66/0.85          | ~ (v1_relat_1 @ X0))),
% 0.66/0.85      inference('demod', [status(thm)], ['69', '70', '71', '85', '86', '91'])).
% 0.66/0.85  thf('93', plain,
% 0.66/0.85      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 0.66/0.85        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.66/0.85        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.66/0.85        | ((sk_D) = (k4_relat_1 @ sk_C))
% 0.66/0.85        | ((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C) != (k6_partfun1 @ sk_B)))),
% 0.66/0.85      inference('sup-', [status(thm)], ['36', '92'])).
% 0.66/0.85  thf('94', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.66/0.85      inference('demod', [status(thm)], ['11', '12', '13', '14'])).
% 0.66/0.85  thf('95', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.66/0.85      inference('demod', [status(thm)], ['2', '7', '8'])).
% 0.66/0.85  thf('96', plain,
% 0.66/0.85      (![X7 : $i]:
% 0.66/0.85         ((v1_funct_1 @ (k2_funct_1 @ X7))
% 0.66/0.85          | ~ (v2_funct_1 @ X7)
% 0.66/0.85          | ~ (v1_funct_1 @ X7)
% 0.66/0.85          | ~ (v1_relat_1 @ X7))),
% 0.66/0.85      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.66/0.85  thf('97', plain,
% 0.66/0.85      (((v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.66/0.85        | ~ (v1_relat_1 @ sk_C)
% 0.66/0.85        | ~ (v1_funct_1 @ sk_C)
% 0.66/0.85        | ~ (v2_funct_1 @ sk_C))),
% 0.66/0.85      inference('sup+', [status(thm)], ['95', '96'])).
% 0.66/0.85  thf('98', plain, ((v1_relat_1 @ sk_C)),
% 0.66/0.85      inference('demod', [status(thm)], ['5', '6'])).
% 0.66/0.85  thf('99', plain, ((v1_funct_1 @ sk_C)),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('100', plain, ((v2_funct_1 @ sk_C)),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('101', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.66/0.85      inference('demod', [status(thm)], ['97', '98', '99', '100'])).
% 0.66/0.85  thf('102', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.66/0.85      inference('demod', [status(thm)], ['2', '7', '8'])).
% 0.66/0.85  thf(t61_funct_1, axiom,
% 0.66/0.85    (![A:$i]:
% 0.66/0.85     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.66/0.85       ( ( v2_funct_1 @ A ) =>
% 0.66/0.85         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.66/0.85             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.66/0.85           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.66/0.85             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.66/0.85  thf('103', plain,
% 0.66/0.85      (![X12 : $i]:
% 0.66/0.85         (~ (v2_funct_1 @ X12)
% 0.66/0.85          | ((k5_relat_1 @ (k2_funct_1 @ X12) @ X12)
% 0.66/0.85              = (k6_relat_1 @ (k2_relat_1 @ X12)))
% 0.66/0.85          | ~ (v1_funct_1 @ X12)
% 0.66/0.85          | ~ (v1_relat_1 @ X12))),
% 0.66/0.85      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.66/0.85  thf('104', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 0.66/0.85      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.66/0.85  thf('105', plain,
% 0.66/0.85      (![X12 : $i]:
% 0.66/0.85         (~ (v2_funct_1 @ X12)
% 0.66/0.85          | ((k5_relat_1 @ (k2_funct_1 @ X12) @ X12)
% 0.66/0.85              = (k6_partfun1 @ (k2_relat_1 @ X12)))
% 0.66/0.85          | ~ (v1_funct_1 @ X12)
% 0.66/0.85          | ~ (v1_relat_1 @ X12))),
% 0.66/0.85      inference('demod', [status(thm)], ['103', '104'])).
% 0.66/0.85  thf('106', plain,
% 0.66/0.85      ((((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C)
% 0.66/0.85          = (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 0.66/0.85        | ~ (v1_relat_1 @ sk_C)
% 0.66/0.85        | ~ (v1_funct_1 @ sk_C)
% 0.66/0.85        | ~ (v2_funct_1 @ sk_C))),
% 0.66/0.85      inference('sup+', [status(thm)], ['102', '105'])).
% 0.66/0.85  thf('107', plain, ((v1_relat_1 @ sk_C)),
% 0.66/0.85      inference('demod', [status(thm)], ['5', '6'])).
% 0.66/0.85  thf('108', plain, ((v1_funct_1 @ sk_C)),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('109', plain, ((v2_funct_1 @ sk_C)),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('110', plain,
% 0.66/0.85      (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C)
% 0.66/0.85         = (k6_partfun1 @ (k2_relat_1 @ sk_C)))),
% 0.66/0.85      inference('demod', [status(thm)], ['106', '107', '108', '109'])).
% 0.66/0.85  thf('111', plain,
% 0.66/0.85      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf(t31_funct_2, axiom,
% 0.66/0.85    (![A:$i,B:$i,C:$i]:
% 0.66/0.85     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.66/0.85         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.66/0.85       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.66/0.85         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.66/0.85           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.66/0.85           ( m1_subset_1 @
% 0.66/0.85             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.66/0.85  thf('112', plain,
% 0.66/0.85      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.66/0.85         (~ (v2_funct_1 @ X49)
% 0.66/0.85          | ((k2_relset_1 @ X51 @ X50 @ X49) != (X50))
% 0.66/0.85          | (m1_subset_1 @ (k2_funct_1 @ X49) @ 
% 0.66/0.85             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 0.66/0.85          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X50)))
% 0.66/0.85          | ~ (v1_funct_2 @ X49 @ X51 @ X50)
% 0.66/0.85          | ~ (v1_funct_1 @ X49))),
% 0.66/0.85      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.66/0.85  thf('113', plain,
% 0.66/0.85      ((~ (v1_funct_1 @ sk_C)
% 0.66/0.85        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.66/0.85        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.66/0.85           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.66/0.85        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.66/0.85        | ~ (v2_funct_1 @ sk_C))),
% 0.66/0.85      inference('sup-', [status(thm)], ['111', '112'])).
% 0.66/0.85  thf('114', plain, ((v1_funct_1 @ sk_C)),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('115', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('116', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.66/0.85      inference('demod', [status(thm)], ['2', '7', '8'])).
% 0.66/0.85  thf('117', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('118', plain, ((v2_funct_1 @ sk_C)),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('119', plain,
% 0.66/0.85      (((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.66/0.85         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.66/0.85        | ((sk_B) != (sk_B)))),
% 0.66/0.85      inference('demod', [status(thm)],
% 0.66/0.85                ['113', '114', '115', '116', '117', '118'])).
% 0.66/0.85  thf('120', plain,
% 0.66/0.85      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.66/0.85        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.66/0.85      inference('simplify', [status(thm)], ['119'])).
% 0.66/0.85  thf('121', plain,
% 0.66/0.85      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.66/0.85         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 0.66/0.85          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.66/0.85      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.66/0.85  thf('122', plain,
% 0.66/0.85      (((k1_relset_1 @ sk_B @ sk_A @ (k4_relat_1 @ sk_C))
% 0.66/0.85         = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.66/0.85      inference('sup-', [status(thm)], ['120', '121'])).
% 0.66/0.85  thf('123', plain,
% 0.66/0.85      (![X4 : $i]:
% 0.66/0.85         (((k4_relat_1 @ (k4_relat_1 @ X4)) = (X4)) | ~ (v1_relat_1 @ X4))),
% 0.66/0.85      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 0.66/0.85  thf('124', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.66/0.85      inference('demod', [status(thm)], ['97', '98', '99', '100'])).
% 0.66/0.85  thf('125', plain,
% 0.66/0.85      (![X6 : $i]:
% 0.66/0.85         (~ (v2_funct_1 @ X6)
% 0.66/0.85          | ((k2_funct_1 @ X6) = (k4_relat_1 @ X6))
% 0.66/0.85          | ~ (v1_funct_1 @ X6)
% 0.66/0.85          | ~ (v1_relat_1 @ X6))),
% 0.66/0.85      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.66/0.85  thf('126', plain,
% 0.66/0.85      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.66/0.85        | ((k2_funct_1 @ (k4_relat_1 @ sk_C))
% 0.66/0.85            = (k4_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.66/0.85        | ~ (v2_funct_1 @ (k4_relat_1 @ sk_C)))),
% 0.66/0.85      inference('sup-', [status(thm)], ['124', '125'])).
% 0.66/0.85  thf('127', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.66/0.85      inference('demod', [status(thm)], ['11', '12', '13', '14'])).
% 0.66/0.85  thf('128', plain,
% 0.66/0.85      ((((k2_funct_1 @ (k4_relat_1 @ sk_C))
% 0.66/0.85          = (k4_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.66/0.85        | ~ (v2_funct_1 @ (k4_relat_1 @ sk_C)))),
% 0.66/0.85      inference('demod', [status(thm)], ['126', '127'])).
% 0.66/0.85  thf('129', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.66/0.85      inference('demod', [status(thm)], ['2', '7', '8'])).
% 0.66/0.85  thf('130', plain,
% 0.66/0.85      (![X7 : $i]:
% 0.66/0.85         ((v2_funct_1 @ (k2_funct_1 @ X7))
% 0.66/0.85          | ~ (v2_funct_1 @ X7)
% 0.66/0.85          | ~ (v1_funct_1 @ X7)
% 0.66/0.85          | ~ (v1_relat_1 @ X7))),
% 0.66/0.85      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.66/0.85  thf('131', plain,
% 0.66/0.85      (((v2_funct_1 @ (k4_relat_1 @ sk_C))
% 0.66/0.85        | ~ (v1_relat_1 @ sk_C)
% 0.66/0.85        | ~ (v1_funct_1 @ sk_C)
% 0.66/0.85        | ~ (v2_funct_1 @ sk_C))),
% 0.66/0.85      inference('sup+', [status(thm)], ['129', '130'])).
% 0.66/0.85  thf('132', plain, ((v1_relat_1 @ sk_C)),
% 0.66/0.85      inference('demod', [status(thm)], ['5', '6'])).
% 0.66/0.85  thf('133', plain, ((v1_funct_1 @ sk_C)),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('134', plain, ((v2_funct_1 @ sk_C)),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('135', plain, ((v2_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.66/0.85      inference('demod', [status(thm)], ['131', '132', '133', '134'])).
% 0.66/0.85  thf('136', plain,
% 0.66/0.85      (((k2_funct_1 @ (k4_relat_1 @ sk_C)) = (k4_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.66/0.85      inference('demod', [status(thm)], ['128', '135'])).
% 0.66/0.85  thf('137', plain,
% 0.66/0.85      (![X7 : $i]:
% 0.66/0.85         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 0.66/0.85          | ~ (v2_funct_1 @ X7)
% 0.66/0.85          | ~ (v1_funct_1 @ X7)
% 0.66/0.85          | ~ (v1_relat_1 @ X7))),
% 0.66/0.85      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.66/0.85  thf('138', plain,
% 0.66/0.85      (((v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.66/0.85        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.66/0.85        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.66/0.85        | ~ (v2_funct_1 @ (k4_relat_1 @ sk_C)))),
% 0.66/0.85      inference('sup+', [status(thm)], ['136', '137'])).
% 0.66/0.85  thf('139', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.66/0.85      inference('demod', [status(thm)], ['11', '12', '13', '14'])).
% 0.66/0.85  thf('140', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.66/0.85      inference('demod', [status(thm)], ['97', '98', '99', '100'])).
% 0.66/0.85  thf('141', plain, ((v2_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.66/0.85      inference('demod', [status(thm)], ['131', '132', '133', '134'])).
% 0.66/0.85  thf('142', plain, ((v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.66/0.85      inference('demod', [status(thm)], ['138', '139', '140', '141'])).
% 0.66/0.85  thf('143', plain,
% 0.66/0.85      (![X0 : $i]:
% 0.66/0.85         (((k2_relat_1 @ (k4_relat_1 @ X0)) = (k1_relat_1 @ X0))
% 0.66/0.85          | ~ (v1_relat_1 @ X0)
% 0.66/0.85          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.66/0.85      inference('sup+', [status(thm)], ['16', '17'])).
% 0.66/0.85  thf('144', plain,
% 0.66/0.85      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.66/0.85        | ((k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.66/0.85            = (k1_relat_1 @ (k4_relat_1 @ sk_C))))),
% 0.66/0.85      inference('sup-', [status(thm)], ['142', '143'])).
% 0.66/0.85  thf('145', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.66/0.85      inference('demod', [status(thm)], ['11', '12', '13', '14'])).
% 0.66/0.85  thf('146', plain,
% 0.66/0.85      (((k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.66/0.85         = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.66/0.85      inference('demod', [status(thm)], ['144', '145'])).
% 0.66/0.85  thf('147', plain,
% 0.66/0.85      ((((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.66/0.85        | ~ (v1_relat_1 @ sk_C))),
% 0.66/0.85      inference('sup+', [status(thm)], ['123', '146'])).
% 0.66/0.85  thf('148', plain, ((v1_relat_1 @ sk_C)),
% 0.66/0.85      inference('demod', [status(thm)], ['5', '6'])).
% 0.66/0.85  thf('149', plain,
% 0.66/0.85      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.66/0.85      inference('demod', [status(thm)], ['147', '148'])).
% 0.66/0.85  thf('150', plain,
% 0.66/0.85      (((k1_relset_1 @ sk_B @ sk_A @ (k4_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.66/0.85      inference('demod', [status(thm)], ['122', '149'])).
% 0.66/0.85  thf('151', plain,
% 0.66/0.85      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('152', plain,
% 0.66/0.85      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.66/0.85         (~ (v2_funct_1 @ X49)
% 0.66/0.85          | ((k2_relset_1 @ X51 @ X50 @ X49) != (X50))
% 0.66/0.85          | (v1_funct_2 @ (k2_funct_1 @ X49) @ X50 @ X51)
% 0.66/0.85          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X50)))
% 0.66/0.85          | ~ (v1_funct_2 @ X49 @ X51 @ X50)
% 0.66/0.85          | ~ (v1_funct_1 @ X49))),
% 0.66/0.85      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.66/0.85  thf('153', plain,
% 0.66/0.85      ((~ (v1_funct_1 @ sk_C)
% 0.66/0.85        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.66/0.85        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.66/0.85        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.66/0.85        | ~ (v2_funct_1 @ sk_C))),
% 0.66/0.85      inference('sup-', [status(thm)], ['151', '152'])).
% 0.66/0.85  thf('154', plain, ((v1_funct_1 @ sk_C)),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('155', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('156', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.66/0.85      inference('demod', [status(thm)], ['2', '7', '8'])).
% 0.66/0.85  thf('157', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('158', plain, ((v2_funct_1 @ sk_C)),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('159', plain,
% 0.66/0.85      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A) | ((sk_B) != (sk_B)))),
% 0.66/0.85      inference('demod', [status(thm)],
% 0.66/0.85                ['153', '154', '155', '156', '157', '158'])).
% 0.66/0.85  thf('160', plain, ((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A)),
% 0.66/0.85      inference('simplify', [status(thm)], ['159'])).
% 0.66/0.85  thf('161', plain,
% 0.66/0.85      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.66/0.85         (~ (v1_funct_2 @ X36 @ X34 @ X35)
% 0.66/0.85          | ((X34) = (k1_relset_1 @ X34 @ X35 @ X36))
% 0.66/0.85          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.66/0.85  thf('162', plain,
% 0.66/0.85      ((~ (zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B)
% 0.66/0.85        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ (k4_relat_1 @ sk_C))))),
% 0.66/0.85      inference('sup-', [status(thm)], ['160', '161'])).
% 0.66/0.85  thf('163', plain,
% 0.66/0.85      (![X32 : $i, X33 : $i]:
% 0.66/0.85         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.66/0.85  thf('164', plain,
% 0.66/0.85      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.66/0.85        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.66/0.85      inference('simplify', [status(thm)], ['119'])).
% 0.66/0.85  thf('165', plain,
% 0.66/0.85      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.66/0.85         (~ (zip_tseitin_0 @ X37 @ X38)
% 0.66/0.85          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 0.66/0.85          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.66/0.85  thf('166', plain,
% 0.66/0.85      (((zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B)
% 0.66/0.85        | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 0.66/0.85      inference('sup-', [status(thm)], ['164', '165'])).
% 0.66/0.85  thf('167', plain,
% 0.66/0.85      ((((sk_A) = (k1_xboole_0))
% 0.66/0.85        | (zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B))),
% 0.66/0.85      inference('sup-', [status(thm)], ['163', '166'])).
% 0.66/0.85  thf('168', plain, (((sk_A) != (k1_xboole_0))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('169', plain, ((zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B)),
% 0.66/0.85      inference('simplify_reflect-', [status(thm)], ['167', '168'])).
% 0.66/0.85  thf('170', plain,
% 0.66/0.85      (((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ (k4_relat_1 @ sk_C)))),
% 0.66/0.85      inference('demod', [status(thm)], ['162', '169'])).
% 0.66/0.85  thf('171', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 0.66/0.85      inference('sup+', [status(thm)], ['150', '170'])).
% 0.66/0.85  thf('172', plain,
% 0.66/0.85      (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 0.66/0.85      inference('demod', [status(thm)], ['110', '171'])).
% 0.66/0.85  thf('173', plain,
% 0.66/0.85      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 0.66/0.85        | ((sk_D) = (k4_relat_1 @ sk_C))
% 0.66/0.85        | ((k6_partfun1 @ sk_B) != (k6_partfun1 @ sk_B)))),
% 0.66/0.85      inference('demod', [status(thm)], ['93', '94', '101', '172'])).
% 0.66/0.85  thf('174', plain, (((sk_D) = (k4_relat_1 @ sk_C))),
% 0.66/0.85      inference('simplify', [status(thm)], ['173'])).
% 0.66/0.85  thf('175', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('176', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.66/0.85      inference('demod', [status(thm)], ['2', '7', '8'])).
% 0.66/0.85  thf('177', plain, (((sk_D) != (k4_relat_1 @ sk_C))),
% 0.66/0.85      inference('demod', [status(thm)], ['175', '176'])).
% 0.66/0.85  thf('178', plain, ($false),
% 0.66/0.85      inference('simplify_reflect-', [status(thm)], ['174', '177'])).
% 0.66/0.85  
% 0.66/0.85  % SZS output end Refutation
% 0.66/0.85  
% 0.66/0.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
