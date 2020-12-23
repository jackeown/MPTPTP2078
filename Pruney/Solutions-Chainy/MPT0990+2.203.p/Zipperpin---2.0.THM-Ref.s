%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fwefryVxo3

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:29 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 264 expanded)
%              Number of leaves         :   23 (  87 expanded)
%              Depth                    :   14
%              Number of atoms          : 1379 (8138 expanded)
%              Number of equality atoms :   75 ( 556 expanded)
%              Maximal formula depth    :   26 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf('1',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_relset_1 @ X18 @ X17 @ X16 )
       != X17 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X16 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) )
      | ~ ( v1_funct_2 @ X16 @ X18 @ X17 )
      | ~ ( v1_funct_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('2',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['2','3','4','5','6'])).

thf('8',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( X0 = X3 )
      | ~ ( r2_relset_1 @ X1 @ X2 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_B @ sk_A @ sk_D_1 @ X0 )
      | ( sk_D_1 = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_D_1
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( r2_relset_1 @ sk_B @ sk_A @ sk_D_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    sk_D_1
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ~ ( r2_relset_1 @ sk_B @ sk_A @ sk_D_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
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

thf('17',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ( ( k1_partfun1 @ X5 @ X6 @ X8 @ X9 @ X4 @ X7 )
        = ( k5_relat_1 @ X4 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( v1_funct_1 @ sk_D_1 )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D_1 )
      = ( k5_relat_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D_1 )
    = ( k5_relat_1 @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('26',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_relset_1 @ X18 @ X17 @ X16 )
       != X17 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) )
      | ~ ( v1_funct_2 @ X16 @ X18 @ X17 )
      | ~ ( v1_funct_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('29',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['29','30','31','32','33'])).

thf('35',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['26','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( B = k1_xboole_0 )
          | ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) )
              = ( k6_partfun1 @ A ) )
            & ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C )
              = ( k6_partfun1 @ B ) ) ) ) ) ) )).

thf('38',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X19 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_2 @ X20 @ X21 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X19 ) ) )
      | ( ( k5_relat_1 @ X20 @ ( k2_funct_1 @ X20 ) )
        = ( k6_partfun1 @ X21 ) )
      | ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relset_1 @ X21 @ X19 @ X20 )
       != X19 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('39',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40','41','42','43'])).

thf('45',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['36','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t22_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
        <=> ! [D: $i] :
              ( ( D != k1_xboole_0 )
             => ! [E: $i] :
                  ( ( ( v1_funct_1 @ E )
                    & ( v1_funct_2 @ E @ B @ D )
                    & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ D ) ) ) )
                 => ! [F: $i] :
                      ( ( ( v1_funct_1 @ F )
                        & ( v1_funct_2 @ F @ B @ D )
                        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ D ) ) ) )
                     => ( ( r2_relset_1 @ A @ D @ ( k1_partfun1 @ A @ B @ B @ D @ C @ E ) @ ( k1_partfun1 @ A @ B @ B @ D @ C @ F ) )
                       => ( r2_relset_1 @ B @ D @ E @ F ) ) ) ) ) ) ) ) )).

thf('50',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X10 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_funct_2 @ X11 @ X12 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X10 ) ) )
      | ( X13 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_funct_2 @ X14 @ X10 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X13 ) ) )
      | ( r2_relset_1 @ X10 @ X13 @ X15 @ X14 )
      | ~ ( r2_relset_1 @ X12 @ X13 @ ( k1_partfun1 @ X12 @ X10 @ X10 @ X13 @ X11 @ X15 ) @ ( k1_partfun1 @ X12 @ X10 @ X10 @ X13 @ X11 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X13 ) ) )
      | ~ ( v1_funct_2 @ X15 @ X10 @ X13 )
      | ~ ( v1_funct_1 @ X15 )
      | ( ( k2_relset_1 @ X12 @ X10 @ X11 )
       != X10 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_2])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
       != sk_B )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X1 ) ) )
      | ~ ( r2_relset_1 @ sk_A @ X1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ X1 @ sk_C @ X0 ) @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ X1 @ sk_C @ X2 ) )
      | ( r2_relset_1 @ sk_B @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X1 ) ) )
      | ~ ( v1_funct_2 @ X2 @ sk_B @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( sk_B != sk_B )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X1 ) ) )
      | ~ ( r2_relset_1 @ sk_A @ X1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ X1 @ sk_C @ X0 ) @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ X1 @ sk_C @ X2 ) )
      | ( r2_relset_1 @ sk_B @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X1 ) ) )
      | ~ ( v1_funct_2 @ X2 @ sk_B @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( X1 = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X1 ) ) )
      | ( r2_relset_1 @ sk_B @ X1 @ X0 @ X2 )
      | ~ ( r2_relset_1 @ sk_A @ X1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ X1 @ sk_C @ X0 ) @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ X1 @ sk_C @ X2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ X1 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X1 ) ) )
      | ( r2_relset_1 @ sk_B @ X1 @ X0 @ X2 )
      | ~ ( r2_relset_1 @ sk_A @ X1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ X1 @ sk_C @ X0 ) @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ X1 @ sk_C @ X2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ X1 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( r2_relset_1 @ sk_B @ sk_A @ X0 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','58'])).

thf('60',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_relset_1 @ X18 @ X17 @ X16 )
       != X17 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X16 ) @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) )
      | ~ ( v1_funct_2 @ X16 @ X18 @ X17 )
      | ~ ( v1_funct_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('63',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['63','64','65','66','67'])).

thf('69',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['34'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( r2_relset_1 @ sk_B @ sk_A @ X0 @ ( k2_funct_1 @ sk_C ) )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['59','60','69','70'])).

thf('72',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( r2_relset_1 @ sk_B @ sk_A @ X0 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D_1 ) @ ( k6_partfun1 @ sk_A ) )
    | ( r2_relset_1 @ sk_B @ sk_A @ sk_D_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D_1 @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['23','73'])).

thf('75',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D_1 )
    = ( k5_relat_1 @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('77',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D_1 ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    r2_relset_1 @ sk_B @ sk_A @ sk_D_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['74','77','78','79','80'])).

thf('82',plain,(
    $false ),
    inference(demod,[status(thm)],['14','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fwefryVxo3
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:00:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.56  % Solved by: fo/fo7.sh
% 0.35/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.56  % done 113 iterations in 0.110s
% 0.35/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.56  % SZS output start Refutation
% 0.35/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.56  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.35/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.35/0.56  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.35/0.56  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.35/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.56  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.35/0.56  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.35/0.56  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.35/0.56  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.35/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.35/0.56  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.35/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.56  thf(t36_funct_2, conjecture,
% 0.35/0.56    (![A:$i,B:$i,C:$i]:
% 0.35/0.56     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.35/0.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.56       ( ![D:$i]:
% 0.35/0.56         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.35/0.56             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.35/0.56           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.35/0.56               ( r2_relset_1 @
% 0.35/0.56                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.35/0.56                 ( k6_partfun1 @ A ) ) & 
% 0.35/0.56               ( v2_funct_1 @ C ) ) =>
% 0.35/0.56             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.35/0.56               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.35/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.35/0.56        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.35/0.56            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.56          ( ![D:$i]:
% 0.35/0.56            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.35/0.56                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.35/0.56              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.35/0.56                  ( r2_relset_1 @
% 0.35/0.56                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.35/0.56                    ( k6_partfun1 @ A ) ) & 
% 0.35/0.56                  ( v2_funct_1 @ C ) ) =>
% 0.35/0.56                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.35/0.56                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.35/0.56    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.35/0.56  thf('0', plain,
% 0.35/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf(t31_funct_2, axiom,
% 0.35/0.56    (![A:$i,B:$i,C:$i]:
% 0.35/0.56     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.35/0.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.56       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.35/0.56         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.35/0.56           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.35/0.56           ( m1_subset_1 @
% 0.35/0.56             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.35/0.56  thf('1', plain,
% 0.35/0.56      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.35/0.56         (~ (v2_funct_1 @ X16)
% 0.35/0.56          | ((k2_relset_1 @ X18 @ X17 @ X16) != (X17))
% 0.35/0.56          | (m1_subset_1 @ (k2_funct_1 @ X16) @ 
% 0.35/0.56             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.35/0.56          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17)))
% 0.35/0.56          | ~ (v1_funct_2 @ X16 @ X18 @ X17)
% 0.35/0.56          | ~ (v1_funct_1 @ X16))),
% 0.35/0.56      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.35/0.56  thf('2', plain,
% 0.35/0.56      ((~ (v1_funct_1 @ sk_C)
% 0.35/0.56        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.35/0.56        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.35/0.56           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.35/0.56        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.35/0.56        | ~ (v2_funct_1 @ sk_C))),
% 0.35/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.35/0.56  thf('3', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('4', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('5', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('6', plain, ((v2_funct_1 @ sk_C)),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('7', plain,
% 0.35/0.56      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.35/0.56         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.35/0.56        | ((sk_B) != (sk_B)))),
% 0.35/0.56      inference('demod', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.35/0.56  thf('8', plain,
% 0.35/0.56      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.35/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.35/0.56      inference('simplify', [status(thm)], ['7'])).
% 0.35/0.56  thf('9', plain,
% 0.35/0.56      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf(redefinition_r2_relset_1, axiom,
% 0.35/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.56     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.35/0.56         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.56       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.35/0.56  thf('10', plain,
% 0.35/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.35/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.35/0.56          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.35/0.56          | ((X0) = (X3))
% 0.35/0.56          | ~ (r2_relset_1 @ X1 @ X2 @ X0 @ X3))),
% 0.35/0.56      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.35/0.56  thf('11', plain,
% 0.35/0.56      (![X0 : $i]:
% 0.35/0.56         (~ (r2_relset_1 @ sk_B @ sk_A @ sk_D_1 @ X0)
% 0.35/0.56          | ((sk_D_1) = (X0))
% 0.35/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.35/0.56      inference('sup-', [status(thm)], ['9', '10'])).
% 0.35/0.56  thf('12', plain,
% 0.35/0.56      ((((sk_D_1) = (k2_funct_1 @ sk_C))
% 0.35/0.56        | ~ (r2_relset_1 @ sk_B @ sk_A @ sk_D_1 @ (k2_funct_1 @ sk_C)))),
% 0.35/0.56      inference('sup-', [status(thm)], ['8', '11'])).
% 0.35/0.56  thf('13', plain, (((sk_D_1) != (k2_funct_1 @ sk_C))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('14', plain,
% 0.35/0.56      (~ (r2_relset_1 @ sk_B @ sk_A @ sk_D_1 @ (k2_funct_1 @ sk_C))),
% 0.35/0.56      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.35/0.56  thf('15', plain,
% 0.35/0.56      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('16', plain,
% 0.35/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf(redefinition_k1_partfun1, axiom,
% 0.35/0.56    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.35/0.56     ( ( ( v1_funct_1 @ E ) & 
% 0.35/0.56         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.35/0.56         ( v1_funct_1 @ F ) & 
% 0.35/0.56         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.35/0.56       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.35/0.56  thf('17', plain,
% 0.35/0.56      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.35/0.56         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6)))
% 0.35/0.56          | ~ (v1_funct_1 @ X4)
% 0.35/0.56          | ~ (v1_funct_1 @ X7)
% 0.35/0.56          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.35/0.56          | ((k1_partfun1 @ X5 @ X6 @ X8 @ X9 @ X4 @ X7)
% 0.35/0.56              = (k5_relat_1 @ X4 @ X7)))),
% 0.35/0.56      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.35/0.56  thf('18', plain,
% 0.35/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.56         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.35/0.56            = (k5_relat_1 @ sk_C @ X0))
% 0.35/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.35/0.56          | ~ (v1_funct_1 @ X0)
% 0.35/0.56          | ~ (v1_funct_1 @ sk_C))),
% 0.35/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.35/0.56  thf('19', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('20', plain,
% 0.35/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.56         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.35/0.56            = (k5_relat_1 @ sk_C @ X0))
% 0.35/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.35/0.56          | ~ (v1_funct_1 @ X0))),
% 0.35/0.56      inference('demod', [status(thm)], ['18', '19'])).
% 0.35/0.56  thf('21', plain,
% 0.35/0.56      ((~ (v1_funct_1 @ sk_D_1)
% 0.35/0.56        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D_1)
% 0.35/0.56            = (k5_relat_1 @ sk_C @ sk_D_1)))),
% 0.35/0.56      inference('sup-', [status(thm)], ['15', '20'])).
% 0.35/0.56  thf('22', plain, ((v1_funct_1 @ sk_D_1)),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('23', plain,
% 0.35/0.56      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D_1)
% 0.35/0.56         = (k5_relat_1 @ sk_C @ sk_D_1))),
% 0.35/0.56      inference('demod', [status(thm)], ['21', '22'])).
% 0.35/0.56  thf('24', plain,
% 0.35/0.56      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.35/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.35/0.56      inference('simplify', [status(thm)], ['7'])).
% 0.35/0.56  thf('25', plain,
% 0.35/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.56         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.35/0.56            = (k5_relat_1 @ sk_C @ X0))
% 0.35/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.35/0.56          | ~ (v1_funct_1 @ X0))),
% 0.35/0.56      inference('demod', [status(thm)], ['18', '19'])).
% 0.35/0.56  thf('26', plain,
% 0.35/0.56      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.35/0.56        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ 
% 0.35/0.56            (k2_funct_1 @ sk_C)) = (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))))),
% 0.35/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.35/0.56  thf('27', plain,
% 0.35/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('28', plain,
% 0.35/0.56      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.35/0.56         (~ (v2_funct_1 @ X16)
% 0.35/0.56          | ((k2_relset_1 @ X18 @ X17 @ X16) != (X17))
% 0.35/0.56          | (v1_funct_1 @ (k2_funct_1 @ X16))
% 0.35/0.56          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17)))
% 0.35/0.56          | ~ (v1_funct_2 @ X16 @ X18 @ X17)
% 0.35/0.56          | ~ (v1_funct_1 @ X16))),
% 0.35/0.56      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.35/0.56  thf('29', plain,
% 0.35/0.56      ((~ (v1_funct_1 @ sk_C)
% 0.35/0.56        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.35/0.56        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.35/0.56        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.35/0.56        | ~ (v2_funct_1 @ sk_C))),
% 0.35/0.56      inference('sup-', [status(thm)], ['27', '28'])).
% 0.35/0.56  thf('30', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('31', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('32', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('33', plain, ((v2_funct_1 @ sk_C)),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('34', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)) | ((sk_B) != (sk_B)))),
% 0.35/0.56      inference('demod', [status(thm)], ['29', '30', '31', '32', '33'])).
% 0.35/0.56  thf('35', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.35/0.56      inference('simplify', [status(thm)], ['34'])).
% 0.35/0.56  thf('36', plain,
% 0.35/0.56      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ (k2_funct_1 @ sk_C))
% 0.35/0.56         = (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))),
% 0.35/0.56      inference('demod', [status(thm)], ['26', '35'])).
% 0.35/0.56  thf('37', plain,
% 0.35/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf(t35_funct_2, axiom,
% 0.35/0.56    (![A:$i,B:$i,C:$i]:
% 0.35/0.56     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.35/0.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.56       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.35/0.56         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.35/0.56           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.35/0.56             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.35/0.56  thf('38', plain,
% 0.35/0.56      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.35/0.56         (((X19) = (k1_xboole_0))
% 0.35/0.56          | ~ (v1_funct_1 @ X20)
% 0.35/0.56          | ~ (v1_funct_2 @ X20 @ X21 @ X19)
% 0.35/0.56          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X19)))
% 0.35/0.56          | ((k5_relat_1 @ X20 @ (k2_funct_1 @ X20)) = (k6_partfun1 @ X21))
% 0.35/0.56          | ~ (v2_funct_1 @ X20)
% 0.35/0.56          | ((k2_relset_1 @ X21 @ X19 @ X20) != (X19)))),
% 0.35/0.56      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.35/0.56  thf('39', plain,
% 0.35/0.56      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.35/0.56        | ~ (v2_funct_1 @ sk_C)
% 0.35/0.56        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.35/0.56        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.35/0.56        | ~ (v1_funct_1 @ sk_C)
% 0.35/0.56        | ((sk_B) = (k1_xboole_0)))),
% 0.35/0.56      inference('sup-', [status(thm)], ['37', '38'])).
% 0.35/0.56  thf('40', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('41', plain, ((v2_funct_1 @ sk_C)),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('42', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('43', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('44', plain,
% 0.35/0.56      ((((sk_B) != (sk_B))
% 0.35/0.56        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.35/0.56        | ((sk_B) = (k1_xboole_0)))),
% 0.35/0.56      inference('demod', [status(thm)], ['39', '40', '41', '42', '43'])).
% 0.35/0.56  thf('45', plain,
% 0.35/0.56      ((((sk_B) = (k1_xboole_0))
% 0.35/0.56        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 0.35/0.56      inference('simplify', [status(thm)], ['44'])).
% 0.35/0.56  thf('46', plain, (((sk_B) != (k1_xboole_0))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('47', plain,
% 0.35/0.56      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 0.35/0.56      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 0.35/0.56  thf('48', plain,
% 0.35/0.56      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ (k2_funct_1 @ sk_C))
% 0.35/0.56         = (k6_partfun1 @ sk_A))),
% 0.35/0.56      inference('demod', [status(thm)], ['36', '47'])).
% 0.35/0.56  thf('49', plain,
% 0.35/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf(t22_funct_2, axiom,
% 0.35/0.56    (![A:$i,B:$i,C:$i]:
% 0.35/0.56     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.35/0.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.56       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.35/0.56         ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) <=>
% 0.35/0.56           ( ![D:$i]:
% 0.35/0.56             ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 0.35/0.56               ( ![E:$i]:
% 0.35/0.56                 ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ D ) & 
% 0.35/0.56                     ( m1_subset_1 @
% 0.35/0.56                       E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ D ) ) ) ) =>
% 0.35/0.56                   ( ![F:$i]:
% 0.35/0.56                     ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ B @ D ) & 
% 0.35/0.56                         ( m1_subset_1 @
% 0.35/0.56                           F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ D ) ) ) ) =>
% 0.35/0.56                       ( ( r2_relset_1 @
% 0.35/0.56                           A @ D @ ( k1_partfun1 @ A @ B @ B @ D @ C @ E ) @ 
% 0.35/0.56                           ( k1_partfun1 @ A @ B @ B @ D @ C @ F ) ) =>
% 0.35/0.56                         ( r2_relset_1 @ B @ D @ E @ F ) ) ) ) ) ) ) ) ) ) ))).
% 0.35/0.56  thf('50', plain,
% 0.35/0.56      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.35/0.56         (((X10) = (k1_xboole_0))
% 0.35/0.56          | ~ (v1_funct_1 @ X11)
% 0.35/0.56          | ~ (v1_funct_2 @ X11 @ X12 @ X10)
% 0.35/0.56          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X10)))
% 0.35/0.56          | ((X13) = (k1_xboole_0))
% 0.35/0.56          | ~ (v1_funct_1 @ X14)
% 0.35/0.56          | ~ (v1_funct_2 @ X14 @ X10 @ X13)
% 0.35/0.56          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X13)))
% 0.35/0.56          | (r2_relset_1 @ X10 @ X13 @ X15 @ X14)
% 0.35/0.56          | ~ (r2_relset_1 @ X12 @ X13 @ 
% 0.35/0.56               (k1_partfun1 @ X12 @ X10 @ X10 @ X13 @ X11 @ X15) @ 
% 0.35/0.56               (k1_partfun1 @ X12 @ X10 @ X10 @ X13 @ X11 @ X14))
% 0.35/0.56          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X13)))
% 0.35/0.56          | ~ (v1_funct_2 @ X15 @ X10 @ X13)
% 0.35/0.56          | ~ (v1_funct_1 @ X15)
% 0.35/0.56          | ((k2_relset_1 @ X12 @ X10 @ X11) != (X10)))),
% 0.35/0.56      inference('cnf', [status(esa)], [t22_funct_2])).
% 0.35/0.56  thf('51', plain,
% 0.35/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.56         (((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.35/0.56          | ~ (v1_funct_1 @ X0)
% 0.35/0.56          | ~ (v1_funct_2 @ X0 @ sk_B @ X1)
% 0.35/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X1)))
% 0.35/0.56          | ~ (r2_relset_1 @ sk_A @ X1 @ 
% 0.35/0.56               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ X1 @ sk_C @ X0) @ 
% 0.35/0.56               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ X1 @ sk_C @ X2))
% 0.35/0.56          | (r2_relset_1 @ sk_B @ X1 @ X0 @ X2)
% 0.35/0.56          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X1)))
% 0.35/0.56          | ~ (v1_funct_2 @ X2 @ sk_B @ X1)
% 0.35/0.56          | ~ (v1_funct_1 @ X2)
% 0.35/0.56          | ((X1) = (k1_xboole_0))
% 0.35/0.56          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.35/0.56          | ~ (v1_funct_1 @ sk_C)
% 0.35/0.56          | ((sk_B) = (k1_xboole_0)))),
% 0.35/0.56      inference('sup-', [status(thm)], ['49', '50'])).
% 0.35/0.56  thf('52', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('53', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('54', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('55', plain,
% 0.35/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.56         (((sk_B) != (sk_B))
% 0.35/0.56          | ~ (v1_funct_1 @ X0)
% 0.35/0.56          | ~ (v1_funct_2 @ X0 @ sk_B @ X1)
% 0.35/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X1)))
% 0.35/0.56          | ~ (r2_relset_1 @ sk_A @ X1 @ 
% 0.35/0.56               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ X1 @ sk_C @ X0) @ 
% 0.35/0.56               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ X1 @ sk_C @ X2))
% 0.35/0.56          | (r2_relset_1 @ sk_B @ X1 @ X0 @ X2)
% 0.35/0.56          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X1)))
% 0.35/0.56          | ~ (v1_funct_2 @ X2 @ sk_B @ X1)
% 0.35/0.56          | ~ (v1_funct_1 @ X2)
% 0.35/0.56          | ((X1) = (k1_xboole_0))
% 0.35/0.56          | ((sk_B) = (k1_xboole_0)))),
% 0.35/0.56      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 0.35/0.56  thf('56', plain,
% 0.35/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.56         (((sk_B) = (k1_xboole_0))
% 0.35/0.56          | ((X1) = (k1_xboole_0))
% 0.35/0.56          | ~ (v1_funct_1 @ X2)
% 0.35/0.56          | ~ (v1_funct_2 @ X2 @ sk_B @ X1)
% 0.35/0.56          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X1)))
% 0.35/0.56          | (r2_relset_1 @ sk_B @ X1 @ X0 @ X2)
% 0.35/0.56          | ~ (r2_relset_1 @ sk_A @ X1 @ 
% 0.35/0.56               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ X1 @ sk_C @ X0) @ 
% 0.35/0.56               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ X1 @ sk_C @ X2))
% 0.35/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X1)))
% 0.35/0.56          | ~ (v1_funct_2 @ X0 @ sk_B @ X1)
% 0.35/0.56          | ~ (v1_funct_1 @ X0))),
% 0.35/0.56      inference('simplify', [status(thm)], ['55'])).
% 0.35/0.56  thf('57', plain, (((sk_B) != (k1_xboole_0))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('58', plain,
% 0.35/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.56         (((X1) = (k1_xboole_0))
% 0.35/0.56          | ~ (v1_funct_1 @ X2)
% 0.35/0.56          | ~ (v1_funct_2 @ X2 @ sk_B @ X1)
% 0.35/0.56          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X1)))
% 0.35/0.56          | (r2_relset_1 @ sk_B @ X1 @ X0 @ X2)
% 0.35/0.56          | ~ (r2_relset_1 @ sk_A @ X1 @ 
% 0.35/0.56               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ X1 @ sk_C @ X0) @ 
% 0.35/0.56               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ X1 @ sk_C @ X2))
% 0.35/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X1)))
% 0.35/0.56          | ~ (v1_funct_2 @ X0 @ sk_B @ X1)
% 0.35/0.56          | ~ (v1_funct_1 @ X0))),
% 0.35/0.56      inference('simplify_reflect-', [status(thm)], ['56', '57'])).
% 0.35/0.56  thf('59', plain,
% 0.35/0.56      (![X0 : $i]:
% 0.35/0.56         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.35/0.56             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.35/0.56             (k6_partfun1 @ sk_A))
% 0.35/0.56          | ~ (v1_funct_1 @ X0)
% 0.35/0.56          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.35/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.35/0.56          | (r2_relset_1 @ sk_B @ sk_A @ X0 @ (k2_funct_1 @ sk_C))
% 0.35/0.56          | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.35/0.56               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.35/0.56          | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.35/0.56          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.35/0.56          | ((sk_A) = (k1_xboole_0)))),
% 0.35/0.56      inference('sup-', [status(thm)], ['48', '58'])).
% 0.35/0.56  thf('60', plain,
% 0.35/0.56      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.35/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.35/0.56      inference('simplify', [status(thm)], ['7'])).
% 0.35/0.56  thf('61', plain,
% 0.35/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('62', plain,
% 0.35/0.56      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.35/0.56         (~ (v2_funct_1 @ X16)
% 0.35/0.56          | ((k2_relset_1 @ X18 @ X17 @ X16) != (X17))
% 0.35/0.56          | (v1_funct_2 @ (k2_funct_1 @ X16) @ X17 @ X18)
% 0.35/0.56          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17)))
% 0.35/0.56          | ~ (v1_funct_2 @ X16 @ X18 @ X17)
% 0.35/0.56          | ~ (v1_funct_1 @ X16))),
% 0.35/0.56      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.35/0.56  thf('63', plain,
% 0.35/0.56      ((~ (v1_funct_1 @ sk_C)
% 0.35/0.56        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.35/0.56        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.35/0.56        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.35/0.56        | ~ (v2_funct_1 @ sk_C))),
% 0.35/0.56      inference('sup-', [status(thm)], ['61', '62'])).
% 0.35/0.56  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('65', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('66', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('67', plain, ((v2_funct_1 @ sk_C)),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('68', plain,
% 0.35/0.56      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A) | ((sk_B) != (sk_B)))),
% 0.35/0.56      inference('demod', [status(thm)], ['63', '64', '65', '66', '67'])).
% 0.35/0.56  thf('69', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 0.35/0.56      inference('simplify', [status(thm)], ['68'])).
% 0.35/0.56  thf('70', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.35/0.56      inference('simplify', [status(thm)], ['34'])).
% 0.35/0.56  thf('71', plain,
% 0.35/0.56      (![X0 : $i]:
% 0.35/0.56         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.35/0.56             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.35/0.56             (k6_partfun1 @ sk_A))
% 0.35/0.56          | ~ (v1_funct_1 @ X0)
% 0.35/0.56          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.35/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.35/0.56          | (r2_relset_1 @ sk_B @ sk_A @ X0 @ (k2_funct_1 @ sk_C))
% 0.35/0.56          | ((sk_A) = (k1_xboole_0)))),
% 0.35/0.56      inference('demod', [status(thm)], ['59', '60', '69', '70'])).
% 0.35/0.56  thf('72', plain, (((sk_A) != (k1_xboole_0))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('73', plain,
% 0.35/0.56      (![X0 : $i]:
% 0.35/0.56         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.35/0.56             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.35/0.56             (k6_partfun1 @ sk_A))
% 0.35/0.56          | ~ (v1_funct_1 @ X0)
% 0.35/0.56          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.35/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.35/0.56          | (r2_relset_1 @ sk_B @ sk_A @ X0 @ (k2_funct_1 @ sk_C)))),
% 0.35/0.56      inference('simplify_reflect-', [status(thm)], ['71', '72'])).
% 0.35/0.56  thf('74', plain,
% 0.35/0.56      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D_1) @ 
% 0.35/0.56           (k6_partfun1 @ sk_A))
% 0.35/0.56        | (r2_relset_1 @ sk_B @ sk_A @ sk_D_1 @ (k2_funct_1 @ sk_C))
% 0.35/0.56        | ~ (m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.35/0.56        | ~ (v1_funct_2 @ sk_D_1 @ sk_B @ sk_A)
% 0.35/0.56        | ~ (v1_funct_1 @ sk_D_1))),
% 0.35/0.56      inference('sup-', [status(thm)], ['23', '73'])).
% 0.35/0.56  thf('75', plain,
% 0.35/0.56      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.35/0.56        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D_1) @ 
% 0.35/0.56        (k6_partfun1 @ sk_A))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('76', plain,
% 0.35/0.56      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D_1)
% 0.35/0.56         = (k5_relat_1 @ sk_C @ sk_D_1))),
% 0.35/0.56      inference('demod', [status(thm)], ['21', '22'])).
% 0.35/0.56  thf('77', plain,
% 0.35/0.56      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D_1) @ 
% 0.35/0.56        (k6_partfun1 @ sk_A))),
% 0.35/0.56      inference('demod', [status(thm)], ['75', '76'])).
% 0.35/0.56  thf('78', plain,
% 0.35/0.56      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('79', plain, ((v1_funct_2 @ sk_D_1 @ sk_B @ sk_A)),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('80', plain, ((v1_funct_1 @ sk_D_1)),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('81', plain,
% 0.35/0.56      ((r2_relset_1 @ sk_B @ sk_A @ sk_D_1 @ (k2_funct_1 @ sk_C))),
% 0.35/0.56      inference('demod', [status(thm)], ['74', '77', '78', '79', '80'])).
% 0.35/0.56  thf('82', plain, ($false), inference('demod', [status(thm)], ['14', '81'])).
% 0.35/0.56  
% 0.35/0.56  % SZS output end Refutation
% 0.35/0.56  
% 0.35/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
