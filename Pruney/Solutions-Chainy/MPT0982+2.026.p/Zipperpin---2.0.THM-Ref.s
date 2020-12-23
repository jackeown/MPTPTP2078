%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7wvAHHzoXI

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:58 EST 2020

% Result     : Theorem 1.03s
% Output     : Refutation 1.03s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 213 expanded)
%              Number of leaves         :   48 (  85 expanded)
%              Depth                    :   13
%              Number of atoms          : 1065 (3956 expanded)
%              Number of equality atoms :   69 ( 254 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t28_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
                = C )
              & ( v2_funct_1 @ E ) )
           => ( ( C = k1_xboole_0 )
              | ( ( k2_relset_1 @ A @ B @ D )
                = B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ( ( ( v1_funct_1 @ E )
              & ( v1_funct_2 @ E @ B @ C )
              & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
           => ( ( ( ( k2_relset_1 @ A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
                  = C )
                & ( v2_funct_1 @ E ) )
             => ( ( C = k1_xboole_0 )
                | ( ( k2_relset_1 @ A @ B @ D )
                  = B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('1',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k8_relset_1 @ X34 @ X35 @ X36 @ X35 )
        = ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('2',plain,
    ( ( k8_relset_1 @ sk_B @ sk_C @ sk_E @ sk_C )
    = ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('4',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( ( k8_relset_1 @ X31 @ X32 @ X30 @ X33 )
        = ( k10_relat_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_C @ sk_E @ X0 )
      = ( k10_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('7',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('8',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_2 @ sk_E @ sk_B @ sk_C ),
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

thf('10',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_funct_2 @ X41 @ X39 @ X40 )
      | ( X39
        = ( k1_relset_1 @ X39 @ X40 @ X41 ) )
      | ~ ( zip_tseitin_1 @ X41 @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('11',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X37: $i,X38: $i] :
      ( ( zip_tseitin_0 @ X37 @ X38 )
      | ( X37 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('13',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
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

thf('14',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( zip_tseitin_0 @ X42 @ X43 )
      | ( zip_tseitin_1 @ X44 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('15',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    zip_tseitin_1 @ sk_E @ sk_C @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('20',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['11','18','19'])).

thf('21',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_E )
    = sk_B ),
    inference(demod,[status(thm)],['8','20'])).

thf('22',plain,
    ( ( k10_relat_1 @ sk_E @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['2','5','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('24',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v5_relat_1 @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('25',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['23','24'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v5_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('29',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('30',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['11','18','19'])).

thf(t164_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('33',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X4 @ ( k1_relat_1 @ X5 ) )
      | ~ ( v2_funct_1 @ X5 )
      | ( ( k10_relat_1 @ X5 @ ( k9_relat_1 @ X5 @ X4 ) )
        = X4 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k10_relat_1 @ sk_E @ ( k9_relat_1 @ sk_E @ X0 ) )
        = X0 )
      | ~ ( v2_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('37',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k10_relat_1 @ sk_E @ ( k9_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['34','37','38','39'])).

thf('41',plain,
    ( ( k10_relat_1 @ sk_E @ ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) ) )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['31','40'])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('42',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) )
        = ( k9_relat_1 @ X2 @ ( k2_relat_1 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('43',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( m1_subset_1 @ ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) )).

thf('45',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X13 @ X14 @ X16 @ X17 @ X12 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relset_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('50',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k4_relset_1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 )
        = ( k5_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['47','52'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('54',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('55',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
    = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('59',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ( ( k1_partfun1 @ X46 @ X47 @ X49 @ X50 @ X45 @ X48 )
        = ( k5_relat_1 @ X45 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['57','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['56','65'])).

thf('67',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['55','66'])).

thf('68',plain,
    ( ( ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['42','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['28','29'])).

thf('70',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['35','36'])).

thf('71',plain,
    ( ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) )
    = sk_C ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,
    ( ( k10_relat_1 @ sk_E @ sk_C )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['41','71'])).

thf('73',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['22','72'])).

thf('74',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('77',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ( k2_relat_1 @ sk_D )
 != sk_B ),
    inference(demod,[status(thm)],['74','77'])).

thf('79',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['73','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7wvAHHzoXI
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:21:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.03/1.30  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.03/1.30  % Solved by: fo/fo7.sh
% 1.03/1.30  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.03/1.30  % done 535 iterations in 0.840s
% 1.03/1.30  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.03/1.30  % SZS output start Refutation
% 1.03/1.30  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.03/1.30  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.03/1.30  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.03/1.30  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.03/1.30  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.03/1.30  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.03/1.30  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 1.03/1.30  thf(sk_B_type, type, sk_B: $i).
% 1.03/1.30  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.03/1.30  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.03/1.30  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.03/1.30  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.03/1.30  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.03/1.30  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.03/1.30  thf(sk_D_type, type, sk_D: $i).
% 1.03/1.30  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 1.03/1.30  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.03/1.30  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 1.03/1.30  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.03/1.30  thf(sk_E_type, type, sk_E: $i).
% 1.03/1.30  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.03/1.30  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.03/1.30  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.03/1.30  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.03/1.30  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.03/1.30  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.03/1.30  thf(sk_C_type, type, sk_C: $i).
% 1.03/1.30  thf(sk_A_type, type, sk_A: $i).
% 1.03/1.30  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.03/1.30  thf(t28_funct_2, conjecture,
% 1.03/1.30    (![A:$i,B:$i,C:$i,D:$i]:
% 1.03/1.30     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.03/1.30         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.03/1.30       ( ![E:$i]:
% 1.03/1.30         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.03/1.30             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.03/1.30           ( ( ( ( k2_relset_1 @
% 1.03/1.30                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 1.03/1.30                 ( C ) ) & 
% 1.03/1.30               ( v2_funct_1 @ E ) ) =>
% 1.03/1.30             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.03/1.30               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ))).
% 1.03/1.30  thf(zf_stmt_0, negated_conjecture,
% 1.03/1.30    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.03/1.30        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.03/1.30            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.03/1.30          ( ![E:$i]:
% 1.03/1.30            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.03/1.30                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.03/1.30              ( ( ( ( k2_relset_1 @
% 1.03/1.30                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 1.03/1.30                    ( C ) ) & 
% 1.03/1.30                  ( v2_funct_1 @ E ) ) =>
% 1.03/1.30                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.03/1.30                  ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ) )),
% 1.03/1.30    inference('cnf.neg', [status(esa)], [t28_funct_2])).
% 1.03/1.30  thf('0', plain,
% 1.03/1.30      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.03/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.30  thf(t38_relset_1, axiom,
% 1.03/1.30    (![A:$i,B:$i,C:$i]:
% 1.03/1.30     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.03/1.30       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 1.03/1.30         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.03/1.30  thf('1', plain,
% 1.03/1.30      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.03/1.30         (((k8_relset_1 @ X34 @ X35 @ X36 @ X35)
% 1.03/1.30            = (k1_relset_1 @ X34 @ X35 @ X36))
% 1.03/1.30          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 1.03/1.30      inference('cnf', [status(esa)], [t38_relset_1])).
% 1.03/1.30  thf('2', plain,
% 1.03/1.30      (((k8_relset_1 @ sk_B @ sk_C @ sk_E @ sk_C)
% 1.03/1.30         = (k1_relset_1 @ sk_B @ sk_C @ sk_E))),
% 1.03/1.30      inference('sup-', [status(thm)], ['0', '1'])).
% 1.03/1.30  thf('3', plain,
% 1.03/1.30      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.03/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.30  thf(redefinition_k8_relset_1, axiom,
% 1.03/1.30    (![A:$i,B:$i,C:$i,D:$i]:
% 1.03/1.30     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.03/1.30       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 1.03/1.30  thf('4', plain,
% 1.03/1.30      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.03/1.30         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 1.03/1.30          | ((k8_relset_1 @ X31 @ X32 @ X30 @ X33) = (k10_relat_1 @ X30 @ X33)))),
% 1.03/1.30      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 1.03/1.30  thf('5', plain,
% 1.03/1.30      (![X0 : $i]:
% 1.03/1.30         ((k8_relset_1 @ sk_B @ sk_C @ sk_E @ X0) = (k10_relat_1 @ sk_E @ X0))),
% 1.03/1.30      inference('sup-', [status(thm)], ['3', '4'])).
% 1.03/1.30  thf('6', plain,
% 1.03/1.30      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.03/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.30  thf(redefinition_k1_relset_1, axiom,
% 1.03/1.30    (![A:$i,B:$i,C:$i]:
% 1.03/1.30     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.03/1.30       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.03/1.30  thf('7', plain,
% 1.03/1.30      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.03/1.30         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 1.03/1.30          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.03/1.30      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.03/1.30  thf('8', plain, (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 1.03/1.30      inference('sup-', [status(thm)], ['6', '7'])).
% 1.03/1.30  thf('9', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 1.03/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.30  thf(d1_funct_2, axiom,
% 1.03/1.30    (![A:$i,B:$i,C:$i]:
% 1.03/1.30     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.03/1.30       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.03/1.30           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.03/1.30             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.03/1.30         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.03/1.30           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.03/1.30             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.03/1.30  thf(zf_stmt_1, axiom,
% 1.03/1.30    (![C:$i,B:$i,A:$i]:
% 1.03/1.30     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.03/1.30       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.03/1.30  thf('10', plain,
% 1.03/1.30      (![X39 : $i, X40 : $i, X41 : $i]:
% 1.03/1.30         (~ (v1_funct_2 @ X41 @ X39 @ X40)
% 1.03/1.30          | ((X39) = (k1_relset_1 @ X39 @ X40 @ X41))
% 1.03/1.30          | ~ (zip_tseitin_1 @ X41 @ X40 @ X39))),
% 1.03/1.30      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.03/1.30  thf('11', plain,
% 1.03/1.30      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 1.03/1.30        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 1.03/1.30      inference('sup-', [status(thm)], ['9', '10'])).
% 1.03/1.30  thf(zf_stmt_2, axiom,
% 1.03/1.30    (![B:$i,A:$i]:
% 1.03/1.30     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.03/1.30       ( zip_tseitin_0 @ B @ A ) ))).
% 1.03/1.30  thf('12', plain,
% 1.03/1.30      (![X37 : $i, X38 : $i]:
% 1.03/1.30         ((zip_tseitin_0 @ X37 @ X38) | ((X37) = (k1_xboole_0)))),
% 1.03/1.30      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.03/1.30  thf('13', plain,
% 1.03/1.30      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.03/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.30  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.03/1.30  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.03/1.30  thf(zf_stmt_5, axiom,
% 1.03/1.30    (![A:$i,B:$i,C:$i]:
% 1.03/1.30     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.03/1.30       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.03/1.30         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.03/1.30           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.03/1.30             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.03/1.30  thf('14', plain,
% 1.03/1.30      (![X42 : $i, X43 : $i, X44 : $i]:
% 1.03/1.30         (~ (zip_tseitin_0 @ X42 @ X43)
% 1.03/1.30          | (zip_tseitin_1 @ X44 @ X42 @ X43)
% 1.03/1.30          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42))))),
% 1.03/1.30      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.03/1.30  thf('15', plain,
% 1.03/1.30      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 1.03/1.30      inference('sup-', [status(thm)], ['13', '14'])).
% 1.03/1.30  thf('16', plain,
% 1.03/1.30      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 1.03/1.30      inference('sup-', [status(thm)], ['12', '15'])).
% 1.03/1.30  thf('17', plain, (((sk_C) != (k1_xboole_0))),
% 1.03/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.30  thf('18', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 1.03/1.30      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 1.03/1.30  thf('19', plain,
% 1.03/1.30      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 1.03/1.30      inference('sup-', [status(thm)], ['6', '7'])).
% 1.03/1.30  thf('20', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 1.03/1.30      inference('demod', [status(thm)], ['11', '18', '19'])).
% 1.03/1.30  thf('21', plain, (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (sk_B))),
% 1.03/1.30      inference('demod', [status(thm)], ['8', '20'])).
% 1.03/1.30  thf('22', plain, (((k10_relat_1 @ sk_E @ sk_C) = (sk_B))),
% 1.03/1.30      inference('demod', [status(thm)], ['2', '5', '21'])).
% 1.03/1.30  thf('23', plain,
% 1.03/1.30      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.03/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.30  thf(cc2_relset_1, axiom,
% 1.03/1.30    (![A:$i,B:$i,C:$i]:
% 1.03/1.30     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.03/1.30       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.03/1.30  thf('24', plain,
% 1.03/1.30      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.03/1.30         ((v5_relat_1 @ X9 @ X11)
% 1.03/1.30          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 1.03/1.30      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.03/1.30  thf('25', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 1.03/1.30      inference('sup-', [status(thm)], ['23', '24'])).
% 1.03/1.30  thf(d19_relat_1, axiom,
% 1.03/1.30    (![A:$i,B:$i]:
% 1.03/1.30     ( ( v1_relat_1 @ B ) =>
% 1.03/1.30       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.03/1.30  thf('26', plain,
% 1.03/1.30      (![X0 : $i, X1 : $i]:
% 1.03/1.30         (~ (v5_relat_1 @ X0 @ X1)
% 1.03/1.30          | (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 1.03/1.30          | ~ (v1_relat_1 @ X0))),
% 1.03/1.30      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.03/1.30  thf('27', plain,
% 1.03/1.30      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 1.03/1.30      inference('sup-', [status(thm)], ['25', '26'])).
% 1.03/1.30  thf('28', plain,
% 1.03/1.30      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.03/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.30  thf(cc1_relset_1, axiom,
% 1.03/1.30    (![A:$i,B:$i,C:$i]:
% 1.03/1.30     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.03/1.30       ( v1_relat_1 @ C ) ))).
% 1.03/1.30  thf('29', plain,
% 1.03/1.30      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.03/1.30         ((v1_relat_1 @ X6)
% 1.03/1.30          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 1.03/1.30      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.03/1.30  thf('30', plain, ((v1_relat_1 @ sk_D)),
% 1.03/1.30      inference('sup-', [status(thm)], ['28', '29'])).
% 1.03/1.30  thf('31', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 1.03/1.30      inference('demod', [status(thm)], ['27', '30'])).
% 1.03/1.30  thf('32', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 1.03/1.30      inference('demod', [status(thm)], ['11', '18', '19'])).
% 1.03/1.30  thf(t164_funct_1, axiom,
% 1.03/1.30    (![A:$i,B:$i]:
% 1.03/1.30     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.03/1.30       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 1.03/1.30         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 1.03/1.30  thf('33', plain,
% 1.03/1.30      (![X4 : $i, X5 : $i]:
% 1.03/1.30         (~ (r1_tarski @ X4 @ (k1_relat_1 @ X5))
% 1.03/1.30          | ~ (v2_funct_1 @ X5)
% 1.03/1.30          | ((k10_relat_1 @ X5 @ (k9_relat_1 @ X5 @ X4)) = (X4))
% 1.03/1.30          | ~ (v1_funct_1 @ X5)
% 1.03/1.30          | ~ (v1_relat_1 @ X5))),
% 1.03/1.30      inference('cnf', [status(esa)], [t164_funct_1])).
% 1.03/1.30  thf('34', plain,
% 1.03/1.30      (![X0 : $i]:
% 1.03/1.30         (~ (r1_tarski @ X0 @ sk_B)
% 1.03/1.30          | ~ (v1_relat_1 @ sk_E)
% 1.03/1.30          | ~ (v1_funct_1 @ sk_E)
% 1.03/1.30          | ((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ X0)) = (X0))
% 1.03/1.30          | ~ (v2_funct_1 @ sk_E))),
% 1.03/1.30      inference('sup-', [status(thm)], ['32', '33'])).
% 1.03/1.30  thf('35', plain,
% 1.03/1.30      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.03/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.30  thf('36', plain,
% 1.03/1.30      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.03/1.30         ((v1_relat_1 @ X6)
% 1.03/1.30          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 1.03/1.30      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.03/1.30  thf('37', plain, ((v1_relat_1 @ sk_E)),
% 1.03/1.30      inference('sup-', [status(thm)], ['35', '36'])).
% 1.03/1.30  thf('38', plain, ((v1_funct_1 @ sk_E)),
% 1.03/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.30  thf('39', plain, ((v2_funct_1 @ sk_E)),
% 1.03/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.30  thf('40', plain,
% 1.03/1.30      (![X0 : $i]:
% 1.03/1.30         (~ (r1_tarski @ X0 @ sk_B)
% 1.03/1.30          | ((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ X0)) = (X0)))),
% 1.03/1.30      inference('demod', [status(thm)], ['34', '37', '38', '39'])).
% 1.03/1.30  thf('41', plain,
% 1.03/1.30      (((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)))
% 1.03/1.30         = (k2_relat_1 @ sk_D))),
% 1.03/1.30      inference('sup-', [status(thm)], ['31', '40'])).
% 1.03/1.30  thf(t160_relat_1, axiom,
% 1.03/1.30    (![A:$i]:
% 1.03/1.30     ( ( v1_relat_1 @ A ) =>
% 1.03/1.30       ( ![B:$i]:
% 1.03/1.30         ( ( v1_relat_1 @ B ) =>
% 1.03/1.30           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.03/1.30             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.03/1.30  thf('42', plain,
% 1.03/1.30      (![X2 : $i, X3 : $i]:
% 1.03/1.30         (~ (v1_relat_1 @ X2)
% 1.03/1.30          | ((k2_relat_1 @ (k5_relat_1 @ X3 @ X2))
% 1.03/1.30              = (k9_relat_1 @ X2 @ (k2_relat_1 @ X3)))
% 1.03/1.30          | ~ (v1_relat_1 @ X3))),
% 1.03/1.30      inference('cnf', [status(esa)], [t160_relat_1])).
% 1.03/1.30  thf('43', plain,
% 1.03/1.30      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.03/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.30  thf('44', plain,
% 1.03/1.30      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.03/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.30  thf(dt_k4_relset_1, axiom,
% 1.03/1.30    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.03/1.30     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.03/1.30         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.03/1.30       ( m1_subset_1 @
% 1.03/1.30         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.03/1.30         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 1.03/1.30  thf('45', plain,
% 1.03/1.30      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 1.03/1.30         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 1.03/1.30          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 1.03/1.30          | (m1_subset_1 @ (k4_relset_1 @ X13 @ X14 @ X16 @ X17 @ X12 @ X15) @ 
% 1.03/1.30             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X17))))),
% 1.03/1.30      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 1.03/1.30  thf('46', plain,
% 1.03/1.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.30         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 1.03/1.30           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.03/1.30          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 1.03/1.30      inference('sup-', [status(thm)], ['44', '45'])).
% 1.03/1.30  thf('47', plain,
% 1.03/1.30      ((m1_subset_1 @ 
% 1.03/1.30        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 1.03/1.30        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.03/1.30      inference('sup-', [status(thm)], ['43', '46'])).
% 1.03/1.30  thf('48', plain,
% 1.03/1.30      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.03/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.30  thf('49', plain,
% 1.03/1.30      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.03/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.30  thf(redefinition_k4_relset_1, axiom,
% 1.03/1.30    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.03/1.30     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.03/1.30         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.03/1.30       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.03/1.30  thf('50', plain,
% 1.03/1.30      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.03/1.30         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 1.03/1.30          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 1.03/1.30          | ((k4_relset_1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27)
% 1.03/1.30              = (k5_relat_1 @ X24 @ X27)))),
% 1.03/1.30      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 1.03/1.30  thf('51', plain,
% 1.03/1.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.30         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 1.03/1.30            = (k5_relat_1 @ sk_D @ X0))
% 1.03/1.30          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 1.03/1.30      inference('sup-', [status(thm)], ['49', '50'])).
% 1.03/1.30  thf('52', plain,
% 1.03/1.30      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.03/1.30         = (k5_relat_1 @ sk_D @ sk_E))),
% 1.03/1.30      inference('sup-', [status(thm)], ['48', '51'])).
% 1.03/1.30  thf('53', plain,
% 1.03/1.30      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 1.03/1.30        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.03/1.30      inference('demod', [status(thm)], ['47', '52'])).
% 1.03/1.30  thf(redefinition_k2_relset_1, axiom,
% 1.03/1.30    (![A:$i,B:$i,C:$i]:
% 1.03/1.30     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.03/1.30       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.03/1.30  thf('54', plain,
% 1.03/1.30      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.03/1.30         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 1.03/1.30          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 1.03/1.30      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.03/1.30  thf('55', plain,
% 1.03/1.30      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E))
% 1.03/1.30         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 1.03/1.30      inference('sup-', [status(thm)], ['53', '54'])).
% 1.03/1.30  thf('56', plain,
% 1.03/1.30      (((k2_relset_1 @ sk_A @ sk_C @ 
% 1.03/1.30         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) = (sk_C))),
% 1.03/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.30  thf('57', plain,
% 1.03/1.30      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.03/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.30  thf('58', plain,
% 1.03/1.30      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.03/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.30  thf(redefinition_k1_partfun1, axiom,
% 1.03/1.30    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.03/1.30     ( ( ( v1_funct_1 @ E ) & 
% 1.03/1.30         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.03/1.30         ( v1_funct_1 @ F ) & 
% 1.03/1.30         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.03/1.30       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.03/1.30  thf('59', plain,
% 1.03/1.30      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 1.03/1.30         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 1.03/1.30          | ~ (v1_funct_1 @ X45)
% 1.03/1.30          | ~ (v1_funct_1 @ X48)
% 1.03/1.30          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 1.03/1.30          | ((k1_partfun1 @ X46 @ X47 @ X49 @ X50 @ X45 @ X48)
% 1.03/1.30              = (k5_relat_1 @ X45 @ X48)))),
% 1.03/1.30      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.03/1.30  thf('60', plain,
% 1.03/1.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.30         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 1.03/1.30            = (k5_relat_1 @ sk_D @ X0))
% 1.03/1.30          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.03/1.30          | ~ (v1_funct_1 @ X0)
% 1.03/1.30          | ~ (v1_funct_1 @ sk_D))),
% 1.03/1.30      inference('sup-', [status(thm)], ['58', '59'])).
% 1.03/1.30  thf('61', plain, ((v1_funct_1 @ sk_D)),
% 1.03/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.30  thf('62', plain,
% 1.03/1.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.30         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 1.03/1.30            = (k5_relat_1 @ sk_D @ X0))
% 1.03/1.30          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.03/1.30          | ~ (v1_funct_1 @ X0))),
% 1.03/1.30      inference('demod', [status(thm)], ['60', '61'])).
% 1.03/1.30  thf('63', plain,
% 1.03/1.30      ((~ (v1_funct_1 @ sk_E)
% 1.03/1.30        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.03/1.30            = (k5_relat_1 @ sk_D @ sk_E)))),
% 1.03/1.30      inference('sup-', [status(thm)], ['57', '62'])).
% 1.03/1.30  thf('64', plain, ((v1_funct_1 @ sk_E)),
% 1.03/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.30  thf('65', plain,
% 1.03/1.30      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.03/1.30         = (k5_relat_1 @ sk_D @ sk_E))),
% 1.03/1.30      inference('demod', [status(thm)], ['63', '64'])).
% 1.03/1.30  thf('66', plain,
% 1.03/1.30      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 1.03/1.30      inference('demod', [status(thm)], ['56', '65'])).
% 1.03/1.30  thf('67', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 1.03/1.30      inference('sup+', [status(thm)], ['55', '66'])).
% 1.03/1.30  thf('68', plain,
% 1.03/1.30      ((((k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)) = (sk_C))
% 1.03/1.30        | ~ (v1_relat_1 @ sk_D)
% 1.03/1.30        | ~ (v1_relat_1 @ sk_E))),
% 1.03/1.30      inference('sup+', [status(thm)], ['42', '67'])).
% 1.03/1.30  thf('69', plain, ((v1_relat_1 @ sk_D)),
% 1.03/1.30      inference('sup-', [status(thm)], ['28', '29'])).
% 1.03/1.30  thf('70', plain, ((v1_relat_1 @ sk_E)),
% 1.03/1.30      inference('sup-', [status(thm)], ['35', '36'])).
% 1.03/1.30  thf('71', plain, (((k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)) = (sk_C))),
% 1.03/1.30      inference('demod', [status(thm)], ['68', '69', '70'])).
% 1.03/1.30  thf('72', plain, (((k10_relat_1 @ sk_E @ sk_C) = (k2_relat_1 @ sk_D))),
% 1.03/1.30      inference('demod', [status(thm)], ['41', '71'])).
% 1.03/1.30  thf('73', plain, (((sk_B) = (k2_relat_1 @ sk_D))),
% 1.03/1.30      inference('sup+', [status(thm)], ['22', '72'])).
% 1.03/1.30  thf('74', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) != (sk_B))),
% 1.03/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.30  thf('75', plain,
% 1.03/1.30      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.03/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.30  thf('76', plain,
% 1.03/1.30      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.03/1.30         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 1.03/1.30          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 1.03/1.30      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.03/1.30  thf('77', plain,
% 1.03/1.30      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.03/1.30      inference('sup-', [status(thm)], ['75', '76'])).
% 1.03/1.30  thf('78', plain, (((k2_relat_1 @ sk_D) != (sk_B))),
% 1.03/1.30      inference('demod', [status(thm)], ['74', '77'])).
% 1.03/1.30  thf('79', plain, ($false),
% 1.03/1.30      inference('simplify_reflect-', [status(thm)], ['73', '78'])).
% 1.03/1.30  
% 1.03/1.30  % SZS output end Refutation
% 1.03/1.30  
% 1.12/1.31  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
