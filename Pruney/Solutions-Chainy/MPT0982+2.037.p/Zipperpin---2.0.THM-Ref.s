%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pbdwC0HBaV

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:00 EST 2020

% Result     : Theorem 1.13s
% Output     : Refutation 1.13s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 225 expanded)
%              Number of leaves         :   49 (  89 expanded)
%              Depth                    :   13
%              Number of atoms          : 1089 (4012 expanded)
%              Number of equality atoms :   69 ( 254 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

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
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k8_relset_1 @ X35 @ X36 @ X37 @ X36 )
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k8_relset_1 @ X32 @ X33 @ X31 @ X34 )
        = ( k10_relat_1 @ X31 @ X34 ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
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
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_funct_2 @ X42 @ X40 @ X41 )
      | ( X40
        = ( k1_relset_1 @ X40 @ X41 @ X42 ) )
      | ~ ( zip_tseitin_1 @ X42 @ X41 @ X40 ) ) ),
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
    ! [X38: $i,X39: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 )
      | ( X38 = k1_xboole_0 ) ) ),
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
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( zip_tseitin_0 @ X43 @ X44 )
      | ( zip_tseitin_1 @ X45 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v5_relat_1 @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
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
    ! [X2: $i,X3: $i] :
      ( ~ ( v5_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k2_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('31',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('32',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['27','32'])).

thf('34',plain,
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

thf('35',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X8 @ ( k1_relat_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ( ( k10_relat_1 @ X9 @ ( k9_relat_1 @ X9 @ X8 ) )
        = X8 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k10_relat_1 @ sk_E @ ( k9_relat_1 @ sk_E @ X0 ) )
        = X0 )
      | ~ ( v2_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('41',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k10_relat_1 @ sk_E @ ( k9_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['36','41','42','43'])).

thf('45',plain,
    ( ( k10_relat_1 @ sk_E @ ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) ) )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['33','44'])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('46',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) )
        = ( k9_relat_1 @ X6 @ ( k2_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('47',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( m1_subset_1 @ ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) )).

thf('49',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X14 @ X15 @ X17 @ X18 @ X13 @ X16 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relset_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('54',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( ( k4_relset_1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28 )
        = ( k5_relat_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['51','56'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('58',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('59',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
    = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
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

thf('63',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ( ( k1_partfun1 @ X47 @ X48 @ X50 @ X51 @ X46 @ X49 )
        = ( k5_relat_1 @ X46 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['60','69'])).

thf('71',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['59','70'])).

thf('72',plain,
    ( ( ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['46','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['30','31'])).

thf('74',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['39','40'])).

thf('75',plain,
    ( ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) )
    = sk_C ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ( k10_relat_1 @ sk_E @ sk_C )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['45','75'])).

thf('77',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['22','76'])).

thf('78',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('81',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ( k2_relat_1 @ sk_D )
 != sk_B ),
    inference(demod,[status(thm)],['78','81'])).

thf('83',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['77','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pbdwC0HBaV
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:30:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.13/1.31  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.13/1.31  % Solved by: fo/fo7.sh
% 1.13/1.31  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.13/1.31  % done 559 iterations in 0.857s
% 1.13/1.31  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.13/1.31  % SZS output start Refutation
% 1.13/1.31  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.13/1.31  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.13/1.31  thf(sk_E_type, type, sk_E: $i).
% 1.13/1.31  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.13/1.31  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.13/1.31  thf(sk_D_type, type, sk_D: $i).
% 1.13/1.31  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.13/1.31  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.13/1.31  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.13/1.31  thf(sk_C_type, type, sk_C: $i).
% 1.13/1.31  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.13/1.31  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.13/1.31  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 1.13/1.31  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 1.13/1.31  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.13/1.31  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.13/1.31  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.13/1.31  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 1.13/1.31  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.13/1.31  thf(sk_A_type, type, sk_A: $i).
% 1.13/1.31  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.13/1.31  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.13/1.31  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.13/1.31  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.13/1.31  thf(sk_B_type, type, sk_B: $i).
% 1.13/1.31  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.13/1.31  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.13/1.31  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.13/1.31  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.13/1.31  thf(t28_funct_2, conjecture,
% 1.13/1.31    (![A:$i,B:$i,C:$i,D:$i]:
% 1.13/1.31     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.13/1.31         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.13/1.31       ( ![E:$i]:
% 1.13/1.31         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.13/1.31             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.13/1.31           ( ( ( ( k2_relset_1 @
% 1.13/1.31                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 1.13/1.31                 ( C ) ) & 
% 1.13/1.31               ( v2_funct_1 @ E ) ) =>
% 1.13/1.31             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.13/1.31               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ))).
% 1.13/1.31  thf(zf_stmt_0, negated_conjecture,
% 1.13/1.31    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.13/1.31        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.13/1.31            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.13/1.31          ( ![E:$i]:
% 1.13/1.31            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.13/1.31                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.13/1.31              ( ( ( ( k2_relset_1 @
% 1.13/1.31                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 1.13/1.31                    ( C ) ) & 
% 1.13/1.31                  ( v2_funct_1 @ E ) ) =>
% 1.13/1.31                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.13/1.31                  ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ) )),
% 1.13/1.31    inference('cnf.neg', [status(esa)], [t28_funct_2])).
% 1.13/1.31  thf('0', plain,
% 1.13/1.31      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.13/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.31  thf(t38_relset_1, axiom,
% 1.13/1.31    (![A:$i,B:$i,C:$i]:
% 1.13/1.31     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.13/1.31       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 1.13/1.31         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.13/1.31  thf('1', plain,
% 1.13/1.31      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.13/1.31         (((k8_relset_1 @ X35 @ X36 @ X37 @ X36)
% 1.13/1.31            = (k1_relset_1 @ X35 @ X36 @ X37))
% 1.13/1.31          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 1.13/1.31      inference('cnf', [status(esa)], [t38_relset_1])).
% 1.13/1.31  thf('2', plain,
% 1.13/1.31      (((k8_relset_1 @ sk_B @ sk_C @ sk_E @ sk_C)
% 1.13/1.31         = (k1_relset_1 @ sk_B @ sk_C @ sk_E))),
% 1.13/1.31      inference('sup-', [status(thm)], ['0', '1'])).
% 1.13/1.31  thf('3', plain,
% 1.13/1.31      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.13/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.31  thf(redefinition_k8_relset_1, axiom,
% 1.13/1.31    (![A:$i,B:$i,C:$i,D:$i]:
% 1.13/1.31     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.13/1.31       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 1.13/1.31  thf('4', plain,
% 1.13/1.31      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.13/1.31         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.13/1.31          | ((k8_relset_1 @ X32 @ X33 @ X31 @ X34) = (k10_relat_1 @ X31 @ X34)))),
% 1.13/1.31      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 1.13/1.31  thf('5', plain,
% 1.13/1.31      (![X0 : $i]:
% 1.13/1.31         ((k8_relset_1 @ sk_B @ sk_C @ sk_E @ X0) = (k10_relat_1 @ sk_E @ X0))),
% 1.13/1.31      inference('sup-', [status(thm)], ['3', '4'])).
% 1.13/1.31  thf('6', plain,
% 1.13/1.31      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.13/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.31  thf(redefinition_k1_relset_1, axiom,
% 1.13/1.31    (![A:$i,B:$i,C:$i]:
% 1.13/1.31     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.13/1.31       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.13/1.31  thf('7', plain,
% 1.13/1.31      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.13/1.31         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 1.13/1.31          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 1.13/1.31      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.13/1.31  thf('8', plain, (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 1.13/1.31      inference('sup-', [status(thm)], ['6', '7'])).
% 1.13/1.31  thf('9', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 1.13/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.31  thf(d1_funct_2, axiom,
% 1.13/1.31    (![A:$i,B:$i,C:$i]:
% 1.13/1.31     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.13/1.31       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.13/1.31           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.13/1.31             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.13/1.31         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.13/1.31           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.13/1.31             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.13/1.31  thf(zf_stmt_1, axiom,
% 1.13/1.31    (![C:$i,B:$i,A:$i]:
% 1.13/1.31     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.13/1.31       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.13/1.31  thf('10', plain,
% 1.13/1.31      (![X40 : $i, X41 : $i, X42 : $i]:
% 1.13/1.31         (~ (v1_funct_2 @ X42 @ X40 @ X41)
% 1.13/1.31          | ((X40) = (k1_relset_1 @ X40 @ X41 @ X42))
% 1.13/1.31          | ~ (zip_tseitin_1 @ X42 @ X41 @ X40))),
% 1.13/1.31      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.13/1.31  thf('11', plain,
% 1.13/1.31      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 1.13/1.31        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 1.13/1.31      inference('sup-', [status(thm)], ['9', '10'])).
% 1.13/1.31  thf(zf_stmt_2, axiom,
% 1.13/1.31    (![B:$i,A:$i]:
% 1.13/1.31     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.13/1.31       ( zip_tseitin_0 @ B @ A ) ))).
% 1.13/1.31  thf('12', plain,
% 1.13/1.31      (![X38 : $i, X39 : $i]:
% 1.13/1.31         ((zip_tseitin_0 @ X38 @ X39) | ((X38) = (k1_xboole_0)))),
% 1.13/1.31      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.13/1.31  thf('13', plain,
% 1.13/1.31      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.13/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.31  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.13/1.31  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.13/1.31  thf(zf_stmt_5, axiom,
% 1.13/1.31    (![A:$i,B:$i,C:$i]:
% 1.13/1.31     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.13/1.31       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.13/1.31         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.13/1.31           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.13/1.31             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.13/1.31  thf('14', plain,
% 1.13/1.31      (![X43 : $i, X44 : $i, X45 : $i]:
% 1.13/1.31         (~ (zip_tseitin_0 @ X43 @ X44)
% 1.13/1.31          | (zip_tseitin_1 @ X45 @ X43 @ X44)
% 1.13/1.31          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43))))),
% 1.13/1.31      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.13/1.31  thf('15', plain,
% 1.13/1.31      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 1.13/1.31      inference('sup-', [status(thm)], ['13', '14'])).
% 1.13/1.31  thf('16', plain,
% 1.13/1.31      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 1.13/1.31      inference('sup-', [status(thm)], ['12', '15'])).
% 1.13/1.31  thf('17', plain, (((sk_C) != (k1_xboole_0))),
% 1.13/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.31  thf('18', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 1.13/1.31      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 1.13/1.31  thf('19', plain,
% 1.13/1.31      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 1.13/1.31      inference('sup-', [status(thm)], ['6', '7'])).
% 1.13/1.31  thf('20', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 1.13/1.31      inference('demod', [status(thm)], ['11', '18', '19'])).
% 1.13/1.31  thf('21', plain, (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (sk_B))),
% 1.13/1.31      inference('demod', [status(thm)], ['8', '20'])).
% 1.13/1.31  thf('22', plain, (((k10_relat_1 @ sk_E @ sk_C) = (sk_B))),
% 1.13/1.31      inference('demod', [status(thm)], ['2', '5', '21'])).
% 1.13/1.31  thf('23', plain,
% 1.13/1.31      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.13/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.31  thf(cc2_relset_1, axiom,
% 1.13/1.31    (![A:$i,B:$i,C:$i]:
% 1.13/1.31     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.13/1.31       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.13/1.31  thf('24', plain,
% 1.13/1.31      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.13/1.31         ((v5_relat_1 @ X10 @ X12)
% 1.13/1.31          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 1.13/1.31      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.13/1.31  thf('25', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 1.13/1.31      inference('sup-', [status(thm)], ['23', '24'])).
% 1.13/1.31  thf(d19_relat_1, axiom,
% 1.13/1.31    (![A:$i,B:$i]:
% 1.13/1.31     ( ( v1_relat_1 @ B ) =>
% 1.13/1.31       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.13/1.31  thf('26', plain,
% 1.13/1.31      (![X2 : $i, X3 : $i]:
% 1.13/1.31         (~ (v5_relat_1 @ X2 @ X3)
% 1.13/1.31          | (r1_tarski @ (k2_relat_1 @ X2) @ X3)
% 1.13/1.31          | ~ (v1_relat_1 @ X2))),
% 1.13/1.31      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.13/1.31  thf('27', plain,
% 1.13/1.31      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 1.13/1.31      inference('sup-', [status(thm)], ['25', '26'])).
% 1.13/1.31  thf('28', plain,
% 1.13/1.31      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.13/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.31  thf(cc2_relat_1, axiom,
% 1.13/1.31    (![A:$i]:
% 1.13/1.31     ( ( v1_relat_1 @ A ) =>
% 1.13/1.31       ( ![B:$i]:
% 1.13/1.31         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.13/1.31  thf('29', plain,
% 1.13/1.31      (![X0 : $i, X1 : $i]:
% 1.13/1.31         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.13/1.31          | (v1_relat_1 @ X0)
% 1.13/1.31          | ~ (v1_relat_1 @ X1))),
% 1.13/1.31      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.13/1.31  thf('30', plain,
% 1.13/1.31      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 1.13/1.31      inference('sup-', [status(thm)], ['28', '29'])).
% 1.13/1.31  thf(fc6_relat_1, axiom,
% 1.13/1.31    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.13/1.31  thf('31', plain,
% 1.13/1.31      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 1.13/1.31      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.13/1.31  thf('32', plain, ((v1_relat_1 @ sk_D)),
% 1.13/1.31      inference('demod', [status(thm)], ['30', '31'])).
% 1.13/1.31  thf('33', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 1.13/1.31      inference('demod', [status(thm)], ['27', '32'])).
% 1.13/1.31  thf('34', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 1.13/1.31      inference('demod', [status(thm)], ['11', '18', '19'])).
% 1.13/1.31  thf(t164_funct_1, axiom,
% 1.13/1.31    (![A:$i,B:$i]:
% 1.13/1.31     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.13/1.31       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 1.13/1.31         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 1.13/1.31  thf('35', plain,
% 1.13/1.31      (![X8 : $i, X9 : $i]:
% 1.13/1.31         (~ (r1_tarski @ X8 @ (k1_relat_1 @ X9))
% 1.13/1.31          | ~ (v2_funct_1 @ X9)
% 1.13/1.31          | ((k10_relat_1 @ X9 @ (k9_relat_1 @ X9 @ X8)) = (X8))
% 1.13/1.31          | ~ (v1_funct_1 @ X9)
% 1.13/1.31          | ~ (v1_relat_1 @ X9))),
% 1.13/1.31      inference('cnf', [status(esa)], [t164_funct_1])).
% 1.13/1.31  thf('36', plain,
% 1.13/1.31      (![X0 : $i]:
% 1.13/1.31         (~ (r1_tarski @ X0 @ sk_B)
% 1.13/1.31          | ~ (v1_relat_1 @ sk_E)
% 1.13/1.31          | ~ (v1_funct_1 @ sk_E)
% 1.13/1.31          | ((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ X0)) = (X0))
% 1.13/1.31          | ~ (v2_funct_1 @ sk_E))),
% 1.13/1.31      inference('sup-', [status(thm)], ['34', '35'])).
% 1.13/1.31  thf('37', plain,
% 1.13/1.31      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.13/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.31  thf('38', plain,
% 1.13/1.31      (![X0 : $i, X1 : $i]:
% 1.13/1.31         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.13/1.31          | (v1_relat_1 @ X0)
% 1.13/1.31          | ~ (v1_relat_1 @ X1))),
% 1.13/1.31      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.13/1.31  thf('39', plain,
% 1.13/1.31      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)) | (v1_relat_1 @ sk_E))),
% 1.13/1.31      inference('sup-', [status(thm)], ['37', '38'])).
% 1.13/1.31  thf('40', plain,
% 1.13/1.31      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 1.13/1.31      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.13/1.31  thf('41', plain, ((v1_relat_1 @ sk_E)),
% 1.13/1.31      inference('demod', [status(thm)], ['39', '40'])).
% 1.13/1.31  thf('42', plain, ((v1_funct_1 @ sk_E)),
% 1.13/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.31  thf('43', plain, ((v2_funct_1 @ sk_E)),
% 1.13/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.31  thf('44', plain,
% 1.13/1.31      (![X0 : $i]:
% 1.13/1.31         (~ (r1_tarski @ X0 @ sk_B)
% 1.13/1.31          | ((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ X0)) = (X0)))),
% 1.13/1.31      inference('demod', [status(thm)], ['36', '41', '42', '43'])).
% 1.13/1.31  thf('45', plain,
% 1.13/1.31      (((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)))
% 1.13/1.31         = (k2_relat_1 @ sk_D))),
% 1.13/1.31      inference('sup-', [status(thm)], ['33', '44'])).
% 1.13/1.31  thf(t160_relat_1, axiom,
% 1.13/1.31    (![A:$i]:
% 1.13/1.31     ( ( v1_relat_1 @ A ) =>
% 1.13/1.31       ( ![B:$i]:
% 1.13/1.31         ( ( v1_relat_1 @ B ) =>
% 1.13/1.31           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.13/1.31             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.13/1.31  thf('46', plain,
% 1.13/1.31      (![X6 : $i, X7 : $i]:
% 1.13/1.31         (~ (v1_relat_1 @ X6)
% 1.13/1.31          | ((k2_relat_1 @ (k5_relat_1 @ X7 @ X6))
% 1.13/1.31              = (k9_relat_1 @ X6 @ (k2_relat_1 @ X7)))
% 1.13/1.31          | ~ (v1_relat_1 @ X7))),
% 1.13/1.31      inference('cnf', [status(esa)], [t160_relat_1])).
% 1.13/1.31  thf('47', plain,
% 1.13/1.31      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.13/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.31  thf('48', plain,
% 1.13/1.31      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.13/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.31  thf(dt_k4_relset_1, axiom,
% 1.13/1.31    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.13/1.31     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.13/1.31         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.13/1.31       ( m1_subset_1 @
% 1.13/1.31         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.13/1.31         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 1.13/1.31  thf('49', plain,
% 1.13/1.31      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 1.13/1.31         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 1.13/1.31          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 1.13/1.31          | (m1_subset_1 @ (k4_relset_1 @ X14 @ X15 @ X17 @ X18 @ X13 @ X16) @ 
% 1.13/1.31             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X18))))),
% 1.13/1.31      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 1.13/1.31  thf('50', plain,
% 1.13/1.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.13/1.31         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 1.13/1.31           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.13/1.31          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 1.13/1.31      inference('sup-', [status(thm)], ['48', '49'])).
% 1.13/1.31  thf('51', plain,
% 1.13/1.31      ((m1_subset_1 @ 
% 1.13/1.31        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 1.13/1.31        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.13/1.31      inference('sup-', [status(thm)], ['47', '50'])).
% 1.13/1.31  thf('52', plain,
% 1.13/1.31      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.13/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.31  thf('53', plain,
% 1.13/1.31      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.13/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.31  thf(redefinition_k4_relset_1, axiom,
% 1.13/1.31    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.13/1.31     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.13/1.31         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.13/1.31       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.13/1.31  thf('54', plain,
% 1.13/1.31      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 1.13/1.31         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 1.13/1.31          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 1.13/1.31          | ((k4_relset_1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28)
% 1.13/1.31              = (k5_relat_1 @ X25 @ X28)))),
% 1.13/1.31      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 1.13/1.31  thf('55', plain,
% 1.13/1.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.13/1.31         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 1.13/1.31            = (k5_relat_1 @ sk_D @ X0))
% 1.13/1.31          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 1.13/1.31      inference('sup-', [status(thm)], ['53', '54'])).
% 1.13/1.31  thf('56', plain,
% 1.13/1.31      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.13/1.31         = (k5_relat_1 @ sk_D @ sk_E))),
% 1.13/1.31      inference('sup-', [status(thm)], ['52', '55'])).
% 1.13/1.31  thf('57', plain,
% 1.13/1.31      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 1.13/1.31        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.13/1.31      inference('demod', [status(thm)], ['51', '56'])).
% 1.13/1.31  thf(redefinition_k2_relset_1, axiom,
% 1.13/1.31    (![A:$i,B:$i,C:$i]:
% 1.13/1.31     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.13/1.31       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.13/1.31  thf('58', plain,
% 1.13/1.31      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.13/1.31         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 1.13/1.31          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.13/1.31      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.13/1.31  thf('59', plain,
% 1.13/1.31      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E))
% 1.13/1.31         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 1.13/1.31      inference('sup-', [status(thm)], ['57', '58'])).
% 1.13/1.31  thf('60', plain,
% 1.13/1.31      (((k2_relset_1 @ sk_A @ sk_C @ 
% 1.13/1.31         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) = (sk_C))),
% 1.13/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.31  thf('61', plain,
% 1.13/1.31      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.13/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.31  thf('62', plain,
% 1.13/1.31      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.13/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.31  thf(redefinition_k1_partfun1, axiom,
% 1.13/1.31    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.13/1.31     ( ( ( v1_funct_1 @ E ) & 
% 1.13/1.31         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.13/1.31         ( v1_funct_1 @ F ) & 
% 1.13/1.31         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.13/1.31       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.13/1.31  thf('63', plain,
% 1.13/1.31      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 1.13/1.31         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 1.13/1.31          | ~ (v1_funct_1 @ X46)
% 1.13/1.31          | ~ (v1_funct_1 @ X49)
% 1.13/1.31          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 1.13/1.31          | ((k1_partfun1 @ X47 @ X48 @ X50 @ X51 @ X46 @ X49)
% 1.13/1.31              = (k5_relat_1 @ X46 @ X49)))),
% 1.13/1.31      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.13/1.31  thf('64', plain,
% 1.13/1.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.13/1.31         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 1.13/1.31            = (k5_relat_1 @ sk_D @ X0))
% 1.13/1.31          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.13/1.31          | ~ (v1_funct_1 @ X0)
% 1.13/1.31          | ~ (v1_funct_1 @ sk_D))),
% 1.13/1.31      inference('sup-', [status(thm)], ['62', '63'])).
% 1.13/1.31  thf('65', plain, ((v1_funct_1 @ sk_D)),
% 1.13/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.31  thf('66', plain,
% 1.13/1.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.13/1.31         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 1.13/1.31            = (k5_relat_1 @ sk_D @ X0))
% 1.13/1.31          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.13/1.31          | ~ (v1_funct_1 @ X0))),
% 1.13/1.31      inference('demod', [status(thm)], ['64', '65'])).
% 1.13/1.31  thf('67', plain,
% 1.13/1.31      ((~ (v1_funct_1 @ sk_E)
% 1.13/1.31        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.13/1.31            = (k5_relat_1 @ sk_D @ sk_E)))),
% 1.13/1.31      inference('sup-', [status(thm)], ['61', '66'])).
% 1.13/1.31  thf('68', plain, ((v1_funct_1 @ sk_E)),
% 1.13/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.31  thf('69', plain,
% 1.13/1.31      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.13/1.31         = (k5_relat_1 @ sk_D @ sk_E))),
% 1.13/1.31      inference('demod', [status(thm)], ['67', '68'])).
% 1.13/1.31  thf('70', plain,
% 1.13/1.31      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 1.13/1.31      inference('demod', [status(thm)], ['60', '69'])).
% 1.13/1.31  thf('71', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 1.13/1.31      inference('sup+', [status(thm)], ['59', '70'])).
% 1.13/1.31  thf('72', plain,
% 1.13/1.31      ((((k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)) = (sk_C))
% 1.13/1.31        | ~ (v1_relat_1 @ sk_D)
% 1.13/1.31        | ~ (v1_relat_1 @ sk_E))),
% 1.13/1.31      inference('sup+', [status(thm)], ['46', '71'])).
% 1.13/1.31  thf('73', plain, ((v1_relat_1 @ sk_D)),
% 1.13/1.31      inference('demod', [status(thm)], ['30', '31'])).
% 1.13/1.31  thf('74', plain, ((v1_relat_1 @ sk_E)),
% 1.13/1.31      inference('demod', [status(thm)], ['39', '40'])).
% 1.13/1.31  thf('75', plain, (((k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)) = (sk_C))),
% 1.13/1.31      inference('demod', [status(thm)], ['72', '73', '74'])).
% 1.13/1.31  thf('76', plain, (((k10_relat_1 @ sk_E @ sk_C) = (k2_relat_1 @ sk_D))),
% 1.13/1.31      inference('demod', [status(thm)], ['45', '75'])).
% 1.13/1.31  thf('77', plain, (((sk_B) = (k2_relat_1 @ sk_D))),
% 1.13/1.31      inference('sup+', [status(thm)], ['22', '76'])).
% 1.13/1.31  thf('78', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) != (sk_B))),
% 1.13/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.31  thf('79', plain,
% 1.13/1.31      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.13/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.31  thf('80', plain,
% 1.13/1.31      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.13/1.31         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 1.13/1.31          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.13/1.31      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.13/1.31  thf('81', plain,
% 1.13/1.31      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.13/1.31      inference('sup-', [status(thm)], ['79', '80'])).
% 1.13/1.31  thf('82', plain, (((k2_relat_1 @ sk_D) != (sk_B))),
% 1.13/1.31      inference('demod', [status(thm)], ['78', '81'])).
% 1.13/1.31  thf('83', plain, ($false),
% 1.13/1.31      inference('simplify_reflect-', [status(thm)], ['77', '82'])).
% 1.13/1.31  
% 1.13/1.31  % SZS output end Refutation
% 1.13/1.31  
% 1.13/1.32  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
