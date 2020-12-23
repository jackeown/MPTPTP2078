%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZIBo8EVaam

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:00 EST 2020

% Result     : Theorem 1.97s
% Output     : Refutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 220 expanded)
%              Number of leaves         :   47 (  86 expanded)
%              Depth                    :   13
%              Number of atoms          : 1098 (4017 expanded)
%              Number of equality atoms :   70 ( 257 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k8_relset_1 @ X36 @ X37 @ X38 @ X37 )
        = ( k1_relset_1 @ X36 @ X37 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k8_relset_1 @ X33 @ X34 @ X32 @ X35 )
        = ( k10_relat_1 @ X32 @ X35 ) ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
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
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ( X41
        = ( k1_relset_1 @ X41 @ X42 @ X43 ) )
      | ~ ( zip_tseitin_1 @ X43 @ X42 @ X41 ) ) ),
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
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X39 = k1_xboole_0 ) ) ),
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
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( zip_tseitin_0 @ X44 @ X45 )
      | ( zip_tseitin_1 @ X46 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ) ),
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

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('24',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X11 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('25',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('27',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('28',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['25','28'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference('sup-',[status(thm)],['29','30'])).

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
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X9 @ ( k1_relat_1 @ X10 ) )
      | ~ ( v2_funct_1 @ X10 )
      | ( ( k10_relat_1 @ X10 @ ( k9_relat_1 @ X10 @ X9 ) )
        = X9 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('36',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('38',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('39',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k10_relat_1 @ sk_E @ ( k9_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['34','39','40','41'])).

thf('43',plain,
    ( ( k10_relat_1 @ sk_E @ ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) ) )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['31','42'])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('44',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) )
        = ( k9_relat_1 @ X7 @ ( k2_relat_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('45',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( m1_subset_1 @ ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) )).

thf('47',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X15 @ X16 @ X18 @ X19 @ X14 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relset_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('52',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( ( k4_relset_1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29 )
        = ( k5_relat_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['49','54'])).

thf('56',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('57',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
    = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
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

thf('61',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) )
      | ( ( k1_partfun1 @ X48 @ X49 @ X51 @ X52 @ X47 @ X50 )
        = ( k5_relat_1 @ X47 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['59','64'])).

thf('66',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['58','67'])).

thf('69',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['57','68'])).

thf('70',plain,
    ( ( ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['44','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('73',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('75',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['37','38'])).

thf('77',plain,
    ( ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) )
    = sk_C ),
    inference(demod,[status(thm)],['70','75','76'])).

thf('78',plain,
    ( ( k10_relat_1 @ sk_E @ sk_C )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['43','77'])).

thf('79',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['22','78'])).

thf('80',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('82',plain,(
    ( k2_relat_1 @ sk_D )
 != sk_B ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['79','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZIBo8EVaam
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:48:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.97/2.15  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.97/2.15  % Solved by: fo/fo7.sh
% 1.97/2.15  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.97/2.15  % done 648 iterations in 1.695s
% 1.97/2.15  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.97/2.15  % SZS output start Refutation
% 1.97/2.15  thf(sk_B_type, type, sk_B: $i).
% 1.97/2.15  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.97/2.15  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.97/2.15  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.97/2.15  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.97/2.15  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.97/2.15  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 1.97/2.15  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 1.97/2.15  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.97/2.15  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.97/2.15  thf(sk_A_type, type, sk_A: $i).
% 1.97/2.15  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.97/2.15  thf(sk_D_type, type, sk_D: $i).
% 1.97/2.15  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.97/2.15  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 1.97/2.15  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.97/2.15  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.97/2.15  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.97/2.15  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.97/2.15  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.97/2.15  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.97/2.15  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.97/2.15  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.97/2.15  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.97/2.15  thf(sk_E_type, type, sk_E: $i).
% 1.97/2.15  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.97/2.15  thf(sk_C_type, type, sk_C: $i).
% 1.97/2.15  thf(t28_funct_2, conjecture,
% 1.97/2.15    (![A:$i,B:$i,C:$i,D:$i]:
% 1.97/2.15     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.97/2.15         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.97/2.15       ( ![E:$i]:
% 1.97/2.15         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.97/2.15             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.97/2.15           ( ( ( ( k2_relset_1 @
% 1.97/2.15                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 1.97/2.15                 ( C ) ) & 
% 1.97/2.15               ( v2_funct_1 @ E ) ) =>
% 1.97/2.15             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.97/2.15               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ))).
% 1.97/2.15  thf(zf_stmt_0, negated_conjecture,
% 1.97/2.15    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.97/2.15        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.97/2.15            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.97/2.15          ( ![E:$i]:
% 1.97/2.15            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.97/2.15                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.97/2.15              ( ( ( ( k2_relset_1 @
% 1.97/2.15                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 1.97/2.15                    ( C ) ) & 
% 1.97/2.15                  ( v2_funct_1 @ E ) ) =>
% 1.97/2.15                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.97/2.15                  ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ) )),
% 1.97/2.15    inference('cnf.neg', [status(esa)], [t28_funct_2])).
% 1.97/2.15  thf('0', plain,
% 1.97/2.15      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.97/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.15  thf(t38_relset_1, axiom,
% 1.97/2.15    (![A:$i,B:$i,C:$i]:
% 1.97/2.15     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.97/2.15       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 1.97/2.15         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.97/2.15  thf('1', plain,
% 1.97/2.15      (![X36 : $i, X37 : $i, X38 : $i]:
% 1.97/2.15         (((k8_relset_1 @ X36 @ X37 @ X38 @ X37)
% 1.97/2.15            = (k1_relset_1 @ X36 @ X37 @ X38))
% 1.97/2.15          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 1.97/2.15      inference('cnf', [status(esa)], [t38_relset_1])).
% 1.97/2.15  thf('2', plain,
% 1.97/2.15      (((k8_relset_1 @ sk_B @ sk_C @ sk_E @ sk_C)
% 1.97/2.15         = (k1_relset_1 @ sk_B @ sk_C @ sk_E))),
% 1.97/2.15      inference('sup-', [status(thm)], ['0', '1'])).
% 1.97/2.15  thf('3', plain,
% 1.97/2.15      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.97/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.15  thf(redefinition_k8_relset_1, axiom,
% 1.97/2.15    (![A:$i,B:$i,C:$i,D:$i]:
% 1.97/2.15     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.97/2.15       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 1.97/2.15  thf('4', plain,
% 1.97/2.15      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.97/2.15         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 1.97/2.15          | ((k8_relset_1 @ X33 @ X34 @ X32 @ X35) = (k10_relat_1 @ X32 @ X35)))),
% 1.97/2.15      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 1.97/2.15  thf('5', plain,
% 1.97/2.15      (![X0 : $i]:
% 1.97/2.15         ((k8_relset_1 @ sk_B @ sk_C @ sk_E @ X0) = (k10_relat_1 @ sk_E @ X0))),
% 1.97/2.15      inference('sup-', [status(thm)], ['3', '4'])).
% 1.97/2.15  thf('6', plain,
% 1.97/2.15      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.97/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.15  thf(redefinition_k1_relset_1, axiom,
% 1.97/2.15    (![A:$i,B:$i,C:$i]:
% 1.97/2.15     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.97/2.15       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.97/2.15  thf('7', plain,
% 1.97/2.15      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.97/2.15         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 1.97/2.15          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.97/2.15      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.97/2.15  thf('8', plain, (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 1.97/2.15      inference('sup-', [status(thm)], ['6', '7'])).
% 1.97/2.15  thf('9', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 1.97/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.15  thf(d1_funct_2, axiom,
% 1.97/2.15    (![A:$i,B:$i,C:$i]:
% 1.97/2.15     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.97/2.15       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.97/2.15           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.97/2.15             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.97/2.15         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.97/2.15           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.97/2.15             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.97/2.15  thf(zf_stmt_1, axiom,
% 1.97/2.15    (![C:$i,B:$i,A:$i]:
% 1.97/2.15     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.97/2.15       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.97/2.15  thf('10', plain,
% 1.97/2.15      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.97/2.15         (~ (v1_funct_2 @ X43 @ X41 @ X42)
% 1.97/2.15          | ((X41) = (k1_relset_1 @ X41 @ X42 @ X43))
% 1.97/2.15          | ~ (zip_tseitin_1 @ X43 @ X42 @ X41))),
% 1.97/2.15      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.97/2.15  thf('11', plain,
% 1.97/2.15      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 1.97/2.15        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 1.97/2.15      inference('sup-', [status(thm)], ['9', '10'])).
% 1.97/2.15  thf(zf_stmt_2, axiom,
% 1.97/2.15    (![B:$i,A:$i]:
% 1.97/2.15     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.97/2.15       ( zip_tseitin_0 @ B @ A ) ))).
% 1.97/2.15  thf('12', plain,
% 1.97/2.15      (![X39 : $i, X40 : $i]:
% 1.97/2.15         ((zip_tseitin_0 @ X39 @ X40) | ((X39) = (k1_xboole_0)))),
% 1.97/2.15      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.97/2.15  thf('13', plain,
% 1.97/2.15      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.97/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.15  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.97/2.15  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.97/2.15  thf(zf_stmt_5, axiom,
% 1.97/2.15    (![A:$i,B:$i,C:$i]:
% 1.97/2.15     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.97/2.15       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.97/2.15         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.97/2.15           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.97/2.15             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.97/2.15  thf('14', plain,
% 1.97/2.15      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.97/2.15         (~ (zip_tseitin_0 @ X44 @ X45)
% 1.97/2.15          | (zip_tseitin_1 @ X46 @ X44 @ X45)
% 1.97/2.15          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44))))),
% 1.97/2.15      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.97/2.15  thf('15', plain,
% 1.97/2.15      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 1.97/2.15      inference('sup-', [status(thm)], ['13', '14'])).
% 1.97/2.15  thf('16', plain,
% 1.97/2.15      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 1.97/2.15      inference('sup-', [status(thm)], ['12', '15'])).
% 1.97/2.15  thf('17', plain, (((sk_C) != (k1_xboole_0))),
% 1.97/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.15  thf('18', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 1.97/2.15      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 1.97/2.15  thf('19', plain,
% 1.97/2.15      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 1.97/2.15      inference('sup-', [status(thm)], ['6', '7'])).
% 1.97/2.15  thf('20', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 1.97/2.15      inference('demod', [status(thm)], ['11', '18', '19'])).
% 1.97/2.15  thf('21', plain, (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (sk_B))),
% 1.97/2.15      inference('demod', [status(thm)], ['8', '20'])).
% 1.97/2.15  thf('22', plain, (((k10_relat_1 @ sk_E @ sk_C) = (sk_B))),
% 1.97/2.15      inference('demod', [status(thm)], ['2', '5', '21'])).
% 1.97/2.15  thf('23', plain,
% 1.97/2.15      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.97/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.15  thf(dt_k2_relset_1, axiom,
% 1.97/2.15    (![A:$i,B:$i,C:$i]:
% 1.97/2.15     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.97/2.15       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 1.97/2.15  thf('24', plain,
% 1.97/2.15      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.97/2.15         ((m1_subset_1 @ (k2_relset_1 @ X11 @ X12 @ X13) @ (k1_zfmisc_1 @ X12))
% 1.97/2.15          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 1.97/2.15      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 1.97/2.15  thf('25', plain,
% 1.97/2.15      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_D) @ (k1_zfmisc_1 @ sk_B))),
% 1.97/2.15      inference('sup-', [status(thm)], ['23', '24'])).
% 1.97/2.15  thf('26', plain,
% 1.97/2.15      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.97/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.15  thf(redefinition_k2_relset_1, axiom,
% 1.97/2.15    (![A:$i,B:$i,C:$i]:
% 1.97/2.15     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.97/2.15       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.97/2.15  thf('27', plain,
% 1.97/2.15      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.97/2.15         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 1.97/2.15          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.97/2.15      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.97/2.15  thf('28', plain,
% 1.97/2.15      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.97/2.15      inference('sup-', [status(thm)], ['26', '27'])).
% 1.97/2.15  thf('29', plain,
% 1.97/2.15      ((m1_subset_1 @ (k2_relat_1 @ sk_D) @ (k1_zfmisc_1 @ sk_B))),
% 1.97/2.15      inference('demod', [status(thm)], ['25', '28'])).
% 1.97/2.15  thf(t3_subset, axiom,
% 1.97/2.15    (![A:$i,B:$i]:
% 1.97/2.15     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.97/2.15  thf('30', plain,
% 1.97/2.15      (![X0 : $i, X1 : $i]:
% 1.97/2.15         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 1.97/2.15      inference('cnf', [status(esa)], [t3_subset])).
% 1.97/2.15  thf('31', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 1.97/2.15      inference('sup-', [status(thm)], ['29', '30'])).
% 1.97/2.15  thf('32', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 1.97/2.15      inference('demod', [status(thm)], ['11', '18', '19'])).
% 1.97/2.15  thf(t164_funct_1, axiom,
% 1.97/2.15    (![A:$i,B:$i]:
% 1.97/2.15     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.97/2.15       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 1.97/2.15         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 1.97/2.15  thf('33', plain,
% 1.97/2.15      (![X9 : $i, X10 : $i]:
% 1.97/2.15         (~ (r1_tarski @ X9 @ (k1_relat_1 @ X10))
% 1.97/2.15          | ~ (v2_funct_1 @ X10)
% 1.97/2.15          | ((k10_relat_1 @ X10 @ (k9_relat_1 @ X10 @ X9)) = (X9))
% 1.97/2.15          | ~ (v1_funct_1 @ X10)
% 1.97/2.15          | ~ (v1_relat_1 @ X10))),
% 1.97/2.15      inference('cnf', [status(esa)], [t164_funct_1])).
% 1.97/2.15  thf('34', plain,
% 1.97/2.15      (![X0 : $i]:
% 1.97/2.15         (~ (r1_tarski @ X0 @ sk_B)
% 1.97/2.15          | ~ (v1_relat_1 @ sk_E)
% 1.97/2.15          | ~ (v1_funct_1 @ sk_E)
% 1.97/2.15          | ((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ X0)) = (X0))
% 1.97/2.15          | ~ (v2_funct_1 @ sk_E))),
% 1.97/2.15      inference('sup-', [status(thm)], ['32', '33'])).
% 1.97/2.15  thf('35', plain,
% 1.97/2.15      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.97/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.15  thf(cc2_relat_1, axiom,
% 1.97/2.15    (![A:$i]:
% 1.97/2.15     ( ( v1_relat_1 @ A ) =>
% 1.97/2.15       ( ![B:$i]:
% 1.97/2.15         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.97/2.15  thf('36', plain,
% 1.97/2.15      (![X3 : $i, X4 : $i]:
% 1.97/2.15         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 1.97/2.15          | (v1_relat_1 @ X3)
% 1.97/2.15          | ~ (v1_relat_1 @ X4))),
% 1.97/2.15      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.97/2.15  thf('37', plain,
% 1.97/2.15      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)) | (v1_relat_1 @ sk_E))),
% 1.97/2.15      inference('sup-', [status(thm)], ['35', '36'])).
% 1.97/2.15  thf(fc6_relat_1, axiom,
% 1.97/2.15    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.97/2.15  thf('38', plain,
% 1.97/2.15      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 1.97/2.15      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.97/2.15  thf('39', plain, ((v1_relat_1 @ sk_E)),
% 1.97/2.15      inference('demod', [status(thm)], ['37', '38'])).
% 1.97/2.15  thf('40', plain, ((v1_funct_1 @ sk_E)),
% 1.97/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.15  thf('41', plain, ((v2_funct_1 @ sk_E)),
% 1.97/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.15  thf('42', plain,
% 1.97/2.15      (![X0 : $i]:
% 1.97/2.15         (~ (r1_tarski @ X0 @ sk_B)
% 1.97/2.15          | ((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ X0)) = (X0)))),
% 1.97/2.15      inference('demod', [status(thm)], ['34', '39', '40', '41'])).
% 1.97/2.15  thf('43', plain,
% 1.97/2.15      (((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)))
% 1.97/2.15         = (k2_relat_1 @ sk_D))),
% 1.97/2.15      inference('sup-', [status(thm)], ['31', '42'])).
% 1.97/2.15  thf(t160_relat_1, axiom,
% 1.97/2.15    (![A:$i]:
% 1.97/2.15     ( ( v1_relat_1 @ A ) =>
% 1.97/2.15       ( ![B:$i]:
% 1.97/2.15         ( ( v1_relat_1 @ B ) =>
% 1.97/2.15           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.97/2.15             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.97/2.15  thf('44', plain,
% 1.97/2.15      (![X7 : $i, X8 : $i]:
% 1.97/2.15         (~ (v1_relat_1 @ X7)
% 1.97/2.15          | ((k2_relat_1 @ (k5_relat_1 @ X8 @ X7))
% 1.97/2.15              = (k9_relat_1 @ X7 @ (k2_relat_1 @ X8)))
% 1.97/2.15          | ~ (v1_relat_1 @ X8))),
% 1.97/2.15      inference('cnf', [status(esa)], [t160_relat_1])).
% 1.97/2.15  thf('45', plain,
% 1.97/2.15      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.97/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.15  thf('46', plain,
% 1.97/2.15      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.97/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.15  thf(dt_k4_relset_1, axiom,
% 1.97/2.15    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.97/2.15     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.97/2.15         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.97/2.15       ( m1_subset_1 @
% 1.97/2.15         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.97/2.15         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 1.97/2.15  thf('47', plain,
% 1.97/2.15      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 1.97/2.15         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 1.97/2.15          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 1.97/2.15          | (m1_subset_1 @ (k4_relset_1 @ X15 @ X16 @ X18 @ X19 @ X14 @ X17) @ 
% 1.97/2.15             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X19))))),
% 1.97/2.15      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 1.97/2.15  thf('48', plain,
% 1.97/2.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.97/2.15         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 1.97/2.15           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.97/2.15          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 1.97/2.15      inference('sup-', [status(thm)], ['46', '47'])).
% 1.97/2.15  thf('49', plain,
% 1.97/2.15      ((m1_subset_1 @ 
% 1.97/2.15        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 1.97/2.15        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.97/2.15      inference('sup-', [status(thm)], ['45', '48'])).
% 1.97/2.15  thf('50', plain,
% 1.97/2.15      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.97/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.15  thf('51', plain,
% 1.97/2.15      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.97/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.15  thf(redefinition_k4_relset_1, axiom,
% 1.97/2.15    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.97/2.15     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.97/2.15         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.97/2.15       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.97/2.15  thf('52', plain,
% 1.97/2.15      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.97/2.15         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 1.97/2.15          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.97/2.15          | ((k4_relset_1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29)
% 1.97/2.15              = (k5_relat_1 @ X26 @ X29)))),
% 1.97/2.15      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 1.97/2.15  thf('53', plain,
% 1.97/2.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.97/2.15         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 1.97/2.15            = (k5_relat_1 @ sk_D @ X0))
% 1.97/2.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 1.97/2.15      inference('sup-', [status(thm)], ['51', '52'])).
% 1.97/2.15  thf('54', plain,
% 1.97/2.15      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.97/2.15         = (k5_relat_1 @ sk_D @ sk_E))),
% 1.97/2.15      inference('sup-', [status(thm)], ['50', '53'])).
% 1.97/2.15  thf('55', plain,
% 1.97/2.15      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 1.97/2.15        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.97/2.15      inference('demod', [status(thm)], ['49', '54'])).
% 1.97/2.15  thf('56', plain,
% 1.97/2.15      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.97/2.15         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 1.97/2.15          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.97/2.15      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.97/2.15  thf('57', plain,
% 1.97/2.15      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E))
% 1.97/2.15         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 1.97/2.15      inference('sup-', [status(thm)], ['55', '56'])).
% 1.97/2.15  thf('58', plain,
% 1.97/2.15      (((k2_relset_1 @ sk_A @ sk_C @ 
% 1.97/2.15         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) = (sk_C))),
% 1.97/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.15  thf('59', plain,
% 1.97/2.15      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.97/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.15  thf('60', plain,
% 1.97/2.15      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.97/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.15  thf(redefinition_k1_partfun1, axiom,
% 1.97/2.15    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.97/2.15     ( ( ( v1_funct_1 @ E ) & 
% 1.97/2.15         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.97/2.15         ( v1_funct_1 @ F ) & 
% 1.97/2.15         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.97/2.15       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.97/2.15  thf('61', plain,
% 1.97/2.15      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 1.97/2.15         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 1.97/2.15          | ~ (v1_funct_1 @ X47)
% 1.97/2.15          | ~ (v1_funct_1 @ X50)
% 1.97/2.15          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 1.97/2.15          | ((k1_partfun1 @ X48 @ X49 @ X51 @ X52 @ X47 @ X50)
% 1.97/2.15              = (k5_relat_1 @ X47 @ X50)))),
% 1.97/2.15      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.97/2.15  thf('62', plain,
% 1.97/2.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.97/2.15         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 1.97/2.15            = (k5_relat_1 @ sk_D @ X0))
% 1.97/2.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.97/2.15          | ~ (v1_funct_1 @ X0)
% 1.97/2.15          | ~ (v1_funct_1 @ sk_D))),
% 1.97/2.15      inference('sup-', [status(thm)], ['60', '61'])).
% 1.97/2.15  thf('63', plain, ((v1_funct_1 @ sk_D)),
% 1.97/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.15  thf('64', plain,
% 1.97/2.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.97/2.15         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 1.97/2.15            = (k5_relat_1 @ sk_D @ X0))
% 1.97/2.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.97/2.15          | ~ (v1_funct_1 @ X0))),
% 1.97/2.15      inference('demod', [status(thm)], ['62', '63'])).
% 1.97/2.15  thf('65', plain,
% 1.97/2.15      ((~ (v1_funct_1 @ sk_E)
% 1.97/2.15        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.97/2.15            = (k5_relat_1 @ sk_D @ sk_E)))),
% 1.97/2.15      inference('sup-', [status(thm)], ['59', '64'])).
% 1.97/2.15  thf('66', plain, ((v1_funct_1 @ sk_E)),
% 1.97/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.15  thf('67', plain,
% 1.97/2.15      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.97/2.15         = (k5_relat_1 @ sk_D @ sk_E))),
% 1.97/2.15      inference('demod', [status(thm)], ['65', '66'])).
% 1.97/2.15  thf('68', plain,
% 1.97/2.15      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 1.97/2.15      inference('demod', [status(thm)], ['58', '67'])).
% 1.97/2.15  thf('69', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 1.97/2.15      inference('sup+', [status(thm)], ['57', '68'])).
% 1.97/2.15  thf('70', plain,
% 1.97/2.15      ((((k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)) = (sk_C))
% 1.97/2.15        | ~ (v1_relat_1 @ sk_D)
% 1.97/2.15        | ~ (v1_relat_1 @ sk_E))),
% 1.97/2.15      inference('sup+', [status(thm)], ['44', '69'])).
% 1.97/2.15  thf('71', plain,
% 1.97/2.15      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.97/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.15  thf('72', plain,
% 1.97/2.15      (![X3 : $i, X4 : $i]:
% 1.97/2.15         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 1.97/2.15          | (v1_relat_1 @ X3)
% 1.97/2.15          | ~ (v1_relat_1 @ X4))),
% 1.97/2.15      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.97/2.15  thf('73', plain,
% 1.97/2.15      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 1.97/2.15      inference('sup-', [status(thm)], ['71', '72'])).
% 1.97/2.15  thf('74', plain,
% 1.97/2.15      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 1.97/2.15      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.97/2.15  thf('75', plain, ((v1_relat_1 @ sk_D)),
% 1.97/2.15      inference('demod', [status(thm)], ['73', '74'])).
% 1.97/2.15  thf('76', plain, ((v1_relat_1 @ sk_E)),
% 1.97/2.15      inference('demod', [status(thm)], ['37', '38'])).
% 1.97/2.15  thf('77', plain, (((k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)) = (sk_C))),
% 1.97/2.15      inference('demod', [status(thm)], ['70', '75', '76'])).
% 1.97/2.15  thf('78', plain, (((k10_relat_1 @ sk_E @ sk_C) = (k2_relat_1 @ sk_D))),
% 1.97/2.15      inference('demod', [status(thm)], ['43', '77'])).
% 1.97/2.15  thf('79', plain, (((sk_B) = (k2_relat_1 @ sk_D))),
% 1.97/2.15      inference('sup+', [status(thm)], ['22', '78'])).
% 1.97/2.15  thf('80', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) != (sk_B))),
% 1.97/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.15  thf('81', plain,
% 1.97/2.15      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.97/2.15      inference('sup-', [status(thm)], ['26', '27'])).
% 1.97/2.15  thf('82', plain, (((k2_relat_1 @ sk_D) != (sk_B))),
% 1.97/2.15      inference('demod', [status(thm)], ['80', '81'])).
% 1.97/2.15  thf('83', plain, ($false),
% 1.97/2.15      inference('simplify_reflect-', [status(thm)], ['79', '82'])).
% 1.97/2.15  
% 1.97/2.15  % SZS output end Refutation
% 1.97/2.15  
% 1.97/2.16  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
