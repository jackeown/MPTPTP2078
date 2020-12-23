%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GJroakr6XU

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:42 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 246 expanded)
%              Number of leaves         :   35 (  89 expanded)
%              Depth                    :   15
%              Number of atoms          :  723 (3405 expanded)
%              Number of equality atoms :   66 ( 269 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ( ( k9_relat_1 @ X6 @ ( k1_relat_1 @ X6 ) )
        = ( k2_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

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

thf('1',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ( X24
        = ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('4',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
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

thf('7',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('8',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('14',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','11','14'])).

thf('16',plain,(
    ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','15'])).

thf('17',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','11','14'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k1_relat_1 @ X8 )
       != ( k1_tarski @ X7 ) )
      | ( ( k2_relat_1 @ X8 )
        = ( k1_tarski @ ( k1_funct_1 @ X8 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference(eq_res,[status(thm)],['19'])).

thf('21',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('23',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('24',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21','24'])).

thf('26',plain,(
    ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ sk_C )
 != ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['16','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','11','14'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t39_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) )
          = ( k2_relset_1 @ B @ A @ C ) )
        & ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) )
          = ( k1_relset_1 @ B @ A @ C ) ) ) ) )).

thf('30',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k7_relset_1 @ X19 @ X20 @ X21 @ ( k8_relset_1 @ X19 @ X20 @ X21 @ X20 ) )
        = ( k2_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[t39_relset_1])).

thf('31',plain,
    ( ( k7_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ sk_C @ ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ sk_C @ sk_B ) )
    = ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('33',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( ( k7_relset_1 @ X16 @ X17 @ X15 @ X18 )
        = ( k9_relat_1 @ X15 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','11','14'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k9_relat_1 @ sk_C @ ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ sk_C @ sk_B ) )
    = ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['31','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t48_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( k8_relset_1 @ A @ B @ C @ B )
          = A ) ) ) )).

thf('39',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( X32 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ X30 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X32 ) ) )
      | ( ( k8_relset_1 @ X30 @ X32 @ X31 @ X32 )
        = X30 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_2])).

thf('40',plain,
    ( ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ sk_C @ sk_B )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','11','14'])).

thf('43',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ sk_C @ sk_B )
      = ( k1_relat_1 @ sk_C ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','43','44'])).

thf('46',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ sk_C @ sk_B )
    = ( k1_relat_1 @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    = ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['37','47'])).

thf('49',plain,(
    ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['26','48'])).

thf('50',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['22','23'])).

thf('52',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    $false ),
    inference(simplify,[status(thm)],['52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GJroakr6XU
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:19:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.59  % Solved by: fo/fo7.sh
% 0.39/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.59  % done 85 iterations in 0.134s
% 0.39/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.59  % SZS output start Refutation
% 0.39/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.59  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.39/0.59  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.39/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.59  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.39/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.59  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.39/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.39/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.59  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.39/0.59  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.39/0.59  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.39/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.59  thf(t146_relat_1, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( v1_relat_1 @ A ) =>
% 0.39/0.59       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.39/0.59  thf('0', plain,
% 0.39/0.59      (![X6 : $i]:
% 0.39/0.59         (((k9_relat_1 @ X6 @ (k1_relat_1 @ X6)) = (k2_relat_1 @ X6))
% 0.39/0.59          | ~ (v1_relat_1 @ X6))),
% 0.39/0.59      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.39/0.59  thf(t62_funct_2, conjecture,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.39/0.59         ( m1_subset_1 @
% 0.39/0.59           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.39/0.59       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.39/0.59         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.39/0.59           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.39/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.59    (~( ![A:$i,B:$i,C:$i]:
% 0.39/0.59        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.39/0.59            ( m1_subset_1 @
% 0.39/0.59              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.39/0.59          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.39/0.59            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.39/0.59              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.39/0.59    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.39/0.59  thf('1', plain,
% 0.39/0.59      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)
% 0.39/0.59         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('2', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(d1_funct_2, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.59       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.39/0.59           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.39/0.59             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.39/0.59         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.59           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.39/0.59             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.39/0.59  thf(zf_stmt_1, axiom,
% 0.39/0.59    (![C:$i,B:$i,A:$i]:
% 0.39/0.59     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.39/0.59       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.39/0.59  thf('3', plain,
% 0.39/0.59      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.39/0.59         (~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.39/0.59          | ((X24) = (k1_relset_1 @ X24 @ X25 @ X26))
% 0.39/0.59          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.59  thf('4', plain,
% 0.39/0.59      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.39/0.59        | ((k1_tarski @ sk_A)
% 0.39/0.59            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.59  thf(zf_stmt_2, axiom,
% 0.39/0.59    (![B:$i,A:$i]:
% 0.39/0.59     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.59       ( zip_tseitin_0 @ B @ A ) ))).
% 0.39/0.59  thf('5', plain,
% 0.39/0.59      (![X22 : $i, X23 : $i]:
% 0.39/0.59         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.39/0.59  thf('6', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_C @ 
% 0.39/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.39/0.59  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.39/0.59  thf(zf_stmt_5, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.59       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.39/0.59         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.39/0.59           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.39/0.59             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.39/0.59  thf('7', plain,
% 0.39/0.59      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.39/0.59         (~ (zip_tseitin_0 @ X27 @ X28)
% 0.39/0.59          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 0.39/0.59          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.39/0.59  thf('8', plain,
% 0.39/0.59      (((zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.39/0.59        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.59  thf('9', plain,
% 0.39/0.59      ((((sk_B) = (k1_xboole_0))
% 0.39/0.59        | (zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['5', '8'])).
% 0.39/0.59  thf('10', plain, (((sk_B) != (k1_xboole_0))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('11', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))),
% 0.39/0.59      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.39/0.59  thf('12', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_C @ 
% 0.39/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(redefinition_k1_relset_1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.59       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.39/0.59  thf('13', plain,
% 0.39/0.59      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.39/0.59         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 0.39/0.59          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.39/0.59      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.39/0.59  thf('14', plain,
% 0.39/0.59      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.39/0.59      inference('sup-', [status(thm)], ['12', '13'])).
% 0.39/0.59  thf('15', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.39/0.59      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.39/0.59  thf('16', plain,
% 0.39/0.59      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ sk_C)
% 0.39/0.59         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.39/0.59      inference('demod', [status(thm)], ['1', '15'])).
% 0.39/0.59  thf('17', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.39/0.59      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.39/0.59  thf(t14_funct_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.59       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.39/0.59         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.39/0.59  thf('18', plain,
% 0.39/0.59      (![X7 : $i, X8 : $i]:
% 0.39/0.59         (((k1_relat_1 @ X8) != (k1_tarski @ X7))
% 0.39/0.59          | ((k2_relat_1 @ X8) = (k1_tarski @ (k1_funct_1 @ X8 @ X7)))
% 0.39/0.59          | ~ (v1_funct_1 @ X8)
% 0.39/0.59          | ~ (v1_relat_1 @ X8))),
% 0.39/0.59      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.39/0.59  thf('19', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_C))
% 0.39/0.59          | ~ (v1_relat_1 @ X0)
% 0.39/0.59          | ~ (v1_funct_1 @ X0)
% 0.39/0.59          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['17', '18'])).
% 0.39/0.59  thf('20', plain,
% 0.39/0.59      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.39/0.59        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.59        | ~ (v1_relat_1 @ sk_C))),
% 0.39/0.59      inference('eq_res', [status(thm)], ['19'])).
% 0.39/0.59  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('22', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_C @ 
% 0.39/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(cc1_relset_1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.59       ( v1_relat_1 @ C ) ))).
% 0.39/0.59  thf('23', plain,
% 0.39/0.59      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.39/0.59         ((v1_relat_1 @ X9)
% 0.39/0.59          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.39/0.59      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.39/0.59  thf('24', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.59      inference('sup-', [status(thm)], ['22', '23'])).
% 0.39/0.59  thf('25', plain,
% 0.39/0.59      (((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.39/0.59      inference('demod', [status(thm)], ['20', '21', '24'])).
% 0.39/0.59  thf('26', plain,
% 0.39/0.59      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ sk_C)
% 0.39/0.59         != (k2_relat_1 @ sk_C))),
% 0.39/0.59      inference('demod', [status(thm)], ['16', '25'])).
% 0.39/0.59  thf('27', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_C @ 
% 0.39/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('28', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.39/0.59      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.39/0.59  thf('29', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_C @ 
% 0.39/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))),
% 0.39/0.59      inference('demod', [status(thm)], ['27', '28'])).
% 0.39/0.59  thf(t39_relset_1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.39/0.59       ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.39/0.59           ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.39/0.59         ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.39/0.59           ( k1_relset_1 @ B @ A @ C ) ) ) ))).
% 0.39/0.59  thf('30', plain,
% 0.39/0.59      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.39/0.59         (((k7_relset_1 @ X19 @ X20 @ X21 @ 
% 0.39/0.59            (k8_relset_1 @ X19 @ X20 @ X21 @ X20))
% 0.39/0.59            = (k2_relset_1 @ X19 @ X20 @ X21))
% 0.39/0.59          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.39/0.59      inference('cnf', [status(esa)], [t39_relset_1])).
% 0.39/0.59  thf('31', plain,
% 0.39/0.59      (((k7_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ sk_C @ 
% 0.39/0.59         (k8_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ sk_C @ sk_B))
% 0.39/0.59         = (k2_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ sk_C))),
% 0.39/0.59      inference('sup-', [status(thm)], ['29', '30'])).
% 0.39/0.59  thf('32', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_C @ 
% 0.39/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(redefinition_k7_relset_1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.59       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.39/0.59  thf('33', plain,
% 0.39/0.59      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.39/0.59         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.39/0.59          | ((k7_relset_1 @ X16 @ X17 @ X15 @ X18) = (k9_relat_1 @ X15 @ X18)))),
% 0.39/0.59      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.39/0.59  thf('34', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C @ X0)
% 0.39/0.59           = (k9_relat_1 @ sk_C @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['32', '33'])).
% 0.39/0.59  thf('35', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.39/0.59      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.39/0.59  thf('36', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((k7_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ sk_C @ X0)
% 0.39/0.59           = (k9_relat_1 @ sk_C @ X0))),
% 0.39/0.59      inference('demod', [status(thm)], ['34', '35'])).
% 0.39/0.59  thf('37', plain,
% 0.39/0.59      (((k9_relat_1 @ sk_C @ 
% 0.39/0.59         (k8_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ sk_C @ sk_B))
% 0.39/0.59         = (k2_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ sk_C))),
% 0.39/0.59      inference('demod', [status(thm)], ['31', '36'])).
% 0.39/0.59  thf('38', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_C @ 
% 0.39/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))),
% 0.39/0.59      inference('demod', [status(thm)], ['27', '28'])).
% 0.39/0.59  thf(t48_funct_2, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.59       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.59         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( A ) ) ) ))).
% 0.39/0.59  thf('39', plain,
% 0.39/0.59      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.39/0.59         (((X32) = (k1_xboole_0))
% 0.39/0.59          | ~ (v1_funct_1 @ X31)
% 0.39/0.59          | ~ (v1_funct_2 @ X31 @ X30 @ X32)
% 0.39/0.59          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X32)))
% 0.39/0.59          | ((k8_relset_1 @ X30 @ X32 @ X31 @ X32) = (X30)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t48_funct_2])).
% 0.39/0.59  thf('40', plain,
% 0.39/0.59      ((((k8_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ sk_C @ sk_B)
% 0.39/0.59          = (k1_relat_1 @ sk_C))
% 0.39/0.59        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ sk_B)
% 0.39/0.59        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.59        | ((sk_B) = (k1_xboole_0)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['38', '39'])).
% 0.39/0.59  thf('41', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('42', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.39/0.59      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.39/0.59  thf('43', plain, ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ sk_B)),
% 0.39/0.59      inference('demod', [status(thm)], ['41', '42'])).
% 0.39/0.59  thf('44', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('45', plain,
% 0.39/0.59      ((((k8_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ sk_C @ sk_B)
% 0.39/0.59          = (k1_relat_1 @ sk_C))
% 0.39/0.59        | ((sk_B) = (k1_xboole_0)))),
% 0.39/0.59      inference('demod', [status(thm)], ['40', '43', '44'])).
% 0.39/0.59  thf('46', plain, (((sk_B) != (k1_xboole_0))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('47', plain,
% 0.39/0.59      (((k8_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ sk_C @ sk_B)
% 0.39/0.59         = (k1_relat_1 @ sk_C))),
% 0.39/0.59      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 0.39/0.59  thf('48', plain,
% 0.39/0.59      (((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.39/0.59         = (k2_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ sk_C))),
% 0.39/0.59      inference('demod', [status(thm)], ['37', '47'])).
% 0.39/0.59  thf('49', plain,
% 0.39/0.59      (((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C))),
% 0.39/0.59      inference('demod', [status(thm)], ['26', '48'])).
% 0.39/0.59  thf('50', plain,
% 0.39/0.59      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)) | ~ (v1_relat_1 @ sk_C))),
% 0.39/0.59      inference('sup-', [status(thm)], ['0', '49'])).
% 0.39/0.59  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.59      inference('sup-', [status(thm)], ['22', '23'])).
% 0.39/0.59  thf('52', plain, (((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))),
% 0.39/0.59      inference('demod', [status(thm)], ['50', '51'])).
% 0.39/0.59  thf('53', plain, ($false), inference('simplify', [status(thm)], ['52'])).
% 0.39/0.59  
% 0.39/0.59  % SZS output end Refutation
% 0.39/0.59  
% 0.39/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
