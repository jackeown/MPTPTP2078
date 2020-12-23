%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ml7PFJsWJQ

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:50 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 439 expanded)
%              Number of leaves         :   46 ( 152 expanded)
%              Depth                    :   21
%              Number of atoms          :  977 (6713 expanded)
%              Number of equality atoms :   51 ( 403 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(t32_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ D )
          & ( r2_hidden @ C @ A ) )
       => ( ( B = k1_xboole_0 )
          | ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) )
            = C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( v2_funct_1 @ D )
            & ( r2_hidden @ C @ A ) )
         => ( ( B = k1_xboole_0 )
            | ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) )
              = C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t32_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf('2',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X40 @ X41 )
      | ( X42 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X43 @ X40 ) @ ( k2_relset_1 @ X41 @ X42 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D_2 ) )
      | ~ ( v1_funct_2 @ sk_D_2 @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('5',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k7_relset_1 @ X23 @ X24 @ X25 @ X23 )
        = ( k2_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('6',plain,
    ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_A )
    = ( k2_relset_1 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('8',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( ( k7_relset_1 @ X20 @ X21 @ X19 @ X22 )
        = ( k9_relat_1 @ X19 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ X0 )
      = ( k9_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k9_relat_1 @ sk_D_2 @ sk_A )
    = ( k2_relset_1 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k9_relat_1 @ sk_D_2 @ sk_A ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','10','11','12'])).

thf('14',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k9_relat_1 @ sk_D_2 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

thf('16',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C ) @ ( k9_relat_1 @ sk_D_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','15'])).

thf(d12_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_funct_1 @ A )
        & ( v1_relat_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) )
                  & ( r2_hidden @ E @ B )
                  & ( D
                    = ( k1_funct_1 @ A @ E ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( D
          = ( k1_funct_1 @ A @ E ) )
        & ( r2_hidden @ E @ B )
        & ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i,X13: $i,X14: $i] :
      ( ( X13
       != ( k9_relat_1 @ X11 @ X10 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X14 @ X10 @ X11 ) @ X14 @ X10 @ X11 )
      | ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('18',plain,(
    ! [X10: $i,X11: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( r2_hidden @ X14 @ ( k9_relat_1 @ X11 @ X10 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X14 @ X10 @ X11 ) @ X14 @ X10 @ X11 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( zip_tseitin_0 @ ( sk_E_1 @ ( k1_funct_1 @ sk_D_2 @ sk_C ) @ sk_A @ sk_D_2 ) @ ( k1_funct_1 @ sk_D_2 @ sk_C ) @ sk_A @ sk_D_2 )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('25',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ ( k1_funct_1 @ sk_D_2 @ sk_C ) @ sk_A @ sk_D_2 ) @ ( k1_funct_1 @ sk_D_2 @ sk_C ) @ sk_A @ sk_D_2 ),
    inference(demod,[status(thm)],['19','20','25'])).

thf('27',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X5 @ X7 )
      | ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('28',plain,(
    r2_hidden @ ( sk_E_1 @ ( k1_funct_1 @ sk_D_2 @ sk_C ) @ sk_A @ sk_D_2 ) @ sk_A ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ ( k1_funct_1 @ sk_D_2 @ sk_C ) @ sk_A @ sk_D_2 ) @ ( k1_funct_1 @ sk_D_2 @ sk_C ) @ sk_A @ sk_D_2 ),
    inference(demod,[status(thm)],['19','20','25'])).

thf('30',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X5 @ ( k1_relat_1 @ X4 ) )
      | ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('31',plain,(
    r2_hidden @ ( sk_E_1 @ ( k1_funct_1 @ sk_D_2 @ sk_C ) @ sk_A @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t56_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( v2_funct_1 @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) )
       => ( ( A
            = ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) )
          & ( A
            = ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ) )).

thf('32',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ~ ( r2_hidden @ X18 @ ( k1_relat_1 @ X17 ) )
      | ( X18
        = ( k1_funct_1 @ ( k2_funct_1 @ X17 ) @ ( k1_funct_1 @ X17 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t56_funct_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ( ( sk_E_1 @ ( k1_funct_1 @ sk_D_2 @ sk_C ) @ sk_A @ sk_D_2 )
      = ( k1_funct_1 @ ( k2_funct_1 @ sk_D_2 ) @ ( k1_funct_1 @ sk_D_2 @ ( sk_E_1 @ ( k1_funct_1 @ sk_D_2 @ sk_C ) @ sk_A @ sk_D_2 ) ) ) )
    | ~ ( v2_funct_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['23','24'])).

thf('35',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v2_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( sk_E_1 @ ( k1_funct_1 @ sk_D_2 @ sk_C ) @ sk_A @ sk_D_2 )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_D_2 ) @ ( k1_funct_1 @ sk_D_2 @ ( sk_E_1 @ ( k1_funct_1 @ sk_D_2 @ sk_C ) @ sk_A @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['33','34','35','36'])).

thf('38',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ ( k1_funct_1 @ sk_D_2 @ sk_C ) @ sk_A @ sk_D_2 ) @ ( k1_funct_1 @ sk_D_2 @ sk_C ) @ sk_A @ sk_D_2 ),
    inference(demod,[status(thm)],['19','20','25'])).

thf('39',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X6
        = ( k1_funct_1 @ X4 @ X5 ) )
      | ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('40',plain,
    ( ( k1_funct_1 @ sk_D_2 @ sk_C )
    = ( k1_funct_1 @ sk_D_2 @ ( sk_E_1 @ ( k1_funct_1 @ sk_D_2 @ sk_C ) @ sk_A @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_E_1 @ ( k1_funct_1 @ sk_D_2 @ sk_C ) @ sk_A @ sk_D_2 )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_D_2 ) @ ( k1_funct_1 @ sk_D_2 @ sk_C ) ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,(
    r2_hidden @ ( k1_funct_1 @ ( k2_funct_1 @ sk_D_2 ) @ ( k1_funct_1 @ sk_D_2 @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['28','41'])).

thf('43',plain,
    ( ( k1_funct_1 @ sk_D_2 @ sk_C )
    = ( k1_funct_1 @ sk_D_2 @ ( sk_E_1 @ ( k1_funct_1 @ sk_D_2 @ sk_C ) @ sk_A @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('44',plain,
    ( ( sk_E_1 @ ( k1_funct_1 @ sk_D_2 @ sk_C ) @ sk_A @ sk_D_2 )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_D_2 ) @ ( k1_funct_1 @ sk_D_2 @ sk_C ) ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('45',plain,
    ( ( k1_funct_1 @ sk_D_2 @ sk_C )
    = ( k1_funct_1 @ sk_D_2 @ ( k1_funct_1 @ ( k2_funct_1 @ sk_D_2 ) @ ( k1_funct_1 @ sk_D_2 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(t25_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_2 @ C @ A @ B )
        & ( v1_funct_1 @ C ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( v2_funct_1 @ C )
        <=> ! [D: $i,E: $i] :
              ( ( ( ( k1_funct_1 @ C @ D )
                  = ( k1_funct_1 @ C @ E ) )
                & ( r2_hidden @ E @ A )
                & ( r2_hidden @ D @ A ) )
             => ( D = E ) ) ) ) ) )).

thf(zf_stmt_4,axiom,(
    ! [E: $i,D: $i,C: $i,A: $i] :
      ( ( zip_tseitin_2 @ E @ D @ C @ A )
    <=> ( ( r2_hidden @ D @ A )
        & ( r2_hidden @ E @ A )
        & ( ( k1_funct_1 @ C @ D )
          = ( k1_funct_1 @ C @ E ) ) ) ) )).

thf('46',plain,(
    ! [X28: $i,X30: $i,X31: $i,X32: $i] :
      ( ( zip_tseitin_2 @ X30 @ X28 @ X31 @ X32 )
      | ( ( k1_funct_1 @ X31 @ X28 )
       != ( k1_funct_1 @ X31 @ X30 ) )
      | ~ ( r2_hidden @ X30 @ X32 )
      | ~ ( r2_hidden @ X28 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ sk_D_2 @ X0 )
       != ( k1_funct_1 @ sk_D_2 @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ ( k2_funct_1 @ sk_D_2 ) @ ( k1_funct_1 @ sk_D_2 @ sk_C ) ) @ X1 )
      | ( zip_tseitin_2 @ ( k1_funct_1 @ ( k2_funct_1 @ sk_D_2 ) @ ( k1_funct_1 @ sk_D_2 @ sk_C ) ) @ X0 @ sk_D_2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ ( k1_funct_1 @ ( k2_funct_1 @ sk_D_2 ) @ ( k1_funct_1 @ sk_D_2 @ sk_C ) ) @ X0 @ sk_D_2 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( k1_funct_1 @ sk_D_2 @ X0 )
       != ( k1_funct_1 @ sk_D_2 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_A )
    | ( zip_tseitin_2 @ ( k1_funct_1 @ ( k2_funct_1 @ sk_D_2 ) @ ( k1_funct_1 @ sk_D_2 @ sk_C ) ) @ sk_C @ sk_D_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['48'])).

thf('50',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    zip_tseitin_2 @ ( k1_funct_1 @ ( k2_funct_1 @ sk_D_2 ) @ ( k1_funct_1 @ sk_D_2 @ sk_C ) ) @ sk_C @ sk_D_2 @ sk_A ),
    inference(demod,[status(thm)],['49','50'])).

thf(zf_stmt_5,axiom,(
    ! [C: $i,A: $i] :
      ( ( zip_tseitin_3 @ C @ A )
     => ( ( v2_funct_1 @ C )
      <=> ! [D: $i,E: $i] :
            ( ( zip_tseitin_2 @ E @ D @ C @ A )
           => ( D = E ) ) ) ) )).

thf('52',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( v2_funct_1 @ X34 )
      | ( X36 = X35 )
      | ~ ( zip_tseitin_2 @ X35 @ X36 @ X34 @ X33 )
      | ~ ( zip_tseitin_3 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('53',plain,
    ( ~ ( zip_tseitin_3 @ sk_D_2 @ sk_A )
    | ( sk_C
      = ( k1_funct_1 @ ( k2_funct_1 @ sk_D_2 ) @ ( k1_funct_1 @ sk_D_2 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(zf_stmt_6,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf('54',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_1 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('55',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_7,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zf_stmt_8,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(zf_stmt_9,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_10,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( zip_tseitin_1 @ B @ A )
       => ( zip_tseitin_3 @ C @ A ) ) ) )).

thf('56',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_1 @ X37 @ X38 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ X38 @ X37 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ( zip_tseitin_3 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('57',plain,
    ( ( zip_tseitin_3 @ sk_D_2 @ sk_A )
    | ~ ( v1_funct_2 @ sk_D_2 @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( zip_tseitin_3 @ sk_D_2 @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_3 @ sk_D_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['54','60'])).

thf('62',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    zip_tseitin_3 @ sk_D_2 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['61','62'])).

thf('64',plain,(
    v2_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( sk_C
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_D_2 ) @ ( k1_funct_1 @ sk_D_2 @ sk_C ) ) ),
    inference(demod,[status(thm)],['53','63','64'])).

thf('66',plain,(
    ( k1_funct_1 @ ( k2_funct_1 @ sk_D_2 ) @ ( k1_funct_1 @ sk_D_2 @ sk_C ) )
 != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ml7PFJsWJQ
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:53:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 103 iterations in 0.073s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.52  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.52  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.52  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.52  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $i > $o).
% 0.20/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.52  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.20/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.52  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.20/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.20/0.52  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.52  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.52  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.20/0.52  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.52  thf(t32_funct_2, conjecture,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.52     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.52         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.52       ( ( ( v2_funct_1 @ D ) & ( r2_hidden @ C @ A ) ) =>
% 0.20/0.52         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.52           ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) ) =
% 0.20/0.52             ( C ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.52        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.52            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.52          ( ( ( v2_funct_1 @ D ) & ( r2_hidden @ C @ A ) ) =>
% 0.20/0.52            ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.52              ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) ) =
% 0.20/0.52                ( C ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t32_funct_2])).
% 0.20/0.52  thf('0', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t6_funct_2, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.52     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.52         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.52       ( ( r2_hidden @ C @ A ) =>
% 0.20/0.52         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.52           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X40 @ X41)
% 0.20/0.52          | ((X42) = (k1_xboole_0))
% 0.20/0.52          | ~ (v1_funct_1 @ X43)
% 0.20/0.52          | ~ (v1_funct_2 @ X43 @ X41 @ X42)
% 0.20/0.52          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.20/0.52          | (r2_hidden @ (k1_funct_1 @ X43 @ X40) @ 
% 0.20/0.52             (k2_relset_1 @ X41 @ X42 @ X43)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ 
% 0.20/0.52           (k2_relset_1 @ sk_A @ sk_B @ sk_D_2))
% 0.20/0.52          | ~ (v1_funct_2 @ sk_D_2 @ sk_A @ sk_B)
% 0.20/0.52          | ~ (v1_funct_1 @ sk_D_2)
% 0.20/0.52          | ((sk_B) = (k1_xboole_0))
% 0.20/0.52          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t38_relset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.20/0.52         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.52         (((k7_relset_1 @ X23 @ X24 @ X25 @ X23)
% 0.20/0.52            = (k2_relset_1 @ X23 @ X24 @ X25))
% 0.20/0.52          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.20/0.52      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (((k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_A)
% 0.20/0.52         = (k2_relset_1 @ sk_A @ sk_B @ sk_D_2))),
% 0.20/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(redefinition_k7_relset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.20/0.52          | ((k7_relset_1 @ X20 @ X21 @ X19 @ X22) = (k9_relat_1 @ X19 @ X22)))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ X0)
% 0.20/0.52           = (k9_relat_1 @ sk_D_2 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (((k9_relat_1 @ sk_D_2 @ sk_A) = (k2_relset_1 @ sk_A @ sk_B @ sk_D_2))),
% 0.20/0.52      inference('demod', [status(thm)], ['6', '9'])).
% 0.20/0.52  thf('11', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('12', plain, ((v1_funct_1 @ sk_D_2)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ 
% 0.20/0.52           (k9_relat_1 @ sk_D_2 @ sk_A))
% 0.20/0.52          | ((sk_B) = (k1_xboole_0))
% 0.20/0.52          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['3', '10', '11', '12'])).
% 0.20/0.52  thf('14', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ 
% 0.20/0.52           (k9_relat_1 @ sk_D_2 @ sk_A))
% 0.20/0.52          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C) @ (k9_relat_1 @ sk_D_2 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['0', '15'])).
% 0.20/0.52  thf(d12_funct_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.20/0.52       ( ![B:$i,C:$i]:
% 0.20/0.52         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.20/0.52           ( ![D:$i]:
% 0.20/0.52             ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.52               ( ?[E:$i]:
% 0.20/0.52                 ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.52                   ( r2_hidden @ E @ B ) & ( ( D ) = ( k1_funct_1 @ A @ E ) ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.52  thf(zf_stmt_2, axiom,
% 0.20/0.52    (![E:$i,D:$i,B:$i,A:$i]:
% 0.20/0.52     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.20/0.52       ( ( ( D ) = ( k1_funct_1 @ A @ E ) ) & ( r2_hidden @ E @ B ) & 
% 0.20/0.52         ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_3, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.52       ( ![B:$i,C:$i]:
% 0.20/0.52         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.20/0.52           ( ![D:$i]:
% 0.20/0.52             ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.52               ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ))).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X10 : $i, X11 : $i, X13 : $i, X14 : $i]:
% 0.20/0.52         (((X13) != (k9_relat_1 @ X11 @ X10))
% 0.20/0.52          | (zip_tseitin_0 @ (sk_E_1 @ X14 @ X10 @ X11) @ X14 @ X10 @ X11)
% 0.20/0.52          | ~ (r2_hidden @ X14 @ X13)
% 0.20/0.52          | ~ (v1_funct_1 @ X11)
% 0.20/0.52          | ~ (v1_relat_1 @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X10 : $i, X11 : $i, X14 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ X11)
% 0.20/0.52          | ~ (v1_funct_1 @ X11)
% 0.20/0.52          | ~ (r2_hidden @ X14 @ (k9_relat_1 @ X11 @ X10))
% 0.20/0.52          | (zip_tseitin_0 @ (sk_E_1 @ X14 @ X10 @ X11) @ X14 @ X10 @ X11))),
% 0.20/0.52      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (((zip_tseitin_0 @ 
% 0.20/0.52         (sk_E_1 @ (k1_funct_1 @ sk_D_2 @ sk_C) @ sk_A @ sk_D_2) @ 
% 0.20/0.52         (k1_funct_1 @ sk_D_2 @ sk_C) @ sk_A @ sk_D_2)
% 0.20/0.52        | ~ (v1_funct_1 @ sk_D_2)
% 0.20/0.52        | ~ (v1_relat_1 @ sk_D_2))),
% 0.20/0.52      inference('sup-', [status(thm)], ['16', '18'])).
% 0.20/0.52  thf('20', plain, ((v1_funct_1 @ sk_D_2)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(cc2_relat_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.20/0.52          | (v1_relat_1 @ X0)
% 0.20/0.52          | ~ (v1_relat_1 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_2))),
% 0.20/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.52  thf(fc6_relat_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.52  thf('25', plain, ((v1_relat_1 @ sk_D_2)),
% 0.20/0.52      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      ((zip_tseitin_0 @ 
% 0.20/0.52        (sk_E_1 @ (k1_funct_1 @ sk_D_2 @ sk_C) @ sk_A @ sk_D_2) @ 
% 0.20/0.52        (k1_funct_1 @ sk_D_2 @ sk_C) @ sk_A @ sk_D_2)),
% 0.20/0.52      inference('demod', [status(thm)], ['19', '20', '25'])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.52         ((r2_hidden @ X5 @ X7) | ~ (zip_tseitin_0 @ X5 @ X6 @ X7 @ X4))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      ((r2_hidden @ (sk_E_1 @ (k1_funct_1 @ sk_D_2 @ sk_C) @ sk_A @ sk_D_2) @ 
% 0.20/0.52        sk_A)),
% 0.20/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      ((zip_tseitin_0 @ 
% 0.20/0.52        (sk_E_1 @ (k1_funct_1 @ sk_D_2 @ sk_C) @ sk_A @ sk_D_2) @ 
% 0.20/0.52        (k1_funct_1 @ sk_D_2 @ sk_C) @ sk_A @ sk_D_2)),
% 0.20/0.52      inference('demod', [status(thm)], ['19', '20', '25'])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.52         ((r2_hidden @ X5 @ (k1_relat_1 @ X4))
% 0.20/0.52          | ~ (zip_tseitin_0 @ X5 @ X6 @ X7 @ X4))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      ((r2_hidden @ (sk_E_1 @ (k1_funct_1 @ sk_D_2 @ sk_C) @ sk_A @ sk_D_2) @ 
% 0.20/0.52        (k1_relat_1 @ sk_D_2))),
% 0.20/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.52  thf(t56_funct_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.52       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) ) =>
% 0.20/0.52         ( ( ( A ) =
% 0.20/0.52             ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) ) & 
% 0.20/0.52           ( ( A ) =
% 0.20/0.52             ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ))).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      (![X17 : $i, X18 : $i]:
% 0.20/0.52         (~ (v2_funct_1 @ X17)
% 0.20/0.52          | ~ (r2_hidden @ X18 @ (k1_relat_1 @ X17))
% 0.20/0.52          | ((X18)
% 0.20/0.52              = (k1_funct_1 @ (k2_funct_1 @ X17) @ (k1_funct_1 @ X17 @ X18)))
% 0.20/0.52          | ~ (v1_funct_1 @ X17)
% 0.20/0.52          | ~ (v1_relat_1 @ X17))),
% 0.20/0.52      inference('cnf', [status(esa)], [t56_funct_1])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      ((~ (v1_relat_1 @ sk_D_2)
% 0.20/0.52        | ~ (v1_funct_1 @ sk_D_2)
% 0.20/0.52        | ((sk_E_1 @ (k1_funct_1 @ sk_D_2 @ sk_C) @ sk_A @ sk_D_2)
% 0.20/0.52            = (k1_funct_1 @ (k2_funct_1 @ sk_D_2) @ 
% 0.20/0.52               (k1_funct_1 @ sk_D_2 @ 
% 0.20/0.52                (sk_E_1 @ (k1_funct_1 @ sk_D_2 @ sk_C) @ sk_A @ sk_D_2))))
% 0.20/0.52        | ~ (v2_funct_1 @ sk_D_2))),
% 0.20/0.52      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.52  thf('34', plain, ((v1_relat_1 @ sk_D_2)),
% 0.20/0.52      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.52  thf('35', plain, ((v1_funct_1 @ sk_D_2)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('36', plain, ((v2_funct_1 @ sk_D_2)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (((sk_E_1 @ (k1_funct_1 @ sk_D_2 @ sk_C) @ sk_A @ sk_D_2)
% 0.20/0.52         = (k1_funct_1 @ (k2_funct_1 @ sk_D_2) @ 
% 0.20/0.52            (k1_funct_1 @ sk_D_2 @ 
% 0.20/0.52             (sk_E_1 @ (k1_funct_1 @ sk_D_2 @ sk_C) @ sk_A @ sk_D_2))))),
% 0.20/0.52      inference('demod', [status(thm)], ['33', '34', '35', '36'])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      ((zip_tseitin_0 @ 
% 0.20/0.52        (sk_E_1 @ (k1_funct_1 @ sk_D_2 @ sk_C) @ sk_A @ sk_D_2) @ 
% 0.20/0.52        (k1_funct_1 @ sk_D_2 @ sk_C) @ sk_A @ sk_D_2)),
% 0.20/0.52      inference('demod', [status(thm)], ['19', '20', '25'])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.52         (((X6) = (k1_funct_1 @ X4 @ X5))
% 0.20/0.52          | ~ (zip_tseitin_0 @ X5 @ X6 @ X7 @ X4))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      (((k1_funct_1 @ sk_D_2 @ sk_C)
% 0.20/0.52         = (k1_funct_1 @ sk_D_2 @ 
% 0.20/0.52            (sk_E_1 @ (k1_funct_1 @ sk_D_2 @ sk_C) @ sk_A @ sk_D_2)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      (((sk_E_1 @ (k1_funct_1 @ sk_D_2 @ sk_C) @ sk_A @ sk_D_2)
% 0.20/0.52         = (k1_funct_1 @ (k2_funct_1 @ sk_D_2) @ (k1_funct_1 @ sk_D_2 @ sk_C)))),
% 0.20/0.52      inference('demod', [status(thm)], ['37', '40'])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      ((r2_hidden @ 
% 0.20/0.52        (k1_funct_1 @ (k2_funct_1 @ sk_D_2) @ (k1_funct_1 @ sk_D_2 @ sk_C)) @ 
% 0.20/0.52        sk_A)),
% 0.20/0.52      inference('demod', [status(thm)], ['28', '41'])).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      (((k1_funct_1 @ sk_D_2 @ sk_C)
% 0.20/0.52         = (k1_funct_1 @ sk_D_2 @ 
% 0.20/0.52            (sk_E_1 @ (k1_funct_1 @ sk_D_2 @ sk_C) @ sk_A @ sk_D_2)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.52  thf('44', plain,
% 0.20/0.52      (((sk_E_1 @ (k1_funct_1 @ sk_D_2 @ sk_C) @ sk_A @ sk_D_2)
% 0.20/0.52         = (k1_funct_1 @ (k2_funct_1 @ sk_D_2) @ (k1_funct_1 @ sk_D_2 @ sk_C)))),
% 0.20/0.52      inference('demod', [status(thm)], ['37', '40'])).
% 0.20/0.52  thf('45', plain,
% 0.20/0.52      (((k1_funct_1 @ sk_D_2 @ sk_C)
% 0.20/0.52         = (k1_funct_1 @ sk_D_2 @ 
% 0.20/0.52            (k1_funct_1 @ (k2_funct_1 @ sk_D_2) @ (k1_funct_1 @ sk_D_2 @ sk_C))))),
% 0.20/0.52      inference('demod', [status(thm)], ['43', '44'])).
% 0.20/0.52  thf(t25_funct_2, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.52         ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.52       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.52         ( ( v2_funct_1 @ C ) <=>
% 0.20/0.52           ( ![D:$i,E:$i]:
% 0.20/0.52             ( ( ( ( k1_funct_1 @ C @ D ) = ( k1_funct_1 @ C @ E ) ) & 
% 0.20/0.52                 ( r2_hidden @ E @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.20/0.52               ( ( D ) = ( E ) ) ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_4, axiom,
% 0.20/0.52    (![E:$i,D:$i,C:$i,A:$i]:
% 0.20/0.52     ( ( zip_tseitin_2 @ E @ D @ C @ A ) <=>
% 0.20/0.52       ( ( r2_hidden @ D @ A ) & ( r2_hidden @ E @ A ) & 
% 0.20/0.52         ( ( k1_funct_1 @ C @ D ) = ( k1_funct_1 @ C @ E ) ) ) ))).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      (![X28 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.52         ((zip_tseitin_2 @ X30 @ X28 @ X31 @ X32)
% 0.20/0.52          | ((k1_funct_1 @ X31 @ X28) != (k1_funct_1 @ X31 @ X30))
% 0.20/0.52          | ~ (r2_hidden @ X30 @ X32)
% 0.20/0.52          | ~ (r2_hidden @ X28 @ X32))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.20/0.52  thf('47', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((k1_funct_1 @ sk_D_2 @ X0) != (k1_funct_1 @ sk_D_2 @ sk_C))
% 0.20/0.52          | ~ (r2_hidden @ X0 @ X1)
% 0.20/0.52          | ~ (r2_hidden @ 
% 0.20/0.52               (k1_funct_1 @ (k2_funct_1 @ sk_D_2) @ 
% 0.20/0.52                (k1_funct_1 @ sk_D_2 @ sk_C)) @ 
% 0.20/0.52               X1)
% 0.20/0.52          | (zip_tseitin_2 @ 
% 0.20/0.52             (k1_funct_1 @ (k2_funct_1 @ sk_D_2) @ (k1_funct_1 @ sk_D_2 @ sk_C)) @ 
% 0.20/0.52             X0 @ sk_D_2 @ X1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((zip_tseitin_2 @ 
% 0.20/0.52           (k1_funct_1 @ (k2_funct_1 @ sk_D_2) @ (k1_funct_1 @ sk_D_2 @ sk_C)) @ 
% 0.20/0.52           X0 @ sk_D_2 @ sk_A)
% 0.20/0.52          | ~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.52          | ((k1_funct_1 @ sk_D_2 @ X0) != (k1_funct_1 @ sk_D_2 @ sk_C)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['42', '47'])).
% 0.20/0.52  thf('49', plain,
% 0.20/0.52      ((~ (r2_hidden @ sk_C @ sk_A)
% 0.20/0.52        | (zip_tseitin_2 @ 
% 0.20/0.52           (k1_funct_1 @ (k2_funct_1 @ sk_D_2) @ (k1_funct_1 @ sk_D_2 @ sk_C)) @ 
% 0.20/0.52           sk_C @ sk_D_2 @ sk_A))),
% 0.20/0.52      inference('eq_res', [status(thm)], ['48'])).
% 0.20/0.52  thf('50', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('51', plain,
% 0.20/0.52      ((zip_tseitin_2 @ 
% 0.20/0.52        (k1_funct_1 @ (k2_funct_1 @ sk_D_2) @ (k1_funct_1 @ sk_D_2 @ sk_C)) @ 
% 0.20/0.52        sk_C @ sk_D_2 @ sk_A)),
% 0.20/0.52      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.52  thf(zf_stmt_5, axiom,
% 0.20/0.52    (![C:$i,A:$i]:
% 0.20/0.52     ( ( zip_tseitin_3 @ C @ A ) =>
% 0.20/0.52       ( ( v2_funct_1 @ C ) <=>
% 0.20/0.52         ( ![D:$i,E:$i]:
% 0.20/0.52           ( ( zip_tseitin_2 @ E @ D @ C @ A ) => ( ( D ) = ( E ) ) ) ) ) ))).
% 0.20/0.52  thf('52', plain,
% 0.20/0.52      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.20/0.52         (~ (v2_funct_1 @ X34)
% 0.20/0.52          | ((X36) = (X35))
% 0.20/0.52          | ~ (zip_tseitin_2 @ X35 @ X36 @ X34 @ X33)
% 0.20/0.52          | ~ (zip_tseitin_3 @ X34 @ X33))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.52  thf('53', plain,
% 0.20/0.52      ((~ (zip_tseitin_3 @ sk_D_2 @ sk_A)
% 0.20/0.52        | ((sk_C)
% 0.20/0.52            = (k1_funct_1 @ (k2_funct_1 @ sk_D_2) @ 
% 0.20/0.52               (k1_funct_1 @ sk_D_2 @ sk_C)))
% 0.20/0.52        | ~ (v2_funct_1 @ sk_D_2))),
% 0.20/0.52      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.52  thf(zf_stmt_6, axiom,
% 0.20/0.52    (![B:$i,A:$i]:
% 0.20/0.52     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.52       ( zip_tseitin_1 @ B @ A ) ))).
% 0.20/0.52  thf('54', plain,
% 0.20/0.52      (![X26 : $i, X27 : $i]:
% 0.20/0.52         ((zip_tseitin_1 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.20/0.52  thf('55', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(zf_stmt_7, type, zip_tseitin_3 : $i > $i > $o).
% 0.20/0.52  thf(zf_stmt_8, type, zip_tseitin_2 : $i > $i > $i > $i > $o).
% 0.20/0.52  thf(zf_stmt_9, type, zip_tseitin_1 : $i > $i > $o).
% 0.20/0.52  thf(zf_stmt_10, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.52       ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_3 @ C @ A ) ) ))).
% 0.20/0.52  thf('56', plain,
% 0.20/0.52      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.20/0.52         (~ (zip_tseitin_1 @ X37 @ X38)
% 0.20/0.52          | ~ (v1_funct_1 @ X39)
% 0.20/0.52          | ~ (v1_funct_2 @ X39 @ X38 @ X37)
% 0.20/0.52          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 0.20/0.52          | (zip_tseitin_3 @ X39 @ X38))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_10])).
% 0.20/0.52  thf('57', plain,
% 0.20/0.52      (((zip_tseitin_3 @ sk_D_2 @ sk_A)
% 0.20/0.52        | ~ (v1_funct_2 @ sk_D_2 @ sk_A @ sk_B)
% 0.20/0.52        | ~ (v1_funct_1 @ sk_D_2)
% 0.20/0.52        | ~ (zip_tseitin_1 @ sk_B @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.52  thf('58', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('59', plain, ((v1_funct_1 @ sk_D_2)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('60', plain,
% 0.20/0.52      (((zip_tseitin_3 @ sk_D_2 @ sk_A) | ~ (zip_tseitin_1 @ sk_B @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.20/0.52  thf('61', plain,
% 0.20/0.52      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_3 @ sk_D_2 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['54', '60'])).
% 0.20/0.52  thf('62', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('63', plain, ((zip_tseitin_3 @ sk_D_2 @ sk_A)),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['61', '62'])).
% 0.20/0.52  thf('64', plain, ((v2_funct_1 @ sk_D_2)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('65', plain,
% 0.20/0.52      (((sk_C)
% 0.20/0.52         = (k1_funct_1 @ (k2_funct_1 @ sk_D_2) @ (k1_funct_1 @ sk_D_2 @ sk_C)))),
% 0.20/0.52      inference('demod', [status(thm)], ['53', '63', '64'])).
% 0.20/0.52  thf('66', plain,
% 0.20/0.52      (((k1_funct_1 @ (k2_funct_1 @ sk_D_2) @ (k1_funct_1 @ sk_D_2 @ sk_C))
% 0.20/0.52         != (sk_C))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('67', plain, ($false),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
