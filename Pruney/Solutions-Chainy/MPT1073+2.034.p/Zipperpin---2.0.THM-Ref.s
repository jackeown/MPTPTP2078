%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QDp7kheruh

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:18 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 150 expanded)
%              Number of leaves         :   40 (  62 expanded)
%              Depth                    :   13
%              Number of atoms          :  716 (1690 expanded)
%              Number of equality atoms :   42 (  81 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t190_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ B @ C )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
     => ~ ( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) )
          & ! [E: $i] :
              ( ( m1_subset_1 @ E @ B )
             => ( A
               != ( k1_funct_1 @ D @ E ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ B @ C )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
       => ~ ( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) )
            & ! [E: $i] :
                ( ( m1_subset_1 @ E @ B )
               => ( A
                 != ( k1_funct_1 @ D @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t190_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X16 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('7',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('9',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_C ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('13',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('15',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ( X27
        = ( k1_relset_1 @ X27 @ X28 @ X29 ) )
      | ~ ( zip_tseitin_1 @ X29 @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('19',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['16','23'])).

thf('25',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('26',plain,(
    ! [X9: $i] :
      ( ( ( k9_relat_1 @ X9 @ ( k1_relat_1 @ X9 ) )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('27',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k9_relat_1 @ X8 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X6 @ X7 ) @ ( k1_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('32',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('33',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['30','33'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('36',plain,(
    m1_subset_1 @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ sk_B )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','36'])).

thf('38',plain,(
    ! [X33: $i] :
      ( ( sk_A
       != ( k1_funct_1 @ sk_D_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_A
     != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('41',plain,(
    ! [X9: $i] :
      ( ( ( k9_relat_1 @ X9 @ ( k1_relat_1 @ X9 ) )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('42',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k9_relat_1 @ X8 @ X6 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X8 @ X6 @ X7 ) @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ sk_A ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['40','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('47',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ sk_A ) @ sk_D_1 ),
    inference(demod,[status(thm)],['45','46'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('48',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ X11 )
      | ( X12
        = ( k1_funct_1 @ X11 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_A
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('51',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_A != sk_A ) ),
    inference(demod,[status(thm)],['39','52'])).

thf('54',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['53'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('55',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('56',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['11','54','55'])).

thf('57',plain,(
    $false ),
    inference('sup-',[status(thm)],['4','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QDp7kheruh
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:56:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.67  % Solved by: fo/fo7.sh
% 0.46/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.67  % done 155 iterations in 0.219s
% 0.46/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.67  % SZS output start Refutation
% 0.46/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.67  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.46/0.67  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.46/0.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.67  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.46/0.67  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.46/0.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.67  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.46/0.67  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.46/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.67  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.46/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.67  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.46/0.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.67  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.46/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.67  thf(t190_funct_2, conjecture,
% 0.46/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.67     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.46/0.67         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.46/0.67       ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.46/0.67            ( ![E:$i]:
% 0.46/0.67              ( ( m1_subset_1 @ E @ B ) => ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ))).
% 0.46/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.67    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.67        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.46/0.67            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.46/0.67          ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.46/0.67               ( ![E:$i]:
% 0.46/0.67                 ( ( m1_subset_1 @ E @ B ) =>
% 0.46/0.67                   ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) )),
% 0.46/0.67    inference('cnf.neg', [status(esa)], [t190_funct_2])).
% 0.46/0.67  thf('0', plain, ((r2_hidden @ sk_A @ (k2_relset_1 @ sk_B @ sk_C @ sk_D_1))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('1', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(redefinition_k2_relset_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.67       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.46/0.67  thf('2', plain,
% 0.46/0.67      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.46/0.67         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 0.46/0.67          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.46/0.67      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.67  thf('3', plain,
% 0.46/0.67      (((k2_relset_1 @ sk_B @ sk_C @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.46/0.67      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.67  thf('4', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_1))),
% 0.46/0.67      inference('demod', [status(thm)], ['0', '3'])).
% 0.46/0.67  thf('5', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(dt_k2_relset_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.67       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.46/0.67  thf('6', plain,
% 0.46/0.67      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.67         ((m1_subset_1 @ (k2_relset_1 @ X16 @ X17 @ X18) @ (k1_zfmisc_1 @ X17))
% 0.46/0.67          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.46/0.67      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.46/0.67  thf('7', plain,
% 0.46/0.67      ((m1_subset_1 @ (k2_relset_1 @ sk_B @ sk_C @ sk_D_1) @ 
% 0.46/0.67        (k1_zfmisc_1 @ sk_C))),
% 0.46/0.67      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.67  thf('8', plain,
% 0.46/0.67      (((k2_relset_1 @ sk_B @ sk_C @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.46/0.67      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.67  thf('9', plain,
% 0.46/0.67      ((m1_subset_1 @ (k2_relat_1 @ sk_D_1) @ (k1_zfmisc_1 @ sk_C))),
% 0.46/0.67      inference('demod', [status(thm)], ['7', '8'])).
% 0.46/0.67  thf(t5_subset, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.46/0.67          ( v1_xboole_0 @ C ) ) ))).
% 0.46/0.67  thf('10', plain,
% 0.46/0.67      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.67         (~ (r2_hidden @ X2 @ X3)
% 0.46/0.67          | ~ (v1_xboole_0 @ X4)
% 0.46/0.67          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t5_subset])).
% 0.46/0.67  thf('11', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (v1_xboole_0 @ sk_C) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_1)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['9', '10'])).
% 0.46/0.67  thf(d1_funct_2, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.67       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.67           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.46/0.67             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.46/0.67         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.67           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.46/0.67             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.46/0.67  thf(zf_stmt_1, axiom,
% 0.46/0.67    (![B:$i,A:$i]:
% 0.46/0.67     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.67       ( zip_tseitin_0 @ B @ A ) ))).
% 0.46/0.67  thf('12', plain,
% 0.46/0.67      (![X25 : $i, X26 : $i]:
% 0.46/0.67         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.67  thf('13', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.46/0.67  thf(zf_stmt_3, axiom,
% 0.46/0.67    (![C:$i,B:$i,A:$i]:
% 0.46/0.67     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.46/0.67       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.46/0.67  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.46/0.67  thf(zf_stmt_5, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.67       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.46/0.67         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.67           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.46/0.67             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.46/0.67  thf('14', plain,
% 0.46/0.67      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.46/0.67         (~ (zip_tseitin_0 @ X30 @ X31)
% 0.46/0.67          | (zip_tseitin_1 @ X32 @ X30 @ X31)
% 0.46/0.67          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.46/0.67  thf('15', plain,
% 0.46/0.67      (((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)
% 0.46/0.67        | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 0.46/0.67      inference('sup-', [status(thm)], ['13', '14'])).
% 0.46/0.67  thf('16', plain,
% 0.46/0.67      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B))),
% 0.46/0.67      inference('sup-', [status(thm)], ['12', '15'])).
% 0.46/0.67  thf('17', plain, ((v1_funct_2 @ sk_D_1 @ sk_B @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('18', plain,
% 0.46/0.67      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.46/0.67         (~ (v1_funct_2 @ X29 @ X27 @ X28)
% 0.46/0.67          | ((X27) = (k1_relset_1 @ X27 @ X28 @ X29))
% 0.46/0.67          | ~ (zip_tseitin_1 @ X29 @ X28 @ X27))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.67  thf('19', plain,
% 0.46/0.67      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)
% 0.46/0.67        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_D_1)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['17', '18'])).
% 0.46/0.67  thf('20', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(redefinition_k1_relset_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.67       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.46/0.67  thf('21', plain,
% 0.46/0.67      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.67         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 0.46/0.67          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.46/0.67      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.46/0.67  thf('22', plain,
% 0.46/0.67      (((k1_relset_1 @ sk_B @ sk_C @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.46/0.67      inference('sup-', [status(thm)], ['20', '21'])).
% 0.46/0.67  thf('23', plain,
% 0.46/0.67      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)
% 0.46/0.67        | ((sk_B) = (k1_relat_1 @ sk_D_1)))),
% 0.46/0.67      inference('demod', [status(thm)], ['19', '22'])).
% 0.46/0.67  thf('24', plain,
% 0.46/0.67      ((((sk_C) = (k1_xboole_0)) | ((sk_B) = (k1_relat_1 @ sk_D_1)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['16', '23'])).
% 0.46/0.67  thf('25', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_1))),
% 0.46/0.67      inference('demod', [status(thm)], ['0', '3'])).
% 0.46/0.67  thf(t146_relat_1, axiom,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( v1_relat_1 @ A ) =>
% 0.46/0.67       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.46/0.67  thf('26', plain,
% 0.46/0.67      (![X9 : $i]:
% 0.46/0.67         (((k9_relat_1 @ X9 @ (k1_relat_1 @ X9)) = (k2_relat_1 @ X9))
% 0.46/0.67          | ~ (v1_relat_1 @ X9))),
% 0.46/0.67      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.46/0.67  thf(t143_relat_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( v1_relat_1 @ C ) =>
% 0.46/0.67       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.46/0.67         ( ?[D:$i]:
% 0.46/0.67           ( ( r2_hidden @ D @ B ) & 
% 0.46/0.67             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.46/0.67             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.46/0.67  thf('27', plain,
% 0.46/0.67      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.67         (~ (r2_hidden @ X7 @ (k9_relat_1 @ X8 @ X6))
% 0.46/0.67          | (r2_hidden @ (sk_D @ X8 @ X6 @ X7) @ (k1_relat_1 @ X8))
% 0.46/0.67          | ~ (v1_relat_1 @ X8))),
% 0.46/0.67      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.46/0.67  thf('28', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.46/0.67          | ~ (v1_relat_1 @ X0)
% 0.46/0.67          | ~ (v1_relat_1 @ X0)
% 0.46/0.67          | (r2_hidden @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ 
% 0.46/0.67             (k1_relat_1 @ X0)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['26', '27'])).
% 0.46/0.67  thf('29', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         ((r2_hidden @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ (k1_relat_1 @ X0))
% 0.46/0.67          | ~ (v1_relat_1 @ X0)
% 0.46/0.67          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.46/0.67      inference('simplify', [status(thm)], ['28'])).
% 0.46/0.67  thf('30', plain,
% 0.46/0.67      ((~ (v1_relat_1 @ sk_D_1)
% 0.46/0.67        | (r2_hidden @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ 
% 0.46/0.67           (k1_relat_1 @ sk_D_1)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['25', '29'])).
% 0.46/0.67  thf('31', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(cc1_relset_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.67       ( v1_relat_1 @ C ) ))).
% 0.46/0.67  thf('32', plain,
% 0.46/0.67      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.67         ((v1_relat_1 @ X13)
% 0.46/0.67          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.46/0.67      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.46/0.67  thf('33', plain, ((v1_relat_1 @ sk_D_1)),
% 0.46/0.67      inference('sup-', [status(thm)], ['31', '32'])).
% 0.46/0.67  thf('34', plain,
% 0.46/0.67      ((r2_hidden @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ 
% 0.46/0.67        (k1_relat_1 @ sk_D_1))),
% 0.46/0.67      inference('demod', [status(thm)], ['30', '33'])).
% 0.46/0.67  thf(t1_subset, axiom,
% 0.46/0.67    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.46/0.67  thf('35', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X0 @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.46/0.67      inference('cnf', [status(esa)], [t1_subset])).
% 0.46/0.67  thf('36', plain,
% 0.46/0.67      ((m1_subset_1 @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ 
% 0.46/0.67        (k1_relat_1 @ sk_D_1))),
% 0.46/0.67      inference('sup-', [status(thm)], ['34', '35'])).
% 0.46/0.67  thf('37', plain,
% 0.46/0.67      (((m1_subset_1 @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ sk_B)
% 0.46/0.67        | ((sk_C) = (k1_xboole_0)))),
% 0.46/0.67      inference('sup+', [status(thm)], ['24', '36'])).
% 0.46/0.67  thf('38', plain,
% 0.46/0.67      (![X33 : $i]:
% 0.46/0.67         (((sk_A) != (k1_funct_1 @ sk_D_1 @ X33))
% 0.46/0.67          | ~ (m1_subset_1 @ X33 @ sk_B))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('39', plain,
% 0.46/0.67      ((((sk_C) = (k1_xboole_0))
% 0.46/0.67        | ((sk_A)
% 0.46/0.67            != (k1_funct_1 @ sk_D_1 @ 
% 0.46/0.67                (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A))))),
% 0.46/0.67      inference('sup-', [status(thm)], ['37', '38'])).
% 0.46/0.67  thf('40', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_1))),
% 0.46/0.67      inference('demod', [status(thm)], ['0', '3'])).
% 0.46/0.67  thf('41', plain,
% 0.46/0.67      (![X9 : $i]:
% 0.46/0.67         (((k9_relat_1 @ X9 @ (k1_relat_1 @ X9)) = (k2_relat_1 @ X9))
% 0.46/0.67          | ~ (v1_relat_1 @ X9))),
% 0.46/0.67      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.46/0.67  thf('42', plain,
% 0.46/0.67      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.67         (~ (r2_hidden @ X7 @ (k9_relat_1 @ X8 @ X6))
% 0.46/0.67          | (r2_hidden @ (k4_tarski @ (sk_D @ X8 @ X6 @ X7) @ X7) @ X8)
% 0.46/0.67          | ~ (v1_relat_1 @ X8))),
% 0.46/0.67      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.46/0.67  thf('43', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.46/0.67          | ~ (v1_relat_1 @ X0)
% 0.46/0.67          | ~ (v1_relat_1 @ X0)
% 0.46/0.67          | (r2_hidden @ 
% 0.46/0.67             (k4_tarski @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['41', '42'])).
% 0.46/0.67  thf('44', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         ((r2_hidden @ 
% 0.46/0.67           (k4_tarski @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0)
% 0.46/0.67          | ~ (v1_relat_1 @ X0)
% 0.46/0.67          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.46/0.67      inference('simplify', [status(thm)], ['43'])).
% 0.46/0.67  thf('45', plain,
% 0.46/0.67      ((~ (v1_relat_1 @ sk_D_1)
% 0.46/0.67        | (r2_hidden @ 
% 0.46/0.67           (k4_tarski @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ sk_A) @ 
% 0.46/0.67           sk_D_1))),
% 0.46/0.67      inference('sup-', [status(thm)], ['40', '44'])).
% 0.46/0.67  thf('46', plain, ((v1_relat_1 @ sk_D_1)),
% 0.46/0.67      inference('sup-', [status(thm)], ['31', '32'])).
% 0.46/0.67  thf('47', plain,
% 0.46/0.67      ((r2_hidden @ 
% 0.46/0.67        (k4_tarski @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ sk_A) @ 
% 0.46/0.67        sk_D_1)),
% 0.46/0.67      inference('demod', [status(thm)], ['45', '46'])).
% 0.46/0.67  thf(t8_funct_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.46/0.67       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.46/0.67         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.46/0.67           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.46/0.67  thf('48', plain,
% 0.46/0.67      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.67         (~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ X11)
% 0.46/0.67          | ((X12) = (k1_funct_1 @ X11 @ X10))
% 0.46/0.67          | ~ (v1_funct_1 @ X11)
% 0.46/0.67          | ~ (v1_relat_1 @ X11))),
% 0.46/0.67      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.46/0.67  thf('49', plain,
% 0.46/0.67      ((~ (v1_relat_1 @ sk_D_1)
% 0.46/0.67        | ~ (v1_funct_1 @ sk_D_1)
% 0.46/0.67        | ((sk_A)
% 0.46/0.67            = (k1_funct_1 @ sk_D_1 @ 
% 0.46/0.67               (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A))))),
% 0.46/0.67      inference('sup-', [status(thm)], ['47', '48'])).
% 0.46/0.67  thf('50', plain, ((v1_relat_1 @ sk_D_1)),
% 0.46/0.67      inference('sup-', [status(thm)], ['31', '32'])).
% 0.46/0.67  thf('51', plain, ((v1_funct_1 @ sk_D_1)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('52', plain,
% 0.46/0.67      (((sk_A)
% 0.46/0.67         = (k1_funct_1 @ sk_D_1 @ 
% 0.46/0.67            (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A)))),
% 0.46/0.67      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.46/0.67  thf('53', plain, ((((sk_C) = (k1_xboole_0)) | ((sk_A) != (sk_A)))),
% 0.46/0.67      inference('demod', [status(thm)], ['39', '52'])).
% 0.46/0.67  thf('54', plain, (((sk_C) = (k1_xboole_0))),
% 0.46/0.67      inference('simplify', [status(thm)], ['53'])).
% 0.46/0.67  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.46/0.67  thf('55', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.67      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.67  thf('56', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_1))),
% 0.46/0.67      inference('demod', [status(thm)], ['11', '54', '55'])).
% 0.46/0.67  thf('57', plain, ($false), inference('sup-', [status(thm)], ['4', '56'])).
% 0.46/0.67  
% 0.46/0.67  % SZS output end Refutation
% 0.46/0.67  
% 0.46/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
