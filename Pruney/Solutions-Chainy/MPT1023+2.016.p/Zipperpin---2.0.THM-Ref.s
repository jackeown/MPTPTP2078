%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.27SWz0SqVO

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:30 EST 2020

% Result     : Theorem 21.67s
% Output     : Refutation 21.67s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 760 expanded)
%              Number of leaves         :   38 ( 237 expanded)
%              Depth                    :   25
%              Number of atoms          : 1417 (10956 expanded)
%              Number of equality atoms :  141 ( 668 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(t113_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ! [E: $i] :
                ( ( m1_subset_1 @ E @ A )
               => ( ( k1_funct_1 @ C @ E )
                  = ( k1_funct_1 @ D @ E ) ) )
           => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
           => ( ! [E: $i] :
                  ( ( m1_subset_1 @ E @ A )
                 => ( ( k1_funct_1 @ C @ E )
                    = ( k1_funct_1 @ D @ E ) ) )
             => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t113_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('3',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('6',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B_1 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ( X30
        = ( k1_relset_1 @ X30 @ X31 @ X32 ) )
      | ~ ( zip_tseitin_1 @ X32 @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('11',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('14',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B_1 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_D )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = sk_D ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = sk_D ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('23',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('24',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = sk_D ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B_1 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('26',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('28',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C_1 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_C_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('33',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = sk_C_1 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('37',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      = ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
      = ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['33','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('43',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('45',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('47',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B_1 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ( X30
        = ( k1_relset_1 @ X30 @ X31 @ X32 ) )
      | ~ ( zip_tseitin_1 @ X32 @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('51',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('53',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B_1 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_D )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = sk_D ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('56',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = sk_D ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('58',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = sk_D ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B_1 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('60',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C_1 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('61',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_C_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('63',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = sk_C_1 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('65',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( r2_relset_1 @ X25 @ X26 @ X24 @ X27 )
      | ( X24 != X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('66',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_relset_1 @ X25 @ X26 @ X27 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,
    ( ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['63','67'])).

thf('69',plain,
    ( ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['58','68'])).

thf('70',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = sk_A ),
    inference(demod,[status(thm)],['43','72'])).

thf('74',plain,
    ( ( sk_A
      = ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['40','73'])).

thf('75',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['24','74'])).

thf('76',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('78',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C_1 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ sk_C_1 )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = sk_C_1 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D @ sk_C_1 )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ~ ( r1_tarski @ sk_C_1 @ sk_D )
      | ( sk_C_1 = sk_D ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('87',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_D )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = sk_D ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = sk_D ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = sk_D ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ sk_D )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 = sk_D )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['85','92'])).

thf('94',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('95',plain,
    ( ( sk_C_1 = sk_D )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('97',plain,
    ( ( sk_C_1 = sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf(t9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k1_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ! [C: $i] :
                  ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                 => ( ( k1_funct_1 @ A @ C )
                    = ( k1_funct_1 @ B @ C ) ) ) )
           => ( A = B ) ) ) ) )).

thf('98',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( X17 = X16 )
      | ( r2_hidden @ ( sk_C @ X16 @ X17 ) @ ( k1_relat_1 @ X17 ) )
      | ( ( k1_relat_1 @ X17 )
       != ( k1_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( sk_C_1 = sk_D )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('101',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('102',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( sk_C_1 = sk_D )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['99','102','103'])).

thf('105',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( sk_C_1 = sk_D )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_A )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference('sup-',[status(thm)],['76','106'])).

thf('108',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('110',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(demod,[status(thm)],['107','110','111'])).

thf('113',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(simplify,[status(thm)],['112'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('114',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ( m1_subset_1 @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('116',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,
    ( ( sk_C_1 = sk_D )
    | ( m1_subset_1 @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['113','116'])).

thf('118',plain,(
    ! [X36: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ X36 )
        = ( k1_funct_1 @ sk_D @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( sk_C_1 = sk_D )
    | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,
    ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ),
    inference(condensation,[status(thm)],['119'])).

thf('121',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( X17 = X16 )
      | ( ( k1_funct_1 @ X17 @ ( sk_C @ X16 @ X17 ) )
       != ( k1_funct_1 @ X16 @ ( sk_C @ X16 @ X17 ) ) )
      | ( ( k1_relat_1 @ X17 )
       != ( k1_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('122',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_1 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['100','101'])).

thf('124',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('126',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['75'])).

thf('127',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['108','109'])).

thf('129',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(demod,[status(thm)],['122','123','124','125','126','127','128'])).

thf('130',plain,(
    sk_C_1 = sk_D ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_relset_1 @ X25 @ X26 @ X27 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('133',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    $false ),
    inference(demod,[status(thm)],['0','130','133'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.27SWz0SqVO
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:08:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 21.67/21.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 21.67/21.88  % Solved by: fo/fo7.sh
% 21.67/21.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 21.67/21.88  % done 7340 iterations in 21.417s
% 21.67/21.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 21.67/21.88  % SZS output start Refutation
% 21.67/21.88  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 21.67/21.88  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 21.67/21.88  thf(sk_A_type, type, sk_A: $i).
% 21.67/21.88  thf(sk_B_1_type, type, sk_B_1: $i).
% 21.67/21.88  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 21.67/21.88  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 21.67/21.88  thf(sk_C_1_type, type, sk_C_1: $i).
% 21.67/21.88  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 21.67/21.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 21.67/21.88  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 21.67/21.88  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 21.67/21.88  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 21.67/21.88  thf(sk_D_type, type, sk_D: $i).
% 21.67/21.88  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 21.67/21.88  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 21.67/21.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 21.67/21.88  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 21.67/21.88  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 21.67/21.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 21.67/21.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 21.67/21.88  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 21.67/21.88  thf(t113_funct_2, conjecture,
% 21.67/21.88    (![A:$i,B:$i,C:$i]:
% 21.67/21.88     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 21.67/21.88         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 21.67/21.88       ( ![D:$i]:
% 21.67/21.88         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 21.67/21.88             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 21.67/21.88           ( ( ![E:$i]:
% 21.67/21.88               ( ( m1_subset_1 @ E @ A ) =>
% 21.67/21.88                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 21.67/21.88             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 21.67/21.88  thf(zf_stmt_0, negated_conjecture,
% 21.67/21.88    (~( ![A:$i,B:$i,C:$i]:
% 21.67/21.88        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 21.67/21.88            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 21.67/21.88          ( ![D:$i]:
% 21.67/21.88            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 21.67/21.88                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 21.67/21.88              ( ( ![E:$i]:
% 21.67/21.88                  ( ( m1_subset_1 @ E @ A ) =>
% 21.67/21.88                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 21.67/21.88                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 21.67/21.88    inference('cnf.neg', [status(esa)], [t113_funct_2])).
% 21.67/21.88  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)),
% 21.67/21.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.67/21.88  thf(d1_funct_2, axiom,
% 21.67/21.88    (![A:$i,B:$i,C:$i]:
% 21.67/21.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 21.67/21.88       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 21.67/21.88           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 21.67/21.88             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 21.67/21.88         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 21.67/21.88           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 21.67/21.88             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 21.67/21.88  thf(zf_stmt_1, axiom,
% 21.67/21.88    (![B:$i,A:$i]:
% 21.67/21.88     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 21.67/21.88       ( zip_tseitin_0 @ B @ A ) ))).
% 21.67/21.88  thf('1', plain,
% 21.67/21.88      (![X28 : $i, X29 : $i]:
% 21.67/21.88         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 21.67/21.88      inference('cnf', [status(esa)], [zf_stmt_1])).
% 21.67/21.88  thf(t113_zfmisc_1, axiom,
% 21.67/21.88    (![A:$i,B:$i]:
% 21.67/21.88     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 21.67/21.88       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 21.67/21.88  thf('2', plain,
% 21.67/21.88      (![X8 : $i, X9 : $i]:
% 21.67/21.88         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 21.67/21.88      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 21.67/21.88  thf('3', plain,
% 21.67/21.88      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 21.67/21.88      inference('simplify', [status(thm)], ['2'])).
% 21.67/21.88  thf('4', plain,
% 21.67/21.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.67/21.88         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 21.67/21.88      inference('sup+', [status(thm)], ['1', '3'])).
% 21.67/21.88  thf('5', plain,
% 21.67/21.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 21.67/21.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.67/21.88  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 21.67/21.88  thf(zf_stmt_3, axiom,
% 21.67/21.88    (![C:$i,B:$i,A:$i]:
% 21.67/21.88     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 21.67/21.88       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 21.67/21.88  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 21.67/21.88  thf(zf_stmt_5, axiom,
% 21.67/21.88    (![A:$i,B:$i,C:$i]:
% 21.67/21.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 21.67/21.88       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 21.67/21.88         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 21.67/21.88           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 21.67/21.88             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 21.67/21.88  thf('6', plain,
% 21.67/21.88      (![X33 : $i, X34 : $i, X35 : $i]:
% 21.67/21.88         (~ (zip_tseitin_0 @ X33 @ X34)
% 21.67/21.88          | (zip_tseitin_1 @ X35 @ X33 @ X34)
% 21.67/21.88          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 21.67/21.88      inference('cnf', [status(esa)], [zf_stmt_5])).
% 21.67/21.88  thf('7', plain,
% 21.67/21.88      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 21.67/21.88        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 21.67/21.88      inference('sup-', [status(thm)], ['5', '6'])).
% 21.67/21.88  thf('8', plain,
% 21.67/21.88      (![X0 : $i]:
% 21.67/21.88         (((k2_zfmisc_1 @ X0 @ sk_B_1) = (k1_xboole_0))
% 21.67/21.88          | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 21.67/21.88      inference('sup-', [status(thm)], ['4', '7'])).
% 21.67/21.88  thf('9', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 21.67/21.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.67/21.88  thf('10', plain,
% 21.67/21.88      (![X30 : $i, X31 : $i, X32 : $i]:
% 21.67/21.88         (~ (v1_funct_2 @ X32 @ X30 @ X31)
% 21.67/21.88          | ((X30) = (k1_relset_1 @ X30 @ X31 @ X32))
% 21.67/21.88          | ~ (zip_tseitin_1 @ X32 @ X31 @ X30))),
% 21.67/21.88      inference('cnf', [status(esa)], [zf_stmt_3])).
% 21.67/21.88  thf('11', plain,
% 21.67/21.88      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 21.67/21.88        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 21.67/21.88      inference('sup-', [status(thm)], ['9', '10'])).
% 21.67/21.88  thf('12', plain,
% 21.67/21.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 21.67/21.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.67/21.88  thf(redefinition_k1_relset_1, axiom,
% 21.67/21.88    (![A:$i,B:$i,C:$i]:
% 21.67/21.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 21.67/21.88       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 21.67/21.88  thf('13', plain,
% 21.67/21.88      (![X21 : $i, X22 : $i, X23 : $i]:
% 21.67/21.88         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 21.67/21.88          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 21.67/21.88      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 21.67/21.88  thf('14', plain,
% 21.67/21.88      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 21.67/21.88      inference('sup-', [status(thm)], ['12', '13'])).
% 21.67/21.88  thf('15', plain,
% 21.67/21.88      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 21.67/21.88        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 21.67/21.88      inference('demod', [status(thm)], ['11', '14'])).
% 21.67/21.88  thf('16', plain,
% 21.67/21.88      (![X0 : $i]:
% 21.67/21.88         (((k2_zfmisc_1 @ X0 @ sk_B_1) = (k1_xboole_0))
% 21.67/21.88          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 21.67/21.88      inference('sup-', [status(thm)], ['8', '15'])).
% 21.67/21.88  thf('17', plain,
% 21.67/21.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 21.67/21.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.67/21.88  thf(t3_subset, axiom,
% 21.67/21.88    (![A:$i,B:$i]:
% 21.67/21.88     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 21.67/21.88  thf('18', plain,
% 21.67/21.88      (![X13 : $i, X14 : $i]:
% 21.67/21.88         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 21.67/21.88      inference('cnf', [status(esa)], [t3_subset])).
% 21.67/21.88  thf('19', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 21.67/21.88      inference('sup-', [status(thm)], ['17', '18'])).
% 21.67/21.88  thf(d10_xboole_0, axiom,
% 21.67/21.88    (![A:$i,B:$i]:
% 21.67/21.88     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 21.67/21.88  thf('20', plain,
% 21.67/21.88      (![X3 : $i, X5 : $i]:
% 21.67/21.88         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 21.67/21.88      inference('cnf', [status(esa)], [d10_xboole_0])).
% 21.67/21.88  thf('21', plain,
% 21.67/21.88      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_D)
% 21.67/21.88        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_D)))),
% 21.67/21.88      inference('sup-', [status(thm)], ['19', '20'])).
% 21.67/21.88  thf('22', plain,
% 21.67/21.88      ((~ (r1_tarski @ k1_xboole_0 @ sk_D)
% 21.67/21.88        | ((sk_A) = (k1_relat_1 @ sk_D))
% 21.67/21.88        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_D)))),
% 21.67/21.88      inference('sup-', [status(thm)], ['16', '21'])).
% 21.67/21.88  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 21.67/21.88  thf('23', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 21.67/21.88      inference('cnf', [status(esa)], [t2_xboole_1])).
% 21.67/21.88  thf('24', plain,
% 21.67/21.88      ((((sk_A) = (k1_relat_1 @ sk_D))
% 21.67/21.88        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_D)))),
% 21.67/21.88      inference('demod', [status(thm)], ['22', '23'])).
% 21.67/21.88  thf('25', plain,
% 21.67/21.88      (![X0 : $i]:
% 21.67/21.88         (((k2_zfmisc_1 @ X0 @ sk_B_1) = (k1_xboole_0))
% 21.67/21.88          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 21.67/21.88      inference('sup-', [status(thm)], ['8', '15'])).
% 21.67/21.88  thf('26', plain,
% 21.67/21.88      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 21.67/21.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.67/21.88  thf('27', plain,
% 21.67/21.88      (![X13 : $i, X14 : $i]:
% 21.67/21.88         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 21.67/21.88      inference('cnf', [status(esa)], [t3_subset])).
% 21.67/21.88  thf('28', plain, ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 21.67/21.88      inference('sup-', [status(thm)], ['26', '27'])).
% 21.67/21.88  thf('29', plain,
% 21.67/21.88      (![X3 : $i, X5 : $i]:
% 21.67/21.88         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 21.67/21.88      inference('cnf', [status(esa)], [d10_xboole_0])).
% 21.67/21.88  thf('30', plain,
% 21.67/21.88      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C_1)
% 21.67/21.88        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_C_1)))),
% 21.67/21.88      inference('sup-', [status(thm)], ['28', '29'])).
% 21.67/21.88  thf('31', plain,
% 21.67/21.88      ((~ (r1_tarski @ k1_xboole_0 @ sk_C_1)
% 21.67/21.88        | ((sk_A) = (k1_relat_1 @ sk_D))
% 21.67/21.88        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_C_1)))),
% 21.67/21.88      inference('sup-', [status(thm)], ['25', '30'])).
% 21.67/21.88  thf('32', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 21.67/21.88      inference('cnf', [status(esa)], [t2_xboole_1])).
% 21.67/21.88  thf('33', plain,
% 21.67/21.88      ((((sk_A) = (k1_relat_1 @ sk_D))
% 21.67/21.88        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_C_1)))),
% 21.67/21.88      inference('demod', [status(thm)], ['31', '32'])).
% 21.67/21.88  thf('34', plain,
% 21.67/21.88      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 21.67/21.88      inference('cnf', [status(esa)], [d10_xboole_0])).
% 21.67/21.88  thf('35', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 21.67/21.88      inference('simplify', [status(thm)], ['34'])).
% 21.67/21.88  thf('36', plain,
% 21.67/21.88      (![X13 : $i, X15 : $i]:
% 21.67/21.88         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 21.67/21.88      inference('cnf', [status(esa)], [t3_subset])).
% 21.67/21.88  thf('37', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 21.67/21.88      inference('sup-', [status(thm)], ['35', '36'])).
% 21.67/21.88  thf('38', plain,
% 21.67/21.88      (![X21 : $i, X22 : $i, X23 : $i]:
% 21.67/21.88         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 21.67/21.88          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 21.67/21.88      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 21.67/21.88  thf('39', plain,
% 21.67/21.88      (![X0 : $i, X1 : $i]:
% 21.67/21.88         ((k1_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0))
% 21.67/21.88           = (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 21.67/21.88      inference('sup-', [status(thm)], ['37', '38'])).
% 21.67/21.88  thf('40', plain,
% 21.67/21.88      ((((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)
% 21.67/21.88          = (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 21.67/21.88        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 21.67/21.88      inference('sup+', [status(thm)], ['33', '39'])).
% 21.67/21.88  thf('41', plain,
% 21.67/21.88      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 21.67/21.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.67/21.88  thf('42', plain,
% 21.67/21.88      (![X21 : $i, X22 : $i, X23 : $i]:
% 21.67/21.88         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 21.67/21.88          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 21.67/21.88      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 21.67/21.88  thf('43', plain,
% 21.67/21.88      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 21.67/21.88      inference('sup-', [status(thm)], ['41', '42'])).
% 21.67/21.88  thf('44', plain,
% 21.67/21.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.67/21.88         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 21.67/21.88      inference('sup+', [status(thm)], ['1', '3'])).
% 21.67/21.88  thf('45', plain,
% 21.67/21.88      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 21.67/21.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.67/21.88  thf('46', plain,
% 21.67/21.88      (![X33 : $i, X34 : $i, X35 : $i]:
% 21.67/21.88         (~ (zip_tseitin_0 @ X33 @ X34)
% 21.67/21.88          | (zip_tseitin_1 @ X35 @ X33 @ X34)
% 21.67/21.88          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 21.67/21.88      inference('cnf', [status(esa)], [zf_stmt_5])).
% 21.67/21.88  thf('47', plain,
% 21.67/21.88      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 21.67/21.88        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 21.67/21.88      inference('sup-', [status(thm)], ['45', '46'])).
% 21.67/21.88  thf('48', plain,
% 21.67/21.88      (![X0 : $i]:
% 21.67/21.88         (((k2_zfmisc_1 @ X0 @ sk_B_1) = (k1_xboole_0))
% 21.67/21.88          | (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A))),
% 21.67/21.88      inference('sup-', [status(thm)], ['44', '47'])).
% 21.67/21.88  thf('49', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 21.67/21.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.67/21.88  thf('50', plain,
% 21.67/21.88      (![X30 : $i, X31 : $i, X32 : $i]:
% 21.67/21.88         (~ (v1_funct_2 @ X32 @ X30 @ X31)
% 21.67/21.88          | ((X30) = (k1_relset_1 @ X30 @ X31 @ X32))
% 21.67/21.88          | ~ (zip_tseitin_1 @ X32 @ X31 @ X30))),
% 21.67/21.88      inference('cnf', [status(esa)], [zf_stmt_3])).
% 21.67/21.88  thf('51', plain,
% 21.67/21.88      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 21.67/21.88        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 21.67/21.88      inference('sup-', [status(thm)], ['49', '50'])).
% 21.67/21.88  thf('52', plain,
% 21.67/21.88      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 21.67/21.88      inference('sup-', [status(thm)], ['41', '42'])).
% 21.67/21.88  thf('53', plain,
% 21.67/21.88      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 21.67/21.88        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 21.67/21.88      inference('demod', [status(thm)], ['51', '52'])).
% 21.67/21.88  thf('54', plain,
% 21.67/21.88      (![X0 : $i]:
% 21.67/21.88         (((k2_zfmisc_1 @ X0 @ sk_B_1) = (k1_xboole_0))
% 21.67/21.88          | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 21.67/21.88      inference('sup-', [status(thm)], ['48', '53'])).
% 21.67/21.88  thf('55', plain,
% 21.67/21.88      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_D)
% 21.67/21.88        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_D)))),
% 21.67/21.88      inference('sup-', [status(thm)], ['19', '20'])).
% 21.67/21.88  thf('56', plain,
% 21.67/21.88      ((~ (r1_tarski @ k1_xboole_0 @ sk_D)
% 21.67/21.88        | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 21.67/21.88        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_D)))),
% 21.67/21.88      inference('sup-', [status(thm)], ['54', '55'])).
% 21.67/21.88  thf('57', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 21.67/21.88      inference('cnf', [status(esa)], [t2_xboole_1])).
% 21.67/21.88  thf('58', plain,
% 21.67/21.88      ((((sk_A) = (k1_relat_1 @ sk_C_1))
% 21.67/21.88        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_D)))),
% 21.67/21.88      inference('demod', [status(thm)], ['56', '57'])).
% 21.67/21.88  thf('59', plain,
% 21.67/21.88      (![X0 : $i]:
% 21.67/21.88         (((k2_zfmisc_1 @ X0 @ sk_B_1) = (k1_xboole_0))
% 21.67/21.88          | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 21.67/21.88      inference('sup-', [status(thm)], ['48', '53'])).
% 21.67/21.88  thf('60', plain,
% 21.67/21.88      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C_1)
% 21.67/21.88        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_C_1)))),
% 21.67/21.88      inference('sup-', [status(thm)], ['28', '29'])).
% 21.67/21.88  thf('61', plain,
% 21.67/21.88      ((~ (r1_tarski @ k1_xboole_0 @ sk_C_1)
% 21.67/21.88        | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 21.67/21.88        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_C_1)))),
% 21.67/21.88      inference('sup-', [status(thm)], ['59', '60'])).
% 21.67/21.88  thf('62', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 21.67/21.88      inference('cnf', [status(esa)], [t2_xboole_1])).
% 21.67/21.88  thf('63', plain,
% 21.67/21.88      ((((sk_A) = (k1_relat_1 @ sk_C_1))
% 21.67/21.88        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_C_1)))),
% 21.67/21.88      inference('demod', [status(thm)], ['61', '62'])).
% 21.67/21.88  thf('64', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 21.67/21.88      inference('sup-', [status(thm)], ['35', '36'])).
% 21.67/21.88  thf(redefinition_r2_relset_1, axiom,
% 21.67/21.88    (![A:$i,B:$i,C:$i,D:$i]:
% 21.67/21.88     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 21.67/21.88         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 21.67/21.88       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 21.67/21.88  thf('65', plain,
% 21.67/21.88      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 21.67/21.88         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 21.67/21.88          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 21.67/21.88          | (r2_relset_1 @ X25 @ X26 @ X24 @ X27)
% 21.67/21.88          | ((X24) != (X27)))),
% 21.67/21.88      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 21.67/21.88  thf('66', plain,
% 21.67/21.88      (![X25 : $i, X26 : $i, X27 : $i]:
% 21.67/21.88         ((r2_relset_1 @ X25 @ X26 @ X27 @ X27)
% 21.67/21.88          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 21.67/21.88      inference('simplify', [status(thm)], ['65'])).
% 21.67/21.88  thf('67', plain,
% 21.67/21.88      (![X0 : $i, X1 : $i]:
% 21.67/21.88         (r2_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 21.67/21.88          (k2_zfmisc_1 @ X1 @ X0))),
% 21.67/21.88      inference('sup-', [status(thm)], ['64', '66'])).
% 21.67/21.88  thf('68', plain,
% 21.67/21.88      (((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 21.67/21.88        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 21.67/21.88      inference('sup+', [status(thm)], ['63', '67'])).
% 21.67/21.88  thf('69', plain,
% 21.67/21.88      (((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)
% 21.67/21.88        | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 21.67/21.88        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 21.67/21.88      inference('sup+', [status(thm)], ['58', '68'])).
% 21.67/21.88  thf('70', plain,
% 21.67/21.88      ((((sk_A) = (k1_relat_1 @ sk_C_1))
% 21.67/21.88        | (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))),
% 21.67/21.88      inference('simplify', [status(thm)], ['69'])).
% 21.67/21.88  thf('71', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)),
% 21.67/21.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.67/21.88  thf('72', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 21.67/21.88      inference('clc', [status(thm)], ['70', '71'])).
% 21.67/21.88  thf('73', plain, (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (sk_A))),
% 21.67/21.88      inference('demod', [status(thm)], ['43', '72'])).
% 21.67/21.88  thf('74', plain,
% 21.67/21.88      ((((sk_A) = (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 21.67/21.88        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 21.67/21.88      inference('demod', [status(thm)], ['40', '73'])).
% 21.67/21.88  thf('75', plain,
% 21.67/21.88      ((((sk_A) = (k1_relat_1 @ sk_D))
% 21.67/21.88        | ((sk_A) = (k1_relat_1 @ sk_D))
% 21.67/21.88        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 21.67/21.88      inference('sup+', [status(thm)], ['24', '74'])).
% 21.67/21.88  thf('76', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 21.67/21.88      inference('simplify', [status(thm)], ['75'])).
% 21.67/21.88  thf('77', plain,
% 21.67/21.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.67/21.88         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 21.67/21.88      inference('sup+', [status(thm)], ['1', '3'])).
% 21.67/21.88  thf('78', plain,
% 21.67/21.88      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C_1)
% 21.67/21.88        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_C_1)))),
% 21.67/21.88      inference('sup-', [status(thm)], ['28', '29'])).
% 21.67/21.88  thf('79', plain,
% 21.67/21.88      (![X0 : $i]:
% 21.67/21.88         (~ (r1_tarski @ k1_xboole_0 @ sk_C_1)
% 21.67/21.88          | (zip_tseitin_0 @ sk_B_1 @ X0)
% 21.67/21.88          | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_C_1)))),
% 21.67/21.88      inference('sup-', [status(thm)], ['77', '78'])).
% 21.67/21.88  thf('80', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 21.67/21.88      inference('cnf', [status(esa)], [t2_xboole_1])).
% 21.67/21.88  thf('81', plain,
% 21.67/21.88      (![X0 : $i]:
% 21.67/21.88         ((zip_tseitin_0 @ sk_B_1 @ X0)
% 21.67/21.88          | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_C_1)))),
% 21.67/21.88      inference('demod', [status(thm)], ['79', '80'])).
% 21.67/21.88  thf('82', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 21.67/21.88      inference('sup-', [status(thm)], ['17', '18'])).
% 21.67/21.88  thf('83', plain,
% 21.67/21.88      (![X0 : $i]:
% 21.67/21.88         ((r1_tarski @ sk_D @ sk_C_1) | (zip_tseitin_0 @ sk_B_1 @ X0))),
% 21.67/21.88      inference('sup+', [status(thm)], ['81', '82'])).
% 21.67/21.88  thf('84', plain,
% 21.67/21.88      (![X3 : $i, X5 : $i]:
% 21.67/21.88         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 21.67/21.88      inference('cnf', [status(esa)], [d10_xboole_0])).
% 21.67/21.88  thf('85', plain,
% 21.67/21.88      (![X0 : $i]:
% 21.67/21.88         ((zip_tseitin_0 @ sk_B_1 @ X0)
% 21.67/21.88          | ~ (r1_tarski @ sk_C_1 @ sk_D)
% 21.67/21.88          | ((sk_C_1) = (sk_D)))),
% 21.67/21.88      inference('sup-', [status(thm)], ['83', '84'])).
% 21.67/21.88  thf('86', plain,
% 21.67/21.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.67/21.88         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 21.67/21.88      inference('sup+', [status(thm)], ['1', '3'])).
% 21.67/21.88  thf('87', plain,
% 21.67/21.88      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_D)
% 21.67/21.88        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_D)))),
% 21.67/21.88      inference('sup-', [status(thm)], ['19', '20'])).
% 21.67/21.88  thf('88', plain,
% 21.67/21.88      (![X0 : $i]:
% 21.67/21.88         (~ (r1_tarski @ k1_xboole_0 @ sk_D)
% 21.67/21.88          | (zip_tseitin_0 @ sk_B_1 @ X0)
% 21.67/21.88          | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_D)))),
% 21.67/21.88      inference('sup-', [status(thm)], ['86', '87'])).
% 21.67/21.88  thf('89', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 21.67/21.88      inference('cnf', [status(esa)], [t2_xboole_1])).
% 21.67/21.88  thf('90', plain,
% 21.67/21.88      (![X0 : $i]:
% 21.67/21.88         ((zip_tseitin_0 @ sk_B_1 @ X0)
% 21.67/21.88          | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_D)))),
% 21.67/21.88      inference('demod', [status(thm)], ['88', '89'])).
% 21.67/21.88  thf('91', plain, ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 21.67/21.88      inference('sup-', [status(thm)], ['26', '27'])).
% 21.67/21.88  thf('92', plain,
% 21.67/21.88      (![X0 : $i]:
% 21.67/21.88         ((r1_tarski @ sk_C_1 @ sk_D) | (zip_tseitin_0 @ sk_B_1 @ X0))),
% 21.67/21.88      inference('sup+', [status(thm)], ['90', '91'])).
% 21.67/21.88  thf('93', plain,
% 21.67/21.88      (![X0 : $i]: (((sk_C_1) = (sk_D)) | (zip_tseitin_0 @ sk_B_1 @ X0))),
% 21.67/21.88      inference('clc', [status(thm)], ['85', '92'])).
% 21.67/21.88  thf('94', plain,
% 21.67/21.88      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 21.67/21.88        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 21.67/21.88      inference('sup-', [status(thm)], ['45', '46'])).
% 21.67/21.88  thf('95', plain,
% 21.67/21.88      ((((sk_C_1) = (sk_D)) | (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A))),
% 21.67/21.88      inference('sup-', [status(thm)], ['93', '94'])).
% 21.67/21.88  thf('96', plain,
% 21.67/21.88      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 21.67/21.88        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 21.67/21.88      inference('demod', [status(thm)], ['51', '52'])).
% 21.67/21.88  thf('97', plain, ((((sk_C_1) = (sk_D)) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 21.67/21.88      inference('sup-', [status(thm)], ['95', '96'])).
% 21.67/21.88  thf(t9_funct_1, axiom,
% 21.67/21.88    (![A:$i]:
% 21.67/21.88     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 21.67/21.88       ( ![B:$i]:
% 21.67/21.88         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 21.67/21.88           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 21.67/21.88               ( ![C:$i]:
% 21.67/21.88                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 21.67/21.88                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 21.67/21.88             ( ( A ) = ( B ) ) ) ) ) ))).
% 21.67/21.88  thf('98', plain,
% 21.67/21.88      (![X16 : $i, X17 : $i]:
% 21.67/21.88         (~ (v1_relat_1 @ X16)
% 21.67/21.88          | ~ (v1_funct_1 @ X16)
% 21.67/21.88          | ((X17) = (X16))
% 21.67/21.88          | (r2_hidden @ (sk_C @ X16 @ X17) @ (k1_relat_1 @ X17))
% 21.67/21.88          | ((k1_relat_1 @ X17) != (k1_relat_1 @ X16))
% 21.67/21.88          | ~ (v1_funct_1 @ X17)
% 21.67/21.88          | ~ (v1_relat_1 @ X17))),
% 21.67/21.88      inference('cnf', [status(esa)], [t9_funct_1])).
% 21.67/21.88  thf('99', plain,
% 21.67/21.88      (![X0 : $i]:
% 21.67/21.88         (((sk_A) != (k1_relat_1 @ X0))
% 21.67/21.88          | ((sk_C_1) = (sk_D))
% 21.67/21.88          | ~ (v1_relat_1 @ sk_C_1)
% 21.67/21.88          | ~ (v1_funct_1 @ sk_C_1)
% 21.67/21.88          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 21.67/21.88          | ((sk_C_1) = (X0))
% 21.67/21.88          | ~ (v1_funct_1 @ X0)
% 21.67/21.88          | ~ (v1_relat_1 @ X0))),
% 21.67/21.88      inference('sup-', [status(thm)], ['97', '98'])).
% 21.67/21.88  thf('100', plain,
% 21.67/21.88      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 21.67/21.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.67/21.88  thf(cc1_relset_1, axiom,
% 21.67/21.88    (![A:$i,B:$i,C:$i]:
% 21.67/21.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 21.67/21.88       ( v1_relat_1 @ C ) ))).
% 21.67/21.88  thf('101', plain,
% 21.67/21.88      (![X18 : $i, X19 : $i, X20 : $i]:
% 21.67/21.88         ((v1_relat_1 @ X18)
% 21.67/21.88          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 21.67/21.88      inference('cnf', [status(esa)], [cc1_relset_1])).
% 21.67/21.88  thf('102', plain, ((v1_relat_1 @ sk_C_1)),
% 21.67/21.88      inference('sup-', [status(thm)], ['100', '101'])).
% 21.67/21.88  thf('103', plain, ((v1_funct_1 @ sk_C_1)),
% 21.67/21.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.67/21.88  thf('104', plain,
% 21.67/21.88      (![X0 : $i]:
% 21.67/21.88         (((sk_A) != (k1_relat_1 @ X0))
% 21.67/21.88          | ((sk_C_1) = (sk_D))
% 21.67/21.88          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 21.67/21.88          | ((sk_C_1) = (X0))
% 21.67/21.88          | ~ (v1_funct_1 @ X0)
% 21.67/21.88          | ~ (v1_relat_1 @ X0))),
% 21.67/21.88      inference('demod', [status(thm)], ['99', '102', '103'])).
% 21.67/21.88  thf('105', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 21.67/21.88      inference('clc', [status(thm)], ['70', '71'])).
% 21.67/21.88  thf('106', plain,
% 21.67/21.88      (![X0 : $i]:
% 21.67/21.88         (((sk_A) != (k1_relat_1 @ X0))
% 21.67/21.88          | ((sk_C_1) = (sk_D))
% 21.67/21.88          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_A)
% 21.67/21.88          | ((sk_C_1) = (X0))
% 21.67/21.88          | ~ (v1_funct_1 @ X0)
% 21.67/21.88          | ~ (v1_relat_1 @ X0))),
% 21.67/21.88      inference('demod', [status(thm)], ['104', '105'])).
% 21.67/21.88  thf('107', plain,
% 21.67/21.88      ((((sk_A) != (sk_A))
% 21.67/21.88        | ~ (v1_relat_1 @ sk_D)
% 21.67/21.88        | ~ (v1_funct_1 @ sk_D)
% 21.67/21.88        | ((sk_C_1) = (sk_D))
% 21.67/21.88        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A)
% 21.67/21.88        | ((sk_C_1) = (sk_D)))),
% 21.67/21.88      inference('sup-', [status(thm)], ['76', '106'])).
% 21.67/21.88  thf('108', plain,
% 21.67/21.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 21.67/21.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.67/21.88  thf('109', plain,
% 21.67/21.88      (![X18 : $i, X19 : $i, X20 : $i]:
% 21.67/21.88         ((v1_relat_1 @ X18)
% 21.67/21.88          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 21.67/21.88      inference('cnf', [status(esa)], [cc1_relset_1])).
% 21.67/21.88  thf('110', plain, ((v1_relat_1 @ sk_D)),
% 21.67/21.88      inference('sup-', [status(thm)], ['108', '109'])).
% 21.67/21.88  thf('111', plain, ((v1_funct_1 @ sk_D)),
% 21.67/21.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.67/21.88  thf('112', plain,
% 21.67/21.88      ((((sk_A) != (sk_A))
% 21.67/21.88        | ((sk_C_1) = (sk_D))
% 21.67/21.88        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A)
% 21.67/21.88        | ((sk_C_1) = (sk_D)))),
% 21.67/21.88      inference('demod', [status(thm)], ['107', '110', '111'])).
% 21.67/21.88  thf('113', plain,
% 21.67/21.88      (((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A) | ((sk_C_1) = (sk_D)))),
% 21.67/21.88      inference('simplify', [status(thm)], ['112'])).
% 21.67/21.88  thf(d2_subset_1, axiom,
% 21.67/21.88    (![A:$i,B:$i]:
% 21.67/21.88     ( ( ( v1_xboole_0 @ A ) =>
% 21.67/21.88         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 21.67/21.88       ( ( ~( v1_xboole_0 @ A ) ) =>
% 21.67/21.88         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 21.67/21.88  thf('114', plain,
% 21.67/21.88      (![X10 : $i, X11 : $i]:
% 21.67/21.88         (~ (r2_hidden @ X10 @ X11)
% 21.67/21.88          | (m1_subset_1 @ X10 @ X11)
% 21.67/21.88          | (v1_xboole_0 @ X11))),
% 21.67/21.88      inference('cnf', [status(esa)], [d2_subset_1])).
% 21.67/21.88  thf(d1_xboole_0, axiom,
% 21.67/21.88    (![A:$i]:
% 21.67/21.88     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 21.67/21.88  thf('115', plain,
% 21.67/21.88      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 21.67/21.88      inference('cnf', [status(esa)], [d1_xboole_0])).
% 21.67/21.88  thf('116', plain,
% 21.67/21.88      (![X10 : $i, X11 : $i]:
% 21.67/21.88         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 21.67/21.88      inference('clc', [status(thm)], ['114', '115'])).
% 21.67/21.88  thf('117', plain,
% 21.67/21.88      ((((sk_C_1) = (sk_D)) | (m1_subset_1 @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 21.67/21.88      inference('sup-', [status(thm)], ['113', '116'])).
% 21.67/21.88  thf('118', plain,
% 21.67/21.88      (![X36 : $i]:
% 21.67/21.88         (((k1_funct_1 @ sk_C_1 @ X36) = (k1_funct_1 @ sk_D @ X36))
% 21.67/21.88          | ~ (m1_subset_1 @ X36 @ sk_A))),
% 21.67/21.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.67/21.88  thf('119', plain,
% 21.67/21.88      ((((sk_C_1) = (sk_D))
% 21.67/21.88        | ((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 21.67/21.88            = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))))),
% 21.67/21.88      inference('sup-', [status(thm)], ['117', '118'])).
% 21.67/21.88  thf('120', plain,
% 21.67/21.88      (((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 21.67/21.88         = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))),
% 21.67/21.88      inference('condensation', [status(thm)], ['119'])).
% 21.67/21.88  thf('121', plain,
% 21.67/21.88      (![X16 : $i, X17 : $i]:
% 21.67/21.88         (~ (v1_relat_1 @ X16)
% 21.67/21.88          | ~ (v1_funct_1 @ X16)
% 21.67/21.88          | ((X17) = (X16))
% 21.67/21.88          | ((k1_funct_1 @ X17 @ (sk_C @ X16 @ X17))
% 21.67/21.88              != (k1_funct_1 @ X16 @ (sk_C @ X16 @ X17)))
% 21.67/21.88          | ((k1_relat_1 @ X17) != (k1_relat_1 @ X16))
% 21.67/21.88          | ~ (v1_funct_1 @ X17)
% 21.67/21.88          | ~ (v1_relat_1 @ X17))),
% 21.67/21.88      inference('cnf', [status(esa)], [t9_funct_1])).
% 21.67/21.88  thf('122', plain,
% 21.67/21.88      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 21.67/21.88          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 21.67/21.88        | ~ (v1_relat_1 @ sk_C_1)
% 21.67/21.88        | ~ (v1_funct_1 @ sk_C_1)
% 21.67/21.88        | ((k1_relat_1 @ sk_C_1) != (k1_relat_1 @ sk_D))
% 21.67/21.88        | ((sk_C_1) = (sk_D))
% 21.67/21.88        | ~ (v1_funct_1 @ sk_D)
% 21.67/21.88        | ~ (v1_relat_1 @ sk_D))),
% 21.67/21.88      inference('sup-', [status(thm)], ['120', '121'])).
% 21.67/21.88  thf('123', plain, ((v1_relat_1 @ sk_C_1)),
% 21.67/21.88      inference('sup-', [status(thm)], ['100', '101'])).
% 21.67/21.88  thf('124', plain, ((v1_funct_1 @ sk_C_1)),
% 21.67/21.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.67/21.88  thf('125', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 21.67/21.88      inference('clc', [status(thm)], ['70', '71'])).
% 21.67/21.88  thf('126', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 21.67/21.88      inference('simplify', [status(thm)], ['75'])).
% 21.67/21.88  thf('127', plain, ((v1_funct_1 @ sk_D)),
% 21.67/21.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.67/21.88  thf('128', plain, ((v1_relat_1 @ sk_D)),
% 21.67/21.88      inference('sup-', [status(thm)], ['108', '109'])).
% 21.67/21.88  thf('129', plain,
% 21.67/21.88      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 21.67/21.88          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 21.67/21.88        | ((sk_A) != (sk_A))
% 21.67/21.88        | ((sk_C_1) = (sk_D)))),
% 21.67/21.88      inference('demod', [status(thm)],
% 21.67/21.88                ['122', '123', '124', '125', '126', '127', '128'])).
% 21.67/21.88  thf('130', plain, (((sk_C_1) = (sk_D))),
% 21.67/21.88      inference('simplify', [status(thm)], ['129'])).
% 21.67/21.88  thf('131', plain,
% 21.67/21.88      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 21.67/21.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.67/21.88  thf('132', plain,
% 21.67/21.88      (![X25 : $i, X26 : $i, X27 : $i]:
% 21.67/21.88         ((r2_relset_1 @ X25 @ X26 @ X27 @ X27)
% 21.67/21.88          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 21.67/21.88      inference('simplify', [status(thm)], ['65'])).
% 21.67/21.88  thf('133', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_C_1)),
% 21.67/21.88      inference('sup-', [status(thm)], ['131', '132'])).
% 21.67/21.88  thf('134', plain, ($false),
% 21.67/21.88      inference('demod', [status(thm)], ['0', '130', '133'])).
% 21.67/21.88  
% 21.67/21.88  % SZS output end Refutation
% 21.67/21.88  
% 21.67/21.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
