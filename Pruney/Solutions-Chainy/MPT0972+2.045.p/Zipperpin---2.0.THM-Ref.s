%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZVf7oWJCfu

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:39 EST 2020

% Result     : Theorem 3.93s
% Output     : Refutation 3.93s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 784 expanded)
%              Number of leaves         :   36 ( 243 expanded)
%              Depth                    :   24
%              Number of atoms          : 1211 (11299 expanded)
%              Number of equality atoms :  119 ( 686 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t18_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ! [E: $i] :
                ( ( r2_hidden @ E @ A )
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
                  ( ( r2_hidden @ E @ A )
                 => ( ( k1_funct_1 @ C @ E )
                    = ( k1_funct_1 @ D @ E ) ) )
             => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ),
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
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('3',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('11',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('14',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_D )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_D ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_D ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('23',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('24',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_D ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('26',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('28',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C_1 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_C_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('33',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C_1 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('37',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      = ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['33','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('43',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('45',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('47',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('51',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('53',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_D )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_D ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('56',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_D ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('58',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_D ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('60',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C_1 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('61',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_C_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('63',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
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
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( r2_relset_1 @ X20 @ X21 @ X19 @ X22 )
      | ( X19 != X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('66',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_relset_1 @ X20 @ X21 @ X22 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,
    ( ( r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['63','67'])).

thf('69',plain,
    ( ( r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['58','68'])).

thf('70',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = sk_A ),
    inference(demod,[status(thm)],['43','72'])).

thf('74',plain,
    ( ( sk_A
      = ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
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

thf('77',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['70','71'])).

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

thf('78',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( X15 = X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X15 ) @ ( k1_relat_1 @ X15 ) )
      | ( ( k1_relat_1 @ X15 )
       != ( k1_relat_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('81',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('82',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('83',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('84',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_A )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['79','84','85','86'])).

thf('88',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['76','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('91',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('93',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['88','93','94'])).

thf('96',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X31: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ X31 )
        = ( k1_funct_1 @ sk_D @ X31 ) )
      | ~ ( r2_hidden @ X31 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( sk_C_1 = sk_D )
    | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ),
    inference(condensation,[status(thm)],['98'])).

thf('100',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( X15 = X14 )
      | ( ( k1_funct_1 @ X15 @ ( sk_C @ X14 @ X15 ) )
       != ( k1_funct_1 @ X14 @ ( sk_C @ X14 @ X15 ) ) )
      | ( ( k1_relat_1 @ X15 )
       != ( k1_relat_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('101',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_1 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['82','83'])).

thf('103',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('105',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['75'])).

thf('106',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['91','92'])).

thf('108',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(demod,[status(thm)],['101','102','103','104','105','106','107'])).

thf('109',plain,(
    sk_C_1 = sk_D ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_relset_1 @ X20 @ X21 @ X22 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('112',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    $false ),
    inference(demod,[status(thm)],['0','109','112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZVf7oWJCfu
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:37:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 3.93/4.14  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.93/4.14  % Solved by: fo/fo7.sh
% 3.93/4.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.93/4.14  % done 3067 iterations in 3.693s
% 3.93/4.14  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.93/4.14  % SZS output start Refutation
% 3.93/4.14  thf(sk_D_type, type, sk_D: $i).
% 3.93/4.14  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.93/4.14  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.93/4.14  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.93/4.14  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.93/4.14  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.93/4.14  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.93/4.14  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.93/4.14  thf(sk_B_type, type, sk_B: $i).
% 3.93/4.14  thf(sk_A_type, type, sk_A: $i).
% 3.93/4.14  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.93/4.14  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.93/4.14  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.93/4.14  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.93/4.14  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 3.93/4.14  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.93/4.14  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.93/4.14  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.93/4.14  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.93/4.14  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.93/4.14  thf(t18_funct_2, conjecture,
% 3.93/4.14    (![A:$i,B:$i,C:$i]:
% 3.93/4.14     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.93/4.14         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.93/4.14       ( ![D:$i]:
% 3.93/4.14         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.93/4.14             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.93/4.14           ( ( ![E:$i]:
% 3.93/4.14               ( ( r2_hidden @ E @ A ) =>
% 3.93/4.14                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 3.93/4.14             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 3.93/4.14  thf(zf_stmt_0, negated_conjecture,
% 3.93/4.14    (~( ![A:$i,B:$i,C:$i]:
% 3.93/4.14        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.93/4.14            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.93/4.14          ( ![D:$i]:
% 3.93/4.14            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.93/4.14                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.93/4.14              ( ( ![E:$i]:
% 3.93/4.14                  ( ( r2_hidden @ E @ A ) =>
% 3.93/4.14                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 3.93/4.14                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 3.93/4.14    inference('cnf.neg', [status(esa)], [t18_funct_2])).
% 3.93/4.14  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.93/4.14  thf(d1_funct_2, axiom,
% 3.93/4.14    (![A:$i,B:$i,C:$i]:
% 3.93/4.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.93/4.14       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.93/4.14           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.93/4.14             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.93/4.14         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.93/4.14           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.93/4.14             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.93/4.14  thf(zf_stmt_1, axiom,
% 3.93/4.14    (![B:$i,A:$i]:
% 3.93/4.14     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.93/4.14       ( zip_tseitin_0 @ B @ A ) ))).
% 3.93/4.14  thf('1', plain,
% 3.93/4.14      (![X23 : $i, X24 : $i]:
% 3.93/4.14         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.93/4.14  thf(t113_zfmisc_1, axiom,
% 3.93/4.14    (![A:$i,B:$i]:
% 3.93/4.14     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.93/4.14       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.93/4.14  thf('2', plain,
% 3.93/4.14      (![X5 : $i, X6 : $i]:
% 3.93/4.14         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 3.93/4.14      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.93/4.14  thf('3', plain,
% 3.93/4.14      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 3.93/4.14      inference('simplify', [status(thm)], ['2'])).
% 3.93/4.14  thf('4', plain,
% 3.93/4.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.93/4.14         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 3.93/4.14      inference('sup+', [status(thm)], ['1', '3'])).
% 3.93/4.14  thf('5', plain,
% 3.93/4.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.93/4.14  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.93/4.14  thf(zf_stmt_3, axiom,
% 3.93/4.14    (![C:$i,B:$i,A:$i]:
% 3.93/4.14     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.93/4.14       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.93/4.14  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 3.93/4.14  thf(zf_stmt_5, axiom,
% 3.93/4.14    (![A:$i,B:$i,C:$i]:
% 3.93/4.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.93/4.14       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.93/4.14         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.93/4.14           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.93/4.14             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.93/4.14  thf('6', plain,
% 3.93/4.14      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.93/4.14         (~ (zip_tseitin_0 @ X28 @ X29)
% 3.93/4.14          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 3.93/4.14          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.93/4.14  thf('7', plain,
% 3.93/4.14      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 3.93/4.14      inference('sup-', [status(thm)], ['5', '6'])).
% 3.93/4.14  thf('8', plain,
% 3.93/4.14      (![X0 : $i]:
% 3.93/4.14         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 3.93/4.14          | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 3.93/4.14      inference('sup-', [status(thm)], ['4', '7'])).
% 3.93/4.14  thf('9', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.93/4.14  thf('10', plain,
% 3.93/4.14      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.93/4.14         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 3.93/4.14          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 3.93/4.14          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.93/4.14  thf('11', plain,
% 3.93/4.14      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 3.93/4.14        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 3.93/4.14      inference('sup-', [status(thm)], ['9', '10'])).
% 3.93/4.14  thf('12', plain,
% 3.93/4.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.93/4.14  thf(redefinition_k1_relset_1, axiom,
% 3.93/4.14    (![A:$i,B:$i,C:$i]:
% 3.93/4.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.93/4.14       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.93/4.14  thf('13', plain,
% 3.93/4.14      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.93/4.14         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 3.93/4.14          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 3.93/4.14      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.93/4.14  thf('14', plain,
% 3.93/4.14      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 3.93/4.14      inference('sup-', [status(thm)], ['12', '13'])).
% 3.93/4.14  thf('15', plain,
% 3.93/4.14      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.93/4.14      inference('demod', [status(thm)], ['11', '14'])).
% 3.93/4.14  thf('16', plain,
% 3.93/4.14      (![X0 : $i]:
% 3.93/4.14         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 3.93/4.14          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.93/4.14      inference('sup-', [status(thm)], ['8', '15'])).
% 3.93/4.14  thf('17', plain,
% 3.93/4.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.93/4.14  thf(t3_subset, axiom,
% 3.93/4.14    (![A:$i,B:$i]:
% 3.93/4.14     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.93/4.14  thf('18', plain,
% 3.93/4.14      (![X7 : $i, X8 : $i]:
% 3.93/4.14         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 3.93/4.14      inference('cnf', [status(esa)], [t3_subset])).
% 3.93/4.14  thf('19', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 3.93/4.14      inference('sup-', [status(thm)], ['17', '18'])).
% 3.93/4.14  thf(d10_xboole_0, axiom,
% 3.93/4.14    (![A:$i,B:$i]:
% 3.93/4.14     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.93/4.14  thf('20', plain,
% 3.93/4.14      (![X0 : $i, X2 : $i]:
% 3.93/4.14         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.93/4.14      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.93/4.14  thf('21', plain,
% 3.93/4.14      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_D)
% 3.93/4.14        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 3.93/4.14      inference('sup-', [status(thm)], ['19', '20'])).
% 3.93/4.14  thf('22', plain,
% 3.93/4.14      ((~ (r1_tarski @ k1_xboole_0 @ sk_D)
% 3.93/4.14        | ((sk_A) = (k1_relat_1 @ sk_D))
% 3.93/4.14        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 3.93/4.14      inference('sup-', [status(thm)], ['16', '21'])).
% 3.93/4.14  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 3.93/4.14  thf('23', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 3.93/4.14      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.93/4.14  thf('24', plain,
% 3.93/4.14      ((((sk_A) = (k1_relat_1 @ sk_D)) | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 3.93/4.14      inference('demod', [status(thm)], ['22', '23'])).
% 3.93/4.14  thf('25', plain,
% 3.93/4.14      (![X0 : $i]:
% 3.93/4.14         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 3.93/4.14          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.93/4.14      inference('sup-', [status(thm)], ['8', '15'])).
% 3.93/4.14  thf('26', plain,
% 3.93/4.14      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.93/4.14  thf('27', plain,
% 3.93/4.14      (![X7 : $i, X8 : $i]:
% 3.93/4.14         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 3.93/4.14      inference('cnf', [status(esa)], [t3_subset])).
% 3.93/4.14  thf('28', plain, ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 3.93/4.14      inference('sup-', [status(thm)], ['26', '27'])).
% 3.93/4.14  thf('29', plain,
% 3.93/4.14      (![X0 : $i, X2 : $i]:
% 3.93/4.14         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.93/4.14      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.93/4.14  thf('30', plain,
% 3.93/4.14      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C_1)
% 3.93/4.14        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 3.93/4.14      inference('sup-', [status(thm)], ['28', '29'])).
% 3.93/4.14  thf('31', plain,
% 3.93/4.14      ((~ (r1_tarski @ k1_xboole_0 @ sk_C_1)
% 3.93/4.14        | ((sk_A) = (k1_relat_1 @ sk_D))
% 3.93/4.14        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 3.93/4.14      inference('sup-', [status(thm)], ['25', '30'])).
% 3.93/4.14  thf('32', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 3.93/4.14      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.93/4.14  thf('33', plain,
% 3.93/4.14      ((((sk_A) = (k1_relat_1 @ sk_D))
% 3.93/4.14        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 3.93/4.14      inference('demod', [status(thm)], ['31', '32'])).
% 3.93/4.14  thf('34', plain,
% 3.93/4.14      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 3.93/4.14      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.93/4.14  thf('35', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.93/4.14      inference('simplify', [status(thm)], ['34'])).
% 3.93/4.14  thf('36', plain,
% 3.93/4.14      (![X7 : $i, X9 : $i]:
% 3.93/4.14         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 3.93/4.14      inference('cnf', [status(esa)], [t3_subset])).
% 3.93/4.14  thf('37', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 3.93/4.14      inference('sup-', [status(thm)], ['35', '36'])).
% 3.93/4.14  thf('38', plain,
% 3.93/4.14      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.93/4.14         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 3.93/4.14          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 3.93/4.14      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.93/4.14  thf('39', plain,
% 3.93/4.14      (![X0 : $i, X1 : $i]:
% 3.93/4.14         ((k1_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0))
% 3.93/4.14           = (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 3.93/4.14      inference('sup-', [status(thm)], ['37', '38'])).
% 3.93/4.14  thf('40', plain,
% 3.93/4.14      ((((k1_relset_1 @ sk_A @ sk_B @ sk_C_1)
% 3.93/4.14          = (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 3.93/4.14        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.93/4.14      inference('sup+', [status(thm)], ['33', '39'])).
% 3.93/4.14  thf('41', plain,
% 3.93/4.14      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.93/4.14  thf('42', plain,
% 3.93/4.14      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.93/4.14         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 3.93/4.14          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 3.93/4.14      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.93/4.14  thf('43', plain,
% 3.93/4.14      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 3.93/4.14      inference('sup-', [status(thm)], ['41', '42'])).
% 3.93/4.14  thf('44', plain,
% 3.93/4.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.93/4.14         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 3.93/4.14      inference('sup+', [status(thm)], ['1', '3'])).
% 3.93/4.14  thf('45', plain,
% 3.93/4.14      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.93/4.14  thf('46', plain,
% 3.93/4.14      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.93/4.14         (~ (zip_tseitin_0 @ X28 @ X29)
% 3.93/4.14          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 3.93/4.14          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.93/4.14  thf('47', plain,
% 3.93/4.14      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 3.93/4.14        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 3.93/4.14      inference('sup-', [status(thm)], ['45', '46'])).
% 3.93/4.14  thf('48', plain,
% 3.93/4.14      (![X0 : $i]:
% 3.93/4.14         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 3.93/4.14          | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 3.93/4.14      inference('sup-', [status(thm)], ['44', '47'])).
% 3.93/4.14  thf('49', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.93/4.14  thf('50', plain,
% 3.93/4.14      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.93/4.14         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 3.93/4.14          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 3.93/4.14          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.93/4.14  thf('51', plain,
% 3.93/4.14      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 3.93/4.14        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 3.93/4.14      inference('sup-', [status(thm)], ['49', '50'])).
% 3.93/4.14  thf('52', plain,
% 3.93/4.14      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 3.93/4.14      inference('sup-', [status(thm)], ['41', '42'])).
% 3.93/4.14  thf('53', plain,
% 3.93/4.14      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 3.93/4.14        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 3.93/4.14      inference('demod', [status(thm)], ['51', '52'])).
% 3.93/4.14  thf('54', plain,
% 3.93/4.14      (![X0 : $i]:
% 3.93/4.14         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 3.93/4.14          | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 3.93/4.14      inference('sup-', [status(thm)], ['48', '53'])).
% 3.93/4.14  thf('55', plain,
% 3.93/4.14      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_D)
% 3.93/4.14        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 3.93/4.14      inference('sup-', [status(thm)], ['19', '20'])).
% 3.93/4.14  thf('56', plain,
% 3.93/4.14      ((~ (r1_tarski @ k1_xboole_0 @ sk_D)
% 3.93/4.14        | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 3.93/4.14        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 3.93/4.14      inference('sup-', [status(thm)], ['54', '55'])).
% 3.93/4.14  thf('57', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 3.93/4.14      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.93/4.14  thf('58', plain,
% 3.93/4.14      ((((sk_A) = (k1_relat_1 @ sk_C_1))
% 3.93/4.14        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 3.93/4.14      inference('demod', [status(thm)], ['56', '57'])).
% 3.93/4.14  thf('59', plain,
% 3.93/4.14      (![X0 : $i]:
% 3.93/4.14         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 3.93/4.14          | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 3.93/4.14      inference('sup-', [status(thm)], ['48', '53'])).
% 3.93/4.14  thf('60', plain,
% 3.93/4.14      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C_1)
% 3.93/4.14        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 3.93/4.14      inference('sup-', [status(thm)], ['28', '29'])).
% 3.93/4.14  thf('61', plain,
% 3.93/4.14      ((~ (r1_tarski @ k1_xboole_0 @ sk_C_1)
% 3.93/4.14        | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 3.93/4.14        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 3.93/4.14      inference('sup-', [status(thm)], ['59', '60'])).
% 3.93/4.14  thf('62', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 3.93/4.14      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.93/4.14  thf('63', plain,
% 3.93/4.14      ((((sk_A) = (k1_relat_1 @ sk_C_1))
% 3.93/4.14        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 3.93/4.14      inference('demod', [status(thm)], ['61', '62'])).
% 3.93/4.14  thf('64', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 3.93/4.14      inference('sup-', [status(thm)], ['35', '36'])).
% 3.93/4.14  thf(redefinition_r2_relset_1, axiom,
% 3.93/4.14    (![A:$i,B:$i,C:$i,D:$i]:
% 3.93/4.14     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.93/4.14         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.93/4.14       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.93/4.14  thf('65', plain,
% 3.93/4.14      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 3.93/4.14         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 3.93/4.14          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 3.93/4.14          | (r2_relset_1 @ X20 @ X21 @ X19 @ X22)
% 3.93/4.14          | ((X19) != (X22)))),
% 3.93/4.14      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.93/4.14  thf('66', plain,
% 3.93/4.14      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.93/4.14         ((r2_relset_1 @ X20 @ X21 @ X22 @ X22)
% 3.93/4.14          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 3.93/4.14      inference('simplify', [status(thm)], ['65'])).
% 3.93/4.14  thf('67', plain,
% 3.93/4.14      (![X0 : $i, X1 : $i]:
% 3.93/4.14         (r2_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 3.93/4.14          (k2_zfmisc_1 @ X1 @ X0))),
% 3.93/4.14      inference('sup-', [status(thm)], ['64', '66'])).
% 3.93/4.14  thf('68', plain,
% 3.93/4.14      (((r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 3.93/4.14        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 3.93/4.14      inference('sup+', [status(thm)], ['63', '67'])).
% 3.93/4.14  thf('69', plain,
% 3.93/4.14      (((r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)
% 3.93/4.14        | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 3.93/4.14        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 3.93/4.14      inference('sup+', [status(thm)], ['58', '68'])).
% 3.93/4.14  thf('70', plain,
% 3.93/4.14      ((((sk_A) = (k1_relat_1 @ sk_C_1))
% 3.93/4.14        | (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D))),
% 3.93/4.14      inference('simplify', [status(thm)], ['69'])).
% 3.93/4.14  thf('71', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.93/4.14  thf('72', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 3.93/4.14      inference('clc', [status(thm)], ['70', '71'])).
% 3.93/4.14  thf('73', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_A))),
% 3.93/4.14      inference('demod', [status(thm)], ['43', '72'])).
% 3.93/4.14  thf('74', plain,
% 3.93/4.14      ((((sk_A) = (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 3.93/4.14        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.93/4.14      inference('demod', [status(thm)], ['40', '73'])).
% 3.93/4.14  thf('75', plain,
% 3.93/4.14      ((((sk_A) = (k1_relat_1 @ sk_D))
% 3.93/4.14        | ((sk_A) = (k1_relat_1 @ sk_D))
% 3.93/4.14        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.93/4.14      inference('sup+', [status(thm)], ['24', '74'])).
% 3.93/4.14  thf('76', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 3.93/4.14      inference('simplify', [status(thm)], ['75'])).
% 3.93/4.14  thf('77', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 3.93/4.14      inference('clc', [status(thm)], ['70', '71'])).
% 3.93/4.14  thf(t9_funct_1, axiom,
% 3.93/4.14    (![A:$i]:
% 3.93/4.14     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.93/4.14       ( ![B:$i]:
% 3.93/4.14         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.93/4.14           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 3.93/4.14               ( ![C:$i]:
% 3.93/4.14                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 3.93/4.14                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 3.93/4.14             ( ( A ) = ( B ) ) ) ) ) ))).
% 3.93/4.14  thf('78', plain,
% 3.93/4.14      (![X14 : $i, X15 : $i]:
% 3.93/4.14         (~ (v1_relat_1 @ X14)
% 3.93/4.14          | ~ (v1_funct_1 @ X14)
% 3.93/4.14          | ((X15) = (X14))
% 3.93/4.14          | (r2_hidden @ (sk_C @ X14 @ X15) @ (k1_relat_1 @ X15))
% 3.93/4.14          | ((k1_relat_1 @ X15) != (k1_relat_1 @ X14))
% 3.93/4.14          | ~ (v1_funct_1 @ X15)
% 3.93/4.14          | ~ (v1_relat_1 @ X15))),
% 3.93/4.14      inference('cnf', [status(esa)], [t9_funct_1])).
% 3.93/4.14  thf('79', plain,
% 3.93/4.14      (![X0 : $i]:
% 3.93/4.14         (((sk_A) != (k1_relat_1 @ X0))
% 3.93/4.14          | ~ (v1_relat_1 @ sk_C_1)
% 3.93/4.14          | ~ (v1_funct_1 @ sk_C_1)
% 3.93/4.14          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 3.93/4.14          | ((sk_C_1) = (X0))
% 3.93/4.14          | ~ (v1_funct_1 @ X0)
% 3.93/4.14          | ~ (v1_relat_1 @ X0))),
% 3.93/4.14      inference('sup-', [status(thm)], ['77', '78'])).
% 3.93/4.14  thf('80', plain,
% 3.93/4.14      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.93/4.14  thf(cc2_relat_1, axiom,
% 3.93/4.14    (![A:$i]:
% 3.93/4.14     ( ( v1_relat_1 @ A ) =>
% 3.93/4.14       ( ![B:$i]:
% 3.93/4.14         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 3.93/4.14  thf('81', plain,
% 3.93/4.14      (![X10 : $i, X11 : $i]:
% 3.93/4.14         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 3.93/4.14          | (v1_relat_1 @ X10)
% 3.93/4.14          | ~ (v1_relat_1 @ X11))),
% 3.93/4.14      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.93/4.14  thf('82', plain,
% 3.93/4.14      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_1))),
% 3.93/4.14      inference('sup-', [status(thm)], ['80', '81'])).
% 3.93/4.14  thf(fc6_relat_1, axiom,
% 3.93/4.14    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 3.93/4.14  thf('83', plain,
% 3.93/4.14      (![X12 : $i, X13 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X12 @ X13))),
% 3.93/4.14      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.93/4.14  thf('84', plain, ((v1_relat_1 @ sk_C_1)),
% 3.93/4.14      inference('demod', [status(thm)], ['82', '83'])).
% 3.93/4.14  thf('85', plain, ((v1_funct_1 @ sk_C_1)),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.93/4.14  thf('86', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 3.93/4.14      inference('clc', [status(thm)], ['70', '71'])).
% 3.93/4.14  thf('87', plain,
% 3.93/4.14      (![X0 : $i]:
% 3.93/4.14         (((sk_A) != (k1_relat_1 @ X0))
% 3.93/4.14          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_A)
% 3.93/4.14          | ((sk_C_1) = (X0))
% 3.93/4.14          | ~ (v1_funct_1 @ X0)
% 3.93/4.14          | ~ (v1_relat_1 @ X0))),
% 3.93/4.14      inference('demod', [status(thm)], ['79', '84', '85', '86'])).
% 3.93/4.14  thf('88', plain,
% 3.93/4.14      ((((sk_A) != (sk_A))
% 3.93/4.14        | ~ (v1_relat_1 @ sk_D)
% 3.93/4.14        | ~ (v1_funct_1 @ sk_D)
% 3.93/4.14        | ((sk_C_1) = (sk_D))
% 3.93/4.14        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 3.93/4.14      inference('sup-', [status(thm)], ['76', '87'])).
% 3.93/4.14  thf('89', plain,
% 3.93/4.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.93/4.14  thf('90', plain,
% 3.93/4.14      (![X10 : $i, X11 : $i]:
% 3.93/4.14         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 3.93/4.14          | (v1_relat_1 @ X10)
% 3.93/4.14          | ~ (v1_relat_1 @ X11))),
% 3.93/4.14      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.93/4.14  thf('91', plain,
% 3.93/4.14      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 3.93/4.14      inference('sup-', [status(thm)], ['89', '90'])).
% 3.93/4.14  thf('92', plain,
% 3.93/4.14      (![X12 : $i, X13 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X12 @ X13))),
% 3.93/4.14      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.93/4.14  thf('93', plain, ((v1_relat_1 @ sk_D)),
% 3.93/4.14      inference('demod', [status(thm)], ['91', '92'])).
% 3.93/4.14  thf('94', plain, ((v1_funct_1 @ sk_D)),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.93/4.14  thf('95', plain,
% 3.93/4.14      ((((sk_A) != (sk_A))
% 3.93/4.14        | ((sk_C_1) = (sk_D))
% 3.93/4.14        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 3.93/4.14      inference('demod', [status(thm)], ['88', '93', '94'])).
% 3.93/4.14  thf('96', plain,
% 3.93/4.14      (((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A) | ((sk_C_1) = (sk_D)))),
% 3.93/4.14      inference('simplify', [status(thm)], ['95'])).
% 3.93/4.14  thf('97', plain,
% 3.93/4.14      (![X31 : $i]:
% 3.93/4.14         (((k1_funct_1 @ sk_C_1 @ X31) = (k1_funct_1 @ sk_D @ X31))
% 3.93/4.14          | ~ (r2_hidden @ X31 @ sk_A))),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.93/4.14  thf('98', plain,
% 3.93/4.14      ((((sk_C_1) = (sk_D))
% 3.93/4.14        | ((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 3.93/4.14            = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))))),
% 3.93/4.14      inference('sup-', [status(thm)], ['96', '97'])).
% 3.93/4.14  thf('99', plain,
% 3.93/4.14      (((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 3.93/4.14         = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))),
% 3.93/4.14      inference('condensation', [status(thm)], ['98'])).
% 3.93/4.14  thf('100', plain,
% 3.93/4.14      (![X14 : $i, X15 : $i]:
% 3.93/4.14         (~ (v1_relat_1 @ X14)
% 3.93/4.14          | ~ (v1_funct_1 @ X14)
% 3.93/4.14          | ((X15) = (X14))
% 3.93/4.14          | ((k1_funct_1 @ X15 @ (sk_C @ X14 @ X15))
% 3.93/4.14              != (k1_funct_1 @ X14 @ (sk_C @ X14 @ X15)))
% 3.93/4.14          | ((k1_relat_1 @ X15) != (k1_relat_1 @ X14))
% 3.93/4.14          | ~ (v1_funct_1 @ X15)
% 3.93/4.14          | ~ (v1_relat_1 @ X15))),
% 3.93/4.14      inference('cnf', [status(esa)], [t9_funct_1])).
% 3.93/4.14  thf('101', plain,
% 3.93/4.14      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 3.93/4.14          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 3.93/4.14        | ~ (v1_relat_1 @ sk_C_1)
% 3.93/4.14        | ~ (v1_funct_1 @ sk_C_1)
% 3.93/4.14        | ((k1_relat_1 @ sk_C_1) != (k1_relat_1 @ sk_D))
% 3.93/4.14        | ((sk_C_1) = (sk_D))
% 3.93/4.14        | ~ (v1_funct_1 @ sk_D)
% 3.93/4.14        | ~ (v1_relat_1 @ sk_D))),
% 3.93/4.14      inference('sup-', [status(thm)], ['99', '100'])).
% 3.93/4.14  thf('102', plain, ((v1_relat_1 @ sk_C_1)),
% 3.93/4.14      inference('demod', [status(thm)], ['82', '83'])).
% 3.93/4.14  thf('103', plain, ((v1_funct_1 @ sk_C_1)),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.93/4.14  thf('104', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 3.93/4.14      inference('clc', [status(thm)], ['70', '71'])).
% 3.93/4.14  thf('105', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 3.93/4.14      inference('simplify', [status(thm)], ['75'])).
% 3.93/4.14  thf('106', plain, ((v1_funct_1 @ sk_D)),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.93/4.14  thf('107', plain, ((v1_relat_1 @ sk_D)),
% 3.93/4.14      inference('demod', [status(thm)], ['91', '92'])).
% 3.93/4.14  thf('108', plain,
% 3.93/4.14      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 3.93/4.14          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 3.93/4.14        | ((sk_A) != (sk_A))
% 3.93/4.14        | ((sk_C_1) = (sk_D)))),
% 3.93/4.14      inference('demod', [status(thm)],
% 3.93/4.14                ['101', '102', '103', '104', '105', '106', '107'])).
% 3.93/4.14  thf('109', plain, (((sk_C_1) = (sk_D))),
% 3.93/4.14      inference('simplify', [status(thm)], ['108'])).
% 3.93/4.14  thf('110', plain,
% 3.93/4.14      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.93/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.93/4.14  thf('111', plain,
% 3.93/4.14      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.93/4.14         ((r2_relset_1 @ X20 @ X21 @ X22 @ X22)
% 3.93/4.14          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 3.93/4.14      inference('simplify', [status(thm)], ['65'])).
% 3.93/4.14  thf('112', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1)),
% 3.93/4.14      inference('sup-', [status(thm)], ['110', '111'])).
% 3.93/4.14  thf('113', plain, ($false),
% 3.93/4.14      inference('demod', [status(thm)], ['0', '109', '112'])).
% 3.93/4.14  
% 3.93/4.14  % SZS output end Refutation
% 3.93/4.14  
% 3.93/4.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
