%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.G3JjPntBjs

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:36 EST 2020

% Result     : Theorem 4.86s
% Output     : Refutation 4.86s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 772 expanded)
%              Number of leaves         :   35 ( 239 expanded)
%              Depth                    :   24
%              Number of atoms          : 1187 (11243 expanded)
%              Number of equality atoms :  119 ( 686 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

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
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ( X24
        = ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ( X24
        = ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 )
      | ( X18 != X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('66',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_relset_1 @ X19 @ X20 @ X21 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( X11 = X10 )
      | ( r2_hidden @ ( sk_C @ X10 @ X11 ) @ ( k1_relat_1 @ X11 ) )
      | ( ( k1_relat_1 @ X11 )
       != ( k1_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('81',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('82',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_A )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['79','82','83','84'])).

thf('86',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['76','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('89',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['86','89','90'])).

thf('92',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X30: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ X30 )
        = ( k1_funct_1 @ sk_D @ X30 ) )
      | ~ ( r2_hidden @ X30 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( sk_C_1 = sk_D )
    | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ),
    inference(condensation,[status(thm)],['94'])).

thf('96',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( X11 = X10 )
      | ( ( k1_funct_1 @ X11 @ ( sk_C @ X10 @ X11 ) )
       != ( k1_funct_1 @ X10 @ ( sk_C @ X10 @ X11 ) ) )
      | ( ( k1_relat_1 @ X11 )
       != ( k1_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('97',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_1 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['80','81'])).

thf('99',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('101',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['75'])).

thf('102',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['87','88'])).

thf('104',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(demod,[status(thm)],['97','98','99','100','101','102','103'])).

thf('105',plain,(
    sk_C_1 = sk_D ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_relset_1 @ X19 @ X20 @ X21 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('108',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    $false ),
    inference(demod,[status(thm)],['0','105','108'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.G3JjPntBjs
% 0.13/0.36  % Computer   : n005.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 15:05:33 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 4.86/5.04  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.86/5.04  % Solved by: fo/fo7.sh
% 4.86/5.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.86/5.04  % done 3106 iterations in 4.572s
% 4.86/5.04  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.86/5.04  % SZS output start Refutation
% 4.86/5.04  thf(sk_A_type, type, sk_A: $i).
% 4.86/5.04  thf(sk_C_1_type, type, sk_C_1: $i).
% 4.86/5.04  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.86/5.04  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.86/5.04  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.86/5.04  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.86/5.04  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 4.86/5.04  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.86/5.04  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.86/5.04  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 4.86/5.04  thf(sk_D_type, type, sk_D: $i).
% 4.86/5.04  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 4.86/5.04  thf(sk_B_type, type, sk_B: $i).
% 4.86/5.04  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.86/5.04  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.86/5.04  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.86/5.04  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 4.86/5.04  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.86/5.04  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.86/5.04  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 4.86/5.04  thf(t18_funct_2, conjecture,
% 4.86/5.04    (![A:$i,B:$i,C:$i]:
% 4.86/5.04     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.86/5.04         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.86/5.04       ( ![D:$i]:
% 4.86/5.04         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 4.86/5.04             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.86/5.04           ( ( ![E:$i]:
% 4.86/5.04               ( ( r2_hidden @ E @ A ) =>
% 4.86/5.04                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 4.86/5.04             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 4.86/5.04  thf(zf_stmt_0, negated_conjecture,
% 4.86/5.04    (~( ![A:$i,B:$i,C:$i]:
% 4.86/5.04        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.86/5.04            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.86/5.04          ( ![D:$i]:
% 4.86/5.04            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 4.86/5.04                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.86/5.04              ( ( ![E:$i]:
% 4.86/5.04                  ( ( r2_hidden @ E @ A ) =>
% 4.86/5.04                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 4.86/5.04                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 4.86/5.04    inference('cnf.neg', [status(esa)], [t18_funct_2])).
% 4.86/5.04  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)),
% 4.86/5.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.04  thf(d1_funct_2, axiom,
% 4.86/5.04    (![A:$i,B:$i,C:$i]:
% 4.86/5.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.86/5.04       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.86/5.04           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 4.86/5.04             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 4.86/5.04         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.86/5.04           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 4.86/5.04             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 4.86/5.04  thf(zf_stmt_1, axiom,
% 4.86/5.04    (![B:$i,A:$i]:
% 4.86/5.04     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.86/5.04       ( zip_tseitin_0 @ B @ A ) ))).
% 4.86/5.04  thf('1', plain,
% 4.86/5.04      (![X22 : $i, X23 : $i]:
% 4.86/5.04         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 4.86/5.04      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.86/5.04  thf(t113_zfmisc_1, axiom,
% 4.86/5.04    (![A:$i,B:$i]:
% 4.86/5.04     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 4.86/5.04       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 4.86/5.04  thf('2', plain,
% 4.86/5.04      (![X5 : $i, X6 : $i]:
% 4.86/5.04         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 4.86/5.04      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 4.86/5.04  thf('3', plain,
% 4.86/5.04      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 4.86/5.04      inference('simplify', [status(thm)], ['2'])).
% 4.86/5.04  thf('4', plain,
% 4.86/5.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.86/5.04         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 4.86/5.04      inference('sup+', [status(thm)], ['1', '3'])).
% 4.86/5.04  thf('5', plain,
% 4.86/5.04      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.86/5.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.04  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 4.86/5.04  thf(zf_stmt_3, axiom,
% 4.86/5.04    (![C:$i,B:$i,A:$i]:
% 4.86/5.04     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 4.86/5.04       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 4.86/5.04  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 4.86/5.04  thf(zf_stmt_5, axiom,
% 4.86/5.04    (![A:$i,B:$i,C:$i]:
% 4.86/5.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.86/5.04       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 4.86/5.04         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.86/5.04           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 4.86/5.04             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 4.86/5.04  thf('6', plain,
% 4.86/5.04      (![X27 : $i, X28 : $i, X29 : $i]:
% 4.86/5.04         (~ (zip_tseitin_0 @ X27 @ X28)
% 4.86/5.04          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 4.86/5.04          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 4.86/5.04      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.86/5.04  thf('7', plain,
% 4.86/5.04      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 4.86/5.04      inference('sup-', [status(thm)], ['5', '6'])).
% 4.86/5.04  thf('8', plain,
% 4.86/5.04      (![X0 : $i]:
% 4.86/5.04         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 4.86/5.04          | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 4.86/5.04      inference('sup-', [status(thm)], ['4', '7'])).
% 4.86/5.04  thf('9', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 4.86/5.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.04  thf('10', plain,
% 4.86/5.04      (![X24 : $i, X25 : $i, X26 : $i]:
% 4.86/5.04         (~ (v1_funct_2 @ X26 @ X24 @ X25)
% 4.86/5.04          | ((X24) = (k1_relset_1 @ X24 @ X25 @ X26))
% 4.86/5.04          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 4.86/5.04      inference('cnf', [status(esa)], [zf_stmt_3])).
% 4.86/5.04  thf('11', plain,
% 4.86/5.04      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 4.86/5.04        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 4.86/5.04      inference('sup-', [status(thm)], ['9', '10'])).
% 4.86/5.04  thf('12', plain,
% 4.86/5.04      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.86/5.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.04  thf(redefinition_k1_relset_1, axiom,
% 4.86/5.04    (![A:$i,B:$i,C:$i]:
% 4.86/5.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.86/5.04       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 4.86/5.04  thf('13', plain,
% 4.86/5.04      (![X15 : $i, X16 : $i, X17 : $i]:
% 4.86/5.04         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 4.86/5.04          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 4.86/5.04      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.86/5.04  thf('14', plain,
% 4.86/5.04      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 4.86/5.04      inference('sup-', [status(thm)], ['12', '13'])).
% 4.86/5.04  thf('15', plain,
% 4.86/5.04      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 4.86/5.04      inference('demod', [status(thm)], ['11', '14'])).
% 4.86/5.04  thf('16', plain,
% 4.86/5.04      (![X0 : $i]:
% 4.86/5.04         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 4.86/5.04          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 4.86/5.04      inference('sup-', [status(thm)], ['8', '15'])).
% 4.86/5.04  thf('17', plain,
% 4.86/5.04      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.86/5.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.04  thf(t3_subset, axiom,
% 4.86/5.04    (![A:$i,B:$i]:
% 4.86/5.04     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.86/5.04  thf('18', plain,
% 4.86/5.04      (![X7 : $i, X8 : $i]:
% 4.86/5.04         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 4.86/5.04      inference('cnf', [status(esa)], [t3_subset])).
% 4.86/5.04  thf('19', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 4.86/5.04      inference('sup-', [status(thm)], ['17', '18'])).
% 4.86/5.04  thf(d10_xboole_0, axiom,
% 4.86/5.04    (![A:$i,B:$i]:
% 4.86/5.04     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.86/5.04  thf('20', plain,
% 4.86/5.04      (![X0 : $i, X2 : $i]:
% 4.86/5.04         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 4.86/5.04      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.86/5.04  thf('21', plain,
% 4.86/5.04      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_D)
% 4.86/5.04        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 4.86/5.04      inference('sup-', [status(thm)], ['19', '20'])).
% 4.86/5.04  thf('22', plain,
% 4.86/5.04      ((~ (r1_tarski @ k1_xboole_0 @ sk_D)
% 4.86/5.04        | ((sk_A) = (k1_relat_1 @ sk_D))
% 4.86/5.04        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 4.86/5.04      inference('sup-', [status(thm)], ['16', '21'])).
% 4.86/5.04  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 4.86/5.04  thf('23', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 4.86/5.04      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.86/5.04  thf('24', plain,
% 4.86/5.04      ((((sk_A) = (k1_relat_1 @ sk_D)) | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 4.86/5.04      inference('demod', [status(thm)], ['22', '23'])).
% 4.86/5.04  thf('25', plain,
% 4.86/5.04      (![X0 : $i]:
% 4.86/5.04         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 4.86/5.04          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 4.86/5.04      inference('sup-', [status(thm)], ['8', '15'])).
% 4.86/5.04  thf('26', plain,
% 4.86/5.04      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.86/5.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.04  thf('27', plain,
% 4.86/5.04      (![X7 : $i, X8 : $i]:
% 4.86/5.04         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 4.86/5.04      inference('cnf', [status(esa)], [t3_subset])).
% 4.86/5.04  thf('28', plain, ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 4.86/5.04      inference('sup-', [status(thm)], ['26', '27'])).
% 4.86/5.04  thf('29', plain,
% 4.86/5.04      (![X0 : $i, X2 : $i]:
% 4.86/5.04         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 4.86/5.04      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.86/5.04  thf('30', plain,
% 4.86/5.04      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C_1)
% 4.86/5.04        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 4.86/5.04      inference('sup-', [status(thm)], ['28', '29'])).
% 4.86/5.04  thf('31', plain,
% 4.86/5.04      ((~ (r1_tarski @ k1_xboole_0 @ sk_C_1)
% 4.86/5.04        | ((sk_A) = (k1_relat_1 @ sk_D))
% 4.86/5.04        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 4.86/5.04      inference('sup-', [status(thm)], ['25', '30'])).
% 4.86/5.04  thf('32', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 4.86/5.04      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.86/5.04  thf('33', plain,
% 4.86/5.04      ((((sk_A) = (k1_relat_1 @ sk_D))
% 4.86/5.04        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 4.86/5.04      inference('demod', [status(thm)], ['31', '32'])).
% 4.86/5.04  thf('34', plain,
% 4.86/5.04      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 4.86/5.04      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.86/5.04  thf('35', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 4.86/5.04      inference('simplify', [status(thm)], ['34'])).
% 4.86/5.04  thf('36', plain,
% 4.86/5.04      (![X7 : $i, X9 : $i]:
% 4.86/5.04         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 4.86/5.04      inference('cnf', [status(esa)], [t3_subset])).
% 4.86/5.04  thf('37', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 4.86/5.04      inference('sup-', [status(thm)], ['35', '36'])).
% 4.86/5.04  thf('38', plain,
% 4.86/5.04      (![X15 : $i, X16 : $i, X17 : $i]:
% 4.86/5.04         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 4.86/5.04          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 4.86/5.04      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.86/5.04  thf('39', plain,
% 4.86/5.04      (![X0 : $i, X1 : $i]:
% 4.86/5.04         ((k1_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0))
% 4.86/5.04           = (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 4.86/5.04      inference('sup-', [status(thm)], ['37', '38'])).
% 4.86/5.04  thf('40', plain,
% 4.86/5.04      ((((k1_relset_1 @ sk_A @ sk_B @ sk_C_1)
% 4.86/5.04          = (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 4.86/5.04        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 4.86/5.04      inference('sup+', [status(thm)], ['33', '39'])).
% 4.86/5.04  thf('41', plain,
% 4.86/5.04      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.86/5.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.04  thf('42', plain,
% 4.86/5.04      (![X15 : $i, X16 : $i, X17 : $i]:
% 4.86/5.04         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 4.86/5.04          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 4.86/5.04      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.86/5.04  thf('43', plain,
% 4.86/5.04      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 4.86/5.04      inference('sup-', [status(thm)], ['41', '42'])).
% 4.86/5.04  thf('44', plain,
% 4.86/5.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.86/5.04         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 4.86/5.04      inference('sup+', [status(thm)], ['1', '3'])).
% 4.86/5.04  thf('45', plain,
% 4.86/5.04      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.86/5.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.04  thf('46', plain,
% 4.86/5.04      (![X27 : $i, X28 : $i, X29 : $i]:
% 4.86/5.04         (~ (zip_tseitin_0 @ X27 @ X28)
% 4.86/5.04          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 4.86/5.04          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 4.86/5.04      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.86/5.04  thf('47', plain,
% 4.86/5.04      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 4.86/5.04        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 4.86/5.04      inference('sup-', [status(thm)], ['45', '46'])).
% 4.86/5.04  thf('48', plain,
% 4.86/5.04      (![X0 : $i]:
% 4.86/5.04         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 4.86/5.04          | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 4.86/5.04      inference('sup-', [status(thm)], ['44', '47'])).
% 4.86/5.04  thf('49', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 4.86/5.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.04  thf('50', plain,
% 4.86/5.04      (![X24 : $i, X25 : $i, X26 : $i]:
% 4.86/5.04         (~ (v1_funct_2 @ X26 @ X24 @ X25)
% 4.86/5.04          | ((X24) = (k1_relset_1 @ X24 @ X25 @ X26))
% 4.86/5.04          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 4.86/5.04      inference('cnf', [status(esa)], [zf_stmt_3])).
% 4.86/5.04  thf('51', plain,
% 4.86/5.04      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 4.86/5.04        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 4.86/5.04      inference('sup-', [status(thm)], ['49', '50'])).
% 4.86/5.04  thf('52', plain,
% 4.86/5.04      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 4.86/5.04      inference('sup-', [status(thm)], ['41', '42'])).
% 4.86/5.04  thf('53', plain,
% 4.86/5.04      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 4.86/5.04        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 4.86/5.04      inference('demod', [status(thm)], ['51', '52'])).
% 4.86/5.04  thf('54', plain,
% 4.86/5.04      (![X0 : $i]:
% 4.86/5.04         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 4.86/5.04          | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 4.86/5.04      inference('sup-', [status(thm)], ['48', '53'])).
% 4.86/5.04  thf('55', plain,
% 4.86/5.04      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_D)
% 4.86/5.04        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 4.86/5.04      inference('sup-', [status(thm)], ['19', '20'])).
% 4.86/5.04  thf('56', plain,
% 4.86/5.04      ((~ (r1_tarski @ k1_xboole_0 @ sk_D)
% 4.86/5.04        | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 4.86/5.04        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 4.86/5.04      inference('sup-', [status(thm)], ['54', '55'])).
% 4.86/5.04  thf('57', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 4.86/5.04      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.86/5.04  thf('58', plain,
% 4.86/5.04      ((((sk_A) = (k1_relat_1 @ sk_C_1))
% 4.86/5.04        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 4.86/5.04      inference('demod', [status(thm)], ['56', '57'])).
% 4.86/5.04  thf('59', plain,
% 4.86/5.04      (![X0 : $i]:
% 4.86/5.04         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 4.86/5.04          | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 4.86/5.04      inference('sup-', [status(thm)], ['48', '53'])).
% 4.86/5.04  thf('60', plain,
% 4.86/5.04      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C_1)
% 4.86/5.04        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 4.86/5.04      inference('sup-', [status(thm)], ['28', '29'])).
% 4.86/5.04  thf('61', plain,
% 4.86/5.04      ((~ (r1_tarski @ k1_xboole_0 @ sk_C_1)
% 4.86/5.04        | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 4.86/5.04        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 4.86/5.04      inference('sup-', [status(thm)], ['59', '60'])).
% 4.86/5.04  thf('62', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 4.86/5.04      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.86/5.04  thf('63', plain,
% 4.86/5.04      ((((sk_A) = (k1_relat_1 @ sk_C_1))
% 4.86/5.04        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 4.86/5.04      inference('demod', [status(thm)], ['61', '62'])).
% 4.86/5.04  thf('64', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 4.86/5.04      inference('sup-', [status(thm)], ['35', '36'])).
% 4.86/5.04  thf(redefinition_r2_relset_1, axiom,
% 4.86/5.04    (![A:$i,B:$i,C:$i,D:$i]:
% 4.86/5.04     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.86/5.04         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.86/5.04       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 4.86/5.04  thf('65', plain,
% 4.86/5.04      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 4.86/5.04         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 4.86/5.04          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 4.86/5.04          | (r2_relset_1 @ X19 @ X20 @ X18 @ X21)
% 4.86/5.04          | ((X18) != (X21)))),
% 4.86/5.04      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 4.86/5.04  thf('66', plain,
% 4.86/5.04      (![X19 : $i, X20 : $i, X21 : $i]:
% 4.86/5.04         ((r2_relset_1 @ X19 @ X20 @ X21 @ X21)
% 4.86/5.04          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 4.86/5.04      inference('simplify', [status(thm)], ['65'])).
% 4.86/5.04  thf('67', plain,
% 4.86/5.04      (![X0 : $i, X1 : $i]:
% 4.86/5.04         (r2_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 4.86/5.04          (k2_zfmisc_1 @ X1 @ X0))),
% 4.86/5.04      inference('sup-', [status(thm)], ['64', '66'])).
% 4.86/5.04  thf('68', plain,
% 4.86/5.04      (((r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 4.86/5.04        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 4.86/5.04      inference('sup+', [status(thm)], ['63', '67'])).
% 4.86/5.04  thf('69', plain,
% 4.86/5.04      (((r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)
% 4.86/5.04        | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 4.86/5.04        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 4.86/5.04      inference('sup+', [status(thm)], ['58', '68'])).
% 4.86/5.04  thf('70', plain,
% 4.86/5.04      ((((sk_A) = (k1_relat_1 @ sk_C_1))
% 4.86/5.04        | (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D))),
% 4.86/5.04      inference('simplify', [status(thm)], ['69'])).
% 4.86/5.04  thf('71', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)),
% 4.86/5.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.04  thf('72', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 4.86/5.04      inference('clc', [status(thm)], ['70', '71'])).
% 4.86/5.04  thf('73', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_A))),
% 4.86/5.04      inference('demod', [status(thm)], ['43', '72'])).
% 4.86/5.04  thf('74', plain,
% 4.86/5.04      ((((sk_A) = (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 4.86/5.04        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 4.86/5.05      inference('demod', [status(thm)], ['40', '73'])).
% 4.86/5.05  thf('75', plain,
% 4.86/5.05      ((((sk_A) = (k1_relat_1 @ sk_D))
% 4.86/5.05        | ((sk_A) = (k1_relat_1 @ sk_D))
% 4.86/5.05        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 4.86/5.05      inference('sup+', [status(thm)], ['24', '74'])).
% 4.86/5.05  thf('76', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 4.86/5.05      inference('simplify', [status(thm)], ['75'])).
% 4.86/5.05  thf('77', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 4.86/5.05      inference('clc', [status(thm)], ['70', '71'])).
% 4.86/5.05  thf(t9_funct_1, axiom,
% 4.86/5.05    (![A:$i]:
% 4.86/5.05     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.86/5.05       ( ![B:$i]:
% 4.86/5.05         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 4.86/5.05           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 4.86/5.05               ( ![C:$i]:
% 4.86/5.05                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 4.86/5.05                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 4.86/5.05             ( ( A ) = ( B ) ) ) ) ) ))).
% 4.86/5.05  thf('78', plain,
% 4.86/5.05      (![X10 : $i, X11 : $i]:
% 4.86/5.05         (~ (v1_relat_1 @ X10)
% 4.86/5.05          | ~ (v1_funct_1 @ X10)
% 4.86/5.05          | ((X11) = (X10))
% 4.86/5.05          | (r2_hidden @ (sk_C @ X10 @ X11) @ (k1_relat_1 @ X11))
% 4.86/5.05          | ((k1_relat_1 @ X11) != (k1_relat_1 @ X10))
% 4.86/5.05          | ~ (v1_funct_1 @ X11)
% 4.86/5.05          | ~ (v1_relat_1 @ X11))),
% 4.86/5.05      inference('cnf', [status(esa)], [t9_funct_1])).
% 4.86/5.05  thf('79', plain,
% 4.86/5.05      (![X0 : $i]:
% 4.86/5.05         (((sk_A) != (k1_relat_1 @ X0))
% 4.86/5.05          | ~ (v1_relat_1 @ sk_C_1)
% 4.86/5.05          | ~ (v1_funct_1 @ sk_C_1)
% 4.86/5.05          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 4.86/5.05          | ((sk_C_1) = (X0))
% 4.86/5.05          | ~ (v1_funct_1 @ X0)
% 4.86/5.05          | ~ (v1_relat_1 @ X0))),
% 4.86/5.05      inference('sup-', [status(thm)], ['77', '78'])).
% 4.86/5.05  thf('80', plain,
% 4.86/5.05      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.86/5.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.05  thf(cc1_relset_1, axiom,
% 4.86/5.05    (![A:$i,B:$i,C:$i]:
% 4.86/5.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.86/5.05       ( v1_relat_1 @ C ) ))).
% 4.86/5.05  thf('81', plain,
% 4.86/5.05      (![X12 : $i, X13 : $i, X14 : $i]:
% 4.86/5.05         ((v1_relat_1 @ X12)
% 4.86/5.05          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 4.86/5.05      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.86/5.05  thf('82', plain, ((v1_relat_1 @ sk_C_1)),
% 4.86/5.05      inference('sup-', [status(thm)], ['80', '81'])).
% 4.86/5.05  thf('83', plain, ((v1_funct_1 @ sk_C_1)),
% 4.86/5.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.05  thf('84', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 4.86/5.05      inference('clc', [status(thm)], ['70', '71'])).
% 4.86/5.05  thf('85', plain,
% 4.86/5.05      (![X0 : $i]:
% 4.86/5.05         (((sk_A) != (k1_relat_1 @ X0))
% 4.86/5.05          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_A)
% 4.86/5.05          | ((sk_C_1) = (X0))
% 4.86/5.05          | ~ (v1_funct_1 @ X0)
% 4.86/5.05          | ~ (v1_relat_1 @ X0))),
% 4.86/5.05      inference('demod', [status(thm)], ['79', '82', '83', '84'])).
% 4.86/5.05  thf('86', plain,
% 4.86/5.05      ((((sk_A) != (sk_A))
% 4.86/5.05        | ~ (v1_relat_1 @ sk_D)
% 4.86/5.05        | ~ (v1_funct_1 @ sk_D)
% 4.86/5.05        | ((sk_C_1) = (sk_D))
% 4.86/5.05        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 4.86/5.05      inference('sup-', [status(thm)], ['76', '85'])).
% 4.86/5.05  thf('87', plain,
% 4.86/5.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.86/5.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.05  thf('88', plain,
% 4.86/5.05      (![X12 : $i, X13 : $i, X14 : $i]:
% 4.86/5.05         ((v1_relat_1 @ X12)
% 4.86/5.05          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 4.86/5.05      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.86/5.05  thf('89', plain, ((v1_relat_1 @ sk_D)),
% 4.86/5.05      inference('sup-', [status(thm)], ['87', '88'])).
% 4.86/5.05  thf('90', plain, ((v1_funct_1 @ sk_D)),
% 4.86/5.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.05  thf('91', plain,
% 4.86/5.05      ((((sk_A) != (sk_A))
% 4.86/5.05        | ((sk_C_1) = (sk_D))
% 4.86/5.05        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 4.86/5.05      inference('demod', [status(thm)], ['86', '89', '90'])).
% 4.86/5.05  thf('92', plain,
% 4.86/5.05      (((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A) | ((sk_C_1) = (sk_D)))),
% 4.86/5.05      inference('simplify', [status(thm)], ['91'])).
% 4.86/5.05  thf('93', plain,
% 4.86/5.05      (![X30 : $i]:
% 4.86/5.05         (((k1_funct_1 @ sk_C_1 @ X30) = (k1_funct_1 @ sk_D @ X30))
% 4.86/5.05          | ~ (r2_hidden @ X30 @ sk_A))),
% 4.86/5.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.05  thf('94', plain,
% 4.86/5.05      ((((sk_C_1) = (sk_D))
% 4.86/5.05        | ((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 4.86/5.05            = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))))),
% 4.86/5.05      inference('sup-', [status(thm)], ['92', '93'])).
% 4.86/5.05  thf('95', plain,
% 4.86/5.05      (((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 4.86/5.05         = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))),
% 4.86/5.05      inference('condensation', [status(thm)], ['94'])).
% 4.86/5.05  thf('96', plain,
% 4.86/5.05      (![X10 : $i, X11 : $i]:
% 4.86/5.05         (~ (v1_relat_1 @ X10)
% 4.86/5.05          | ~ (v1_funct_1 @ X10)
% 4.86/5.05          | ((X11) = (X10))
% 4.86/5.05          | ((k1_funct_1 @ X11 @ (sk_C @ X10 @ X11))
% 4.86/5.05              != (k1_funct_1 @ X10 @ (sk_C @ X10 @ X11)))
% 4.86/5.05          | ((k1_relat_1 @ X11) != (k1_relat_1 @ X10))
% 4.86/5.05          | ~ (v1_funct_1 @ X11)
% 4.86/5.05          | ~ (v1_relat_1 @ X11))),
% 4.86/5.05      inference('cnf', [status(esa)], [t9_funct_1])).
% 4.86/5.05  thf('97', plain,
% 4.86/5.05      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 4.86/5.05          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 4.86/5.05        | ~ (v1_relat_1 @ sk_C_1)
% 4.86/5.05        | ~ (v1_funct_1 @ sk_C_1)
% 4.86/5.05        | ((k1_relat_1 @ sk_C_1) != (k1_relat_1 @ sk_D))
% 4.86/5.05        | ((sk_C_1) = (sk_D))
% 4.86/5.05        | ~ (v1_funct_1 @ sk_D)
% 4.86/5.05        | ~ (v1_relat_1 @ sk_D))),
% 4.86/5.05      inference('sup-', [status(thm)], ['95', '96'])).
% 4.86/5.05  thf('98', plain, ((v1_relat_1 @ sk_C_1)),
% 4.86/5.05      inference('sup-', [status(thm)], ['80', '81'])).
% 4.86/5.05  thf('99', plain, ((v1_funct_1 @ sk_C_1)),
% 4.86/5.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.05  thf('100', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 4.86/5.05      inference('clc', [status(thm)], ['70', '71'])).
% 4.86/5.05  thf('101', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 4.86/5.05      inference('simplify', [status(thm)], ['75'])).
% 4.86/5.05  thf('102', plain, ((v1_funct_1 @ sk_D)),
% 4.86/5.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.05  thf('103', plain, ((v1_relat_1 @ sk_D)),
% 4.86/5.05      inference('sup-', [status(thm)], ['87', '88'])).
% 4.86/5.05  thf('104', plain,
% 4.86/5.05      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 4.86/5.05          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 4.86/5.05        | ((sk_A) != (sk_A))
% 4.86/5.05        | ((sk_C_1) = (sk_D)))),
% 4.86/5.05      inference('demod', [status(thm)],
% 4.86/5.05                ['97', '98', '99', '100', '101', '102', '103'])).
% 4.86/5.05  thf('105', plain, (((sk_C_1) = (sk_D))),
% 4.86/5.05      inference('simplify', [status(thm)], ['104'])).
% 4.86/5.05  thf('106', plain,
% 4.86/5.05      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.86/5.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.05  thf('107', plain,
% 4.86/5.05      (![X19 : $i, X20 : $i, X21 : $i]:
% 4.86/5.05         ((r2_relset_1 @ X19 @ X20 @ X21 @ X21)
% 4.86/5.05          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 4.86/5.05      inference('simplify', [status(thm)], ['65'])).
% 4.86/5.05  thf('108', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1)),
% 4.86/5.05      inference('sup-', [status(thm)], ['106', '107'])).
% 4.86/5.05  thf('109', plain, ($false),
% 4.86/5.05      inference('demod', [status(thm)], ['0', '105', '108'])).
% 4.86/5.05  
% 4.86/5.05  % SZS output end Refutation
% 4.86/5.05  
% 4.86/5.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
