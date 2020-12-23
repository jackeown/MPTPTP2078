%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.haI3ub7Ins

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:37 EST 2020

% Result     : Theorem 5.24s
% Output     : Refutation 5.24s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 814 expanded)
%              Number of leaves         :   35 ( 253 expanded)
%              Depth                    :   24
%              Number of atoms          : 1199 (11509 expanded)
%              Number of equality atoms :  119 ( 686 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('3',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ( X27
        = ( k1_relset_1 @ X27 @ X28 @ X29 ) )
      | ~ ( zip_tseitin_1 @ X29 @ X28 @ X27 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('23',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('24',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_D ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('28',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C_1 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_C_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('35',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C_1 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('39',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      = ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['35','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('45',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('47',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('49',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ( X27
        = ( k1_relset_1 @ X27 @ X28 @ X29 ) )
      | ~ ( zip_tseitin_1 @ X29 @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('53',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('55',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_D )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_D ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('58',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_D ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('60',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_D ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('62',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C_1 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('63',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_C_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('65',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C_1 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('67',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( r2_relset_1 @ X22 @ X23 @ X21 @ X24 )
      | ( X21 != X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('68',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_relset_1 @ X22 @ X23 @ X24 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','68'])).

thf('70',plain,
    ( ( r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['65','69'])).

thf('71',plain,
    ( ( r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['60','70'])).

thf('72',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = sk_A ),
    inference(demod,[status(thm)],['45','74'])).

thf('76',plain,
    ( ( sk_A
      = ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['42','75'])).

thf('77',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['26','76'])).

thf('78',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['72','73'])).

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

thf('80',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( X14 = X13 )
      | ( r2_hidden @ ( sk_C @ X13 @ X14 ) @ ( k1_relat_1 @ X14 ) )
      | ( ( k1_relat_1 @ X14 )
       != ( k1_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('83',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('84',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_A )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['81','84','85','86'])).

thf('88',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['78','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('91',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['88','91','92'])).

thf('94',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X33: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ X33 )
        = ( k1_funct_1 @ sk_D @ X33 ) )
      | ~ ( r2_hidden @ X33 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( sk_C_1 = sk_D )
    | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ),
    inference(condensation,[status(thm)],['96'])).

thf('98',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( X14 = X13 )
      | ( ( k1_funct_1 @ X14 @ ( sk_C @ X13 @ X14 ) )
       != ( k1_funct_1 @ X13 @ ( sk_C @ X13 @ X14 ) ) )
      | ( ( k1_relat_1 @ X14 )
       != ( k1_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('99',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_1 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['82','83'])).

thf('101',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('103',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['77'])).

thf('104',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['89','90'])).

thf('106',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(demod,[status(thm)],['99','100','101','102','103','104','105'])).

thf('107',plain,(
    sk_C_1 = sk_D ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_relset_1 @ X22 @ X23 @ X24 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('110',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    $false ),
    inference(demod,[status(thm)],['0','107','110'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.haI3ub7Ins
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:49:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 5.24/5.42  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.24/5.42  % Solved by: fo/fo7.sh
% 5.24/5.42  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.24/5.42  % done 3601 iterations in 4.972s
% 5.24/5.42  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.24/5.42  % SZS output start Refutation
% 5.24/5.42  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.24/5.42  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 5.24/5.42  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.24/5.42  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.24/5.42  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 5.24/5.42  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 5.24/5.42  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 5.24/5.42  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.24/5.42  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 5.24/5.42  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 5.24/5.42  thf(sk_A_type, type, sk_A: $i).
% 5.24/5.42  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 5.24/5.42  thf(sk_D_type, type, sk_D: $i).
% 5.24/5.42  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.24/5.42  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.24/5.42  thf(sk_B_type, type, sk_B: $i).
% 5.24/5.42  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.24/5.42  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 5.24/5.42  thf(sk_C_1_type, type, sk_C_1: $i).
% 5.24/5.42  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 5.24/5.42  thf(t18_funct_2, conjecture,
% 5.24/5.42    (![A:$i,B:$i,C:$i]:
% 5.24/5.42     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.24/5.42         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.24/5.42       ( ![D:$i]:
% 5.24/5.42         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 5.24/5.42             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.24/5.42           ( ( ![E:$i]:
% 5.24/5.42               ( ( r2_hidden @ E @ A ) =>
% 5.24/5.42                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 5.24/5.42             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 5.24/5.42  thf(zf_stmt_0, negated_conjecture,
% 5.24/5.42    (~( ![A:$i,B:$i,C:$i]:
% 5.24/5.42        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.24/5.42            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.24/5.42          ( ![D:$i]:
% 5.24/5.42            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 5.24/5.42                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.24/5.42              ( ( ![E:$i]:
% 5.24/5.42                  ( ( r2_hidden @ E @ A ) =>
% 5.24/5.42                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 5.24/5.42                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 5.24/5.42    inference('cnf.neg', [status(esa)], [t18_funct_2])).
% 5.24/5.42  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)),
% 5.24/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.24/5.42  thf(d1_funct_2, axiom,
% 5.24/5.42    (![A:$i,B:$i,C:$i]:
% 5.24/5.42     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.24/5.42       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 5.24/5.42           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 5.24/5.42             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 5.24/5.42         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 5.24/5.42           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 5.24/5.42             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 5.24/5.42  thf(zf_stmt_1, axiom,
% 5.24/5.42    (![B:$i,A:$i]:
% 5.24/5.42     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 5.24/5.42       ( zip_tseitin_0 @ B @ A ) ))).
% 5.24/5.42  thf('1', plain,
% 5.24/5.42      (![X25 : $i, X26 : $i]:
% 5.24/5.42         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 5.24/5.42      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.24/5.42  thf(t113_zfmisc_1, axiom,
% 5.24/5.42    (![A:$i,B:$i]:
% 5.24/5.42     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 5.24/5.42       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 5.24/5.42  thf('2', plain,
% 5.24/5.42      (![X4 : $i, X5 : $i]:
% 5.24/5.42         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 5.24/5.42      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 5.24/5.42  thf('3', plain,
% 5.24/5.42      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 5.24/5.42      inference('simplify', [status(thm)], ['2'])).
% 5.24/5.42  thf('4', plain,
% 5.24/5.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.24/5.42         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 5.24/5.42      inference('sup+', [status(thm)], ['1', '3'])).
% 5.24/5.42  thf('5', plain,
% 5.24/5.42      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.24/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.24/5.42  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 5.24/5.42  thf(zf_stmt_3, axiom,
% 5.24/5.42    (![C:$i,B:$i,A:$i]:
% 5.24/5.42     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 5.24/5.42       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 5.24/5.42  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 5.24/5.42  thf(zf_stmt_5, axiom,
% 5.24/5.42    (![A:$i,B:$i,C:$i]:
% 5.24/5.42     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.24/5.42       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 5.24/5.42         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 5.24/5.42           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 5.24/5.42             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 5.24/5.42  thf('6', plain,
% 5.24/5.42      (![X30 : $i, X31 : $i, X32 : $i]:
% 5.24/5.42         (~ (zip_tseitin_0 @ X30 @ X31)
% 5.24/5.42          | (zip_tseitin_1 @ X32 @ X30 @ X31)
% 5.24/5.42          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 5.24/5.42      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.24/5.42  thf('7', plain,
% 5.24/5.42      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 5.24/5.42      inference('sup-', [status(thm)], ['5', '6'])).
% 5.24/5.42  thf('8', plain,
% 5.24/5.42      (![X0 : $i]:
% 5.24/5.42         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 5.24/5.42          | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 5.24/5.42      inference('sup-', [status(thm)], ['4', '7'])).
% 5.24/5.42  thf('9', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 5.24/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.24/5.42  thf('10', plain,
% 5.24/5.42      (![X27 : $i, X28 : $i, X29 : $i]:
% 5.24/5.42         (~ (v1_funct_2 @ X29 @ X27 @ X28)
% 5.24/5.42          | ((X27) = (k1_relset_1 @ X27 @ X28 @ X29))
% 5.24/5.42          | ~ (zip_tseitin_1 @ X29 @ X28 @ X27))),
% 5.24/5.42      inference('cnf', [status(esa)], [zf_stmt_3])).
% 5.24/5.42  thf('11', plain,
% 5.24/5.42      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 5.24/5.42        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 5.24/5.42      inference('sup-', [status(thm)], ['9', '10'])).
% 5.24/5.42  thf('12', plain,
% 5.24/5.42      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.24/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.24/5.42  thf(redefinition_k1_relset_1, axiom,
% 5.24/5.42    (![A:$i,B:$i,C:$i]:
% 5.24/5.42     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.24/5.42       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 5.24/5.42  thf('13', plain,
% 5.24/5.42      (![X18 : $i, X19 : $i, X20 : $i]:
% 5.24/5.42         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 5.24/5.42          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 5.24/5.42      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 5.24/5.42  thf('14', plain,
% 5.24/5.42      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 5.24/5.42      inference('sup-', [status(thm)], ['12', '13'])).
% 5.24/5.42  thf('15', plain,
% 5.24/5.42      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 5.24/5.42      inference('demod', [status(thm)], ['11', '14'])).
% 5.24/5.42  thf('16', plain,
% 5.24/5.42      (![X0 : $i]:
% 5.24/5.42         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 5.24/5.42          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 5.24/5.42      inference('sup-', [status(thm)], ['8', '15'])).
% 5.24/5.42  thf('17', plain,
% 5.24/5.42      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.24/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.24/5.42  thf(t3_subset, axiom,
% 5.24/5.42    (![A:$i,B:$i]:
% 5.24/5.42     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 5.24/5.42  thf('18', plain,
% 5.24/5.42      (![X7 : $i, X8 : $i]:
% 5.24/5.42         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 5.24/5.42      inference('cnf', [status(esa)], [t3_subset])).
% 5.24/5.42  thf('19', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 5.24/5.42      inference('sup-', [status(thm)], ['17', '18'])).
% 5.24/5.42  thf(d10_xboole_0, axiom,
% 5.24/5.42    (![A:$i,B:$i]:
% 5.24/5.42     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.24/5.42  thf('20', plain,
% 5.24/5.42      (![X0 : $i, X2 : $i]:
% 5.24/5.42         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 5.24/5.42      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.24/5.42  thf('21', plain,
% 5.24/5.42      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_D)
% 5.24/5.42        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 5.24/5.42      inference('sup-', [status(thm)], ['19', '20'])).
% 5.24/5.42  thf('22', plain,
% 5.24/5.42      ((~ (r1_tarski @ k1_xboole_0 @ sk_D)
% 5.24/5.42        | ((sk_A) = (k1_relat_1 @ sk_D))
% 5.24/5.42        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 5.24/5.42      inference('sup-', [status(thm)], ['16', '21'])).
% 5.24/5.42  thf(t4_subset_1, axiom,
% 5.24/5.42    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 5.24/5.42  thf('23', plain,
% 5.24/5.42      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 5.24/5.42      inference('cnf', [status(esa)], [t4_subset_1])).
% 5.24/5.42  thf('24', plain,
% 5.24/5.42      (![X7 : $i, X8 : $i]:
% 5.24/5.42         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 5.24/5.42      inference('cnf', [status(esa)], [t3_subset])).
% 5.24/5.42  thf('25', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 5.24/5.42      inference('sup-', [status(thm)], ['23', '24'])).
% 5.24/5.42  thf('26', plain,
% 5.24/5.42      ((((sk_A) = (k1_relat_1 @ sk_D)) | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 5.24/5.42      inference('demod', [status(thm)], ['22', '25'])).
% 5.24/5.42  thf('27', plain,
% 5.24/5.42      (![X0 : $i]:
% 5.24/5.42         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 5.24/5.42          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 5.24/5.42      inference('sup-', [status(thm)], ['8', '15'])).
% 5.24/5.42  thf('28', plain,
% 5.24/5.42      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.24/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.24/5.42  thf('29', plain,
% 5.24/5.42      (![X7 : $i, X8 : $i]:
% 5.24/5.42         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 5.24/5.42      inference('cnf', [status(esa)], [t3_subset])).
% 5.24/5.42  thf('30', plain, ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 5.24/5.42      inference('sup-', [status(thm)], ['28', '29'])).
% 5.24/5.42  thf('31', plain,
% 5.24/5.42      (![X0 : $i, X2 : $i]:
% 5.24/5.42         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 5.24/5.42      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.24/5.42  thf('32', plain,
% 5.24/5.42      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C_1)
% 5.24/5.42        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 5.24/5.42      inference('sup-', [status(thm)], ['30', '31'])).
% 5.24/5.42  thf('33', plain,
% 5.24/5.42      ((~ (r1_tarski @ k1_xboole_0 @ sk_C_1)
% 5.24/5.42        | ((sk_A) = (k1_relat_1 @ sk_D))
% 5.24/5.42        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 5.24/5.42      inference('sup-', [status(thm)], ['27', '32'])).
% 5.24/5.42  thf('34', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 5.24/5.42      inference('sup-', [status(thm)], ['23', '24'])).
% 5.24/5.42  thf('35', plain,
% 5.24/5.42      ((((sk_A) = (k1_relat_1 @ sk_D))
% 5.24/5.42        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 5.24/5.42      inference('demod', [status(thm)], ['33', '34'])).
% 5.24/5.42  thf('36', plain,
% 5.24/5.42      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 5.24/5.42      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.24/5.42  thf('37', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 5.24/5.42      inference('simplify', [status(thm)], ['36'])).
% 5.24/5.42  thf('38', plain,
% 5.24/5.42      (![X7 : $i, X9 : $i]:
% 5.24/5.42         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 5.24/5.42      inference('cnf', [status(esa)], [t3_subset])).
% 5.24/5.42  thf('39', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 5.24/5.42      inference('sup-', [status(thm)], ['37', '38'])).
% 5.24/5.42  thf('40', plain,
% 5.24/5.42      (![X18 : $i, X19 : $i, X20 : $i]:
% 5.24/5.42         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 5.24/5.42          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 5.24/5.42      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 5.24/5.42  thf('41', plain,
% 5.24/5.42      (![X0 : $i, X1 : $i]:
% 5.24/5.42         ((k1_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0))
% 5.24/5.42           = (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 5.24/5.42      inference('sup-', [status(thm)], ['39', '40'])).
% 5.24/5.42  thf('42', plain,
% 5.24/5.42      ((((k1_relset_1 @ sk_A @ sk_B @ sk_C_1)
% 5.24/5.42          = (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 5.24/5.42        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 5.24/5.42      inference('sup+', [status(thm)], ['35', '41'])).
% 5.24/5.42  thf('43', plain,
% 5.24/5.42      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.24/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.24/5.42  thf('44', plain,
% 5.24/5.42      (![X18 : $i, X19 : $i, X20 : $i]:
% 5.24/5.42         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 5.24/5.42          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 5.24/5.42      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 5.24/5.42  thf('45', plain,
% 5.24/5.42      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 5.24/5.42      inference('sup-', [status(thm)], ['43', '44'])).
% 5.24/5.42  thf('46', plain,
% 5.24/5.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.24/5.42         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 5.24/5.42      inference('sup+', [status(thm)], ['1', '3'])).
% 5.24/5.42  thf('47', plain,
% 5.24/5.42      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.24/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.24/5.42  thf('48', plain,
% 5.24/5.42      (![X30 : $i, X31 : $i, X32 : $i]:
% 5.24/5.42         (~ (zip_tseitin_0 @ X30 @ X31)
% 5.24/5.42          | (zip_tseitin_1 @ X32 @ X30 @ X31)
% 5.24/5.42          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 5.24/5.42      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.24/5.42  thf('49', plain,
% 5.24/5.42      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 5.24/5.42        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 5.24/5.42      inference('sup-', [status(thm)], ['47', '48'])).
% 5.24/5.42  thf('50', plain,
% 5.24/5.42      (![X0 : $i]:
% 5.24/5.42         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 5.24/5.42          | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 5.24/5.42      inference('sup-', [status(thm)], ['46', '49'])).
% 5.24/5.42  thf('51', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 5.24/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.24/5.42  thf('52', plain,
% 5.24/5.42      (![X27 : $i, X28 : $i, X29 : $i]:
% 5.24/5.42         (~ (v1_funct_2 @ X29 @ X27 @ X28)
% 5.24/5.42          | ((X27) = (k1_relset_1 @ X27 @ X28 @ X29))
% 5.24/5.42          | ~ (zip_tseitin_1 @ X29 @ X28 @ X27))),
% 5.24/5.42      inference('cnf', [status(esa)], [zf_stmt_3])).
% 5.24/5.42  thf('53', plain,
% 5.24/5.42      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 5.24/5.42        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 5.24/5.42      inference('sup-', [status(thm)], ['51', '52'])).
% 5.24/5.42  thf('54', plain,
% 5.24/5.42      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 5.24/5.42      inference('sup-', [status(thm)], ['43', '44'])).
% 5.24/5.42  thf('55', plain,
% 5.24/5.42      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 5.24/5.42        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 5.24/5.42      inference('demod', [status(thm)], ['53', '54'])).
% 5.24/5.42  thf('56', plain,
% 5.24/5.42      (![X0 : $i]:
% 5.24/5.42         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 5.24/5.42          | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 5.24/5.42      inference('sup-', [status(thm)], ['50', '55'])).
% 5.24/5.42  thf('57', plain,
% 5.24/5.42      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_D)
% 5.24/5.42        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 5.24/5.42      inference('sup-', [status(thm)], ['19', '20'])).
% 5.24/5.42  thf('58', plain,
% 5.24/5.42      ((~ (r1_tarski @ k1_xboole_0 @ sk_D)
% 5.24/5.42        | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 5.24/5.42        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 5.24/5.42      inference('sup-', [status(thm)], ['56', '57'])).
% 5.24/5.42  thf('59', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 5.24/5.42      inference('sup-', [status(thm)], ['23', '24'])).
% 5.24/5.42  thf('60', plain,
% 5.24/5.42      ((((sk_A) = (k1_relat_1 @ sk_C_1))
% 5.24/5.42        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 5.24/5.42      inference('demod', [status(thm)], ['58', '59'])).
% 5.24/5.42  thf('61', plain,
% 5.24/5.42      (![X0 : $i]:
% 5.24/5.42         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 5.24/5.42          | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 5.24/5.42      inference('sup-', [status(thm)], ['50', '55'])).
% 5.24/5.42  thf('62', plain,
% 5.24/5.42      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C_1)
% 5.24/5.42        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 5.24/5.42      inference('sup-', [status(thm)], ['30', '31'])).
% 5.24/5.42  thf('63', plain,
% 5.24/5.42      ((~ (r1_tarski @ k1_xboole_0 @ sk_C_1)
% 5.24/5.42        | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 5.24/5.42        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 5.24/5.42      inference('sup-', [status(thm)], ['61', '62'])).
% 5.24/5.42  thf('64', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 5.24/5.42      inference('sup-', [status(thm)], ['23', '24'])).
% 5.24/5.42  thf('65', plain,
% 5.24/5.42      ((((sk_A) = (k1_relat_1 @ sk_C_1))
% 5.24/5.42        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 5.24/5.42      inference('demod', [status(thm)], ['63', '64'])).
% 5.24/5.42  thf('66', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 5.24/5.42      inference('sup-', [status(thm)], ['37', '38'])).
% 5.24/5.42  thf(redefinition_r2_relset_1, axiom,
% 5.24/5.42    (![A:$i,B:$i,C:$i,D:$i]:
% 5.24/5.42     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.24/5.42         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.24/5.42       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 5.24/5.42  thf('67', plain,
% 5.24/5.42      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 5.24/5.42         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 5.24/5.42          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 5.24/5.42          | (r2_relset_1 @ X22 @ X23 @ X21 @ X24)
% 5.24/5.42          | ((X21) != (X24)))),
% 5.24/5.42      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 5.24/5.42  thf('68', plain,
% 5.24/5.42      (![X22 : $i, X23 : $i, X24 : $i]:
% 5.24/5.42         ((r2_relset_1 @ X22 @ X23 @ X24 @ X24)
% 5.24/5.42          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 5.24/5.42      inference('simplify', [status(thm)], ['67'])).
% 5.24/5.42  thf('69', plain,
% 5.24/5.42      (![X0 : $i, X1 : $i]:
% 5.24/5.42         (r2_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 5.24/5.42          (k2_zfmisc_1 @ X1 @ X0))),
% 5.24/5.42      inference('sup-', [status(thm)], ['66', '68'])).
% 5.24/5.42  thf('70', plain,
% 5.24/5.42      (((r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 5.24/5.42        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 5.24/5.42      inference('sup+', [status(thm)], ['65', '69'])).
% 5.24/5.42  thf('71', plain,
% 5.24/5.42      (((r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)
% 5.24/5.42        | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 5.24/5.42        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 5.24/5.42      inference('sup+', [status(thm)], ['60', '70'])).
% 5.24/5.42  thf('72', plain,
% 5.24/5.42      ((((sk_A) = (k1_relat_1 @ sk_C_1))
% 5.24/5.42        | (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D))),
% 5.24/5.42      inference('simplify', [status(thm)], ['71'])).
% 5.24/5.42  thf('73', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)),
% 5.24/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.24/5.42  thf('74', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 5.24/5.42      inference('clc', [status(thm)], ['72', '73'])).
% 5.24/5.42  thf('75', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_A))),
% 5.24/5.42      inference('demod', [status(thm)], ['45', '74'])).
% 5.24/5.42  thf('76', plain,
% 5.24/5.42      ((((sk_A) = (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 5.24/5.42        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 5.24/5.42      inference('demod', [status(thm)], ['42', '75'])).
% 5.24/5.42  thf('77', plain,
% 5.24/5.42      ((((sk_A) = (k1_relat_1 @ sk_D))
% 5.24/5.42        | ((sk_A) = (k1_relat_1 @ sk_D))
% 5.24/5.42        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 5.24/5.42      inference('sup+', [status(thm)], ['26', '76'])).
% 5.24/5.42  thf('78', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 5.24/5.42      inference('simplify', [status(thm)], ['77'])).
% 5.24/5.42  thf('79', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 5.24/5.42      inference('clc', [status(thm)], ['72', '73'])).
% 5.24/5.42  thf(t9_funct_1, axiom,
% 5.24/5.42    (![A:$i]:
% 5.24/5.42     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.24/5.42       ( ![B:$i]:
% 5.24/5.42         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 5.24/5.42           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 5.24/5.42               ( ![C:$i]:
% 5.24/5.42                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 5.24/5.42                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 5.24/5.42             ( ( A ) = ( B ) ) ) ) ) ))).
% 5.24/5.42  thf('80', plain,
% 5.24/5.42      (![X13 : $i, X14 : $i]:
% 5.24/5.42         (~ (v1_relat_1 @ X13)
% 5.24/5.42          | ~ (v1_funct_1 @ X13)
% 5.24/5.42          | ((X14) = (X13))
% 5.24/5.42          | (r2_hidden @ (sk_C @ X13 @ X14) @ (k1_relat_1 @ X14))
% 5.24/5.42          | ((k1_relat_1 @ X14) != (k1_relat_1 @ X13))
% 5.24/5.42          | ~ (v1_funct_1 @ X14)
% 5.24/5.42          | ~ (v1_relat_1 @ X14))),
% 5.24/5.42      inference('cnf', [status(esa)], [t9_funct_1])).
% 5.24/5.42  thf('81', plain,
% 5.24/5.42      (![X0 : $i]:
% 5.24/5.42         (((sk_A) != (k1_relat_1 @ X0))
% 5.24/5.42          | ~ (v1_relat_1 @ sk_C_1)
% 5.24/5.42          | ~ (v1_funct_1 @ sk_C_1)
% 5.24/5.42          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 5.24/5.42          | ((sk_C_1) = (X0))
% 5.24/5.42          | ~ (v1_funct_1 @ X0)
% 5.24/5.42          | ~ (v1_relat_1 @ X0))),
% 5.24/5.42      inference('sup-', [status(thm)], ['79', '80'])).
% 5.24/5.42  thf('82', plain,
% 5.24/5.42      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.24/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.24/5.42  thf(cc1_relset_1, axiom,
% 5.24/5.42    (![A:$i,B:$i,C:$i]:
% 5.24/5.42     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.24/5.42       ( v1_relat_1 @ C ) ))).
% 5.24/5.42  thf('83', plain,
% 5.24/5.42      (![X15 : $i, X16 : $i, X17 : $i]:
% 5.24/5.42         ((v1_relat_1 @ X15)
% 5.24/5.42          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 5.24/5.42      inference('cnf', [status(esa)], [cc1_relset_1])).
% 5.24/5.42  thf('84', plain, ((v1_relat_1 @ sk_C_1)),
% 5.24/5.42      inference('sup-', [status(thm)], ['82', '83'])).
% 5.24/5.42  thf('85', plain, ((v1_funct_1 @ sk_C_1)),
% 5.24/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.24/5.42  thf('86', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 5.24/5.42      inference('clc', [status(thm)], ['72', '73'])).
% 5.24/5.42  thf('87', plain,
% 5.24/5.42      (![X0 : $i]:
% 5.24/5.42         (((sk_A) != (k1_relat_1 @ X0))
% 5.24/5.42          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_A)
% 5.24/5.42          | ((sk_C_1) = (X0))
% 5.24/5.42          | ~ (v1_funct_1 @ X0)
% 5.24/5.42          | ~ (v1_relat_1 @ X0))),
% 5.24/5.42      inference('demod', [status(thm)], ['81', '84', '85', '86'])).
% 5.24/5.42  thf('88', plain,
% 5.24/5.42      ((((sk_A) != (sk_A))
% 5.24/5.42        | ~ (v1_relat_1 @ sk_D)
% 5.24/5.42        | ~ (v1_funct_1 @ sk_D)
% 5.24/5.42        | ((sk_C_1) = (sk_D))
% 5.24/5.42        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 5.24/5.42      inference('sup-', [status(thm)], ['78', '87'])).
% 5.24/5.42  thf('89', plain,
% 5.24/5.42      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.24/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.24/5.42  thf('90', plain,
% 5.24/5.42      (![X15 : $i, X16 : $i, X17 : $i]:
% 5.24/5.42         ((v1_relat_1 @ X15)
% 5.24/5.42          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 5.24/5.42      inference('cnf', [status(esa)], [cc1_relset_1])).
% 5.24/5.42  thf('91', plain, ((v1_relat_1 @ sk_D)),
% 5.24/5.42      inference('sup-', [status(thm)], ['89', '90'])).
% 5.24/5.42  thf('92', plain, ((v1_funct_1 @ sk_D)),
% 5.24/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.24/5.42  thf('93', plain,
% 5.24/5.42      ((((sk_A) != (sk_A))
% 5.24/5.42        | ((sk_C_1) = (sk_D))
% 5.24/5.42        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 5.24/5.42      inference('demod', [status(thm)], ['88', '91', '92'])).
% 5.24/5.42  thf('94', plain,
% 5.24/5.42      (((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A) | ((sk_C_1) = (sk_D)))),
% 5.24/5.42      inference('simplify', [status(thm)], ['93'])).
% 5.24/5.42  thf('95', plain,
% 5.24/5.42      (![X33 : $i]:
% 5.24/5.42         (((k1_funct_1 @ sk_C_1 @ X33) = (k1_funct_1 @ sk_D @ X33))
% 5.24/5.42          | ~ (r2_hidden @ X33 @ sk_A))),
% 5.24/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.24/5.42  thf('96', plain,
% 5.24/5.42      ((((sk_C_1) = (sk_D))
% 5.24/5.42        | ((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 5.24/5.42            = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))))),
% 5.24/5.42      inference('sup-', [status(thm)], ['94', '95'])).
% 5.24/5.42  thf('97', plain,
% 5.24/5.42      (((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 5.24/5.42         = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))),
% 5.24/5.42      inference('condensation', [status(thm)], ['96'])).
% 5.24/5.42  thf('98', plain,
% 5.24/5.42      (![X13 : $i, X14 : $i]:
% 5.24/5.42         (~ (v1_relat_1 @ X13)
% 5.24/5.42          | ~ (v1_funct_1 @ X13)
% 5.24/5.42          | ((X14) = (X13))
% 5.24/5.42          | ((k1_funct_1 @ X14 @ (sk_C @ X13 @ X14))
% 5.24/5.42              != (k1_funct_1 @ X13 @ (sk_C @ X13 @ X14)))
% 5.24/5.42          | ((k1_relat_1 @ X14) != (k1_relat_1 @ X13))
% 5.24/5.42          | ~ (v1_funct_1 @ X14)
% 5.24/5.42          | ~ (v1_relat_1 @ X14))),
% 5.24/5.42      inference('cnf', [status(esa)], [t9_funct_1])).
% 5.24/5.42  thf('99', plain,
% 5.24/5.42      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 5.24/5.42          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 5.24/5.42        | ~ (v1_relat_1 @ sk_C_1)
% 5.24/5.42        | ~ (v1_funct_1 @ sk_C_1)
% 5.24/5.42        | ((k1_relat_1 @ sk_C_1) != (k1_relat_1 @ sk_D))
% 5.24/5.42        | ((sk_C_1) = (sk_D))
% 5.24/5.42        | ~ (v1_funct_1 @ sk_D)
% 5.24/5.42        | ~ (v1_relat_1 @ sk_D))),
% 5.24/5.42      inference('sup-', [status(thm)], ['97', '98'])).
% 5.24/5.42  thf('100', plain, ((v1_relat_1 @ sk_C_1)),
% 5.24/5.42      inference('sup-', [status(thm)], ['82', '83'])).
% 5.24/5.42  thf('101', plain, ((v1_funct_1 @ sk_C_1)),
% 5.24/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.24/5.42  thf('102', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 5.24/5.42      inference('clc', [status(thm)], ['72', '73'])).
% 5.24/5.42  thf('103', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 5.24/5.42      inference('simplify', [status(thm)], ['77'])).
% 5.24/5.42  thf('104', plain, ((v1_funct_1 @ sk_D)),
% 5.24/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.24/5.42  thf('105', plain, ((v1_relat_1 @ sk_D)),
% 5.24/5.42      inference('sup-', [status(thm)], ['89', '90'])).
% 5.24/5.42  thf('106', plain,
% 5.24/5.42      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 5.24/5.42          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 5.24/5.42        | ((sk_A) != (sk_A))
% 5.24/5.42        | ((sk_C_1) = (sk_D)))),
% 5.24/5.42      inference('demod', [status(thm)],
% 5.24/5.42                ['99', '100', '101', '102', '103', '104', '105'])).
% 5.24/5.42  thf('107', plain, (((sk_C_1) = (sk_D))),
% 5.24/5.42      inference('simplify', [status(thm)], ['106'])).
% 5.24/5.42  thf('108', plain,
% 5.24/5.42      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.24/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.24/5.42  thf('109', plain,
% 5.24/5.42      (![X22 : $i, X23 : $i, X24 : $i]:
% 5.24/5.42         ((r2_relset_1 @ X22 @ X23 @ X24 @ X24)
% 5.24/5.42          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 5.24/5.42      inference('simplify', [status(thm)], ['67'])).
% 5.24/5.42  thf('110', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1)),
% 5.24/5.42      inference('sup-', [status(thm)], ['108', '109'])).
% 5.24/5.42  thf('111', plain, ($false),
% 5.24/5.42      inference('demod', [status(thm)], ['0', '107', '110'])).
% 5.24/5.42  
% 5.24/5.42  % SZS output end Refutation
% 5.24/5.42  
% 5.24/5.43  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
