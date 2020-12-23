%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7DzC85T75G

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:39 EST 2020

% Result     : Theorem 4.84s
% Output     : Refutation 4.84s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 826 expanded)
%              Number of leaves         :   36 ( 257 expanded)
%              Depth                    :   24
%              Number of atoms          : 1223 (11565 expanded)
%              Number of equality atoms :  119 ( 686 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( r2_relset_1 @ X23 @ X24 @ X22 @ X25 )
      | ( X22 != X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('68',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_relset_1 @ X23 @ X24 @ X25 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ( X18 = X17 )
      | ( r2_hidden @ ( sk_C @ X17 @ X18 ) @ ( k1_relat_1 @ X18 ) )
      | ( ( k1_relat_1 @ X18 )
       != ( k1_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('83',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('84',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('85',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('86',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_A )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['81','86','87','88'])).

thf('90',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['78','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('93',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('95',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['90','95','96'])).

thf('98',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X34: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ X34 )
        = ( k1_funct_1 @ sk_D @ X34 ) )
      | ~ ( r2_hidden @ X34 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( sk_C_1 = sk_D )
    | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ),
    inference(condensation,[status(thm)],['100'])).

thf('102',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ( X18 = X17 )
      | ( ( k1_funct_1 @ X18 @ ( sk_C @ X17 @ X18 ) )
       != ( k1_funct_1 @ X17 @ ( sk_C @ X17 @ X18 ) ) )
      | ( ( k1_relat_1 @ X18 )
       != ( k1_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('103',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_1 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['84','85'])).

thf('105',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('107',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['77'])).

thf('108',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['93','94'])).

thf('110',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(demod,[status(thm)],['103','104','105','106','107','108','109'])).

thf('111',plain,(
    sk_C_1 = sk_D ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_relset_1 @ X23 @ X24 @ X25 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('114',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    $false ),
    inference(demod,[status(thm)],['0','111','114'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7DzC85T75G
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:47:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 4.84/5.07  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.84/5.07  % Solved by: fo/fo7.sh
% 4.84/5.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.84/5.07  % done 3429 iterations in 4.622s
% 4.84/5.07  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.84/5.07  % SZS output start Refutation
% 4.84/5.07  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.84/5.07  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.84/5.07  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.84/5.07  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.84/5.07  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.84/5.07  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.84/5.07  thf(sk_B_type, type, sk_B: $i).
% 4.84/5.07  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 4.84/5.07  thf(sk_A_type, type, sk_A: $i).
% 4.84/5.07  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.84/5.07  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.84/5.07  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.84/5.07  thf(sk_C_1_type, type, sk_C_1: $i).
% 4.84/5.07  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 4.84/5.07  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 4.84/5.07  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.84/5.07  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.84/5.07  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 4.84/5.07  thf(sk_D_type, type, sk_D: $i).
% 4.84/5.07  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 4.84/5.07  thf(t18_funct_2, conjecture,
% 4.84/5.07    (![A:$i,B:$i,C:$i]:
% 4.84/5.07     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.84/5.07         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.84/5.07       ( ![D:$i]:
% 4.84/5.07         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 4.84/5.07             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.84/5.07           ( ( ![E:$i]:
% 4.84/5.07               ( ( r2_hidden @ E @ A ) =>
% 4.84/5.07                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 4.84/5.07             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 4.84/5.07  thf(zf_stmt_0, negated_conjecture,
% 4.84/5.07    (~( ![A:$i,B:$i,C:$i]:
% 4.84/5.07        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.84/5.07            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.84/5.07          ( ![D:$i]:
% 4.84/5.07            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 4.84/5.07                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.84/5.07              ( ( ![E:$i]:
% 4.84/5.07                  ( ( r2_hidden @ E @ A ) =>
% 4.84/5.07                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 4.84/5.07                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 4.84/5.07    inference('cnf.neg', [status(esa)], [t18_funct_2])).
% 4.84/5.07  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)),
% 4.84/5.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.07  thf(d1_funct_2, axiom,
% 4.84/5.07    (![A:$i,B:$i,C:$i]:
% 4.84/5.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.84/5.07       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.84/5.07           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 4.84/5.07             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 4.84/5.07         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.84/5.07           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 4.84/5.07             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 4.84/5.07  thf(zf_stmt_1, axiom,
% 4.84/5.07    (![B:$i,A:$i]:
% 4.84/5.07     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.84/5.07       ( zip_tseitin_0 @ B @ A ) ))).
% 4.84/5.07  thf('1', plain,
% 4.84/5.07      (![X26 : $i, X27 : $i]:
% 4.84/5.07         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 4.84/5.07      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.84/5.07  thf(t113_zfmisc_1, axiom,
% 4.84/5.07    (![A:$i,B:$i]:
% 4.84/5.07     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 4.84/5.07       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 4.84/5.07  thf('2', plain,
% 4.84/5.07      (![X4 : $i, X5 : $i]:
% 4.84/5.07         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 4.84/5.07      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 4.84/5.07  thf('3', plain,
% 4.84/5.07      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 4.84/5.07      inference('simplify', [status(thm)], ['2'])).
% 4.84/5.07  thf('4', plain,
% 4.84/5.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.84/5.07         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 4.84/5.07      inference('sup+', [status(thm)], ['1', '3'])).
% 4.84/5.07  thf('5', plain,
% 4.84/5.07      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.84/5.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.07  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 4.84/5.07  thf(zf_stmt_3, axiom,
% 4.84/5.07    (![C:$i,B:$i,A:$i]:
% 4.84/5.07     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 4.84/5.07       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 4.84/5.07  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 4.84/5.07  thf(zf_stmt_5, axiom,
% 4.84/5.07    (![A:$i,B:$i,C:$i]:
% 4.84/5.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.84/5.07       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 4.84/5.07         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.84/5.07           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 4.84/5.07             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 4.84/5.07  thf('6', plain,
% 4.84/5.07      (![X31 : $i, X32 : $i, X33 : $i]:
% 4.84/5.07         (~ (zip_tseitin_0 @ X31 @ X32)
% 4.84/5.07          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 4.84/5.07          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 4.84/5.07      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.84/5.07  thf('7', plain,
% 4.84/5.07      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 4.84/5.07      inference('sup-', [status(thm)], ['5', '6'])).
% 4.84/5.07  thf('8', plain,
% 4.84/5.07      (![X0 : $i]:
% 4.84/5.07         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 4.84/5.07          | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 4.84/5.07      inference('sup-', [status(thm)], ['4', '7'])).
% 4.84/5.07  thf('9', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 4.84/5.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.07  thf('10', plain,
% 4.84/5.07      (![X28 : $i, X29 : $i, X30 : $i]:
% 4.84/5.07         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 4.84/5.07          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 4.84/5.07          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 4.84/5.07      inference('cnf', [status(esa)], [zf_stmt_3])).
% 4.84/5.07  thf('11', plain,
% 4.84/5.07      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 4.84/5.07        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 4.84/5.07      inference('sup-', [status(thm)], ['9', '10'])).
% 4.84/5.07  thf('12', plain,
% 4.84/5.07      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.84/5.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.07  thf(redefinition_k1_relset_1, axiom,
% 4.84/5.07    (![A:$i,B:$i,C:$i]:
% 4.84/5.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.84/5.07       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 4.84/5.07  thf('13', plain,
% 4.84/5.07      (![X19 : $i, X20 : $i, X21 : $i]:
% 4.84/5.07         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 4.84/5.07          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 4.84/5.07      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.84/5.07  thf('14', plain,
% 4.84/5.07      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 4.84/5.07      inference('sup-', [status(thm)], ['12', '13'])).
% 4.84/5.07  thf('15', plain,
% 4.84/5.07      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 4.84/5.07      inference('demod', [status(thm)], ['11', '14'])).
% 4.84/5.07  thf('16', plain,
% 4.84/5.07      (![X0 : $i]:
% 4.84/5.07         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 4.84/5.07          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 4.84/5.07      inference('sup-', [status(thm)], ['8', '15'])).
% 4.84/5.07  thf('17', plain,
% 4.84/5.07      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.84/5.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.07  thf(t3_subset, axiom,
% 4.84/5.07    (![A:$i,B:$i]:
% 4.84/5.07     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.84/5.07  thf('18', plain,
% 4.84/5.07      (![X7 : $i, X8 : $i]:
% 4.84/5.07         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 4.84/5.07      inference('cnf', [status(esa)], [t3_subset])).
% 4.84/5.07  thf('19', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 4.84/5.07      inference('sup-', [status(thm)], ['17', '18'])).
% 4.84/5.07  thf(d10_xboole_0, axiom,
% 4.84/5.07    (![A:$i,B:$i]:
% 4.84/5.07     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.84/5.07  thf('20', plain,
% 4.84/5.07      (![X0 : $i, X2 : $i]:
% 4.84/5.07         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 4.84/5.07      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.84/5.07  thf('21', plain,
% 4.84/5.07      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_D)
% 4.84/5.07        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 4.84/5.07      inference('sup-', [status(thm)], ['19', '20'])).
% 4.84/5.07  thf('22', plain,
% 4.84/5.07      ((~ (r1_tarski @ k1_xboole_0 @ sk_D)
% 4.84/5.07        | ((sk_A) = (k1_relat_1 @ sk_D))
% 4.84/5.07        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 4.84/5.07      inference('sup-', [status(thm)], ['16', '21'])).
% 4.84/5.07  thf(t4_subset_1, axiom,
% 4.84/5.07    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 4.84/5.07  thf('23', plain,
% 4.84/5.07      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 4.84/5.07      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.84/5.07  thf('24', plain,
% 4.84/5.07      (![X7 : $i, X8 : $i]:
% 4.84/5.07         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 4.84/5.07      inference('cnf', [status(esa)], [t3_subset])).
% 4.84/5.07  thf('25', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 4.84/5.07      inference('sup-', [status(thm)], ['23', '24'])).
% 4.84/5.07  thf('26', plain,
% 4.84/5.07      ((((sk_A) = (k1_relat_1 @ sk_D)) | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 4.84/5.07      inference('demod', [status(thm)], ['22', '25'])).
% 4.84/5.07  thf('27', plain,
% 4.84/5.07      (![X0 : $i]:
% 4.84/5.07         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 4.84/5.07          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 4.84/5.07      inference('sup-', [status(thm)], ['8', '15'])).
% 4.84/5.07  thf('28', plain,
% 4.84/5.07      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.84/5.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.07  thf('29', plain,
% 4.84/5.07      (![X7 : $i, X8 : $i]:
% 4.84/5.07         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 4.84/5.07      inference('cnf', [status(esa)], [t3_subset])).
% 4.84/5.07  thf('30', plain, ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 4.84/5.07      inference('sup-', [status(thm)], ['28', '29'])).
% 4.84/5.07  thf('31', plain,
% 4.84/5.07      (![X0 : $i, X2 : $i]:
% 4.84/5.07         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 4.84/5.07      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.84/5.07  thf('32', plain,
% 4.84/5.07      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C_1)
% 4.84/5.07        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 4.84/5.07      inference('sup-', [status(thm)], ['30', '31'])).
% 4.84/5.07  thf('33', plain,
% 4.84/5.07      ((~ (r1_tarski @ k1_xboole_0 @ sk_C_1)
% 4.84/5.07        | ((sk_A) = (k1_relat_1 @ sk_D))
% 4.84/5.07        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 4.84/5.07      inference('sup-', [status(thm)], ['27', '32'])).
% 4.84/5.07  thf('34', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 4.84/5.07      inference('sup-', [status(thm)], ['23', '24'])).
% 4.84/5.07  thf('35', plain,
% 4.84/5.07      ((((sk_A) = (k1_relat_1 @ sk_D))
% 4.84/5.07        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 4.84/5.07      inference('demod', [status(thm)], ['33', '34'])).
% 4.84/5.07  thf('36', plain,
% 4.84/5.07      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 4.84/5.07      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.84/5.07  thf('37', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 4.84/5.07      inference('simplify', [status(thm)], ['36'])).
% 4.84/5.07  thf('38', plain,
% 4.84/5.07      (![X7 : $i, X9 : $i]:
% 4.84/5.07         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 4.84/5.07      inference('cnf', [status(esa)], [t3_subset])).
% 4.84/5.07  thf('39', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 4.84/5.07      inference('sup-', [status(thm)], ['37', '38'])).
% 4.84/5.07  thf('40', plain,
% 4.84/5.07      (![X19 : $i, X20 : $i, X21 : $i]:
% 4.84/5.07         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 4.84/5.07          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 4.84/5.07      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.84/5.07  thf('41', plain,
% 4.84/5.07      (![X0 : $i, X1 : $i]:
% 4.84/5.07         ((k1_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0))
% 4.84/5.07           = (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 4.84/5.07      inference('sup-', [status(thm)], ['39', '40'])).
% 4.84/5.07  thf('42', plain,
% 4.84/5.07      ((((k1_relset_1 @ sk_A @ sk_B @ sk_C_1)
% 4.84/5.07          = (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 4.84/5.07        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 4.84/5.07      inference('sup+', [status(thm)], ['35', '41'])).
% 4.84/5.07  thf('43', plain,
% 4.84/5.07      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.84/5.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.07  thf('44', plain,
% 4.84/5.07      (![X19 : $i, X20 : $i, X21 : $i]:
% 4.84/5.07         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 4.84/5.07          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 4.84/5.07      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.84/5.07  thf('45', plain,
% 4.84/5.07      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 4.84/5.07      inference('sup-', [status(thm)], ['43', '44'])).
% 4.84/5.07  thf('46', plain,
% 4.84/5.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.84/5.07         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 4.84/5.07      inference('sup+', [status(thm)], ['1', '3'])).
% 4.84/5.07  thf('47', plain,
% 4.84/5.07      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.84/5.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.07  thf('48', plain,
% 4.84/5.07      (![X31 : $i, X32 : $i, X33 : $i]:
% 4.84/5.07         (~ (zip_tseitin_0 @ X31 @ X32)
% 4.84/5.07          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 4.84/5.07          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 4.84/5.07      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.84/5.07  thf('49', plain,
% 4.84/5.07      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 4.84/5.07        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 4.84/5.07      inference('sup-', [status(thm)], ['47', '48'])).
% 4.84/5.07  thf('50', plain,
% 4.84/5.07      (![X0 : $i]:
% 4.84/5.07         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 4.84/5.07          | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 4.84/5.07      inference('sup-', [status(thm)], ['46', '49'])).
% 4.84/5.07  thf('51', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 4.84/5.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.07  thf('52', plain,
% 4.84/5.07      (![X28 : $i, X29 : $i, X30 : $i]:
% 4.84/5.07         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 4.84/5.07          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 4.84/5.07          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 4.84/5.07      inference('cnf', [status(esa)], [zf_stmt_3])).
% 4.84/5.07  thf('53', plain,
% 4.84/5.07      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 4.84/5.07        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 4.84/5.07      inference('sup-', [status(thm)], ['51', '52'])).
% 4.84/5.07  thf('54', plain,
% 4.84/5.07      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 4.84/5.07      inference('sup-', [status(thm)], ['43', '44'])).
% 4.84/5.07  thf('55', plain,
% 4.84/5.07      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 4.84/5.07        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 4.84/5.07      inference('demod', [status(thm)], ['53', '54'])).
% 4.84/5.07  thf('56', plain,
% 4.84/5.07      (![X0 : $i]:
% 4.84/5.07         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 4.84/5.07          | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 4.84/5.07      inference('sup-', [status(thm)], ['50', '55'])).
% 4.84/5.07  thf('57', plain,
% 4.84/5.07      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_D)
% 4.84/5.07        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 4.84/5.07      inference('sup-', [status(thm)], ['19', '20'])).
% 4.84/5.07  thf('58', plain,
% 4.84/5.07      ((~ (r1_tarski @ k1_xboole_0 @ sk_D)
% 4.84/5.07        | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 4.84/5.07        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 4.84/5.07      inference('sup-', [status(thm)], ['56', '57'])).
% 4.84/5.07  thf('59', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 4.84/5.07      inference('sup-', [status(thm)], ['23', '24'])).
% 4.84/5.07  thf('60', plain,
% 4.84/5.07      ((((sk_A) = (k1_relat_1 @ sk_C_1))
% 4.84/5.07        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 4.84/5.07      inference('demod', [status(thm)], ['58', '59'])).
% 4.84/5.07  thf('61', plain,
% 4.84/5.07      (![X0 : $i]:
% 4.84/5.07         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 4.84/5.07          | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 4.84/5.07      inference('sup-', [status(thm)], ['50', '55'])).
% 4.84/5.07  thf('62', plain,
% 4.84/5.07      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C_1)
% 4.84/5.07        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 4.84/5.07      inference('sup-', [status(thm)], ['30', '31'])).
% 4.84/5.07  thf('63', plain,
% 4.84/5.07      ((~ (r1_tarski @ k1_xboole_0 @ sk_C_1)
% 4.84/5.07        | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 4.84/5.07        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 4.84/5.07      inference('sup-', [status(thm)], ['61', '62'])).
% 4.84/5.07  thf('64', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 4.84/5.07      inference('sup-', [status(thm)], ['23', '24'])).
% 4.84/5.07  thf('65', plain,
% 4.84/5.07      ((((sk_A) = (k1_relat_1 @ sk_C_1))
% 4.84/5.07        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 4.84/5.07      inference('demod', [status(thm)], ['63', '64'])).
% 4.84/5.07  thf('66', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 4.84/5.07      inference('sup-', [status(thm)], ['37', '38'])).
% 4.84/5.07  thf(redefinition_r2_relset_1, axiom,
% 4.84/5.07    (![A:$i,B:$i,C:$i,D:$i]:
% 4.84/5.07     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.84/5.07         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.84/5.07       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 4.84/5.07  thf('67', plain,
% 4.84/5.07      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 4.84/5.07         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 4.84/5.07          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 4.84/5.07          | (r2_relset_1 @ X23 @ X24 @ X22 @ X25)
% 4.84/5.07          | ((X22) != (X25)))),
% 4.84/5.07      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 4.84/5.07  thf('68', plain,
% 4.84/5.07      (![X23 : $i, X24 : $i, X25 : $i]:
% 4.84/5.07         ((r2_relset_1 @ X23 @ X24 @ X25 @ X25)
% 4.84/5.07          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 4.84/5.07      inference('simplify', [status(thm)], ['67'])).
% 4.84/5.07  thf('69', plain,
% 4.84/5.07      (![X0 : $i, X1 : $i]:
% 4.84/5.07         (r2_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 4.84/5.07          (k2_zfmisc_1 @ X1 @ X0))),
% 4.84/5.07      inference('sup-', [status(thm)], ['66', '68'])).
% 4.84/5.07  thf('70', plain,
% 4.84/5.07      (((r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 4.84/5.07        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 4.84/5.07      inference('sup+', [status(thm)], ['65', '69'])).
% 4.84/5.07  thf('71', plain,
% 4.84/5.07      (((r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)
% 4.84/5.07        | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 4.84/5.07        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 4.84/5.07      inference('sup+', [status(thm)], ['60', '70'])).
% 4.84/5.07  thf('72', plain,
% 4.84/5.07      ((((sk_A) = (k1_relat_1 @ sk_C_1))
% 4.84/5.07        | (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D))),
% 4.84/5.07      inference('simplify', [status(thm)], ['71'])).
% 4.84/5.07  thf('73', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)),
% 4.84/5.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.07  thf('74', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 4.84/5.07      inference('clc', [status(thm)], ['72', '73'])).
% 4.84/5.07  thf('75', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_A))),
% 4.84/5.07      inference('demod', [status(thm)], ['45', '74'])).
% 4.84/5.07  thf('76', plain,
% 4.84/5.07      ((((sk_A) = (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 4.84/5.07        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 4.84/5.07      inference('demod', [status(thm)], ['42', '75'])).
% 4.84/5.07  thf('77', plain,
% 4.84/5.07      ((((sk_A) = (k1_relat_1 @ sk_D))
% 4.84/5.07        | ((sk_A) = (k1_relat_1 @ sk_D))
% 4.84/5.07        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 4.84/5.07      inference('sup+', [status(thm)], ['26', '76'])).
% 4.84/5.07  thf('78', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 4.84/5.07      inference('simplify', [status(thm)], ['77'])).
% 4.84/5.07  thf('79', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 4.84/5.07      inference('clc', [status(thm)], ['72', '73'])).
% 4.84/5.07  thf(t9_funct_1, axiom,
% 4.84/5.07    (![A:$i]:
% 4.84/5.07     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.84/5.07       ( ![B:$i]:
% 4.84/5.07         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 4.84/5.07           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 4.84/5.07               ( ![C:$i]:
% 4.84/5.07                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 4.84/5.07                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 4.84/5.07             ( ( A ) = ( B ) ) ) ) ) ))).
% 4.84/5.07  thf('80', plain,
% 4.84/5.07      (![X17 : $i, X18 : $i]:
% 4.84/5.07         (~ (v1_relat_1 @ X17)
% 4.84/5.07          | ~ (v1_funct_1 @ X17)
% 4.84/5.07          | ((X18) = (X17))
% 4.84/5.07          | (r2_hidden @ (sk_C @ X17 @ X18) @ (k1_relat_1 @ X18))
% 4.84/5.07          | ((k1_relat_1 @ X18) != (k1_relat_1 @ X17))
% 4.84/5.07          | ~ (v1_funct_1 @ X18)
% 4.84/5.07          | ~ (v1_relat_1 @ X18))),
% 4.84/5.07      inference('cnf', [status(esa)], [t9_funct_1])).
% 4.84/5.07  thf('81', plain,
% 4.84/5.07      (![X0 : $i]:
% 4.84/5.07         (((sk_A) != (k1_relat_1 @ X0))
% 4.84/5.07          | ~ (v1_relat_1 @ sk_C_1)
% 4.84/5.07          | ~ (v1_funct_1 @ sk_C_1)
% 4.84/5.07          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 4.84/5.07          | ((sk_C_1) = (X0))
% 4.84/5.07          | ~ (v1_funct_1 @ X0)
% 4.84/5.07          | ~ (v1_relat_1 @ X0))),
% 4.84/5.07      inference('sup-', [status(thm)], ['79', '80'])).
% 4.84/5.07  thf('82', plain,
% 4.84/5.07      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.84/5.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.07  thf(cc2_relat_1, axiom,
% 4.84/5.07    (![A:$i]:
% 4.84/5.07     ( ( v1_relat_1 @ A ) =>
% 4.84/5.07       ( ![B:$i]:
% 4.84/5.07         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 4.84/5.07  thf('83', plain,
% 4.84/5.07      (![X13 : $i, X14 : $i]:
% 4.84/5.07         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 4.84/5.07          | (v1_relat_1 @ X13)
% 4.84/5.07          | ~ (v1_relat_1 @ X14))),
% 4.84/5.07      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.84/5.07  thf('84', plain,
% 4.84/5.07      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_1))),
% 4.84/5.07      inference('sup-', [status(thm)], ['82', '83'])).
% 4.84/5.07  thf(fc6_relat_1, axiom,
% 4.84/5.07    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 4.84/5.07  thf('85', plain,
% 4.84/5.07      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X15 @ X16))),
% 4.84/5.07      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.84/5.07  thf('86', plain, ((v1_relat_1 @ sk_C_1)),
% 4.84/5.07      inference('demod', [status(thm)], ['84', '85'])).
% 4.84/5.07  thf('87', plain, ((v1_funct_1 @ sk_C_1)),
% 4.84/5.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.07  thf('88', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 4.84/5.07      inference('clc', [status(thm)], ['72', '73'])).
% 4.84/5.07  thf('89', plain,
% 4.84/5.07      (![X0 : $i]:
% 4.84/5.07         (((sk_A) != (k1_relat_1 @ X0))
% 4.84/5.07          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_A)
% 4.84/5.07          | ((sk_C_1) = (X0))
% 4.84/5.07          | ~ (v1_funct_1 @ X0)
% 4.84/5.07          | ~ (v1_relat_1 @ X0))),
% 4.84/5.07      inference('demod', [status(thm)], ['81', '86', '87', '88'])).
% 4.84/5.07  thf('90', plain,
% 4.84/5.07      ((((sk_A) != (sk_A))
% 4.84/5.07        | ~ (v1_relat_1 @ sk_D)
% 4.84/5.07        | ~ (v1_funct_1 @ sk_D)
% 4.84/5.07        | ((sk_C_1) = (sk_D))
% 4.84/5.07        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 4.84/5.07      inference('sup-', [status(thm)], ['78', '89'])).
% 4.84/5.07  thf('91', plain,
% 4.84/5.07      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.84/5.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.07  thf('92', plain,
% 4.84/5.07      (![X13 : $i, X14 : $i]:
% 4.84/5.07         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 4.84/5.07          | (v1_relat_1 @ X13)
% 4.84/5.07          | ~ (v1_relat_1 @ X14))),
% 4.84/5.07      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.84/5.07  thf('93', plain,
% 4.84/5.07      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 4.84/5.07      inference('sup-', [status(thm)], ['91', '92'])).
% 4.84/5.07  thf('94', plain,
% 4.84/5.07      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X15 @ X16))),
% 4.84/5.07      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.84/5.07  thf('95', plain, ((v1_relat_1 @ sk_D)),
% 4.84/5.07      inference('demod', [status(thm)], ['93', '94'])).
% 4.84/5.07  thf('96', plain, ((v1_funct_1 @ sk_D)),
% 4.84/5.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.07  thf('97', plain,
% 4.84/5.07      ((((sk_A) != (sk_A))
% 4.84/5.07        | ((sk_C_1) = (sk_D))
% 4.84/5.07        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 4.84/5.07      inference('demod', [status(thm)], ['90', '95', '96'])).
% 4.84/5.07  thf('98', plain,
% 4.84/5.07      (((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A) | ((sk_C_1) = (sk_D)))),
% 4.84/5.07      inference('simplify', [status(thm)], ['97'])).
% 4.84/5.07  thf('99', plain,
% 4.84/5.07      (![X34 : $i]:
% 4.84/5.07         (((k1_funct_1 @ sk_C_1 @ X34) = (k1_funct_1 @ sk_D @ X34))
% 4.84/5.07          | ~ (r2_hidden @ X34 @ sk_A))),
% 4.84/5.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.07  thf('100', plain,
% 4.84/5.07      ((((sk_C_1) = (sk_D))
% 4.84/5.07        | ((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 4.84/5.07            = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))))),
% 4.84/5.07      inference('sup-', [status(thm)], ['98', '99'])).
% 4.84/5.07  thf('101', plain,
% 4.84/5.07      (((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 4.84/5.07         = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))),
% 4.84/5.07      inference('condensation', [status(thm)], ['100'])).
% 4.84/5.07  thf('102', plain,
% 4.84/5.07      (![X17 : $i, X18 : $i]:
% 4.84/5.07         (~ (v1_relat_1 @ X17)
% 4.84/5.07          | ~ (v1_funct_1 @ X17)
% 4.84/5.07          | ((X18) = (X17))
% 4.84/5.07          | ((k1_funct_1 @ X18 @ (sk_C @ X17 @ X18))
% 4.84/5.07              != (k1_funct_1 @ X17 @ (sk_C @ X17 @ X18)))
% 4.84/5.07          | ((k1_relat_1 @ X18) != (k1_relat_1 @ X17))
% 4.84/5.07          | ~ (v1_funct_1 @ X18)
% 4.84/5.07          | ~ (v1_relat_1 @ X18))),
% 4.84/5.07      inference('cnf', [status(esa)], [t9_funct_1])).
% 4.84/5.07  thf('103', plain,
% 4.84/5.07      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 4.84/5.07          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 4.84/5.07        | ~ (v1_relat_1 @ sk_C_1)
% 4.84/5.07        | ~ (v1_funct_1 @ sk_C_1)
% 4.84/5.07        | ((k1_relat_1 @ sk_C_1) != (k1_relat_1 @ sk_D))
% 4.84/5.07        | ((sk_C_1) = (sk_D))
% 4.84/5.07        | ~ (v1_funct_1 @ sk_D)
% 4.84/5.07        | ~ (v1_relat_1 @ sk_D))),
% 4.84/5.07      inference('sup-', [status(thm)], ['101', '102'])).
% 4.84/5.07  thf('104', plain, ((v1_relat_1 @ sk_C_1)),
% 4.84/5.07      inference('demod', [status(thm)], ['84', '85'])).
% 4.84/5.07  thf('105', plain, ((v1_funct_1 @ sk_C_1)),
% 4.84/5.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.07  thf('106', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 4.84/5.07      inference('clc', [status(thm)], ['72', '73'])).
% 4.84/5.07  thf('107', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 4.84/5.07      inference('simplify', [status(thm)], ['77'])).
% 4.84/5.07  thf('108', plain, ((v1_funct_1 @ sk_D)),
% 4.84/5.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.07  thf('109', plain, ((v1_relat_1 @ sk_D)),
% 4.84/5.07      inference('demod', [status(thm)], ['93', '94'])).
% 4.84/5.07  thf('110', plain,
% 4.84/5.07      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 4.84/5.07          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 4.84/5.07        | ((sk_A) != (sk_A))
% 4.84/5.07        | ((sk_C_1) = (sk_D)))),
% 4.84/5.07      inference('demod', [status(thm)],
% 4.84/5.07                ['103', '104', '105', '106', '107', '108', '109'])).
% 4.84/5.07  thf('111', plain, (((sk_C_1) = (sk_D))),
% 4.84/5.07      inference('simplify', [status(thm)], ['110'])).
% 4.84/5.07  thf('112', plain,
% 4.84/5.07      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.84/5.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.07  thf('113', plain,
% 4.84/5.07      (![X23 : $i, X24 : $i, X25 : $i]:
% 4.84/5.07         ((r2_relset_1 @ X23 @ X24 @ X25 @ X25)
% 4.84/5.07          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 4.84/5.07      inference('simplify', [status(thm)], ['67'])).
% 4.84/5.07  thf('114', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1)),
% 4.84/5.07      inference('sup-', [status(thm)], ['112', '113'])).
% 4.84/5.07  thf('115', plain, ($false),
% 4.84/5.07      inference('demod', [status(thm)], ['0', '111', '114'])).
% 4.84/5.07  
% 4.84/5.07  % SZS output end Refutation
% 4.84/5.07  
% 4.84/5.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
