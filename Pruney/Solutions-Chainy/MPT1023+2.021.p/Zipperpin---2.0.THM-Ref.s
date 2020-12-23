%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Yulewttsve

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:31 EST 2020

% Result     : Theorem 11.53s
% Output     : Refutation 11.53s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 798 expanded)
%              Number of leaves         :   36 ( 249 expanded)
%              Depth                    :   25
%              Number of atoms          : 1402 (11195 expanded)
%              Number of equality atoms :  141 ( 668 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
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
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('39',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( r2_relset_1 @ X24 @ X25 @ X23 @ X26 )
      | ( X23 != X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('68',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r2_relset_1 @ X24 @ X25 @ X26 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
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

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('80',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C_1 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ sk_C_1 )
      | ( zip_tseitin_0 @ sk_B @ X0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = sk_C_1 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D @ sk_C_1 )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ~ ( r1_tarski @ sk_C_1 @ sk_D )
      | ( sk_C_1 = sk_D ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('89',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_D )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_D ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D )
      | ( zip_tseitin_0 @ sk_B @ X0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = sk_D ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = sk_D ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ sk_D )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 = sk_D )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['87','94'])).

thf('96',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('97',plain,
    ( ( sk_C_1 = sk_D )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('99',plain,
    ( ( sk_C_1 = sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

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

thf('100',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( X16 = X15 )
      | ( r2_hidden @ ( sk_C @ X15 @ X16 ) @ ( k1_relat_1 @ X16 ) )
      | ( ( k1_relat_1 @ X16 )
       != ( k1_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('101',plain,(
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
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('103',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('104',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( sk_C_1 = sk_D )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['101','104','105'])).

thf('107',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( sk_C_1 = sk_D )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_A )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference('sup-',[status(thm)],['78','108'])).

thf('110',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('112',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(demod,[status(thm)],['109','112','113'])).

thf('115',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(simplify,[status(thm)],['114'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('116',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('117',plain,
    ( ( sk_C_1 = sk_D )
    | ( m1_subset_1 @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X35: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ X35 )
        = ( k1_funct_1 @ sk_D @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ sk_A ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( X16 = X15 )
      | ( ( k1_funct_1 @ X16 @ ( sk_C @ X15 @ X16 ) )
       != ( k1_funct_1 @ X15 @ ( sk_C @ X15 @ X16 ) ) )
      | ( ( k1_relat_1 @ X16 )
       != ( k1_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
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
    inference('sup-',[status(thm)],['102','103'])).

thf('124',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('126',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['77'])).

thf('127',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['110','111'])).

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
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r2_relset_1 @ X24 @ X25 @ X26 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('133',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    $false ),
    inference(demod,[status(thm)],['0','130','133'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Yulewttsve
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 11.53/11.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 11.53/11.73  % Solved by: fo/fo7.sh
% 11.53/11.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 11.53/11.73  % done 7146 iterations in 11.273s
% 11.53/11.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 11.53/11.73  % SZS output start Refutation
% 11.53/11.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 11.53/11.73  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 11.53/11.73  thf(sk_D_type, type, sk_D: $i).
% 11.53/11.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 11.53/11.73  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 11.53/11.73  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 11.53/11.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 11.53/11.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 11.53/11.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 11.53/11.73  thf(sk_B_type, type, sk_B: $i).
% 11.53/11.73  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 11.53/11.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 11.53/11.73  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 11.53/11.73  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 11.53/11.73  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 11.53/11.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 11.53/11.73  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 11.53/11.73  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 11.53/11.73  thf(sk_A_type, type, sk_A: $i).
% 11.53/11.73  thf(sk_C_1_type, type, sk_C_1: $i).
% 11.53/11.73  thf(t113_funct_2, conjecture,
% 11.53/11.73    (![A:$i,B:$i,C:$i]:
% 11.53/11.73     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 11.53/11.73         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 11.53/11.73       ( ![D:$i]:
% 11.53/11.73         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 11.53/11.73             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 11.53/11.73           ( ( ![E:$i]:
% 11.53/11.73               ( ( m1_subset_1 @ E @ A ) =>
% 11.53/11.73                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 11.53/11.73             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 11.53/11.73  thf(zf_stmt_0, negated_conjecture,
% 11.53/11.73    (~( ![A:$i,B:$i,C:$i]:
% 11.53/11.73        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 11.53/11.73            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 11.53/11.73          ( ![D:$i]:
% 11.53/11.73            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 11.53/11.73                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 11.53/11.73              ( ( ![E:$i]:
% 11.53/11.73                  ( ( m1_subset_1 @ E @ A ) =>
% 11.53/11.73                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 11.53/11.73                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 11.53/11.73    inference('cnf.neg', [status(esa)], [t113_funct_2])).
% 11.53/11.73  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)),
% 11.53/11.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.53/11.73  thf(d1_funct_2, axiom,
% 11.53/11.73    (![A:$i,B:$i,C:$i]:
% 11.53/11.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 11.53/11.73       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 11.53/11.73           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 11.53/11.73             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 11.53/11.73         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 11.53/11.73           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 11.53/11.73             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 11.53/11.73  thf(zf_stmt_1, axiom,
% 11.53/11.73    (![B:$i,A:$i]:
% 11.53/11.73     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 11.53/11.73       ( zip_tseitin_0 @ B @ A ) ))).
% 11.53/11.73  thf('1', plain,
% 11.53/11.73      (![X27 : $i, X28 : $i]:
% 11.53/11.73         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 11.53/11.73      inference('cnf', [status(esa)], [zf_stmt_1])).
% 11.53/11.73  thf(t113_zfmisc_1, axiom,
% 11.53/11.73    (![A:$i,B:$i]:
% 11.53/11.73     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 11.53/11.73       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 11.53/11.73  thf('2', plain,
% 11.53/11.73      (![X4 : $i, X5 : $i]:
% 11.53/11.73         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 11.53/11.73      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 11.53/11.73  thf('3', plain,
% 11.53/11.73      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 11.53/11.73      inference('simplify', [status(thm)], ['2'])).
% 11.53/11.73  thf('4', plain,
% 11.53/11.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.53/11.73         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 11.53/11.73      inference('sup+', [status(thm)], ['1', '3'])).
% 11.53/11.73  thf('5', plain,
% 11.53/11.73      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 11.53/11.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.53/11.74  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 11.53/11.74  thf(zf_stmt_3, axiom,
% 11.53/11.74    (![C:$i,B:$i,A:$i]:
% 11.53/11.74     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 11.53/11.74       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 11.53/11.74  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 11.53/11.74  thf(zf_stmt_5, axiom,
% 11.53/11.74    (![A:$i,B:$i,C:$i]:
% 11.53/11.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 11.53/11.74       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 11.53/11.74         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 11.53/11.74           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 11.53/11.74             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 11.53/11.74  thf('6', plain,
% 11.53/11.74      (![X32 : $i, X33 : $i, X34 : $i]:
% 11.53/11.74         (~ (zip_tseitin_0 @ X32 @ X33)
% 11.53/11.74          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 11.53/11.74          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 11.53/11.74      inference('cnf', [status(esa)], [zf_stmt_5])).
% 11.53/11.74  thf('7', plain,
% 11.53/11.74      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 11.53/11.74      inference('sup-', [status(thm)], ['5', '6'])).
% 11.53/11.74  thf('8', plain,
% 11.53/11.74      (![X0 : $i]:
% 11.53/11.74         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 11.53/11.74          | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 11.53/11.74      inference('sup-', [status(thm)], ['4', '7'])).
% 11.53/11.74  thf('9', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 11.53/11.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.53/11.74  thf('10', plain,
% 11.53/11.74      (![X29 : $i, X30 : $i, X31 : $i]:
% 11.53/11.74         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 11.53/11.74          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 11.53/11.74          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 11.53/11.74      inference('cnf', [status(esa)], [zf_stmt_3])).
% 11.53/11.74  thf('11', plain,
% 11.53/11.74      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 11.53/11.74        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 11.53/11.74      inference('sup-', [status(thm)], ['9', '10'])).
% 11.53/11.74  thf('12', plain,
% 11.53/11.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 11.53/11.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.53/11.74  thf(redefinition_k1_relset_1, axiom,
% 11.53/11.74    (![A:$i,B:$i,C:$i]:
% 11.53/11.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 11.53/11.74       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 11.53/11.74  thf('13', plain,
% 11.53/11.74      (![X20 : $i, X21 : $i, X22 : $i]:
% 11.53/11.74         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 11.53/11.74          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 11.53/11.74      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 11.53/11.74  thf('14', plain,
% 11.53/11.74      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 11.53/11.74      inference('sup-', [status(thm)], ['12', '13'])).
% 11.53/11.74  thf('15', plain,
% 11.53/11.74      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 11.53/11.74      inference('demod', [status(thm)], ['11', '14'])).
% 11.53/11.74  thf('16', plain,
% 11.53/11.74      (![X0 : $i]:
% 11.53/11.74         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 11.53/11.74          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 11.53/11.74      inference('sup-', [status(thm)], ['8', '15'])).
% 11.53/11.74  thf('17', plain,
% 11.53/11.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 11.53/11.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.53/11.74  thf(t3_subset, axiom,
% 11.53/11.74    (![A:$i,B:$i]:
% 11.53/11.74     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 11.53/11.74  thf('18', plain,
% 11.53/11.74      (![X9 : $i, X10 : $i]:
% 11.53/11.74         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 11.53/11.74      inference('cnf', [status(esa)], [t3_subset])).
% 11.53/11.74  thf('19', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 11.53/11.74      inference('sup-', [status(thm)], ['17', '18'])).
% 11.53/11.74  thf(d10_xboole_0, axiom,
% 11.53/11.74    (![A:$i,B:$i]:
% 11.53/11.74     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 11.53/11.74  thf('20', plain,
% 11.53/11.74      (![X0 : $i, X2 : $i]:
% 11.53/11.74         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 11.53/11.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 11.53/11.74  thf('21', plain,
% 11.53/11.74      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_D)
% 11.53/11.74        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 11.53/11.74      inference('sup-', [status(thm)], ['19', '20'])).
% 11.53/11.74  thf('22', plain,
% 11.53/11.74      ((~ (r1_tarski @ k1_xboole_0 @ sk_D)
% 11.53/11.74        | ((sk_A) = (k1_relat_1 @ sk_D))
% 11.53/11.74        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 11.53/11.74      inference('sup-', [status(thm)], ['16', '21'])).
% 11.53/11.74  thf(t4_subset_1, axiom,
% 11.53/11.74    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 11.53/11.74  thf('23', plain,
% 11.53/11.74      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 11.53/11.74      inference('cnf', [status(esa)], [t4_subset_1])).
% 11.53/11.74  thf('24', plain,
% 11.53/11.74      (![X9 : $i, X10 : $i]:
% 11.53/11.74         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 11.53/11.74      inference('cnf', [status(esa)], [t3_subset])).
% 11.53/11.74  thf('25', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 11.53/11.74      inference('sup-', [status(thm)], ['23', '24'])).
% 11.53/11.74  thf('26', plain,
% 11.53/11.74      ((((sk_A) = (k1_relat_1 @ sk_D)) | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 11.53/11.74      inference('demod', [status(thm)], ['22', '25'])).
% 11.53/11.74  thf('27', plain,
% 11.53/11.74      (![X0 : $i]:
% 11.53/11.74         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 11.53/11.74          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 11.53/11.74      inference('sup-', [status(thm)], ['8', '15'])).
% 11.53/11.74  thf('28', plain,
% 11.53/11.74      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 11.53/11.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.53/11.74  thf('29', plain,
% 11.53/11.74      (![X9 : $i, X10 : $i]:
% 11.53/11.74         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 11.53/11.74      inference('cnf', [status(esa)], [t3_subset])).
% 11.53/11.74  thf('30', plain, ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 11.53/11.74      inference('sup-', [status(thm)], ['28', '29'])).
% 11.53/11.74  thf('31', plain,
% 11.53/11.74      (![X0 : $i, X2 : $i]:
% 11.53/11.74         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 11.53/11.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 11.53/11.74  thf('32', plain,
% 11.53/11.74      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C_1)
% 11.53/11.74        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 11.53/11.74      inference('sup-', [status(thm)], ['30', '31'])).
% 11.53/11.74  thf('33', plain,
% 11.53/11.74      ((~ (r1_tarski @ k1_xboole_0 @ sk_C_1)
% 11.53/11.74        | ((sk_A) = (k1_relat_1 @ sk_D))
% 11.53/11.74        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 11.53/11.74      inference('sup-', [status(thm)], ['27', '32'])).
% 11.53/11.74  thf('34', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 11.53/11.74      inference('sup-', [status(thm)], ['23', '24'])).
% 11.53/11.74  thf('35', plain,
% 11.53/11.74      ((((sk_A) = (k1_relat_1 @ sk_D))
% 11.53/11.74        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 11.53/11.74      inference('demod', [status(thm)], ['33', '34'])).
% 11.53/11.74  thf('36', plain,
% 11.53/11.74      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 11.53/11.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 11.53/11.74  thf('37', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 11.53/11.74      inference('simplify', [status(thm)], ['36'])).
% 11.53/11.74  thf('38', plain,
% 11.53/11.74      (![X9 : $i, X11 : $i]:
% 11.53/11.74         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 11.53/11.74      inference('cnf', [status(esa)], [t3_subset])).
% 11.53/11.74  thf('39', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 11.53/11.74      inference('sup-', [status(thm)], ['37', '38'])).
% 11.53/11.74  thf('40', plain,
% 11.53/11.74      (![X20 : $i, X21 : $i, X22 : $i]:
% 11.53/11.74         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 11.53/11.74          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 11.53/11.74      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 11.53/11.74  thf('41', plain,
% 11.53/11.74      (![X0 : $i, X1 : $i]:
% 11.53/11.74         ((k1_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0))
% 11.53/11.74           = (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 11.53/11.74      inference('sup-', [status(thm)], ['39', '40'])).
% 11.53/11.74  thf('42', plain,
% 11.53/11.74      ((((k1_relset_1 @ sk_A @ sk_B @ sk_C_1)
% 11.53/11.74          = (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 11.53/11.74        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 11.53/11.74      inference('sup+', [status(thm)], ['35', '41'])).
% 11.53/11.74  thf('43', plain,
% 11.53/11.74      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 11.53/11.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.53/11.74  thf('44', plain,
% 11.53/11.74      (![X20 : $i, X21 : $i, X22 : $i]:
% 11.53/11.74         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 11.53/11.74          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 11.53/11.74      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 11.53/11.74  thf('45', plain,
% 11.53/11.74      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 11.53/11.74      inference('sup-', [status(thm)], ['43', '44'])).
% 11.53/11.74  thf('46', plain,
% 11.53/11.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.53/11.74         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 11.53/11.74      inference('sup+', [status(thm)], ['1', '3'])).
% 11.53/11.74  thf('47', plain,
% 11.53/11.74      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 11.53/11.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.53/11.74  thf('48', plain,
% 11.53/11.74      (![X32 : $i, X33 : $i, X34 : $i]:
% 11.53/11.74         (~ (zip_tseitin_0 @ X32 @ X33)
% 11.53/11.74          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 11.53/11.74          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 11.53/11.74      inference('cnf', [status(esa)], [zf_stmt_5])).
% 11.53/11.74  thf('49', plain,
% 11.53/11.74      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 11.53/11.74        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 11.53/11.74      inference('sup-', [status(thm)], ['47', '48'])).
% 11.53/11.74  thf('50', plain,
% 11.53/11.74      (![X0 : $i]:
% 11.53/11.74         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 11.53/11.74          | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 11.53/11.74      inference('sup-', [status(thm)], ['46', '49'])).
% 11.53/11.74  thf('51', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 11.53/11.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.53/11.74  thf('52', plain,
% 11.53/11.74      (![X29 : $i, X30 : $i, X31 : $i]:
% 11.53/11.74         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 11.53/11.74          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 11.53/11.74          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 11.53/11.74      inference('cnf', [status(esa)], [zf_stmt_3])).
% 11.53/11.74  thf('53', plain,
% 11.53/11.74      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 11.53/11.74        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 11.53/11.74      inference('sup-', [status(thm)], ['51', '52'])).
% 11.53/11.74  thf('54', plain,
% 11.53/11.74      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 11.53/11.74      inference('sup-', [status(thm)], ['43', '44'])).
% 11.53/11.74  thf('55', plain,
% 11.53/11.74      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 11.53/11.74        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 11.53/11.74      inference('demod', [status(thm)], ['53', '54'])).
% 11.53/11.74  thf('56', plain,
% 11.53/11.74      (![X0 : $i]:
% 11.53/11.74         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 11.53/11.74          | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 11.53/11.74      inference('sup-', [status(thm)], ['50', '55'])).
% 11.53/11.74  thf('57', plain,
% 11.53/11.74      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_D)
% 11.53/11.74        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 11.53/11.74      inference('sup-', [status(thm)], ['19', '20'])).
% 11.53/11.74  thf('58', plain,
% 11.53/11.74      ((~ (r1_tarski @ k1_xboole_0 @ sk_D)
% 11.53/11.74        | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 11.53/11.74        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 11.53/11.74      inference('sup-', [status(thm)], ['56', '57'])).
% 11.53/11.74  thf('59', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 11.53/11.74      inference('sup-', [status(thm)], ['23', '24'])).
% 11.53/11.74  thf('60', plain,
% 11.53/11.74      ((((sk_A) = (k1_relat_1 @ sk_C_1))
% 11.53/11.74        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 11.53/11.74      inference('demod', [status(thm)], ['58', '59'])).
% 11.53/11.74  thf('61', plain,
% 11.53/11.74      (![X0 : $i]:
% 11.53/11.74         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 11.53/11.74          | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 11.53/11.74      inference('sup-', [status(thm)], ['50', '55'])).
% 11.53/11.74  thf('62', plain,
% 11.53/11.74      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C_1)
% 11.53/11.74        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 11.53/11.74      inference('sup-', [status(thm)], ['30', '31'])).
% 11.53/11.74  thf('63', plain,
% 11.53/11.74      ((~ (r1_tarski @ k1_xboole_0 @ sk_C_1)
% 11.53/11.74        | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 11.53/11.74        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 11.53/11.74      inference('sup-', [status(thm)], ['61', '62'])).
% 11.53/11.74  thf('64', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 11.53/11.74      inference('sup-', [status(thm)], ['23', '24'])).
% 11.53/11.74  thf('65', plain,
% 11.53/11.74      ((((sk_A) = (k1_relat_1 @ sk_C_1))
% 11.53/11.74        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 11.53/11.74      inference('demod', [status(thm)], ['63', '64'])).
% 11.53/11.74  thf('66', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 11.53/11.74      inference('sup-', [status(thm)], ['37', '38'])).
% 11.53/11.74  thf(redefinition_r2_relset_1, axiom,
% 11.53/11.74    (![A:$i,B:$i,C:$i,D:$i]:
% 11.53/11.74     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 11.53/11.74         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 11.53/11.74       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 11.53/11.74  thf('67', plain,
% 11.53/11.74      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 11.53/11.74         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 11.53/11.74          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 11.53/11.74          | (r2_relset_1 @ X24 @ X25 @ X23 @ X26)
% 11.53/11.74          | ((X23) != (X26)))),
% 11.53/11.74      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 11.53/11.74  thf('68', plain,
% 11.53/11.74      (![X24 : $i, X25 : $i, X26 : $i]:
% 11.53/11.74         ((r2_relset_1 @ X24 @ X25 @ X26 @ X26)
% 11.53/11.74          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 11.53/11.74      inference('simplify', [status(thm)], ['67'])).
% 11.53/11.74  thf('69', plain,
% 11.53/11.74      (![X0 : $i, X1 : $i]:
% 11.53/11.74         (r2_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 11.53/11.74          (k2_zfmisc_1 @ X1 @ X0))),
% 11.53/11.74      inference('sup-', [status(thm)], ['66', '68'])).
% 11.53/11.74  thf('70', plain,
% 11.53/11.74      (((r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 11.53/11.74        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 11.53/11.74      inference('sup+', [status(thm)], ['65', '69'])).
% 11.53/11.74  thf('71', plain,
% 11.53/11.74      (((r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)
% 11.53/11.74        | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 11.53/11.74        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 11.53/11.74      inference('sup+', [status(thm)], ['60', '70'])).
% 11.53/11.74  thf('72', plain,
% 11.53/11.74      ((((sk_A) = (k1_relat_1 @ sk_C_1))
% 11.53/11.74        | (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D))),
% 11.53/11.74      inference('simplify', [status(thm)], ['71'])).
% 11.53/11.74  thf('73', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)),
% 11.53/11.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.53/11.74  thf('74', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 11.53/11.74      inference('clc', [status(thm)], ['72', '73'])).
% 11.53/11.74  thf('75', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_A))),
% 11.53/11.74      inference('demod', [status(thm)], ['45', '74'])).
% 11.53/11.74  thf('76', plain,
% 11.53/11.74      ((((sk_A) = (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 11.53/11.74        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 11.53/11.74      inference('demod', [status(thm)], ['42', '75'])).
% 11.53/11.74  thf('77', plain,
% 11.53/11.74      ((((sk_A) = (k1_relat_1 @ sk_D))
% 11.53/11.74        | ((sk_A) = (k1_relat_1 @ sk_D))
% 11.53/11.74        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 11.53/11.74      inference('sup+', [status(thm)], ['26', '76'])).
% 11.53/11.74  thf('78', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 11.53/11.74      inference('simplify', [status(thm)], ['77'])).
% 11.53/11.74  thf('79', plain,
% 11.53/11.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.53/11.74         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 11.53/11.74      inference('sup+', [status(thm)], ['1', '3'])).
% 11.53/11.74  thf('80', plain,
% 11.53/11.74      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C_1)
% 11.53/11.74        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 11.53/11.74      inference('sup-', [status(thm)], ['30', '31'])).
% 11.53/11.74  thf('81', plain,
% 11.53/11.74      (![X0 : $i]:
% 11.53/11.74         (~ (r1_tarski @ k1_xboole_0 @ sk_C_1)
% 11.53/11.74          | (zip_tseitin_0 @ sk_B @ X0)
% 11.53/11.74          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 11.53/11.74      inference('sup-', [status(thm)], ['79', '80'])).
% 11.53/11.74  thf('82', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 11.53/11.74      inference('sup-', [status(thm)], ['23', '24'])).
% 11.53/11.74  thf('83', plain,
% 11.53/11.74      (![X0 : $i]:
% 11.53/11.74         ((zip_tseitin_0 @ sk_B @ X0)
% 11.53/11.74          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 11.53/11.74      inference('demod', [status(thm)], ['81', '82'])).
% 11.53/11.74  thf('84', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 11.53/11.74      inference('sup-', [status(thm)], ['17', '18'])).
% 11.53/11.74  thf('85', plain,
% 11.53/11.74      (![X0 : $i]: ((r1_tarski @ sk_D @ sk_C_1) | (zip_tseitin_0 @ sk_B @ X0))),
% 11.53/11.74      inference('sup+', [status(thm)], ['83', '84'])).
% 11.53/11.74  thf('86', plain,
% 11.53/11.74      (![X0 : $i, X2 : $i]:
% 11.53/11.74         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 11.53/11.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 11.53/11.74  thf('87', plain,
% 11.53/11.74      (![X0 : $i]:
% 11.53/11.74         ((zip_tseitin_0 @ sk_B @ X0)
% 11.53/11.74          | ~ (r1_tarski @ sk_C_1 @ sk_D)
% 11.53/11.74          | ((sk_C_1) = (sk_D)))),
% 11.53/11.74      inference('sup-', [status(thm)], ['85', '86'])).
% 11.53/11.74  thf('88', plain,
% 11.53/11.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.53/11.74         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 11.53/11.74      inference('sup+', [status(thm)], ['1', '3'])).
% 11.53/11.74  thf('89', plain,
% 11.53/11.74      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_D)
% 11.53/11.74        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 11.53/11.74      inference('sup-', [status(thm)], ['19', '20'])).
% 11.53/11.74  thf('90', plain,
% 11.53/11.74      (![X0 : $i]:
% 11.53/11.74         (~ (r1_tarski @ k1_xboole_0 @ sk_D)
% 11.53/11.74          | (zip_tseitin_0 @ sk_B @ X0)
% 11.53/11.74          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 11.53/11.74      inference('sup-', [status(thm)], ['88', '89'])).
% 11.53/11.74  thf('91', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 11.53/11.74      inference('sup-', [status(thm)], ['23', '24'])).
% 11.53/11.74  thf('92', plain,
% 11.53/11.74      (![X0 : $i]:
% 11.53/11.74         ((zip_tseitin_0 @ sk_B @ X0) | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 11.53/11.74      inference('demod', [status(thm)], ['90', '91'])).
% 11.53/11.74  thf('93', plain, ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 11.53/11.74      inference('sup-', [status(thm)], ['28', '29'])).
% 11.53/11.74  thf('94', plain,
% 11.53/11.74      (![X0 : $i]: ((r1_tarski @ sk_C_1 @ sk_D) | (zip_tseitin_0 @ sk_B @ X0))),
% 11.53/11.74      inference('sup+', [status(thm)], ['92', '93'])).
% 11.53/11.74  thf('95', plain,
% 11.53/11.74      (![X0 : $i]: (((sk_C_1) = (sk_D)) | (zip_tseitin_0 @ sk_B @ X0))),
% 11.53/11.74      inference('clc', [status(thm)], ['87', '94'])).
% 11.53/11.74  thf('96', plain,
% 11.53/11.74      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 11.53/11.74        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 11.53/11.74      inference('sup-', [status(thm)], ['47', '48'])).
% 11.53/11.74  thf('97', plain,
% 11.53/11.74      ((((sk_C_1) = (sk_D)) | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 11.53/11.74      inference('sup-', [status(thm)], ['95', '96'])).
% 11.53/11.74  thf('98', plain,
% 11.53/11.74      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 11.53/11.74        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 11.53/11.74      inference('demod', [status(thm)], ['53', '54'])).
% 11.53/11.74  thf('99', plain, ((((sk_C_1) = (sk_D)) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 11.53/11.74      inference('sup-', [status(thm)], ['97', '98'])).
% 11.53/11.74  thf(t9_funct_1, axiom,
% 11.53/11.74    (![A:$i]:
% 11.53/11.74     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 11.53/11.74       ( ![B:$i]:
% 11.53/11.74         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 11.53/11.74           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 11.53/11.74               ( ![C:$i]:
% 11.53/11.74                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 11.53/11.74                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 11.53/11.74             ( ( A ) = ( B ) ) ) ) ) ))).
% 11.53/11.74  thf('100', plain,
% 11.53/11.74      (![X15 : $i, X16 : $i]:
% 11.53/11.74         (~ (v1_relat_1 @ X15)
% 11.53/11.74          | ~ (v1_funct_1 @ X15)
% 11.53/11.74          | ((X16) = (X15))
% 11.53/11.74          | (r2_hidden @ (sk_C @ X15 @ X16) @ (k1_relat_1 @ X16))
% 11.53/11.74          | ((k1_relat_1 @ X16) != (k1_relat_1 @ X15))
% 11.53/11.74          | ~ (v1_funct_1 @ X16)
% 11.53/11.74          | ~ (v1_relat_1 @ X16))),
% 11.53/11.74      inference('cnf', [status(esa)], [t9_funct_1])).
% 11.53/11.74  thf('101', plain,
% 11.53/11.74      (![X0 : $i]:
% 11.53/11.74         (((sk_A) != (k1_relat_1 @ X0))
% 11.53/11.74          | ((sk_C_1) = (sk_D))
% 11.53/11.74          | ~ (v1_relat_1 @ sk_C_1)
% 11.53/11.74          | ~ (v1_funct_1 @ sk_C_1)
% 11.53/11.74          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 11.53/11.74          | ((sk_C_1) = (X0))
% 11.53/11.74          | ~ (v1_funct_1 @ X0)
% 11.53/11.74          | ~ (v1_relat_1 @ X0))),
% 11.53/11.74      inference('sup-', [status(thm)], ['99', '100'])).
% 11.53/11.74  thf('102', plain,
% 11.53/11.74      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 11.53/11.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.53/11.74  thf(cc1_relset_1, axiom,
% 11.53/11.74    (![A:$i,B:$i,C:$i]:
% 11.53/11.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 11.53/11.74       ( v1_relat_1 @ C ) ))).
% 11.53/11.74  thf('103', plain,
% 11.53/11.74      (![X17 : $i, X18 : $i, X19 : $i]:
% 11.53/11.74         ((v1_relat_1 @ X17)
% 11.53/11.74          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 11.53/11.74      inference('cnf', [status(esa)], [cc1_relset_1])).
% 11.53/11.74  thf('104', plain, ((v1_relat_1 @ sk_C_1)),
% 11.53/11.74      inference('sup-', [status(thm)], ['102', '103'])).
% 11.53/11.74  thf('105', plain, ((v1_funct_1 @ sk_C_1)),
% 11.53/11.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.53/11.74  thf('106', plain,
% 11.53/11.74      (![X0 : $i]:
% 11.53/11.74         (((sk_A) != (k1_relat_1 @ X0))
% 11.53/11.74          | ((sk_C_1) = (sk_D))
% 11.53/11.74          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 11.53/11.74          | ((sk_C_1) = (X0))
% 11.53/11.74          | ~ (v1_funct_1 @ X0)
% 11.53/11.74          | ~ (v1_relat_1 @ X0))),
% 11.53/11.74      inference('demod', [status(thm)], ['101', '104', '105'])).
% 11.53/11.74  thf('107', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 11.53/11.74      inference('clc', [status(thm)], ['72', '73'])).
% 11.53/11.74  thf('108', plain,
% 11.53/11.74      (![X0 : $i]:
% 11.53/11.74         (((sk_A) != (k1_relat_1 @ X0))
% 11.53/11.74          | ((sk_C_1) = (sk_D))
% 11.53/11.74          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_A)
% 11.53/11.74          | ((sk_C_1) = (X0))
% 11.53/11.74          | ~ (v1_funct_1 @ X0)
% 11.53/11.74          | ~ (v1_relat_1 @ X0))),
% 11.53/11.74      inference('demod', [status(thm)], ['106', '107'])).
% 11.53/11.74  thf('109', plain,
% 11.53/11.74      ((((sk_A) != (sk_A))
% 11.53/11.74        | ~ (v1_relat_1 @ sk_D)
% 11.53/11.74        | ~ (v1_funct_1 @ sk_D)
% 11.53/11.74        | ((sk_C_1) = (sk_D))
% 11.53/11.74        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A)
% 11.53/11.74        | ((sk_C_1) = (sk_D)))),
% 11.53/11.74      inference('sup-', [status(thm)], ['78', '108'])).
% 11.53/11.74  thf('110', plain,
% 11.53/11.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 11.53/11.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.53/11.74  thf('111', plain,
% 11.53/11.74      (![X17 : $i, X18 : $i, X19 : $i]:
% 11.53/11.74         ((v1_relat_1 @ X17)
% 11.53/11.74          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 11.53/11.74      inference('cnf', [status(esa)], [cc1_relset_1])).
% 11.53/11.74  thf('112', plain, ((v1_relat_1 @ sk_D)),
% 11.53/11.74      inference('sup-', [status(thm)], ['110', '111'])).
% 11.53/11.74  thf('113', plain, ((v1_funct_1 @ sk_D)),
% 11.53/11.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.53/11.74  thf('114', plain,
% 11.53/11.74      ((((sk_A) != (sk_A))
% 11.53/11.74        | ((sk_C_1) = (sk_D))
% 11.53/11.74        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A)
% 11.53/11.74        | ((sk_C_1) = (sk_D)))),
% 11.53/11.74      inference('demod', [status(thm)], ['109', '112', '113'])).
% 11.53/11.74  thf('115', plain,
% 11.53/11.74      (((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A) | ((sk_C_1) = (sk_D)))),
% 11.53/11.74      inference('simplify', [status(thm)], ['114'])).
% 11.53/11.74  thf(t1_subset, axiom,
% 11.53/11.74    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 11.53/11.74  thf('116', plain,
% 11.53/11.74      (![X7 : $i, X8 : $i]: ((m1_subset_1 @ X7 @ X8) | ~ (r2_hidden @ X7 @ X8))),
% 11.53/11.74      inference('cnf', [status(esa)], [t1_subset])).
% 11.53/11.74  thf('117', plain,
% 11.53/11.74      ((((sk_C_1) = (sk_D)) | (m1_subset_1 @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 11.53/11.74      inference('sup-', [status(thm)], ['115', '116'])).
% 11.53/11.74  thf('118', plain,
% 11.53/11.74      (![X35 : $i]:
% 11.53/11.74         (((k1_funct_1 @ sk_C_1 @ X35) = (k1_funct_1 @ sk_D @ X35))
% 11.53/11.74          | ~ (m1_subset_1 @ X35 @ sk_A))),
% 11.53/11.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.53/11.74  thf('119', plain,
% 11.53/11.74      ((((sk_C_1) = (sk_D))
% 11.53/11.74        | ((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 11.53/11.74            = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))))),
% 11.53/11.74      inference('sup-', [status(thm)], ['117', '118'])).
% 11.53/11.74  thf('120', plain,
% 11.53/11.74      (((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 11.53/11.74         = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))),
% 11.53/11.74      inference('condensation', [status(thm)], ['119'])).
% 11.53/11.74  thf('121', plain,
% 11.53/11.74      (![X15 : $i, X16 : $i]:
% 11.53/11.74         (~ (v1_relat_1 @ X15)
% 11.53/11.74          | ~ (v1_funct_1 @ X15)
% 11.53/11.74          | ((X16) = (X15))
% 11.53/11.74          | ((k1_funct_1 @ X16 @ (sk_C @ X15 @ X16))
% 11.53/11.74              != (k1_funct_1 @ X15 @ (sk_C @ X15 @ X16)))
% 11.53/11.74          | ((k1_relat_1 @ X16) != (k1_relat_1 @ X15))
% 11.53/11.74          | ~ (v1_funct_1 @ X16)
% 11.53/11.74          | ~ (v1_relat_1 @ X16))),
% 11.53/11.74      inference('cnf', [status(esa)], [t9_funct_1])).
% 11.53/11.74  thf('122', plain,
% 11.53/11.74      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 11.53/11.74          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 11.53/11.74        | ~ (v1_relat_1 @ sk_C_1)
% 11.53/11.74        | ~ (v1_funct_1 @ sk_C_1)
% 11.53/11.74        | ((k1_relat_1 @ sk_C_1) != (k1_relat_1 @ sk_D))
% 11.53/11.74        | ((sk_C_1) = (sk_D))
% 11.53/11.74        | ~ (v1_funct_1 @ sk_D)
% 11.53/11.74        | ~ (v1_relat_1 @ sk_D))),
% 11.53/11.74      inference('sup-', [status(thm)], ['120', '121'])).
% 11.53/11.74  thf('123', plain, ((v1_relat_1 @ sk_C_1)),
% 11.53/11.74      inference('sup-', [status(thm)], ['102', '103'])).
% 11.53/11.74  thf('124', plain, ((v1_funct_1 @ sk_C_1)),
% 11.53/11.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.53/11.74  thf('125', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 11.53/11.74      inference('clc', [status(thm)], ['72', '73'])).
% 11.53/11.74  thf('126', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 11.53/11.74      inference('simplify', [status(thm)], ['77'])).
% 11.53/11.74  thf('127', plain, ((v1_funct_1 @ sk_D)),
% 11.53/11.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.53/11.74  thf('128', plain, ((v1_relat_1 @ sk_D)),
% 11.53/11.74      inference('sup-', [status(thm)], ['110', '111'])).
% 11.53/11.74  thf('129', plain,
% 11.53/11.74      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 11.53/11.74          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 11.53/11.74        | ((sk_A) != (sk_A))
% 11.53/11.74        | ((sk_C_1) = (sk_D)))),
% 11.53/11.74      inference('demod', [status(thm)],
% 11.53/11.74                ['122', '123', '124', '125', '126', '127', '128'])).
% 11.53/11.74  thf('130', plain, (((sk_C_1) = (sk_D))),
% 11.53/11.74      inference('simplify', [status(thm)], ['129'])).
% 11.53/11.74  thf('131', plain,
% 11.53/11.74      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 11.53/11.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.53/11.74  thf('132', plain,
% 11.53/11.74      (![X24 : $i, X25 : $i, X26 : $i]:
% 11.53/11.74         ((r2_relset_1 @ X24 @ X25 @ X26 @ X26)
% 11.53/11.74          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 11.53/11.74      inference('simplify', [status(thm)], ['67'])).
% 11.53/11.74  thf('133', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1)),
% 11.53/11.74      inference('sup-', [status(thm)], ['131', '132'])).
% 11.53/11.74  thf('134', plain, ($false),
% 11.53/11.74      inference('demod', [status(thm)], ['0', '130', '133'])).
% 11.53/11.74  
% 11.53/11.74  % SZS output end Refutation
% 11.53/11.74  
% 11.53/11.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
