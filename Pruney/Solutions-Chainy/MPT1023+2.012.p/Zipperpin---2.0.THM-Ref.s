%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.byQJqYyR6Q

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:30 EST 2020

% Result     : Theorem 11.42s
% Output     : Refutation 11.42s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 557 expanded)
%              Number of leaves         :   40 ( 189 expanded)
%              Depth                    :   23
%              Number of atoms          :  947 (6391 expanded)
%              Number of equality atoms :   66 ( 247 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf('1',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
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

thf('2',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ( X38
        = ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('6',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('12',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('13',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('14',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('19',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X22 ) ) )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','15'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('23',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 )
      | ( X4 = X5 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('26',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('27',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( r2_relset_1 @ X29 @ X30 @ X28 @ X31 )
      | ( X28 != X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('28',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( r2_relset_1 @ X29 @ X30 @ X31 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_relset_1 @ X3 @ X2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','30'])).

thf('32',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ~ ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['21','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','16'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X22 ) ) )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('38',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['34','39'])).

thf('41',plain,(
    zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['10','40'])).

thf('42',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','41'])).

thf('43',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ( X38
        = ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('45',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('48',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('52',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['34','39'])).

thf('54',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['49','54'])).

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

thf('56',plain,(
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

thf('57',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('59',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('60',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['49','54'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_A )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','60','61','62'])).

thf('64',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['42','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('67',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['64','67','68'])).

thf('70',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(simplify,[status(thm)],['69'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('71',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('72',plain,
    ( ( sk_C_1 = sk_D )
    | ( m1_subset_1 @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X44: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ X44 )
        = ( k1_funct_1 @ sk_D @ X44 ) )
      | ~ ( m1_subset_1 @ X44 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( sk_C_1 = sk_D )
    | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ),
    inference(condensation,[status(thm)],['74'])).

thf('76',plain,(
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

thf('77',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_1 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['58','59'])).

thf('79',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['49','54'])).

thf('81',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','41'])).

thf('82',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['65','66'])).

thf('84',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(demod,[status(thm)],['77','78','79','80','81','82','83'])).

thf('85',plain,(
    sk_C_1 = sk_D ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( r2_relset_1 @ X29 @ X30 @ X31 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('88',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    $false ),
    inference(demod,[status(thm)],['0','85','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.byQJqYyR6Q
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:42:31 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 11.42/11.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 11.42/11.62  % Solved by: fo/fo7.sh
% 11.42/11.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 11.42/11.62  % done 5783 iterations in 11.162s
% 11.42/11.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 11.42/11.62  % SZS output start Refutation
% 11.42/11.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 11.42/11.62  thf(sk_D_type, type, sk_D: $i).
% 11.42/11.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 11.42/11.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 11.42/11.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 11.42/11.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 11.42/11.62  thf(sk_A_type, type, sk_A: $i).
% 11.42/11.62  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 11.42/11.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 11.42/11.62  thf(sk_C_1_type, type, sk_C_1: $i).
% 11.42/11.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 11.42/11.62  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 11.42/11.62  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 11.42/11.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 11.42/11.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 11.42/11.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 11.42/11.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 11.42/11.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 11.42/11.62  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 11.42/11.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 11.42/11.62  thf(sk_B_type, type, sk_B: $i > $i).
% 11.42/11.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 11.42/11.62  thf(t113_funct_2, conjecture,
% 11.42/11.62    (![A:$i,B:$i,C:$i]:
% 11.42/11.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 11.42/11.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 11.42/11.62       ( ![D:$i]:
% 11.42/11.62         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 11.42/11.62             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 11.42/11.62           ( ( ![E:$i]:
% 11.42/11.62               ( ( m1_subset_1 @ E @ A ) =>
% 11.42/11.62                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 11.42/11.62             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 11.42/11.62  thf(zf_stmt_0, negated_conjecture,
% 11.42/11.62    (~( ![A:$i,B:$i,C:$i]:
% 11.42/11.62        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 11.42/11.62            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 11.42/11.62          ( ![D:$i]:
% 11.42/11.62            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 11.42/11.62                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 11.42/11.62              ( ( ![E:$i]:
% 11.42/11.62                  ( ( m1_subset_1 @ E @ A ) =>
% 11.42/11.62                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 11.42/11.62                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 11.42/11.62    inference('cnf.neg', [status(esa)], [t113_funct_2])).
% 11.42/11.62  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)),
% 11.42/11.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.42/11.62  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 11.42/11.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.42/11.62  thf(d1_funct_2, axiom,
% 11.42/11.62    (![A:$i,B:$i,C:$i]:
% 11.42/11.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 11.42/11.62       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 11.42/11.62           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 11.42/11.62             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 11.42/11.62         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 11.42/11.62           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 11.42/11.62             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 11.42/11.62  thf(zf_stmt_1, axiom,
% 11.42/11.62    (![C:$i,B:$i,A:$i]:
% 11.42/11.62     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 11.42/11.62       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 11.42/11.62  thf('2', plain,
% 11.42/11.62      (![X38 : $i, X39 : $i, X40 : $i]:
% 11.42/11.62         (~ (v1_funct_2 @ X40 @ X38 @ X39)
% 11.42/11.62          | ((X38) = (k1_relset_1 @ X38 @ X39 @ X40))
% 11.42/11.62          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 11.42/11.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 11.42/11.62  thf('3', plain,
% 11.42/11.62      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 11.42/11.62        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 11.42/11.62      inference('sup-', [status(thm)], ['1', '2'])).
% 11.42/11.62  thf('4', plain,
% 11.42/11.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 11.42/11.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.42/11.62  thf(redefinition_k1_relset_1, axiom,
% 11.42/11.62    (![A:$i,B:$i,C:$i]:
% 11.42/11.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 11.42/11.62       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 11.42/11.62  thf('5', plain,
% 11.42/11.62      (![X25 : $i, X26 : $i, X27 : $i]:
% 11.42/11.62         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 11.42/11.62          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 11.42/11.62      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 11.42/11.62  thf('6', plain,
% 11.42/11.62      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 11.42/11.62      inference('sup-', [status(thm)], ['4', '5'])).
% 11.42/11.62  thf('7', plain,
% 11.42/11.62      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 11.42/11.62        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 11.42/11.62      inference('demod', [status(thm)], ['3', '6'])).
% 11.42/11.62  thf('8', plain,
% 11.42/11.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 11.42/11.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.42/11.62  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 11.42/11.62  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 11.42/11.62  thf(zf_stmt_4, axiom,
% 11.42/11.62    (![B:$i,A:$i]:
% 11.42/11.62     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 11.42/11.62       ( zip_tseitin_0 @ B @ A ) ))).
% 11.42/11.62  thf(zf_stmt_5, axiom,
% 11.42/11.62    (![A:$i,B:$i,C:$i]:
% 11.42/11.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 11.42/11.62       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 11.42/11.62         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 11.42/11.62           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 11.42/11.62             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 11.42/11.62  thf('9', plain,
% 11.42/11.62      (![X41 : $i, X42 : $i, X43 : $i]:
% 11.42/11.62         (~ (zip_tseitin_0 @ X41 @ X42)
% 11.42/11.62          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 11.42/11.62          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 11.42/11.62      inference('cnf', [status(esa)], [zf_stmt_5])).
% 11.42/11.62  thf('10', plain,
% 11.42/11.62      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 11.42/11.62        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 11.42/11.62      inference('sup-', [status(thm)], ['8', '9'])).
% 11.42/11.62  thf('11', plain,
% 11.42/11.62      (![X36 : $i, X37 : $i]:
% 11.42/11.62         ((zip_tseitin_0 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 11.42/11.62      inference('cnf', [status(esa)], [zf_stmt_4])).
% 11.42/11.62  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 11.42/11.62  thf('12', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 11.42/11.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 11.42/11.62  thf(d1_xboole_0, axiom,
% 11.42/11.62    (![A:$i]:
% 11.42/11.62     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 11.42/11.62  thf('13', plain,
% 11.42/11.62      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 11.42/11.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 11.42/11.62  thf(t7_ordinal1, axiom,
% 11.42/11.62    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 11.42/11.62  thf('14', plain,
% 11.42/11.62      (![X17 : $i, X18 : $i]:
% 11.42/11.62         (~ (r2_hidden @ X17 @ X18) | ~ (r1_tarski @ X18 @ X17))),
% 11.42/11.62      inference('cnf', [status(esa)], [t7_ordinal1])).
% 11.42/11.62  thf('15', plain,
% 11.42/11.62      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 11.42/11.62      inference('sup-', [status(thm)], ['13', '14'])).
% 11.42/11.62  thf('16', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.42/11.62      inference('sup-', [status(thm)], ['12', '15'])).
% 11.42/11.62  thf('17', plain,
% 11.42/11.62      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 11.42/11.62      inference('sup+', [status(thm)], ['11', '16'])).
% 11.42/11.62  thf('18', plain,
% 11.42/11.62      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 11.42/11.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.42/11.62  thf(cc4_relset_1, axiom,
% 11.42/11.62    (![A:$i,B:$i]:
% 11.42/11.62     ( ( v1_xboole_0 @ A ) =>
% 11.42/11.62       ( ![C:$i]:
% 11.42/11.62         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 11.42/11.62           ( v1_xboole_0 @ C ) ) ) ))).
% 11.42/11.62  thf('19', plain,
% 11.42/11.62      (![X22 : $i, X23 : $i, X24 : $i]:
% 11.42/11.62         (~ (v1_xboole_0 @ X22)
% 11.42/11.62          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X22)))
% 11.42/11.62          | (v1_xboole_0 @ X23))),
% 11.42/11.62      inference('cnf', [status(esa)], [cc4_relset_1])).
% 11.42/11.62  thf('20', plain, (((v1_xboole_0 @ sk_C_1) | ~ (v1_xboole_0 @ sk_B_1))),
% 11.42/11.62      inference('sup-', [status(thm)], ['18', '19'])).
% 11.42/11.62  thf('21', plain,
% 11.42/11.62      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_C_1))),
% 11.42/11.62      inference('sup-', [status(thm)], ['17', '20'])).
% 11.42/11.62  thf('22', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.42/11.62      inference('sup-', [status(thm)], ['12', '15'])).
% 11.42/11.62  thf(t8_boole, axiom,
% 11.42/11.62    (![A:$i,B:$i]:
% 11.42/11.62     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 11.42/11.62  thf('23', plain,
% 11.42/11.62      (![X4 : $i, X5 : $i]:
% 11.42/11.62         (~ (v1_xboole_0 @ X4) | ~ (v1_xboole_0 @ X5) | ((X4) = (X5)))),
% 11.42/11.62      inference('cnf', [status(esa)], [t8_boole])).
% 11.42/11.62  thf('24', plain,
% 11.42/11.62      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 11.42/11.62      inference('sup-', [status(thm)], ['22', '23'])).
% 11.42/11.62  thf('25', plain,
% 11.42/11.62      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 11.42/11.62      inference('sup-', [status(thm)], ['22', '23'])).
% 11.42/11.62  thf(t4_subset_1, axiom,
% 11.42/11.62    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 11.42/11.62  thf('26', plain,
% 11.42/11.62      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 11.42/11.62      inference('cnf', [status(esa)], [t4_subset_1])).
% 11.42/11.62  thf(redefinition_r2_relset_1, axiom,
% 11.42/11.62    (![A:$i,B:$i,C:$i,D:$i]:
% 11.42/11.62     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 11.42/11.62         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 11.42/11.62       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 11.42/11.62  thf('27', plain,
% 11.42/11.62      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 11.42/11.62         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 11.42/11.62          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 11.42/11.62          | (r2_relset_1 @ X29 @ X30 @ X28 @ X31)
% 11.42/11.62          | ((X28) != (X31)))),
% 11.42/11.62      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 11.42/11.62  thf('28', plain,
% 11.42/11.62      (![X29 : $i, X30 : $i, X31 : $i]:
% 11.42/11.62         ((r2_relset_1 @ X29 @ X30 @ X31 @ X31)
% 11.42/11.62          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 11.42/11.62      inference('simplify', [status(thm)], ['27'])).
% 11.42/11.62  thf('29', plain,
% 11.42/11.62      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 11.42/11.62      inference('sup-', [status(thm)], ['26', '28'])).
% 11.42/11.62  thf('30', plain,
% 11.42/11.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.42/11.62         ((r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 11.42/11.62      inference('sup+', [status(thm)], ['25', '29'])).
% 11.42/11.62  thf('31', plain,
% 11.42/11.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.42/11.62         ((r2_relset_1 @ X3 @ X2 @ X1 @ X0)
% 11.42/11.62          | ~ (v1_xboole_0 @ X0)
% 11.42/11.62          | ~ (v1_xboole_0 @ X1))),
% 11.42/11.62      inference('sup+', [status(thm)], ['24', '30'])).
% 11.42/11.62  thf('32', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)),
% 11.42/11.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.42/11.62  thf('33', plain, ((~ (v1_xboole_0 @ sk_C_1) | ~ (v1_xboole_0 @ sk_D))),
% 11.42/11.62      inference('sup-', [status(thm)], ['31', '32'])).
% 11.42/11.62  thf('34', plain,
% 11.42/11.62      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | ~ (v1_xboole_0 @ sk_D))),
% 11.42/11.62      inference('sup-', [status(thm)], ['21', '33'])).
% 11.42/11.62  thf('35', plain,
% 11.42/11.62      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 11.42/11.62      inference('sup+', [status(thm)], ['11', '16'])).
% 11.42/11.62  thf('36', plain,
% 11.42/11.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 11.42/11.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.42/11.62  thf('37', plain,
% 11.42/11.62      (![X22 : $i, X23 : $i, X24 : $i]:
% 11.42/11.62         (~ (v1_xboole_0 @ X22)
% 11.42/11.62          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X22)))
% 11.42/11.62          | (v1_xboole_0 @ X23))),
% 11.42/11.62      inference('cnf', [status(esa)], [cc4_relset_1])).
% 11.42/11.62  thf('38', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_B_1))),
% 11.42/11.62      inference('sup-', [status(thm)], ['36', '37'])).
% 11.42/11.62  thf('39', plain,
% 11.42/11.62      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_D))),
% 11.42/11.62      inference('sup-', [status(thm)], ['35', '38'])).
% 11.42/11.62  thf('40', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 11.42/11.62      inference('clc', [status(thm)], ['34', '39'])).
% 11.42/11.62  thf('41', plain, ((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)),
% 11.42/11.62      inference('demod', [status(thm)], ['10', '40'])).
% 11.42/11.62  thf('42', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 11.42/11.62      inference('demod', [status(thm)], ['7', '41'])).
% 11.42/11.62  thf('43', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 11.42/11.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.42/11.62  thf('44', plain,
% 11.42/11.62      (![X38 : $i, X39 : $i, X40 : $i]:
% 11.42/11.62         (~ (v1_funct_2 @ X40 @ X38 @ X39)
% 11.42/11.62          | ((X38) = (k1_relset_1 @ X38 @ X39 @ X40))
% 11.42/11.62          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 11.42/11.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 11.42/11.62  thf('45', plain,
% 11.42/11.62      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 11.42/11.62        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 11.42/11.62      inference('sup-', [status(thm)], ['43', '44'])).
% 11.42/11.62  thf('46', plain,
% 11.42/11.62      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 11.42/11.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.42/11.62  thf('47', plain,
% 11.42/11.62      (![X25 : $i, X26 : $i, X27 : $i]:
% 11.42/11.62         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 11.42/11.62          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 11.42/11.62      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 11.42/11.62  thf('48', plain,
% 11.42/11.62      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 11.42/11.62      inference('sup-', [status(thm)], ['46', '47'])).
% 11.42/11.62  thf('49', plain,
% 11.42/11.62      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 11.42/11.62        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 11.42/11.62      inference('demod', [status(thm)], ['45', '48'])).
% 11.42/11.62  thf('50', plain,
% 11.42/11.62      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 11.42/11.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.42/11.62  thf('51', plain,
% 11.42/11.62      (![X41 : $i, X42 : $i, X43 : $i]:
% 11.42/11.62         (~ (zip_tseitin_0 @ X41 @ X42)
% 11.42/11.62          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 11.42/11.62          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 11.42/11.62      inference('cnf', [status(esa)], [zf_stmt_5])).
% 11.42/11.62  thf('52', plain,
% 11.42/11.62      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 11.42/11.62        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 11.42/11.62      inference('sup-', [status(thm)], ['50', '51'])).
% 11.42/11.62  thf('53', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 11.42/11.62      inference('clc', [status(thm)], ['34', '39'])).
% 11.42/11.62  thf('54', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)),
% 11.42/11.62      inference('demod', [status(thm)], ['52', '53'])).
% 11.42/11.62  thf('55', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 11.42/11.62      inference('demod', [status(thm)], ['49', '54'])).
% 11.42/11.62  thf(t9_funct_1, axiom,
% 11.42/11.62    (![A:$i]:
% 11.42/11.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 11.42/11.62       ( ![B:$i]:
% 11.42/11.62         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 11.42/11.62           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 11.42/11.62               ( ![C:$i]:
% 11.42/11.62                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 11.42/11.62                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 11.42/11.62             ( ( A ) = ( B ) ) ) ) ) ))).
% 11.42/11.62  thf('56', plain,
% 11.42/11.62      (![X15 : $i, X16 : $i]:
% 11.42/11.62         (~ (v1_relat_1 @ X15)
% 11.42/11.62          | ~ (v1_funct_1 @ X15)
% 11.42/11.62          | ((X16) = (X15))
% 11.42/11.62          | (r2_hidden @ (sk_C @ X15 @ X16) @ (k1_relat_1 @ X16))
% 11.42/11.62          | ((k1_relat_1 @ X16) != (k1_relat_1 @ X15))
% 11.42/11.62          | ~ (v1_funct_1 @ X16)
% 11.42/11.62          | ~ (v1_relat_1 @ X16))),
% 11.42/11.62      inference('cnf', [status(esa)], [t9_funct_1])).
% 11.42/11.62  thf('57', plain,
% 11.42/11.62      (![X0 : $i]:
% 11.42/11.62         (((sk_A) != (k1_relat_1 @ X0))
% 11.42/11.62          | ~ (v1_relat_1 @ sk_C_1)
% 11.42/11.62          | ~ (v1_funct_1 @ sk_C_1)
% 11.42/11.62          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 11.42/11.62          | ((sk_C_1) = (X0))
% 11.42/11.62          | ~ (v1_funct_1 @ X0)
% 11.42/11.62          | ~ (v1_relat_1 @ X0))),
% 11.42/11.62      inference('sup-', [status(thm)], ['55', '56'])).
% 11.42/11.62  thf('58', plain,
% 11.42/11.62      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 11.42/11.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.42/11.62  thf(cc1_relset_1, axiom,
% 11.42/11.62    (![A:$i,B:$i,C:$i]:
% 11.42/11.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 11.42/11.62       ( v1_relat_1 @ C ) ))).
% 11.42/11.62  thf('59', plain,
% 11.42/11.62      (![X19 : $i, X20 : $i, X21 : $i]:
% 11.42/11.62         ((v1_relat_1 @ X19)
% 11.42/11.62          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 11.42/11.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 11.42/11.62  thf('60', plain, ((v1_relat_1 @ sk_C_1)),
% 11.42/11.62      inference('sup-', [status(thm)], ['58', '59'])).
% 11.42/11.62  thf('61', plain, ((v1_funct_1 @ sk_C_1)),
% 11.42/11.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.42/11.62  thf('62', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 11.42/11.62      inference('demod', [status(thm)], ['49', '54'])).
% 11.42/11.62  thf('63', plain,
% 11.42/11.62      (![X0 : $i]:
% 11.42/11.62         (((sk_A) != (k1_relat_1 @ X0))
% 11.42/11.62          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_A)
% 11.42/11.62          | ((sk_C_1) = (X0))
% 11.42/11.62          | ~ (v1_funct_1 @ X0)
% 11.42/11.62          | ~ (v1_relat_1 @ X0))),
% 11.42/11.62      inference('demod', [status(thm)], ['57', '60', '61', '62'])).
% 11.42/11.62  thf('64', plain,
% 11.42/11.62      ((((sk_A) != (sk_A))
% 11.42/11.62        | ~ (v1_relat_1 @ sk_D)
% 11.42/11.62        | ~ (v1_funct_1 @ sk_D)
% 11.42/11.62        | ((sk_C_1) = (sk_D))
% 11.42/11.62        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 11.42/11.62      inference('sup-', [status(thm)], ['42', '63'])).
% 11.42/11.62  thf('65', plain,
% 11.42/11.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 11.42/11.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.42/11.62  thf('66', plain,
% 11.42/11.62      (![X19 : $i, X20 : $i, X21 : $i]:
% 11.42/11.62         ((v1_relat_1 @ X19)
% 11.42/11.62          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 11.42/11.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 11.42/11.62  thf('67', plain, ((v1_relat_1 @ sk_D)),
% 11.42/11.62      inference('sup-', [status(thm)], ['65', '66'])).
% 11.42/11.62  thf('68', plain, ((v1_funct_1 @ sk_D)),
% 11.42/11.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.42/11.62  thf('69', plain,
% 11.42/11.62      ((((sk_A) != (sk_A))
% 11.42/11.62        | ((sk_C_1) = (sk_D))
% 11.42/11.62        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 11.42/11.62      inference('demod', [status(thm)], ['64', '67', '68'])).
% 11.42/11.62  thf('70', plain,
% 11.42/11.62      (((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A) | ((sk_C_1) = (sk_D)))),
% 11.42/11.62      inference('simplify', [status(thm)], ['69'])).
% 11.42/11.62  thf(t1_subset, axiom,
% 11.42/11.62    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 11.42/11.62  thf('71', plain,
% 11.42/11.62      (![X10 : $i, X11 : $i]:
% 11.42/11.62         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 11.42/11.62      inference('cnf', [status(esa)], [t1_subset])).
% 11.42/11.62  thf('72', plain,
% 11.42/11.62      ((((sk_C_1) = (sk_D)) | (m1_subset_1 @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 11.42/11.62      inference('sup-', [status(thm)], ['70', '71'])).
% 11.42/11.62  thf('73', plain,
% 11.42/11.62      (![X44 : $i]:
% 11.42/11.62         (((k1_funct_1 @ sk_C_1 @ X44) = (k1_funct_1 @ sk_D @ X44))
% 11.42/11.62          | ~ (m1_subset_1 @ X44 @ sk_A))),
% 11.42/11.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.42/11.62  thf('74', plain,
% 11.42/11.62      ((((sk_C_1) = (sk_D))
% 11.42/11.62        | ((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 11.42/11.62            = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))))),
% 11.42/11.62      inference('sup-', [status(thm)], ['72', '73'])).
% 11.42/11.62  thf('75', plain,
% 11.42/11.62      (((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 11.42/11.62         = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))),
% 11.42/11.62      inference('condensation', [status(thm)], ['74'])).
% 11.42/11.62  thf('76', plain,
% 11.42/11.62      (![X15 : $i, X16 : $i]:
% 11.42/11.62         (~ (v1_relat_1 @ X15)
% 11.42/11.62          | ~ (v1_funct_1 @ X15)
% 11.42/11.62          | ((X16) = (X15))
% 11.42/11.62          | ((k1_funct_1 @ X16 @ (sk_C @ X15 @ X16))
% 11.42/11.62              != (k1_funct_1 @ X15 @ (sk_C @ X15 @ X16)))
% 11.42/11.62          | ((k1_relat_1 @ X16) != (k1_relat_1 @ X15))
% 11.42/11.62          | ~ (v1_funct_1 @ X16)
% 11.42/11.62          | ~ (v1_relat_1 @ X16))),
% 11.42/11.62      inference('cnf', [status(esa)], [t9_funct_1])).
% 11.42/11.62  thf('77', plain,
% 11.42/11.62      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 11.42/11.62          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 11.42/11.62        | ~ (v1_relat_1 @ sk_C_1)
% 11.42/11.62        | ~ (v1_funct_1 @ sk_C_1)
% 11.42/11.62        | ((k1_relat_1 @ sk_C_1) != (k1_relat_1 @ sk_D))
% 11.42/11.62        | ((sk_C_1) = (sk_D))
% 11.42/11.62        | ~ (v1_funct_1 @ sk_D)
% 11.42/11.62        | ~ (v1_relat_1 @ sk_D))),
% 11.42/11.62      inference('sup-', [status(thm)], ['75', '76'])).
% 11.42/11.62  thf('78', plain, ((v1_relat_1 @ sk_C_1)),
% 11.42/11.62      inference('sup-', [status(thm)], ['58', '59'])).
% 11.42/11.62  thf('79', plain, ((v1_funct_1 @ sk_C_1)),
% 11.42/11.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.42/11.62  thf('80', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 11.42/11.62      inference('demod', [status(thm)], ['49', '54'])).
% 11.42/11.62  thf('81', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 11.42/11.62      inference('demod', [status(thm)], ['7', '41'])).
% 11.42/11.62  thf('82', plain, ((v1_funct_1 @ sk_D)),
% 11.42/11.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.42/11.62  thf('83', plain, ((v1_relat_1 @ sk_D)),
% 11.42/11.62      inference('sup-', [status(thm)], ['65', '66'])).
% 11.42/11.62  thf('84', plain,
% 11.42/11.62      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 11.42/11.62          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 11.42/11.62        | ((sk_A) != (sk_A))
% 11.42/11.62        | ((sk_C_1) = (sk_D)))),
% 11.42/11.62      inference('demod', [status(thm)],
% 11.42/11.62                ['77', '78', '79', '80', '81', '82', '83'])).
% 11.42/11.62  thf('85', plain, (((sk_C_1) = (sk_D))),
% 11.42/11.62      inference('simplify', [status(thm)], ['84'])).
% 11.42/11.62  thf('86', plain,
% 11.42/11.62      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 11.42/11.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.42/11.62  thf('87', plain,
% 11.42/11.62      (![X29 : $i, X30 : $i, X31 : $i]:
% 11.42/11.62         ((r2_relset_1 @ X29 @ X30 @ X31 @ X31)
% 11.42/11.62          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 11.42/11.62      inference('simplify', [status(thm)], ['27'])).
% 11.42/11.62  thf('88', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_C_1)),
% 11.42/11.62      inference('sup-', [status(thm)], ['86', '87'])).
% 11.42/11.62  thf('89', plain, ($false),
% 11.42/11.62      inference('demod', [status(thm)], ['0', '85', '88'])).
% 11.42/11.62  
% 11.42/11.62  % SZS output end Refutation
% 11.42/11.62  
% 11.42/11.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
