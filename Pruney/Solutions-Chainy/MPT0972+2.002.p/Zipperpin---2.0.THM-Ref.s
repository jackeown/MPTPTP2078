%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LTq9EJTzIN

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:32 EST 2020

% Result     : Theorem 6.25s
% Output     : Refutation 6.25s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 502 expanded)
%              Number of leaves         :   36 ( 166 expanded)
%              Depth                    :   21
%              Number of atoms          :  948 (6111 expanded)
%              Number of equality atoms :   73 ( 326 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf('1',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ( X24
        = ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('6',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('12',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('16',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('19',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('20',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('23',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['13','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('27',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('28',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 )
      | ( X18 != X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('29',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_relset_1 @ X19 @ X20 @ X21 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_relset_1 @ X3 @ X2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','31'])).

thf('33',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ~ ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['24','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','16'])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('40',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('43',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['36','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference(clc,[status(thm)],['35','44'])).

thf('46',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['10','45'])).

thf('47',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','46'])).

thf('48',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ( X24
        = ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('50',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('53',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['50','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('57',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference(clc,[status(thm)],['35','44'])).

thf('59',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['54','59'])).

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

thf('61',plain,(
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

thf('62',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('64',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('65',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['54','59'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_A )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['62','65','66','67'])).

thf('69',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['47','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('72',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['69','72','73'])).

thf('75',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X30: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ X30 )
        = ( k1_funct_1 @ sk_D @ X30 ) )
      | ~ ( r2_hidden @ X30 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( sk_C_1 = sk_D )
    | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ),
    inference(condensation,[status(thm)],['77'])).

thf('79',plain,(
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

thf('80',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_1 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['63','64'])).

thf('82',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['54','59'])).

thf('84',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','46'])).

thf('85',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['70','71'])).

thf('87',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(demod,[status(thm)],['80','81','82','83','84','85','86'])).

thf('88',plain,(
    sk_C_1 = sk_D ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_relset_1 @ X19 @ X20 @ X21 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('91',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    $false ),
    inference(demod,[status(thm)],['0','88','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LTq9EJTzIN
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:52:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 6.25/6.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.25/6.51  % Solved by: fo/fo7.sh
% 6.25/6.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.25/6.51  % done 5080 iterations in 6.053s
% 6.25/6.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.25/6.51  % SZS output start Refutation
% 6.25/6.51  thf(sk_D_type, type, sk_D: $i).
% 6.25/6.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 6.25/6.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 6.25/6.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 6.25/6.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 6.25/6.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.25/6.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.25/6.51  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 6.25/6.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.25/6.51  thf(sk_B_type, type, sk_B: $i).
% 6.25/6.51  thf(sk_A_type, type, sk_A: $i).
% 6.25/6.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 6.25/6.51  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 6.25/6.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 6.25/6.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.25/6.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 6.25/6.51  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 6.25/6.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 6.25/6.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.25/6.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.25/6.51  thf(t18_funct_2, conjecture,
% 6.25/6.51    (![A:$i,B:$i,C:$i]:
% 6.25/6.51     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.25/6.51         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.25/6.51       ( ![D:$i]:
% 6.25/6.51         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 6.25/6.51             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.25/6.51           ( ( ![E:$i]:
% 6.25/6.51               ( ( r2_hidden @ E @ A ) =>
% 6.25/6.51                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 6.25/6.51             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 6.25/6.51  thf(zf_stmt_0, negated_conjecture,
% 6.25/6.51    (~( ![A:$i,B:$i,C:$i]:
% 6.25/6.51        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.25/6.51            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.25/6.51          ( ![D:$i]:
% 6.25/6.51            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 6.25/6.51                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.25/6.51              ( ( ![E:$i]:
% 6.25/6.51                  ( ( r2_hidden @ E @ A ) =>
% 6.25/6.51                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 6.25/6.51                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 6.25/6.51    inference('cnf.neg', [status(esa)], [t18_funct_2])).
% 6.25/6.51  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)),
% 6.25/6.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.25/6.51  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 6.25/6.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.25/6.51  thf(d1_funct_2, axiom,
% 6.25/6.51    (![A:$i,B:$i,C:$i]:
% 6.25/6.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.25/6.51       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.25/6.51           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 6.25/6.51             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 6.25/6.51         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.25/6.51           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 6.25/6.51             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 6.25/6.51  thf(zf_stmt_1, axiom,
% 6.25/6.51    (![C:$i,B:$i,A:$i]:
% 6.25/6.51     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 6.25/6.51       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 6.25/6.51  thf('2', plain,
% 6.25/6.51      (![X24 : $i, X25 : $i, X26 : $i]:
% 6.25/6.51         (~ (v1_funct_2 @ X26 @ X24 @ X25)
% 6.25/6.51          | ((X24) = (k1_relset_1 @ X24 @ X25 @ X26))
% 6.25/6.51          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 6.25/6.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.25/6.51  thf('3', plain,
% 6.25/6.51      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 6.25/6.51        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 6.25/6.51      inference('sup-', [status(thm)], ['1', '2'])).
% 6.25/6.51  thf('4', plain,
% 6.25/6.51      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.25/6.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.25/6.51  thf(redefinition_k1_relset_1, axiom,
% 6.25/6.51    (![A:$i,B:$i,C:$i]:
% 6.25/6.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.25/6.51       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 6.25/6.51  thf('5', plain,
% 6.25/6.51      (![X15 : $i, X16 : $i, X17 : $i]:
% 6.25/6.51         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 6.25/6.51          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 6.25/6.51      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.25/6.51  thf('6', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 6.25/6.51      inference('sup-', [status(thm)], ['4', '5'])).
% 6.25/6.51  thf('7', plain,
% 6.25/6.51      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 6.25/6.51      inference('demod', [status(thm)], ['3', '6'])).
% 6.25/6.51  thf('8', plain,
% 6.25/6.51      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.25/6.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.25/6.51  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 6.25/6.51  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 6.25/6.51  thf(zf_stmt_4, axiom,
% 6.25/6.51    (![B:$i,A:$i]:
% 6.25/6.51     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.25/6.51       ( zip_tseitin_0 @ B @ A ) ))).
% 6.25/6.51  thf(zf_stmt_5, axiom,
% 6.25/6.51    (![A:$i,B:$i,C:$i]:
% 6.25/6.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.25/6.51       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 6.25/6.51         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.25/6.51           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 6.25/6.51             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 6.25/6.51  thf('9', plain,
% 6.25/6.51      (![X27 : $i, X28 : $i, X29 : $i]:
% 6.25/6.51         (~ (zip_tseitin_0 @ X27 @ X28)
% 6.25/6.51          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 6.25/6.51          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 6.25/6.51      inference('cnf', [status(esa)], [zf_stmt_5])).
% 6.25/6.51  thf('10', plain,
% 6.25/6.51      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 6.25/6.51      inference('sup-', [status(thm)], ['8', '9'])).
% 6.25/6.51  thf('11', plain,
% 6.25/6.51      (![X22 : $i, X23 : $i]:
% 6.25/6.51         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 6.25/6.51      inference('cnf', [status(esa)], [zf_stmt_4])).
% 6.25/6.51  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 6.25/6.51  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.25/6.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.25/6.51  thf('13', plain,
% 6.25/6.51      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 6.25/6.51      inference('sup+', [status(thm)], ['11', '12'])).
% 6.25/6.51  thf(l13_xboole_0, axiom,
% 6.25/6.51    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 6.25/6.51  thf('14', plain,
% 6.25/6.51      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.25/6.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.25/6.51  thf(t113_zfmisc_1, axiom,
% 6.25/6.51    (![A:$i,B:$i]:
% 6.25/6.51     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 6.25/6.51       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 6.25/6.51  thf('15', plain,
% 6.25/6.51      (![X2 : $i, X3 : $i]:
% 6.25/6.51         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 6.25/6.51      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 6.25/6.51  thf('16', plain,
% 6.25/6.51      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 6.25/6.51      inference('simplify', [status(thm)], ['15'])).
% 6.25/6.51  thf('17', plain,
% 6.25/6.51      (![X0 : $i, X1 : $i]:
% 6.25/6.51         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.25/6.51      inference('sup+', [status(thm)], ['14', '16'])).
% 6.25/6.51  thf('18', plain,
% 6.25/6.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.25/6.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.25/6.51  thf(cc1_subset_1, axiom,
% 6.25/6.51    (![A:$i]:
% 6.25/6.51     ( ( v1_xboole_0 @ A ) =>
% 6.25/6.51       ( ![B:$i]:
% 6.25/6.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 6.25/6.51  thf('19', plain,
% 6.25/6.51      (![X5 : $i, X6 : $i]:
% 6.25/6.51         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 6.25/6.51          | (v1_xboole_0 @ X5)
% 6.25/6.51          | ~ (v1_xboole_0 @ X6))),
% 6.25/6.51      inference('cnf', [status(esa)], [cc1_subset_1])).
% 6.25/6.51  thf('20', plain,
% 6.25/6.51      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C_1))),
% 6.25/6.51      inference('sup-', [status(thm)], ['18', '19'])).
% 6.25/6.51  thf('21', plain,
% 6.25/6.51      ((~ (v1_xboole_0 @ k1_xboole_0)
% 6.25/6.51        | ~ (v1_xboole_0 @ sk_B)
% 6.25/6.51        | (v1_xboole_0 @ sk_C_1))),
% 6.25/6.51      inference('sup-', [status(thm)], ['17', '20'])).
% 6.25/6.51  thf('22', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.25/6.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.25/6.51  thf('23', plain, ((~ (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_C_1))),
% 6.25/6.51      inference('demod', [status(thm)], ['21', '22'])).
% 6.25/6.51  thf('24', plain,
% 6.25/6.51      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | (v1_xboole_0 @ sk_C_1))),
% 6.25/6.51      inference('sup-', [status(thm)], ['13', '23'])).
% 6.25/6.51  thf('25', plain,
% 6.25/6.51      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.25/6.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.25/6.51  thf('26', plain,
% 6.25/6.51      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.25/6.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.25/6.51  thf(t4_subset_1, axiom,
% 6.25/6.51    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 6.25/6.51  thf('27', plain,
% 6.25/6.51      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 6.25/6.51      inference('cnf', [status(esa)], [t4_subset_1])).
% 6.25/6.51  thf(redefinition_r2_relset_1, axiom,
% 6.25/6.51    (![A:$i,B:$i,C:$i,D:$i]:
% 6.25/6.51     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.25/6.51         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.25/6.51       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 6.25/6.51  thf('28', plain,
% 6.25/6.51      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 6.25/6.51         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 6.25/6.51          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 6.25/6.51          | (r2_relset_1 @ X19 @ X20 @ X18 @ X21)
% 6.25/6.51          | ((X18) != (X21)))),
% 6.25/6.51      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 6.25/6.51  thf('29', plain,
% 6.25/6.51      (![X19 : $i, X20 : $i, X21 : $i]:
% 6.25/6.51         ((r2_relset_1 @ X19 @ X20 @ X21 @ X21)
% 6.25/6.51          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 6.25/6.51      inference('simplify', [status(thm)], ['28'])).
% 6.25/6.51  thf('30', plain,
% 6.25/6.51      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 6.25/6.51      inference('sup-', [status(thm)], ['27', '29'])).
% 6.25/6.51  thf('31', plain,
% 6.25/6.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.25/6.51         ((r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 6.25/6.51      inference('sup+', [status(thm)], ['26', '30'])).
% 6.25/6.51  thf('32', plain,
% 6.25/6.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.25/6.51         ((r2_relset_1 @ X3 @ X2 @ X1 @ X0)
% 6.25/6.51          | ~ (v1_xboole_0 @ X0)
% 6.25/6.51          | ~ (v1_xboole_0 @ X1))),
% 6.25/6.51      inference('sup+', [status(thm)], ['25', '31'])).
% 6.25/6.52  thf('33', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)),
% 6.25/6.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.25/6.52  thf('34', plain, ((~ (v1_xboole_0 @ sk_C_1) | ~ (v1_xboole_0 @ sk_D))),
% 6.25/6.52      inference('sup-', [status(thm)], ['32', '33'])).
% 6.25/6.52  thf('35', plain,
% 6.25/6.52      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | ~ (v1_xboole_0 @ sk_D))),
% 6.25/6.52      inference('sup-', [status(thm)], ['24', '34'])).
% 6.25/6.52  thf('36', plain,
% 6.25/6.52      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 6.25/6.52      inference('sup+', [status(thm)], ['11', '12'])).
% 6.25/6.52  thf('37', plain,
% 6.25/6.52      (![X0 : $i, X1 : $i]:
% 6.25/6.52         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.25/6.52      inference('sup+', [status(thm)], ['14', '16'])).
% 6.25/6.52  thf('38', plain,
% 6.25/6.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.25/6.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.25/6.52  thf('39', plain,
% 6.25/6.52      (![X5 : $i, X6 : $i]:
% 6.25/6.52         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 6.25/6.52          | (v1_xboole_0 @ X5)
% 6.25/6.52          | ~ (v1_xboole_0 @ X6))),
% 6.25/6.52      inference('cnf', [status(esa)], [cc1_subset_1])).
% 6.25/6.52  thf('40', plain,
% 6.25/6.52      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_D))),
% 6.25/6.52      inference('sup-', [status(thm)], ['38', '39'])).
% 6.25/6.52  thf('41', plain,
% 6.25/6.52      ((~ (v1_xboole_0 @ k1_xboole_0)
% 6.25/6.52        | ~ (v1_xboole_0 @ sk_B)
% 6.25/6.52        | (v1_xboole_0 @ sk_D))),
% 6.25/6.52      inference('sup-', [status(thm)], ['37', '40'])).
% 6.25/6.52  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.25/6.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.25/6.52  thf('43', plain, ((~ (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_D))),
% 6.25/6.52      inference('demod', [status(thm)], ['41', '42'])).
% 6.25/6.52  thf('44', plain,
% 6.25/6.52      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | (v1_xboole_0 @ sk_D))),
% 6.25/6.52      inference('sup-', [status(thm)], ['36', '43'])).
% 6.25/6.52  thf('45', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 6.25/6.52      inference('clc', [status(thm)], ['35', '44'])).
% 6.25/6.52  thf('46', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 6.25/6.52      inference('demod', [status(thm)], ['10', '45'])).
% 6.25/6.52  thf('47', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 6.25/6.52      inference('demod', [status(thm)], ['7', '46'])).
% 6.25/6.52  thf('48', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 6.25/6.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.25/6.52  thf('49', plain,
% 6.25/6.52      (![X24 : $i, X25 : $i, X26 : $i]:
% 6.25/6.52         (~ (v1_funct_2 @ X26 @ X24 @ X25)
% 6.25/6.52          | ((X24) = (k1_relset_1 @ X24 @ X25 @ X26))
% 6.25/6.52          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 6.25/6.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.25/6.52  thf('50', plain,
% 6.25/6.52      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 6.25/6.52        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 6.25/6.52      inference('sup-', [status(thm)], ['48', '49'])).
% 6.25/6.52  thf('51', plain,
% 6.25/6.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.25/6.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.25/6.52  thf('52', plain,
% 6.25/6.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 6.25/6.52         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 6.25/6.52          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 6.25/6.52      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.25/6.52  thf('53', plain,
% 6.25/6.52      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 6.25/6.52      inference('sup-', [status(thm)], ['51', '52'])).
% 6.25/6.52  thf('54', plain,
% 6.25/6.52      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 6.25/6.52        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 6.25/6.52      inference('demod', [status(thm)], ['50', '53'])).
% 6.25/6.52  thf('55', plain,
% 6.25/6.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.25/6.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.25/6.52  thf('56', plain,
% 6.25/6.52      (![X27 : $i, X28 : $i, X29 : $i]:
% 6.25/6.52         (~ (zip_tseitin_0 @ X27 @ X28)
% 6.25/6.52          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 6.25/6.52          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 6.25/6.52      inference('cnf', [status(esa)], [zf_stmt_5])).
% 6.25/6.52  thf('57', plain,
% 6.25/6.52      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 6.25/6.52        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 6.25/6.52      inference('sup-', [status(thm)], ['55', '56'])).
% 6.25/6.52  thf('58', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 6.25/6.52      inference('clc', [status(thm)], ['35', '44'])).
% 6.25/6.52  thf('59', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)),
% 6.25/6.52      inference('demod', [status(thm)], ['57', '58'])).
% 6.25/6.52  thf('60', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 6.25/6.52      inference('demod', [status(thm)], ['54', '59'])).
% 6.25/6.52  thf(t9_funct_1, axiom,
% 6.25/6.52    (![A:$i]:
% 6.25/6.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.25/6.52       ( ![B:$i]:
% 6.25/6.52         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 6.25/6.52           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 6.25/6.52               ( ![C:$i]:
% 6.25/6.52                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 6.25/6.52                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 6.25/6.52             ( ( A ) = ( B ) ) ) ) ) ))).
% 6.25/6.52  thf('61', plain,
% 6.25/6.52      (![X10 : $i, X11 : $i]:
% 6.25/6.52         (~ (v1_relat_1 @ X10)
% 6.25/6.52          | ~ (v1_funct_1 @ X10)
% 6.25/6.52          | ((X11) = (X10))
% 6.25/6.52          | (r2_hidden @ (sk_C @ X10 @ X11) @ (k1_relat_1 @ X11))
% 6.25/6.52          | ((k1_relat_1 @ X11) != (k1_relat_1 @ X10))
% 6.25/6.52          | ~ (v1_funct_1 @ X11)
% 6.25/6.52          | ~ (v1_relat_1 @ X11))),
% 6.25/6.52      inference('cnf', [status(esa)], [t9_funct_1])).
% 6.25/6.52  thf('62', plain,
% 6.25/6.52      (![X0 : $i]:
% 6.25/6.52         (((sk_A) != (k1_relat_1 @ X0))
% 6.25/6.52          | ~ (v1_relat_1 @ sk_C_1)
% 6.25/6.52          | ~ (v1_funct_1 @ sk_C_1)
% 6.25/6.52          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 6.25/6.52          | ((sk_C_1) = (X0))
% 6.25/6.52          | ~ (v1_funct_1 @ X0)
% 6.25/6.52          | ~ (v1_relat_1 @ X0))),
% 6.25/6.52      inference('sup-', [status(thm)], ['60', '61'])).
% 6.25/6.52  thf('63', plain,
% 6.25/6.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.25/6.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.25/6.52  thf(cc1_relset_1, axiom,
% 6.25/6.52    (![A:$i,B:$i,C:$i]:
% 6.25/6.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.25/6.52       ( v1_relat_1 @ C ) ))).
% 6.25/6.52  thf('64', plain,
% 6.25/6.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 6.25/6.52         ((v1_relat_1 @ X12)
% 6.25/6.52          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 6.25/6.52      inference('cnf', [status(esa)], [cc1_relset_1])).
% 6.25/6.52  thf('65', plain, ((v1_relat_1 @ sk_C_1)),
% 6.25/6.52      inference('sup-', [status(thm)], ['63', '64'])).
% 6.25/6.52  thf('66', plain, ((v1_funct_1 @ sk_C_1)),
% 6.25/6.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.25/6.52  thf('67', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 6.25/6.52      inference('demod', [status(thm)], ['54', '59'])).
% 6.25/6.52  thf('68', plain,
% 6.25/6.52      (![X0 : $i]:
% 6.25/6.52         (((sk_A) != (k1_relat_1 @ X0))
% 6.25/6.52          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_A)
% 6.25/6.52          | ((sk_C_1) = (X0))
% 6.25/6.52          | ~ (v1_funct_1 @ X0)
% 6.25/6.52          | ~ (v1_relat_1 @ X0))),
% 6.25/6.52      inference('demod', [status(thm)], ['62', '65', '66', '67'])).
% 6.25/6.52  thf('69', plain,
% 6.25/6.52      ((((sk_A) != (sk_A))
% 6.25/6.52        | ~ (v1_relat_1 @ sk_D)
% 6.25/6.52        | ~ (v1_funct_1 @ sk_D)
% 6.25/6.52        | ((sk_C_1) = (sk_D))
% 6.25/6.52        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 6.25/6.52      inference('sup-', [status(thm)], ['47', '68'])).
% 6.25/6.52  thf('70', plain,
% 6.25/6.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.25/6.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.25/6.52  thf('71', plain,
% 6.25/6.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 6.25/6.52         ((v1_relat_1 @ X12)
% 6.25/6.52          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 6.25/6.52      inference('cnf', [status(esa)], [cc1_relset_1])).
% 6.25/6.52  thf('72', plain, ((v1_relat_1 @ sk_D)),
% 6.25/6.52      inference('sup-', [status(thm)], ['70', '71'])).
% 6.25/6.52  thf('73', plain, ((v1_funct_1 @ sk_D)),
% 6.25/6.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.25/6.52  thf('74', plain,
% 6.25/6.52      ((((sk_A) != (sk_A))
% 6.25/6.52        | ((sk_C_1) = (sk_D))
% 6.25/6.52        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 6.25/6.52      inference('demod', [status(thm)], ['69', '72', '73'])).
% 6.25/6.52  thf('75', plain,
% 6.25/6.52      (((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A) | ((sk_C_1) = (sk_D)))),
% 6.25/6.52      inference('simplify', [status(thm)], ['74'])).
% 6.25/6.52  thf('76', plain,
% 6.25/6.52      (![X30 : $i]:
% 6.25/6.52         (((k1_funct_1 @ sk_C_1 @ X30) = (k1_funct_1 @ sk_D @ X30))
% 6.25/6.52          | ~ (r2_hidden @ X30 @ sk_A))),
% 6.25/6.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.25/6.52  thf('77', plain,
% 6.25/6.52      ((((sk_C_1) = (sk_D))
% 6.25/6.52        | ((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 6.25/6.52            = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))))),
% 6.25/6.52      inference('sup-', [status(thm)], ['75', '76'])).
% 6.25/6.52  thf('78', plain,
% 6.25/6.52      (((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 6.25/6.52         = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))),
% 6.25/6.52      inference('condensation', [status(thm)], ['77'])).
% 6.25/6.52  thf('79', plain,
% 6.25/6.52      (![X10 : $i, X11 : $i]:
% 6.25/6.52         (~ (v1_relat_1 @ X10)
% 6.25/6.52          | ~ (v1_funct_1 @ X10)
% 6.25/6.52          | ((X11) = (X10))
% 6.25/6.52          | ((k1_funct_1 @ X11 @ (sk_C @ X10 @ X11))
% 6.25/6.52              != (k1_funct_1 @ X10 @ (sk_C @ X10 @ X11)))
% 6.25/6.52          | ((k1_relat_1 @ X11) != (k1_relat_1 @ X10))
% 6.25/6.52          | ~ (v1_funct_1 @ X11)
% 6.25/6.52          | ~ (v1_relat_1 @ X11))),
% 6.25/6.52      inference('cnf', [status(esa)], [t9_funct_1])).
% 6.25/6.52  thf('80', plain,
% 6.25/6.52      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 6.25/6.52          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 6.25/6.52        | ~ (v1_relat_1 @ sk_C_1)
% 6.25/6.52        | ~ (v1_funct_1 @ sk_C_1)
% 6.25/6.52        | ((k1_relat_1 @ sk_C_1) != (k1_relat_1 @ sk_D))
% 6.25/6.52        | ((sk_C_1) = (sk_D))
% 6.25/6.52        | ~ (v1_funct_1 @ sk_D)
% 6.25/6.52        | ~ (v1_relat_1 @ sk_D))),
% 6.25/6.52      inference('sup-', [status(thm)], ['78', '79'])).
% 6.25/6.52  thf('81', plain, ((v1_relat_1 @ sk_C_1)),
% 6.25/6.52      inference('sup-', [status(thm)], ['63', '64'])).
% 6.25/6.52  thf('82', plain, ((v1_funct_1 @ sk_C_1)),
% 6.25/6.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.25/6.52  thf('83', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 6.25/6.52      inference('demod', [status(thm)], ['54', '59'])).
% 6.25/6.52  thf('84', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 6.25/6.52      inference('demod', [status(thm)], ['7', '46'])).
% 6.25/6.52  thf('85', plain, ((v1_funct_1 @ sk_D)),
% 6.25/6.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.25/6.52  thf('86', plain, ((v1_relat_1 @ sk_D)),
% 6.25/6.52      inference('sup-', [status(thm)], ['70', '71'])).
% 6.25/6.52  thf('87', plain,
% 6.25/6.52      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 6.25/6.52          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 6.25/6.52        | ((sk_A) != (sk_A))
% 6.25/6.52        | ((sk_C_1) = (sk_D)))),
% 6.25/6.52      inference('demod', [status(thm)],
% 6.25/6.52                ['80', '81', '82', '83', '84', '85', '86'])).
% 6.25/6.52  thf('88', plain, (((sk_C_1) = (sk_D))),
% 6.25/6.52      inference('simplify', [status(thm)], ['87'])).
% 6.25/6.52  thf('89', plain,
% 6.25/6.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.25/6.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.25/6.52  thf('90', plain,
% 6.25/6.52      (![X19 : $i, X20 : $i, X21 : $i]:
% 6.25/6.52         ((r2_relset_1 @ X19 @ X20 @ X21 @ X21)
% 6.25/6.52          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 6.25/6.52      inference('simplify', [status(thm)], ['28'])).
% 6.25/6.52  thf('91', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1)),
% 6.25/6.52      inference('sup-', [status(thm)], ['89', '90'])).
% 6.25/6.52  thf('92', plain, ($false),
% 6.25/6.52      inference('demod', [status(thm)], ['0', '88', '91'])).
% 6.25/6.52  
% 6.25/6.52  % SZS output end Refutation
% 6.25/6.52  
% 6.25/6.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
