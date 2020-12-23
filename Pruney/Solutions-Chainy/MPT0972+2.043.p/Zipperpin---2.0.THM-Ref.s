%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5ZJx7bQ02K

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:39 EST 2020

% Result     : Theorem 5.03s
% Output     : Refutation 5.03s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 614 expanded)
%              Number of leaves         :   37 ( 200 expanded)
%              Depth                    :   21
%              Number of atoms          :  996 (6817 expanded)
%              Number of equality atoms :   75 ( 406 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ( X27
        = ( k1_relset_1 @ X27 @ X28 @ X29 ) )
      | ~ ( zip_tseitin_1 @ X29 @ X28 @ X27 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
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

thf('14',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('17',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('18',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['13','21'])).

thf('23',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('24',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X15 ) ) )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('25',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('27',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('31',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('32',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( r2_relset_1 @ X22 @ X23 @ X21 @ X24 )
      | ( X21 != X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('33',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_relset_1 @ X22 @ X23 @ X24 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_relset_1 @ X3 @ X2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','35'])).

thf('37',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ~ ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['28','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','18'])).

thf('42',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference(clc,[status(thm)],['39','46'])).

thf('48',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['10','47'])).

thf('49',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','48'])).

thf('50',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ( X27
        = ( k1_relset_1 @ X27 @ X28 @ X29 ) )
      | ~ ( zip_tseitin_1 @ X29 @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('52',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('55',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['52','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('59',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference(clc,[status(thm)],['39','46'])).

thf('61',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['56','61'])).

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

thf('63',plain,(
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

thf('64',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('66',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('67',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('68',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('69',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['56','61'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_A )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['64','69','70','71'])).

thf('73',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['49','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('76',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('78',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['73','78','79'])).

thf('81',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X33: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ X33 )
        = ( k1_funct_1 @ sk_D @ X33 ) )
      | ~ ( r2_hidden @ X33 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( sk_C_1 = sk_D )
    | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ),
    inference(condensation,[status(thm)],['83'])).

thf('85',plain,(
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

thf('86',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_1 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['67','68'])).

thf('88',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['56','61'])).

thf('90',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','48'])).

thf('91',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['76','77'])).

thf('93',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(demod,[status(thm)],['86','87','88','89','90','91','92'])).

thf('94',plain,(
    sk_C_1 = sk_D ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_relset_1 @ X22 @ X23 @ X24 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('97',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    $false ),
    inference(demod,[status(thm)],['0','94','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5ZJx7bQ02K
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:22:04 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  % Running portfolio for 600 s
% 0.20/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 5.03/5.25  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.03/5.25  % Solved by: fo/fo7.sh
% 5.03/5.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.03/5.25  % done 3769 iterations in 4.790s
% 5.03/5.25  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.03/5.25  % SZS output start Refutation
% 5.03/5.25  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 5.03/5.25  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.03/5.25  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 5.03/5.25  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 5.03/5.25  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.03/5.25  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.03/5.25  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 5.03/5.25  thf(sk_B_type, type, sk_B: $i).
% 5.03/5.25  thf(sk_A_type, type, sk_A: $i).
% 5.03/5.25  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 5.03/5.25  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 5.03/5.25  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 5.03/5.25  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 5.03/5.25  thf(sk_C_1_type, type, sk_C_1: $i).
% 5.03/5.25  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.03/5.25  thf(sk_D_type, type, sk_D: $i).
% 5.03/5.25  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.03/5.25  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 5.03/5.25  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 5.03/5.25  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.03/5.25  thf(t18_funct_2, conjecture,
% 5.03/5.25    (![A:$i,B:$i,C:$i]:
% 5.03/5.25     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.03/5.25         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.03/5.25       ( ![D:$i]:
% 5.03/5.25         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 5.03/5.25             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.03/5.25           ( ( ![E:$i]:
% 5.03/5.25               ( ( r2_hidden @ E @ A ) =>
% 5.03/5.25                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 5.03/5.25             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 5.03/5.25  thf(zf_stmt_0, negated_conjecture,
% 5.03/5.25    (~( ![A:$i,B:$i,C:$i]:
% 5.03/5.25        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.03/5.25            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.03/5.25          ( ![D:$i]:
% 5.03/5.25            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 5.03/5.25                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.03/5.25              ( ( ![E:$i]:
% 5.03/5.25                  ( ( r2_hidden @ E @ A ) =>
% 5.03/5.25                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 5.03/5.25                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 5.03/5.25    inference('cnf.neg', [status(esa)], [t18_funct_2])).
% 5.03/5.25  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)),
% 5.03/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.03/5.25  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 5.03/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.03/5.25  thf(d1_funct_2, axiom,
% 5.03/5.25    (![A:$i,B:$i,C:$i]:
% 5.03/5.25     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.03/5.25       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 5.03/5.25           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 5.03/5.25             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 5.03/5.25         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 5.03/5.25           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 5.03/5.25             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 5.03/5.25  thf(zf_stmt_1, axiom,
% 5.03/5.25    (![C:$i,B:$i,A:$i]:
% 5.03/5.25     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 5.03/5.25       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 5.03/5.25  thf('2', plain,
% 5.03/5.25      (![X27 : $i, X28 : $i, X29 : $i]:
% 5.03/5.25         (~ (v1_funct_2 @ X29 @ X27 @ X28)
% 5.03/5.25          | ((X27) = (k1_relset_1 @ X27 @ X28 @ X29))
% 5.03/5.25          | ~ (zip_tseitin_1 @ X29 @ X28 @ X27))),
% 5.03/5.25      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.03/5.25  thf('3', plain,
% 5.03/5.25      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 5.03/5.25        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 5.03/5.25      inference('sup-', [status(thm)], ['1', '2'])).
% 5.03/5.25  thf('4', plain,
% 5.03/5.25      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.03/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.03/5.25  thf(redefinition_k1_relset_1, axiom,
% 5.03/5.25    (![A:$i,B:$i,C:$i]:
% 5.03/5.25     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.03/5.25       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 5.03/5.25  thf('5', plain,
% 5.03/5.25      (![X18 : $i, X19 : $i, X20 : $i]:
% 5.03/5.25         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 5.03/5.25          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 5.03/5.25      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 5.03/5.25  thf('6', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 5.03/5.25      inference('sup-', [status(thm)], ['4', '5'])).
% 5.03/5.25  thf('7', plain,
% 5.03/5.25      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 5.03/5.25      inference('demod', [status(thm)], ['3', '6'])).
% 5.03/5.25  thf('8', plain,
% 5.03/5.25      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.03/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.03/5.25  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 5.03/5.25  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 5.03/5.25  thf(zf_stmt_4, axiom,
% 5.03/5.25    (![B:$i,A:$i]:
% 5.03/5.25     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 5.03/5.25       ( zip_tseitin_0 @ B @ A ) ))).
% 5.03/5.25  thf(zf_stmt_5, axiom,
% 5.03/5.25    (![A:$i,B:$i,C:$i]:
% 5.03/5.25     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.03/5.25       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 5.03/5.25         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 5.03/5.25           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 5.03/5.25             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 5.03/5.25  thf('9', plain,
% 5.03/5.25      (![X30 : $i, X31 : $i, X32 : $i]:
% 5.03/5.25         (~ (zip_tseitin_0 @ X30 @ X31)
% 5.03/5.25          | (zip_tseitin_1 @ X32 @ X30 @ X31)
% 5.03/5.25          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 5.03/5.25      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.03/5.25  thf('10', plain,
% 5.03/5.25      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 5.03/5.25      inference('sup-', [status(thm)], ['8', '9'])).
% 5.03/5.25  thf('11', plain,
% 5.03/5.25      (![X25 : $i, X26 : $i]:
% 5.03/5.25         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 5.03/5.25      inference('cnf', [status(esa)], [zf_stmt_4])).
% 5.03/5.25  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 5.03/5.25  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.03/5.25      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 5.03/5.25  thf('13', plain,
% 5.03/5.25      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 5.03/5.25      inference('sup+', [status(thm)], ['11', '12'])).
% 5.03/5.25  thf('14', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.03/5.25      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 5.03/5.25  thf(t8_boole, axiom,
% 5.03/5.25    (![A:$i,B:$i]:
% 5.03/5.25     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 5.03/5.25  thf('15', plain,
% 5.03/5.25      (![X0 : $i, X1 : $i]:
% 5.03/5.25         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 5.03/5.25      inference('cnf', [status(esa)], [t8_boole])).
% 5.03/5.25  thf('16', plain,
% 5.03/5.25      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 5.03/5.25      inference('sup-', [status(thm)], ['14', '15'])).
% 5.03/5.25  thf(t113_zfmisc_1, axiom,
% 5.03/5.25    (![A:$i,B:$i]:
% 5.03/5.25     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 5.03/5.25       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 5.03/5.25  thf('17', plain,
% 5.03/5.25      (![X3 : $i, X4 : $i]:
% 5.03/5.25         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 5.03/5.25      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 5.03/5.25  thf('18', plain,
% 5.03/5.25      (![X3 : $i]: ((k2_zfmisc_1 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 5.03/5.25      inference('simplify', [status(thm)], ['17'])).
% 5.03/5.25  thf('19', plain,
% 5.03/5.25      (![X0 : $i, X1 : $i]:
% 5.03/5.25         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 5.03/5.25      inference('sup+', [status(thm)], ['16', '18'])).
% 5.03/5.25  thf('20', plain,
% 5.03/5.25      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.03/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.03/5.25  thf('21', plain,
% 5.03/5.25      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 5.03/5.25        | ~ (v1_xboole_0 @ sk_B))),
% 5.03/5.25      inference('sup+', [status(thm)], ['19', '20'])).
% 5.03/5.25  thf('22', plain,
% 5.03/5.25      (![X0 : $i]:
% 5.03/5.25         ((zip_tseitin_0 @ sk_B @ X0)
% 5.03/5.25          | (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 5.03/5.25      inference('sup-', [status(thm)], ['13', '21'])).
% 5.03/5.25  thf('23', plain,
% 5.03/5.25      (![X3 : $i]: ((k2_zfmisc_1 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 5.03/5.25      inference('simplify', [status(thm)], ['17'])).
% 5.03/5.25  thf(cc4_relset_1, axiom,
% 5.03/5.25    (![A:$i,B:$i]:
% 5.03/5.25     ( ( v1_xboole_0 @ A ) =>
% 5.03/5.25       ( ![C:$i]:
% 5.03/5.25         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 5.03/5.25           ( v1_xboole_0 @ C ) ) ) ))).
% 5.03/5.25  thf('24', plain,
% 5.03/5.25      (![X15 : $i, X16 : $i, X17 : $i]:
% 5.03/5.25         (~ (v1_xboole_0 @ X15)
% 5.03/5.25          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X15)))
% 5.03/5.25          | (v1_xboole_0 @ X16))),
% 5.03/5.25      inference('cnf', [status(esa)], [cc4_relset_1])).
% 5.03/5.25  thf('25', plain,
% 5.03/5.25      (![X1 : $i]:
% 5.03/5.25         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 5.03/5.25          | (v1_xboole_0 @ X1)
% 5.03/5.25          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 5.03/5.25      inference('sup-', [status(thm)], ['23', '24'])).
% 5.03/5.25  thf('26', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.03/5.25      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 5.03/5.25  thf('27', plain,
% 5.03/5.25      (![X1 : $i]:
% 5.03/5.25         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 5.03/5.25          | (v1_xboole_0 @ X1))),
% 5.03/5.25      inference('demod', [status(thm)], ['25', '26'])).
% 5.03/5.25  thf('28', plain,
% 5.03/5.25      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | (v1_xboole_0 @ sk_C_1))),
% 5.03/5.25      inference('sup-', [status(thm)], ['22', '27'])).
% 5.03/5.25  thf('29', plain,
% 5.03/5.25      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 5.03/5.25      inference('sup-', [status(thm)], ['14', '15'])).
% 5.03/5.25  thf('30', plain,
% 5.03/5.25      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 5.03/5.25      inference('sup-', [status(thm)], ['14', '15'])).
% 5.03/5.25  thf(t4_subset_1, axiom,
% 5.03/5.25    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 5.03/5.25  thf('31', plain,
% 5.03/5.25      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 5.03/5.25      inference('cnf', [status(esa)], [t4_subset_1])).
% 5.03/5.25  thf(redefinition_r2_relset_1, axiom,
% 5.03/5.25    (![A:$i,B:$i,C:$i,D:$i]:
% 5.03/5.25     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.03/5.25         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.03/5.25       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 5.03/5.25  thf('32', plain,
% 5.03/5.25      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 5.03/5.25         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 5.03/5.25          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 5.03/5.25          | (r2_relset_1 @ X22 @ X23 @ X21 @ X24)
% 5.03/5.25          | ((X21) != (X24)))),
% 5.03/5.25      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 5.03/5.25  thf('33', plain,
% 5.03/5.25      (![X22 : $i, X23 : $i, X24 : $i]:
% 5.03/5.25         ((r2_relset_1 @ X22 @ X23 @ X24 @ X24)
% 5.03/5.25          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 5.03/5.25      inference('simplify', [status(thm)], ['32'])).
% 5.03/5.25  thf('34', plain,
% 5.03/5.25      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 5.03/5.25      inference('sup-', [status(thm)], ['31', '33'])).
% 5.03/5.25  thf('35', plain,
% 5.03/5.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.03/5.25         ((r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 5.03/5.25      inference('sup+', [status(thm)], ['30', '34'])).
% 5.03/5.25  thf('36', plain,
% 5.03/5.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.03/5.25         ((r2_relset_1 @ X3 @ X2 @ X1 @ X0)
% 5.03/5.25          | ~ (v1_xboole_0 @ X0)
% 5.03/5.25          | ~ (v1_xboole_0 @ X1))),
% 5.03/5.25      inference('sup+', [status(thm)], ['29', '35'])).
% 5.03/5.25  thf('37', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)),
% 5.03/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.03/5.25  thf('38', plain, ((~ (v1_xboole_0 @ sk_C_1) | ~ (v1_xboole_0 @ sk_D))),
% 5.03/5.25      inference('sup-', [status(thm)], ['36', '37'])).
% 5.03/5.25  thf('39', plain,
% 5.03/5.25      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | ~ (v1_xboole_0 @ sk_D))),
% 5.03/5.25      inference('sup-', [status(thm)], ['28', '38'])).
% 5.03/5.25  thf('40', plain,
% 5.03/5.25      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 5.03/5.25      inference('sup+', [status(thm)], ['11', '12'])).
% 5.03/5.25  thf('41', plain,
% 5.03/5.25      (![X0 : $i, X1 : $i]:
% 5.03/5.25         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 5.03/5.25      inference('sup+', [status(thm)], ['16', '18'])).
% 5.03/5.25  thf('42', plain,
% 5.03/5.25      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.03/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.03/5.25  thf('43', plain,
% 5.03/5.25      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0))
% 5.03/5.25        | ~ (v1_xboole_0 @ sk_B))),
% 5.03/5.25      inference('sup+', [status(thm)], ['41', '42'])).
% 5.03/5.25  thf('44', plain,
% 5.03/5.25      (![X0 : $i]:
% 5.03/5.25         ((zip_tseitin_0 @ sk_B @ X0)
% 5.03/5.25          | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 5.03/5.25      inference('sup-', [status(thm)], ['40', '43'])).
% 5.03/5.25  thf('45', plain,
% 5.03/5.25      (![X1 : $i]:
% 5.03/5.25         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 5.03/5.25          | (v1_xboole_0 @ X1))),
% 5.03/5.25      inference('demod', [status(thm)], ['25', '26'])).
% 5.03/5.25  thf('46', plain,
% 5.03/5.25      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | (v1_xboole_0 @ sk_D))),
% 5.03/5.25      inference('sup-', [status(thm)], ['44', '45'])).
% 5.03/5.25  thf('47', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 5.03/5.25      inference('clc', [status(thm)], ['39', '46'])).
% 5.03/5.25  thf('48', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 5.03/5.25      inference('demod', [status(thm)], ['10', '47'])).
% 5.03/5.25  thf('49', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 5.03/5.25      inference('demod', [status(thm)], ['7', '48'])).
% 5.03/5.25  thf('50', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 5.03/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.03/5.25  thf('51', plain,
% 5.03/5.25      (![X27 : $i, X28 : $i, X29 : $i]:
% 5.03/5.25         (~ (v1_funct_2 @ X29 @ X27 @ X28)
% 5.03/5.25          | ((X27) = (k1_relset_1 @ X27 @ X28 @ X29))
% 5.03/5.25          | ~ (zip_tseitin_1 @ X29 @ X28 @ X27))),
% 5.03/5.25      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.03/5.25  thf('52', plain,
% 5.03/5.25      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 5.03/5.25        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 5.03/5.25      inference('sup-', [status(thm)], ['50', '51'])).
% 5.03/5.25  thf('53', plain,
% 5.03/5.25      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.03/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.03/5.25  thf('54', plain,
% 5.03/5.25      (![X18 : $i, X19 : $i, X20 : $i]:
% 5.03/5.25         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 5.03/5.25          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 5.03/5.25      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 5.03/5.25  thf('55', plain,
% 5.03/5.25      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 5.03/5.25      inference('sup-', [status(thm)], ['53', '54'])).
% 5.03/5.25  thf('56', plain,
% 5.03/5.25      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 5.03/5.25        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 5.03/5.25      inference('demod', [status(thm)], ['52', '55'])).
% 5.03/5.25  thf('57', plain,
% 5.03/5.25      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.03/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.03/5.25  thf('58', plain,
% 5.03/5.25      (![X30 : $i, X31 : $i, X32 : $i]:
% 5.03/5.25         (~ (zip_tseitin_0 @ X30 @ X31)
% 5.03/5.25          | (zip_tseitin_1 @ X32 @ X30 @ X31)
% 5.03/5.25          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 5.03/5.25      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.03/5.25  thf('59', plain,
% 5.03/5.25      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 5.03/5.25        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 5.03/5.25      inference('sup-', [status(thm)], ['57', '58'])).
% 5.03/5.25  thf('60', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 5.03/5.25      inference('clc', [status(thm)], ['39', '46'])).
% 5.03/5.25  thf('61', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)),
% 5.03/5.25      inference('demod', [status(thm)], ['59', '60'])).
% 5.03/5.25  thf('62', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 5.03/5.25      inference('demod', [status(thm)], ['56', '61'])).
% 5.03/5.25  thf(t9_funct_1, axiom,
% 5.03/5.25    (![A:$i]:
% 5.03/5.25     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.03/5.25       ( ![B:$i]:
% 5.03/5.25         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 5.03/5.25           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 5.03/5.25               ( ![C:$i]:
% 5.03/5.25                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 5.03/5.25                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 5.03/5.25             ( ( A ) = ( B ) ) ) ) ) ))).
% 5.03/5.25  thf('63', plain,
% 5.03/5.25      (![X13 : $i, X14 : $i]:
% 5.03/5.25         (~ (v1_relat_1 @ X13)
% 5.03/5.25          | ~ (v1_funct_1 @ X13)
% 5.03/5.25          | ((X14) = (X13))
% 5.03/5.25          | (r2_hidden @ (sk_C @ X13 @ X14) @ (k1_relat_1 @ X14))
% 5.03/5.25          | ((k1_relat_1 @ X14) != (k1_relat_1 @ X13))
% 5.03/5.25          | ~ (v1_funct_1 @ X14)
% 5.03/5.25          | ~ (v1_relat_1 @ X14))),
% 5.03/5.25      inference('cnf', [status(esa)], [t9_funct_1])).
% 5.03/5.25  thf('64', plain,
% 5.03/5.25      (![X0 : $i]:
% 5.03/5.25         (((sk_A) != (k1_relat_1 @ X0))
% 5.03/5.25          | ~ (v1_relat_1 @ sk_C_1)
% 5.03/5.25          | ~ (v1_funct_1 @ sk_C_1)
% 5.03/5.25          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 5.03/5.25          | ((sk_C_1) = (X0))
% 5.03/5.25          | ~ (v1_funct_1 @ X0)
% 5.03/5.25          | ~ (v1_relat_1 @ X0))),
% 5.03/5.25      inference('sup-', [status(thm)], ['62', '63'])).
% 5.03/5.25  thf('65', plain,
% 5.03/5.25      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.03/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.03/5.25  thf(cc2_relat_1, axiom,
% 5.03/5.25    (![A:$i]:
% 5.03/5.25     ( ( v1_relat_1 @ A ) =>
% 5.03/5.25       ( ![B:$i]:
% 5.03/5.25         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 5.03/5.25  thf('66', plain,
% 5.03/5.25      (![X9 : $i, X10 : $i]:
% 5.03/5.25         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 5.03/5.25          | (v1_relat_1 @ X9)
% 5.03/5.25          | ~ (v1_relat_1 @ X10))),
% 5.03/5.25      inference('cnf', [status(esa)], [cc2_relat_1])).
% 5.03/5.25  thf('67', plain,
% 5.03/5.25      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_1))),
% 5.03/5.25      inference('sup-', [status(thm)], ['65', '66'])).
% 5.03/5.25  thf(fc6_relat_1, axiom,
% 5.03/5.25    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 5.03/5.25  thf('68', plain,
% 5.03/5.25      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 5.03/5.25      inference('cnf', [status(esa)], [fc6_relat_1])).
% 5.03/5.25  thf('69', plain, ((v1_relat_1 @ sk_C_1)),
% 5.03/5.25      inference('demod', [status(thm)], ['67', '68'])).
% 5.03/5.25  thf('70', plain, ((v1_funct_1 @ sk_C_1)),
% 5.03/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.03/5.25  thf('71', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 5.03/5.25      inference('demod', [status(thm)], ['56', '61'])).
% 5.03/5.25  thf('72', plain,
% 5.03/5.25      (![X0 : $i]:
% 5.03/5.25         (((sk_A) != (k1_relat_1 @ X0))
% 5.03/5.25          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_A)
% 5.03/5.25          | ((sk_C_1) = (X0))
% 5.03/5.25          | ~ (v1_funct_1 @ X0)
% 5.03/5.25          | ~ (v1_relat_1 @ X0))),
% 5.03/5.25      inference('demod', [status(thm)], ['64', '69', '70', '71'])).
% 5.03/5.25  thf('73', plain,
% 5.03/5.25      ((((sk_A) != (sk_A))
% 5.03/5.25        | ~ (v1_relat_1 @ sk_D)
% 5.03/5.25        | ~ (v1_funct_1 @ sk_D)
% 5.03/5.25        | ((sk_C_1) = (sk_D))
% 5.03/5.25        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 5.03/5.25      inference('sup-', [status(thm)], ['49', '72'])).
% 5.03/5.25  thf('74', plain,
% 5.03/5.25      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.03/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.03/5.25  thf('75', plain,
% 5.03/5.25      (![X9 : $i, X10 : $i]:
% 5.03/5.25         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 5.03/5.25          | (v1_relat_1 @ X9)
% 5.03/5.25          | ~ (v1_relat_1 @ X10))),
% 5.03/5.25      inference('cnf', [status(esa)], [cc2_relat_1])).
% 5.03/5.25  thf('76', plain,
% 5.03/5.25      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 5.03/5.25      inference('sup-', [status(thm)], ['74', '75'])).
% 5.03/5.25  thf('77', plain,
% 5.03/5.25      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 5.03/5.25      inference('cnf', [status(esa)], [fc6_relat_1])).
% 5.03/5.25  thf('78', plain, ((v1_relat_1 @ sk_D)),
% 5.03/5.25      inference('demod', [status(thm)], ['76', '77'])).
% 5.03/5.25  thf('79', plain, ((v1_funct_1 @ sk_D)),
% 5.03/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.03/5.25  thf('80', plain,
% 5.03/5.25      ((((sk_A) != (sk_A))
% 5.03/5.25        | ((sk_C_1) = (sk_D))
% 5.03/5.25        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 5.03/5.25      inference('demod', [status(thm)], ['73', '78', '79'])).
% 5.03/5.25  thf('81', plain,
% 5.03/5.25      (((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A) | ((sk_C_1) = (sk_D)))),
% 5.03/5.25      inference('simplify', [status(thm)], ['80'])).
% 5.03/5.25  thf('82', plain,
% 5.03/5.25      (![X33 : $i]:
% 5.03/5.25         (((k1_funct_1 @ sk_C_1 @ X33) = (k1_funct_1 @ sk_D @ X33))
% 5.03/5.25          | ~ (r2_hidden @ X33 @ sk_A))),
% 5.03/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.03/5.25  thf('83', plain,
% 5.03/5.25      ((((sk_C_1) = (sk_D))
% 5.03/5.25        | ((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 5.03/5.25            = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))))),
% 5.03/5.25      inference('sup-', [status(thm)], ['81', '82'])).
% 5.03/5.25  thf('84', plain,
% 5.03/5.25      (((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 5.03/5.25         = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))),
% 5.03/5.25      inference('condensation', [status(thm)], ['83'])).
% 5.03/5.25  thf('85', plain,
% 5.03/5.25      (![X13 : $i, X14 : $i]:
% 5.03/5.25         (~ (v1_relat_1 @ X13)
% 5.03/5.25          | ~ (v1_funct_1 @ X13)
% 5.03/5.25          | ((X14) = (X13))
% 5.03/5.25          | ((k1_funct_1 @ X14 @ (sk_C @ X13 @ X14))
% 5.03/5.25              != (k1_funct_1 @ X13 @ (sk_C @ X13 @ X14)))
% 5.03/5.25          | ((k1_relat_1 @ X14) != (k1_relat_1 @ X13))
% 5.03/5.25          | ~ (v1_funct_1 @ X14)
% 5.03/5.25          | ~ (v1_relat_1 @ X14))),
% 5.03/5.25      inference('cnf', [status(esa)], [t9_funct_1])).
% 5.03/5.25  thf('86', plain,
% 5.03/5.25      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 5.03/5.25          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 5.03/5.25        | ~ (v1_relat_1 @ sk_C_1)
% 5.03/5.25        | ~ (v1_funct_1 @ sk_C_1)
% 5.03/5.25        | ((k1_relat_1 @ sk_C_1) != (k1_relat_1 @ sk_D))
% 5.03/5.25        | ((sk_C_1) = (sk_D))
% 5.03/5.25        | ~ (v1_funct_1 @ sk_D)
% 5.03/5.25        | ~ (v1_relat_1 @ sk_D))),
% 5.03/5.25      inference('sup-', [status(thm)], ['84', '85'])).
% 5.03/5.25  thf('87', plain, ((v1_relat_1 @ sk_C_1)),
% 5.03/5.25      inference('demod', [status(thm)], ['67', '68'])).
% 5.03/5.25  thf('88', plain, ((v1_funct_1 @ sk_C_1)),
% 5.03/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.03/5.25  thf('89', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 5.03/5.25      inference('demod', [status(thm)], ['56', '61'])).
% 5.03/5.25  thf('90', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 5.03/5.25      inference('demod', [status(thm)], ['7', '48'])).
% 5.03/5.25  thf('91', plain, ((v1_funct_1 @ sk_D)),
% 5.03/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.03/5.25  thf('92', plain, ((v1_relat_1 @ sk_D)),
% 5.03/5.25      inference('demod', [status(thm)], ['76', '77'])).
% 5.03/5.25  thf('93', plain,
% 5.03/5.25      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 5.03/5.25          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 5.03/5.25        | ((sk_A) != (sk_A))
% 5.03/5.25        | ((sk_C_1) = (sk_D)))),
% 5.03/5.25      inference('demod', [status(thm)],
% 5.03/5.25                ['86', '87', '88', '89', '90', '91', '92'])).
% 5.03/5.25  thf('94', plain, (((sk_C_1) = (sk_D))),
% 5.03/5.25      inference('simplify', [status(thm)], ['93'])).
% 5.03/5.25  thf('95', plain,
% 5.03/5.25      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.03/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.03/5.25  thf('96', plain,
% 5.03/5.25      (![X22 : $i, X23 : $i, X24 : $i]:
% 5.03/5.25         ((r2_relset_1 @ X22 @ X23 @ X24 @ X24)
% 5.03/5.25          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 5.03/5.25      inference('simplify', [status(thm)], ['32'])).
% 5.03/5.25  thf('97', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1)),
% 5.03/5.25      inference('sup-', [status(thm)], ['95', '96'])).
% 5.03/5.25  thf('98', plain, ($false),
% 5.03/5.25      inference('demod', [status(thm)], ['0', '94', '97'])).
% 5.03/5.25  
% 5.03/5.25  % SZS output end Refutation
% 5.03/5.25  
% 5.03/5.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
