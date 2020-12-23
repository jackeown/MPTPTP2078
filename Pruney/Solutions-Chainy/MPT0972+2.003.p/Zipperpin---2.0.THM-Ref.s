%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.22bDDyjLrX

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:32 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 627 expanded)
%              Number of leaves         :   35 ( 201 expanded)
%              Depth                    :   23
%              Number of atoms          : 1064 (8545 expanded)
%              Number of equality atoms :   87 ( 439 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_relset_1 @ X15 @ X16 @ X17 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['2'])).

thf('4',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['1','3'])).

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

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('6',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('12',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('15',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('16',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('19',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['7','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X1 )
      | ( sk_C_1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
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

thf('24',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('25',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_C_1 = X0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ( X21
        = ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('29',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('31',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('32',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['26','33'])).

thf('35',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_B @ X0 @ sk_D )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','12'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('42',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('45',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['38','45'])).

thf('47',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('48',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('50',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['37','50'])).

thf('52',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['1','3'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X1 )
      | ( sk_C_1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('54',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('56',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_C_1 = X0 )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ( X21
        = ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('60',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('63',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['57','64'])).

thf('66',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_B @ X0 @ sk_D )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['52','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['38','45'])).

thf('70',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('71',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('73',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['68','73'])).

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

thf('75',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( X8 = X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X8 ) @ ( k1_relat_1 @ X8 ) )
      | ( ( k1_relat_1 @ X8 )
       != ( k1_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('78',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('79',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['68','73'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_A )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['76','79','80','81'])).

thf('83',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['51','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('86',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['83','86','87'])).

thf('89',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X27: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ X27 )
        = ( k1_funct_1 @ sk_D @ X27 ) )
      | ~ ( r2_hidden @ X27 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( sk_C_1 = sk_D )
    | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ),
    inference(condensation,[status(thm)],['91'])).

thf('93',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( X8 = X7 )
      | ( ( k1_funct_1 @ X8 @ ( sk_C @ X7 @ X8 ) )
       != ( k1_funct_1 @ X7 @ ( sk_C @ X7 @ X8 ) ) )
      | ( ( k1_relat_1 @ X8 )
       != ( k1_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('94',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_1 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['77','78'])).

thf('96',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['68','73'])).

thf('98',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['37','50'])).

thf('99',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['84','85'])).

thf('101',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(demod,[status(thm)],['94','95','96','97','98','99','100'])).

thf('102',plain,(
    sk_C_1 = sk_D ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['2'])).

thf('105',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    $false ),
    inference(demod,[status(thm)],['0','102','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.22bDDyjLrX
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:13:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.44/1.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.44/1.63  % Solved by: fo/fo7.sh
% 1.44/1.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.44/1.63  % done 1506 iterations in 1.181s
% 1.44/1.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.44/1.63  % SZS output start Refutation
% 1.44/1.63  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.44/1.63  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.44/1.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.44/1.63  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.44/1.63  thf(sk_A_type, type, sk_A: $i).
% 1.44/1.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.44/1.63  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.44/1.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.44/1.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.44/1.63  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.44/1.63  thf(sk_B_type, type, sk_B: $i).
% 1.44/1.63  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.44/1.63  thf(sk_D_type, type, sk_D: $i).
% 1.44/1.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.44/1.63  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.44/1.63  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.44/1.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.44/1.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.44/1.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.44/1.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.44/1.63  thf(t18_funct_2, conjecture,
% 1.44/1.63    (![A:$i,B:$i,C:$i]:
% 1.44/1.63     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.44/1.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.44/1.63       ( ![D:$i]:
% 1.44/1.63         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.44/1.63             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.44/1.63           ( ( ![E:$i]:
% 1.44/1.63               ( ( r2_hidden @ E @ A ) =>
% 1.44/1.63                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 1.44/1.63             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 1.44/1.63  thf(zf_stmt_0, negated_conjecture,
% 1.44/1.63    (~( ![A:$i,B:$i,C:$i]:
% 1.44/1.63        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.44/1.63            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.44/1.63          ( ![D:$i]:
% 1.44/1.63            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.44/1.63                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.44/1.63              ( ( ![E:$i]:
% 1.44/1.63                  ( ( r2_hidden @ E @ A ) =>
% 1.44/1.63                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 1.44/1.63                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 1.44/1.63    inference('cnf.neg', [status(esa)], [t18_funct_2])).
% 1.44/1.63  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)),
% 1.44/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.63  thf('1', plain,
% 1.44/1.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.44/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.63  thf(reflexivity_r2_relset_1, axiom,
% 1.44/1.63    (![A:$i,B:$i,C:$i,D:$i]:
% 1.44/1.63     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.44/1.63         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.44/1.63       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 1.44/1.63  thf('2', plain,
% 1.44/1.63      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 1.44/1.63         ((r2_relset_1 @ X15 @ X16 @ X17 @ X17)
% 1.44/1.63          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 1.44/1.63          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.44/1.63      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 1.44/1.63  thf('3', plain,
% 1.44/1.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.63         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 1.44/1.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 1.44/1.63      inference('condensation', [status(thm)], ['2'])).
% 1.44/1.63  thf('4', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D)),
% 1.44/1.63      inference('sup-', [status(thm)], ['1', '3'])).
% 1.44/1.63  thf(d1_funct_2, axiom,
% 1.44/1.63    (![A:$i,B:$i,C:$i]:
% 1.44/1.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.44/1.63       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.44/1.63           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.44/1.63             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.44/1.63         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.44/1.63           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.44/1.63             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.44/1.63  thf(zf_stmt_1, axiom,
% 1.44/1.63    (![B:$i,A:$i]:
% 1.44/1.63     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.44/1.63       ( zip_tseitin_0 @ B @ A ) ))).
% 1.44/1.63  thf('5', plain,
% 1.44/1.63      (![X19 : $i, X20 : $i]:
% 1.44/1.63         ((zip_tseitin_0 @ X19 @ X20) | ((X19) = (k1_xboole_0)))),
% 1.44/1.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.44/1.63  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.44/1.63  thf('6', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.44/1.63      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.44/1.63  thf('7', plain,
% 1.44/1.63      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.44/1.63      inference('sup+', [status(thm)], ['5', '6'])).
% 1.44/1.63  thf('8', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.44/1.63      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.44/1.63  thf(t8_boole, axiom,
% 1.44/1.63    (![A:$i,B:$i]:
% 1.44/1.63     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 1.44/1.63  thf('9', plain,
% 1.44/1.63      (![X0 : $i, X1 : $i]:
% 1.44/1.63         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 1.44/1.63      inference('cnf', [status(esa)], [t8_boole])).
% 1.44/1.63  thf('10', plain,
% 1.44/1.63      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.44/1.63      inference('sup-', [status(thm)], ['8', '9'])).
% 1.44/1.63  thf(t113_zfmisc_1, axiom,
% 1.44/1.63    (![A:$i,B:$i]:
% 1.44/1.63     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.44/1.63       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.44/1.63  thf('11', plain,
% 1.44/1.63      (![X3 : $i, X4 : $i]:
% 1.44/1.63         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 1.44/1.63      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.44/1.63  thf('12', plain,
% 1.44/1.63      (![X3 : $i]: ((k2_zfmisc_1 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 1.44/1.63      inference('simplify', [status(thm)], ['11'])).
% 1.44/1.63  thf('13', plain,
% 1.44/1.63      (![X0 : $i, X1 : $i]:
% 1.44/1.63         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.44/1.63      inference('sup+', [status(thm)], ['10', '12'])).
% 1.44/1.63  thf('14', plain,
% 1.44/1.63      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.44/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.63  thf(cc1_subset_1, axiom,
% 1.44/1.63    (![A:$i]:
% 1.44/1.63     ( ( v1_xboole_0 @ A ) =>
% 1.44/1.63       ( ![B:$i]:
% 1.44/1.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 1.44/1.63  thf('15', plain,
% 1.44/1.63      (![X5 : $i, X6 : $i]:
% 1.44/1.63         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 1.44/1.63          | (v1_xboole_0 @ X5)
% 1.44/1.63          | ~ (v1_xboole_0 @ X6))),
% 1.44/1.63      inference('cnf', [status(esa)], [cc1_subset_1])).
% 1.44/1.63  thf('16', plain,
% 1.44/1.63      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C_1))),
% 1.44/1.63      inference('sup-', [status(thm)], ['14', '15'])).
% 1.44/1.63  thf('17', plain,
% 1.44/1.63      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.44/1.63        | ~ (v1_xboole_0 @ sk_B)
% 1.44/1.63        | (v1_xboole_0 @ sk_C_1))),
% 1.44/1.63      inference('sup-', [status(thm)], ['13', '16'])).
% 1.44/1.63  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.44/1.63      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.44/1.63  thf('19', plain, ((~ (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_C_1))),
% 1.44/1.63      inference('demod', [status(thm)], ['17', '18'])).
% 1.44/1.63  thf('20', plain,
% 1.44/1.63      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | (v1_xboole_0 @ sk_C_1))),
% 1.44/1.63      inference('sup-', [status(thm)], ['7', '19'])).
% 1.44/1.63  thf('21', plain,
% 1.44/1.63      (![X0 : $i, X1 : $i]:
% 1.44/1.63         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 1.44/1.63      inference('cnf', [status(esa)], [t8_boole])).
% 1.44/1.63  thf('22', plain,
% 1.44/1.63      (![X0 : $i, X1 : $i]:
% 1.44/1.63         ((zip_tseitin_0 @ sk_B @ X1)
% 1.44/1.63          | ((sk_C_1) = (X0))
% 1.44/1.63          | ~ (v1_xboole_0 @ X0))),
% 1.44/1.63      inference('sup-', [status(thm)], ['20', '21'])).
% 1.44/1.63  thf('23', plain,
% 1.44/1.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.44/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.63  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.44/1.63  thf(zf_stmt_3, axiom,
% 1.44/1.63    (![C:$i,B:$i,A:$i]:
% 1.44/1.63     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.44/1.63       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.44/1.63  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.44/1.63  thf(zf_stmt_5, axiom,
% 1.44/1.63    (![A:$i,B:$i,C:$i]:
% 1.44/1.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.44/1.63       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.44/1.63         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.44/1.63           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.44/1.63             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.44/1.63  thf('24', plain,
% 1.44/1.63      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.44/1.63         (~ (zip_tseitin_0 @ X24 @ X25)
% 1.44/1.63          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 1.44/1.63          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 1.44/1.63      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.44/1.63  thf('25', plain,
% 1.44/1.63      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.44/1.63      inference('sup-', [status(thm)], ['23', '24'])).
% 1.44/1.63  thf('26', plain,
% 1.44/1.63      (![X0 : $i]:
% 1.44/1.63         (~ (v1_xboole_0 @ X0)
% 1.44/1.63          | ((sk_C_1) = (X0))
% 1.44/1.63          | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 1.44/1.63      inference('sup-', [status(thm)], ['22', '25'])).
% 1.44/1.63  thf('27', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 1.44/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.63  thf('28', plain,
% 1.44/1.63      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.44/1.63         (~ (v1_funct_2 @ X23 @ X21 @ X22)
% 1.44/1.63          | ((X21) = (k1_relset_1 @ X21 @ X22 @ X23))
% 1.44/1.63          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 1.44/1.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.44/1.63  thf('29', plain,
% 1.44/1.63      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 1.44/1.63        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 1.44/1.63      inference('sup-', [status(thm)], ['27', '28'])).
% 1.44/1.63  thf('30', plain,
% 1.44/1.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.44/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.63  thf(redefinition_k1_relset_1, axiom,
% 1.44/1.63    (![A:$i,B:$i,C:$i]:
% 1.44/1.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.44/1.63       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.44/1.63  thf('31', plain,
% 1.44/1.63      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.44/1.63         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 1.44/1.63          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.44/1.63      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.44/1.63  thf('32', plain,
% 1.44/1.63      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.44/1.63      inference('sup-', [status(thm)], ['30', '31'])).
% 1.44/1.63  thf('33', plain,
% 1.44/1.63      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.44/1.63      inference('demod', [status(thm)], ['29', '32'])).
% 1.44/1.63  thf('34', plain,
% 1.44/1.63      (![X0 : $i]:
% 1.44/1.63         (((sk_C_1) = (X0))
% 1.44/1.63          | ~ (v1_xboole_0 @ X0)
% 1.44/1.63          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.44/1.63      inference('sup-', [status(thm)], ['26', '33'])).
% 1.44/1.63  thf('35', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)),
% 1.44/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.63  thf('36', plain,
% 1.44/1.63      (![X0 : $i]:
% 1.44/1.63         (~ (r2_relset_1 @ sk_A @ sk_B @ X0 @ sk_D)
% 1.44/1.63          | ((sk_A) = (k1_relat_1 @ sk_D))
% 1.44/1.63          | ~ (v1_xboole_0 @ X0))),
% 1.44/1.63      inference('sup-', [status(thm)], ['34', '35'])).
% 1.44/1.63  thf('37', plain, ((~ (v1_xboole_0 @ sk_D) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.44/1.63      inference('sup-', [status(thm)], ['4', '36'])).
% 1.44/1.63  thf('38', plain,
% 1.44/1.63      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.44/1.63      inference('sup+', [status(thm)], ['5', '6'])).
% 1.44/1.63  thf('39', plain,
% 1.44/1.63      (![X0 : $i, X1 : $i]:
% 1.44/1.63         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.44/1.63      inference('sup+', [status(thm)], ['10', '12'])).
% 1.44/1.63  thf('40', plain,
% 1.44/1.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.44/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.63  thf('41', plain,
% 1.44/1.63      (![X5 : $i, X6 : $i]:
% 1.44/1.63         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 1.44/1.63          | (v1_xboole_0 @ X5)
% 1.44/1.63          | ~ (v1_xboole_0 @ X6))),
% 1.44/1.63      inference('cnf', [status(esa)], [cc1_subset_1])).
% 1.44/1.63  thf('42', plain,
% 1.44/1.63      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_D))),
% 1.44/1.63      inference('sup-', [status(thm)], ['40', '41'])).
% 1.44/1.63  thf('43', plain,
% 1.44/1.63      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.44/1.63        | ~ (v1_xboole_0 @ sk_B)
% 1.44/1.63        | (v1_xboole_0 @ sk_D))),
% 1.44/1.63      inference('sup-', [status(thm)], ['39', '42'])).
% 1.44/1.63  thf('44', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.44/1.63      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.44/1.63  thf('45', plain, ((~ (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_D))),
% 1.44/1.63      inference('demod', [status(thm)], ['43', '44'])).
% 1.44/1.63  thf('46', plain,
% 1.44/1.63      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | (v1_xboole_0 @ sk_D))),
% 1.44/1.63      inference('sup-', [status(thm)], ['38', '45'])).
% 1.44/1.63  thf('47', plain,
% 1.44/1.63      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.44/1.63      inference('sup-', [status(thm)], ['23', '24'])).
% 1.44/1.63  thf('48', plain,
% 1.44/1.63      (((v1_xboole_0 @ sk_D) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 1.44/1.63      inference('sup-', [status(thm)], ['46', '47'])).
% 1.44/1.63  thf('49', plain,
% 1.44/1.63      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.44/1.63      inference('demod', [status(thm)], ['29', '32'])).
% 1.44/1.63  thf('50', plain, (((v1_xboole_0 @ sk_D) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.44/1.63      inference('sup-', [status(thm)], ['48', '49'])).
% 1.44/1.63  thf('51', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 1.44/1.63      inference('clc', [status(thm)], ['37', '50'])).
% 1.44/1.63  thf('52', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D)),
% 1.44/1.63      inference('sup-', [status(thm)], ['1', '3'])).
% 1.44/1.63  thf('53', plain,
% 1.44/1.63      (![X0 : $i, X1 : $i]:
% 1.44/1.63         ((zip_tseitin_0 @ sk_B @ X1)
% 1.44/1.63          | ((sk_C_1) = (X0))
% 1.44/1.63          | ~ (v1_xboole_0 @ X0))),
% 1.44/1.63      inference('sup-', [status(thm)], ['20', '21'])).
% 1.44/1.63  thf('54', plain,
% 1.44/1.63      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.44/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.63  thf('55', plain,
% 1.44/1.63      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.44/1.63         (~ (zip_tseitin_0 @ X24 @ X25)
% 1.44/1.63          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 1.44/1.63          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 1.44/1.63      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.44/1.63  thf('56', plain,
% 1.44/1.63      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 1.44/1.63        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.44/1.63      inference('sup-', [status(thm)], ['54', '55'])).
% 1.44/1.63  thf('57', plain,
% 1.44/1.63      (![X0 : $i]:
% 1.44/1.63         (~ (v1_xboole_0 @ X0)
% 1.44/1.63          | ((sk_C_1) = (X0))
% 1.44/1.63          | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 1.44/1.63      inference('sup-', [status(thm)], ['53', '56'])).
% 1.44/1.63  thf('58', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 1.44/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.63  thf('59', plain,
% 1.44/1.63      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.44/1.63         (~ (v1_funct_2 @ X23 @ X21 @ X22)
% 1.44/1.63          | ((X21) = (k1_relset_1 @ X21 @ X22 @ X23))
% 1.44/1.63          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 1.44/1.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.44/1.63  thf('60', plain,
% 1.44/1.63      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 1.44/1.63        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 1.44/1.63      inference('sup-', [status(thm)], ['58', '59'])).
% 1.44/1.63  thf('61', plain,
% 1.44/1.63      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.44/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.63  thf('62', plain,
% 1.44/1.63      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.44/1.63         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 1.44/1.63          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.44/1.63      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.44/1.63  thf('63', plain,
% 1.44/1.63      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 1.44/1.63      inference('sup-', [status(thm)], ['61', '62'])).
% 1.44/1.63  thf('64', plain,
% 1.44/1.63      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 1.44/1.63        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.44/1.63      inference('demod', [status(thm)], ['60', '63'])).
% 1.44/1.63  thf('65', plain,
% 1.44/1.63      (![X0 : $i]:
% 1.44/1.63         (((sk_C_1) = (X0))
% 1.44/1.63          | ~ (v1_xboole_0 @ X0)
% 1.44/1.63          | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.44/1.63      inference('sup-', [status(thm)], ['57', '64'])).
% 1.44/1.63  thf('66', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)),
% 1.44/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.63  thf('67', plain,
% 1.44/1.63      (![X0 : $i]:
% 1.44/1.63         (~ (r2_relset_1 @ sk_A @ sk_B @ X0 @ sk_D)
% 1.44/1.63          | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 1.44/1.63          | ~ (v1_xboole_0 @ X0))),
% 1.44/1.63      inference('sup-', [status(thm)], ['65', '66'])).
% 1.44/1.63  thf('68', plain,
% 1.44/1.63      ((~ (v1_xboole_0 @ sk_D) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.44/1.63      inference('sup-', [status(thm)], ['52', '67'])).
% 1.44/1.63  thf('69', plain,
% 1.44/1.63      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | (v1_xboole_0 @ sk_D))),
% 1.44/1.63      inference('sup-', [status(thm)], ['38', '45'])).
% 1.44/1.63  thf('70', plain,
% 1.44/1.63      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 1.44/1.63        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.44/1.63      inference('sup-', [status(thm)], ['54', '55'])).
% 1.44/1.63  thf('71', plain,
% 1.44/1.63      (((v1_xboole_0 @ sk_D) | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 1.44/1.63      inference('sup-', [status(thm)], ['69', '70'])).
% 1.44/1.63  thf('72', plain,
% 1.44/1.63      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 1.44/1.63        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.44/1.63      inference('demod', [status(thm)], ['60', '63'])).
% 1.44/1.63  thf('73', plain, (((v1_xboole_0 @ sk_D) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.44/1.63      inference('sup-', [status(thm)], ['71', '72'])).
% 1.44/1.63  thf('74', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 1.44/1.63      inference('clc', [status(thm)], ['68', '73'])).
% 1.44/1.63  thf(t9_funct_1, axiom,
% 1.44/1.63    (![A:$i]:
% 1.44/1.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.44/1.63       ( ![B:$i]:
% 1.44/1.63         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.44/1.63           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 1.44/1.63               ( ![C:$i]:
% 1.44/1.63                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 1.44/1.63                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 1.44/1.63             ( ( A ) = ( B ) ) ) ) ) ))).
% 1.44/1.63  thf('75', plain,
% 1.44/1.63      (![X7 : $i, X8 : $i]:
% 1.44/1.63         (~ (v1_relat_1 @ X7)
% 1.44/1.63          | ~ (v1_funct_1 @ X7)
% 1.44/1.63          | ((X8) = (X7))
% 1.44/1.63          | (r2_hidden @ (sk_C @ X7 @ X8) @ (k1_relat_1 @ X8))
% 1.44/1.63          | ((k1_relat_1 @ X8) != (k1_relat_1 @ X7))
% 1.44/1.63          | ~ (v1_funct_1 @ X8)
% 1.44/1.63          | ~ (v1_relat_1 @ X8))),
% 1.44/1.63      inference('cnf', [status(esa)], [t9_funct_1])).
% 1.44/1.63  thf('76', plain,
% 1.44/1.63      (![X0 : $i]:
% 1.44/1.63         (((sk_A) != (k1_relat_1 @ X0))
% 1.44/1.63          | ~ (v1_relat_1 @ sk_C_1)
% 1.44/1.63          | ~ (v1_funct_1 @ sk_C_1)
% 1.44/1.63          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 1.44/1.63          | ((sk_C_1) = (X0))
% 1.44/1.63          | ~ (v1_funct_1 @ X0)
% 1.44/1.63          | ~ (v1_relat_1 @ X0))),
% 1.44/1.63      inference('sup-', [status(thm)], ['74', '75'])).
% 1.44/1.63  thf('77', plain,
% 1.44/1.63      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.44/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.63  thf(cc1_relset_1, axiom,
% 1.44/1.63    (![A:$i,B:$i,C:$i]:
% 1.44/1.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.44/1.63       ( v1_relat_1 @ C ) ))).
% 1.44/1.63  thf('78', plain,
% 1.44/1.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.44/1.63         ((v1_relat_1 @ X9)
% 1.44/1.63          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 1.44/1.63      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.44/1.63  thf('79', plain, ((v1_relat_1 @ sk_C_1)),
% 1.44/1.63      inference('sup-', [status(thm)], ['77', '78'])).
% 1.44/1.63  thf('80', plain, ((v1_funct_1 @ sk_C_1)),
% 1.44/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.63  thf('81', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 1.44/1.63      inference('clc', [status(thm)], ['68', '73'])).
% 1.44/1.63  thf('82', plain,
% 1.44/1.63      (![X0 : $i]:
% 1.44/1.63         (((sk_A) != (k1_relat_1 @ X0))
% 1.44/1.63          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_A)
% 1.44/1.63          | ((sk_C_1) = (X0))
% 1.44/1.63          | ~ (v1_funct_1 @ X0)
% 1.44/1.63          | ~ (v1_relat_1 @ X0))),
% 1.44/1.63      inference('demod', [status(thm)], ['76', '79', '80', '81'])).
% 1.44/1.63  thf('83', plain,
% 1.44/1.63      ((((sk_A) != (sk_A))
% 1.44/1.63        | ~ (v1_relat_1 @ sk_D)
% 1.44/1.63        | ~ (v1_funct_1 @ sk_D)
% 1.44/1.63        | ((sk_C_1) = (sk_D))
% 1.44/1.63        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 1.44/1.63      inference('sup-', [status(thm)], ['51', '82'])).
% 1.44/1.63  thf('84', plain,
% 1.44/1.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.44/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.63  thf('85', plain,
% 1.44/1.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.44/1.63         ((v1_relat_1 @ X9)
% 1.44/1.63          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 1.44/1.63      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.44/1.63  thf('86', plain, ((v1_relat_1 @ sk_D)),
% 1.44/1.63      inference('sup-', [status(thm)], ['84', '85'])).
% 1.44/1.63  thf('87', plain, ((v1_funct_1 @ sk_D)),
% 1.44/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.63  thf('88', plain,
% 1.44/1.63      ((((sk_A) != (sk_A))
% 1.44/1.63        | ((sk_C_1) = (sk_D))
% 1.44/1.63        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 1.44/1.63      inference('demod', [status(thm)], ['83', '86', '87'])).
% 1.44/1.63  thf('89', plain,
% 1.44/1.63      (((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A) | ((sk_C_1) = (sk_D)))),
% 1.44/1.63      inference('simplify', [status(thm)], ['88'])).
% 1.44/1.63  thf('90', plain,
% 1.44/1.63      (![X27 : $i]:
% 1.44/1.63         (((k1_funct_1 @ sk_C_1 @ X27) = (k1_funct_1 @ sk_D @ X27))
% 1.44/1.63          | ~ (r2_hidden @ X27 @ sk_A))),
% 1.44/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.63  thf('91', plain,
% 1.44/1.63      ((((sk_C_1) = (sk_D))
% 1.44/1.63        | ((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 1.44/1.63            = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))))),
% 1.44/1.63      inference('sup-', [status(thm)], ['89', '90'])).
% 1.44/1.63  thf('92', plain,
% 1.44/1.63      (((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 1.44/1.63         = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))),
% 1.44/1.63      inference('condensation', [status(thm)], ['91'])).
% 1.44/1.63  thf('93', plain,
% 1.44/1.63      (![X7 : $i, X8 : $i]:
% 1.44/1.63         (~ (v1_relat_1 @ X7)
% 1.44/1.63          | ~ (v1_funct_1 @ X7)
% 1.44/1.63          | ((X8) = (X7))
% 1.44/1.63          | ((k1_funct_1 @ X8 @ (sk_C @ X7 @ X8))
% 1.44/1.63              != (k1_funct_1 @ X7 @ (sk_C @ X7 @ X8)))
% 1.44/1.63          | ((k1_relat_1 @ X8) != (k1_relat_1 @ X7))
% 1.44/1.63          | ~ (v1_funct_1 @ X8)
% 1.44/1.63          | ~ (v1_relat_1 @ X8))),
% 1.44/1.63      inference('cnf', [status(esa)], [t9_funct_1])).
% 1.44/1.63  thf('94', plain,
% 1.44/1.63      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 1.44/1.63          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 1.44/1.63        | ~ (v1_relat_1 @ sk_C_1)
% 1.44/1.63        | ~ (v1_funct_1 @ sk_C_1)
% 1.44/1.63        | ((k1_relat_1 @ sk_C_1) != (k1_relat_1 @ sk_D))
% 1.44/1.63        | ((sk_C_1) = (sk_D))
% 1.44/1.63        | ~ (v1_funct_1 @ sk_D)
% 1.44/1.63        | ~ (v1_relat_1 @ sk_D))),
% 1.44/1.63      inference('sup-', [status(thm)], ['92', '93'])).
% 1.44/1.63  thf('95', plain, ((v1_relat_1 @ sk_C_1)),
% 1.44/1.63      inference('sup-', [status(thm)], ['77', '78'])).
% 1.44/1.63  thf('96', plain, ((v1_funct_1 @ sk_C_1)),
% 1.44/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.63  thf('97', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 1.44/1.63      inference('clc', [status(thm)], ['68', '73'])).
% 1.44/1.63  thf('98', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 1.44/1.63      inference('clc', [status(thm)], ['37', '50'])).
% 1.44/1.63  thf('99', plain, ((v1_funct_1 @ sk_D)),
% 1.44/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.63  thf('100', plain, ((v1_relat_1 @ sk_D)),
% 1.44/1.63      inference('sup-', [status(thm)], ['84', '85'])).
% 1.44/1.63  thf('101', plain,
% 1.44/1.63      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 1.44/1.63          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 1.44/1.63        | ((sk_A) != (sk_A))
% 1.44/1.63        | ((sk_C_1) = (sk_D)))),
% 1.44/1.63      inference('demod', [status(thm)],
% 1.44/1.63                ['94', '95', '96', '97', '98', '99', '100'])).
% 1.44/1.63  thf('102', plain, (((sk_C_1) = (sk_D))),
% 1.44/1.63      inference('simplify', [status(thm)], ['101'])).
% 1.44/1.63  thf('103', plain,
% 1.44/1.63      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.44/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.63  thf('104', plain,
% 1.44/1.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.63         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 1.44/1.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 1.44/1.63      inference('condensation', [status(thm)], ['2'])).
% 1.44/1.63  thf('105', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1)),
% 1.44/1.63      inference('sup-', [status(thm)], ['103', '104'])).
% 1.44/1.63  thf('106', plain, ($false),
% 1.44/1.63      inference('demod', [status(thm)], ['0', '102', '105'])).
% 1.44/1.63  
% 1.44/1.63  % SZS output end Refutation
% 1.44/1.63  
% 1.44/1.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
