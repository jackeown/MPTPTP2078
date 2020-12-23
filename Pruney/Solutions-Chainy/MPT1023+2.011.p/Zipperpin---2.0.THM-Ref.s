%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fPJHong2hw

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:30 EST 2020

% Result     : Theorem 1.68s
% Output     : Refutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 398 expanded)
%              Number of leaves         :   36 ( 133 expanded)
%              Depth                    :   22
%              Number of atoms          :  908 (5968 expanded)
%              Number of equality atoms :   65 ( 242 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('12',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( r2_relset_1 @ X24 @ X25 @ X23 @ X26 )
      | ( X23 != X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('13',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r2_relset_1 @ X24 @ X25 @ X26 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('16',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('19',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X17 ) ) )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('22',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ( sk_D = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ sk_B_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ~ ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['14','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('28',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X17 ) ) )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('30',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['26','31'])).

thf('33',plain,(
    zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['10','32'])).

thf('34',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','33'])).

thf('35',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('37',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('40',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('44',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['26','31'])).

thf('46',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['41','46'])).

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

thf('48',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( X13 = X12 )
      | ( r2_hidden @ ( sk_C @ X12 @ X13 ) @ ( k1_relat_1 @ X13 ) )
      | ( ( k1_relat_1 @ X13 )
       != ( k1_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('51',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('52',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['41','46'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_A )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['49','52','53','54'])).

thf('56',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['34','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('59',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['56','59','60'])).

thf('62',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(simplify,[status(thm)],['61'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('63',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( m1_subset_1 @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('65',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ X5 @ X6 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_C_1 = sk_D )
    | ( m1_subset_1 @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X35: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ X35 )
        = ( k1_funct_1 @ sk_D @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( sk_C_1 = sk_D )
    | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ),
    inference(condensation,[status(thm)],['68'])).

thf('70',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( X13 = X12 )
      | ( ( k1_funct_1 @ X13 @ ( sk_C @ X12 @ X13 ) )
       != ( k1_funct_1 @ X12 @ ( sk_C @ X12 @ X13 ) ) )
      | ( ( k1_relat_1 @ X13 )
       != ( k1_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('71',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_1 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['50','51'])).

thf('73',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['41','46'])).

thf('75',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','33'])).

thf('76',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['57','58'])).

thf('78',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(demod,[status(thm)],['71','72','73','74','75','76','77'])).

thf('79',plain,(
    sk_C_1 = sk_D ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['11','13'])).

thf('81',plain,(
    $false ),
    inference(demod,[status(thm)],['0','79','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fPJHong2hw
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:24:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.68/1.90  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.68/1.90  % Solved by: fo/fo7.sh
% 1.68/1.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.68/1.90  % done 863 iterations in 1.390s
% 1.68/1.90  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.68/1.90  % SZS output start Refutation
% 1.68/1.90  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.68/1.90  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.68/1.90  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.68/1.90  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.68/1.90  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.68/1.90  thf(sk_D_type, type, sk_D: $i).
% 1.68/1.90  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.68/1.90  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.68/1.90  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.68/1.90  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.68/1.90  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.68/1.90  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.68/1.90  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.68/1.90  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.68/1.90  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.68/1.90  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.68/1.90  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.68/1.90  thf(sk_A_type, type, sk_A: $i).
% 1.68/1.90  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.68/1.90  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.68/1.90  thf(t113_funct_2, conjecture,
% 1.68/1.90    (![A:$i,B:$i,C:$i]:
% 1.68/1.90     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.68/1.90         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.68/1.90       ( ![D:$i]:
% 1.68/1.90         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.68/1.90             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.68/1.90           ( ( ![E:$i]:
% 1.68/1.90               ( ( m1_subset_1 @ E @ A ) =>
% 1.68/1.90                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 1.68/1.90             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 1.68/1.90  thf(zf_stmt_0, negated_conjecture,
% 1.68/1.90    (~( ![A:$i,B:$i,C:$i]:
% 1.68/1.90        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.68/1.90            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.68/1.90          ( ![D:$i]:
% 1.68/1.90            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.68/1.90                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.68/1.90              ( ( ![E:$i]:
% 1.68/1.90                  ( ( m1_subset_1 @ E @ A ) =>
% 1.68/1.90                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 1.68/1.90                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 1.68/1.90    inference('cnf.neg', [status(esa)], [t113_funct_2])).
% 1.68/1.90  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)),
% 1.68/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.90  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 1.68/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.90  thf(d1_funct_2, axiom,
% 1.68/1.90    (![A:$i,B:$i,C:$i]:
% 1.68/1.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.68/1.90       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.68/1.90           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.68/1.90             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.68/1.90         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.68/1.90           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.68/1.90             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.68/1.90  thf(zf_stmt_1, axiom,
% 1.68/1.90    (![C:$i,B:$i,A:$i]:
% 1.68/1.90     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.68/1.90       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.68/1.90  thf('2', plain,
% 1.68/1.90      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.68/1.90         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 1.68/1.90          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 1.68/1.90          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 1.68/1.90      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.68/1.90  thf('3', plain,
% 1.68/1.90      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.68/1.90        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 1.68/1.90      inference('sup-', [status(thm)], ['1', '2'])).
% 1.68/1.90  thf('4', plain,
% 1.68/1.90      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.68/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.90  thf(redefinition_k1_relset_1, axiom,
% 1.68/1.90    (![A:$i,B:$i,C:$i]:
% 1.68/1.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.68/1.90       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.68/1.90  thf('5', plain,
% 1.68/1.90      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.68/1.90         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 1.68/1.90          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.68/1.90      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.68/1.90  thf('6', plain,
% 1.68/1.90      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.68/1.90      inference('sup-', [status(thm)], ['4', '5'])).
% 1.68/1.90  thf('7', plain,
% 1.68/1.90      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.68/1.90        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.68/1.90      inference('demod', [status(thm)], ['3', '6'])).
% 1.68/1.90  thf('8', plain,
% 1.68/1.90      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.68/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.90  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.68/1.90  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.68/1.90  thf(zf_stmt_4, axiom,
% 1.68/1.90    (![B:$i,A:$i]:
% 1.68/1.90     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.68/1.90       ( zip_tseitin_0 @ B @ A ) ))).
% 1.68/1.90  thf(zf_stmt_5, axiom,
% 1.68/1.90    (![A:$i,B:$i,C:$i]:
% 1.68/1.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.68/1.90       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.68/1.90         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.68/1.90           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.68/1.90             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.68/1.90  thf('9', plain,
% 1.68/1.90      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.68/1.90         (~ (zip_tseitin_0 @ X32 @ X33)
% 1.68/1.90          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 1.68/1.90          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 1.68/1.90      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.68/1.90  thf('10', plain,
% 1.68/1.90      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.68/1.90        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 1.68/1.90      inference('sup-', [status(thm)], ['8', '9'])).
% 1.68/1.90  thf('11', plain,
% 1.68/1.90      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.68/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.90  thf(redefinition_r2_relset_1, axiom,
% 1.68/1.90    (![A:$i,B:$i,C:$i,D:$i]:
% 1.68/1.90     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.68/1.90         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.68/1.90       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.68/1.90  thf('12', plain,
% 1.68/1.90      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.68/1.90         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 1.68/1.90          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 1.68/1.90          | (r2_relset_1 @ X24 @ X25 @ X23 @ X26)
% 1.68/1.90          | ((X23) != (X26)))),
% 1.68/1.90      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.68/1.90  thf('13', plain,
% 1.68/1.90      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.68/1.90         ((r2_relset_1 @ X24 @ X25 @ X26 @ X26)
% 1.68/1.90          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.68/1.90      inference('simplify', [status(thm)], ['12'])).
% 1.68/1.90  thf('14', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_C_1)),
% 1.68/1.90      inference('sup-', [status(thm)], ['11', '13'])).
% 1.68/1.90  thf('15', plain,
% 1.68/1.90      (![X27 : $i, X28 : $i]:
% 1.68/1.90         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 1.68/1.90      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.68/1.90  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.68/1.90  thf('16', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.68/1.90      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.68/1.90  thf('17', plain,
% 1.68/1.90      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.68/1.90      inference('sup+', [status(thm)], ['15', '16'])).
% 1.68/1.90  thf('18', plain,
% 1.68/1.90      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.68/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.90  thf(cc4_relset_1, axiom,
% 1.68/1.90    (![A:$i,B:$i]:
% 1.68/1.90     ( ( v1_xboole_0 @ A ) =>
% 1.68/1.90       ( ![C:$i]:
% 1.68/1.90         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 1.68/1.90           ( v1_xboole_0 @ C ) ) ) ))).
% 1.68/1.90  thf('19', plain,
% 1.68/1.90      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.68/1.90         (~ (v1_xboole_0 @ X17)
% 1.68/1.90          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X17)))
% 1.68/1.90          | (v1_xboole_0 @ X18))),
% 1.68/1.90      inference('cnf', [status(esa)], [cc4_relset_1])).
% 1.68/1.90  thf('20', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_B_1))),
% 1.68/1.90      inference('sup-', [status(thm)], ['18', '19'])).
% 1.68/1.90  thf('21', plain,
% 1.68/1.90      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_D))),
% 1.68/1.90      inference('sup-', [status(thm)], ['17', '20'])).
% 1.68/1.90  thf(t8_boole, axiom,
% 1.68/1.90    (![A:$i,B:$i]:
% 1.68/1.90     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 1.68/1.90  thf('22', plain,
% 1.68/1.90      (![X3 : $i, X4 : $i]:
% 1.68/1.90         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 1.68/1.90      inference('cnf', [status(esa)], [t8_boole])).
% 1.68/1.90  thf('23', plain,
% 1.68/1.90      (![X0 : $i, X1 : $i]:
% 1.68/1.90         ((zip_tseitin_0 @ sk_B_1 @ X1)
% 1.68/1.90          | ((sk_D) = (X0))
% 1.68/1.90          | ~ (v1_xboole_0 @ X0))),
% 1.68/1.90      inference('sup-', [status(thm)], ['21', '22'])).
% 1.68/1.90  thf('24', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)),
% 1.68/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.90  thf('25', plain,
% 1.68/1.90      (![X0 : $i, X1 : $i]:
% 1.68/1.90         (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ X0)
% 1.68/1.90          | ~ (v1_xboole_0 @ X0)
% 1.68/1.90          | (zip_tseitin_0 @ sk_B_1 @ X1))),
% 1.68/1.90      inference('sup-', [status(thm)], ['23', '24'])).
% 1.68/1.90  thf('26', plain,
% 1.68/1.90      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | ~ (v1_xboole_0 @ sk_C_1))),
% 1.68/1.90      inference('sup-', [status(thm)], ['14', '25'])).
% 1.68/1.90  thf('27', plain,
% 1.68/1.90      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.68/1.90      inference('sup+', [status(thm)], ['15', '16'])).
% 1.68/1.90  thf('28', plain,
% 1.68/1.90      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.68/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.90  thf('29', plain,
% 1.68/1.90      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.68/1.90         (~ (v1_xboole_0 @ X17)
% 1.68/1.90          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X17)))
% 1.68/1.90          | (v1_xboole_0 @ X18))),
% 1.68/1.90      inference('cnf', [status(esa)], [cc4_relset_1])).
% 1.68/1.90  thf('30', plain, (((v1_xboole_0 @ sk_C_1) | ~ (v1_xboole_0 @ sk_B_1))),
% 1.68/1.90      inference('sup-', [status(thm)], ['28', '29'])).
% 1.68/1.90  thf('31', plain,
% 1.68/1.90      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_C_1))),
% 1.68/1.90      inference('sup-', [status(thm)], ['27', '30'])).
% 1.68/1.90  thf('32', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 1.68/1.90      inference('clc', [status(thm)], ['26', '31'])).
% 1.68/1.90  thf('33', plain, ((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)),
% 1.68/1.90      inference('demod', [status(thm)], ['10', '32'])).
% 1.68/1.90  thf('34', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 1.68/1.90      inference('demod', [status(thm)], ['7', '33'])).
% 1.68/1.90  thf('35', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 1.68/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.90  thf('36', plain,
% 1.68/1.90      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.68/1.90         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 1.68/1.90          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 1.68/1.90          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 1.68/1.90      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.68/1.90  thf('37', plain,
% 1.68/1.90      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 1.68/1.90        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 1.68/1.90      inference('sup-', [status(thm)], ['35', '36'])).
% 1.68/1.90  thf('38', plain,
% 1.68/1.90      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.68/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.90  thf('39', plain,
% 1.68/1.90      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.68/1.90         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 1.68/1.90          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.68/1.90      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.68/1.90  thf('40', plain,
% 1.68/1.90      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 1.68/1.90      inference('sup-', [status(thm)], ['38', '39'])).
% 1.68/1.90  thf('41', plain,
% 1.68/1.90      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 1.68/1.90        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.68/1.90      inference('demod', [status(thm)], ['37', '40'])).
% 1.68/1.90  thf('42', plain,
% 1.68/1.90      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.68/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.90  thf('43', plain,
% 1.68/1.90      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.68/1.90         (~ (zip_tseitin_0 @ X32 @ X33)
% 1.68/1.90          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 1.68/1.90          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 1.68/1.90      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.68/1.90  thf('44', plain,
% 1.68/1.90      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 1.68/1.90        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 1.68/1.90      inference('sup-', [status(thm)], ['42', '43'])).
% 1.68/1.90  thf('45', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 1.68/1.90      inference('clc', [status(thm)], ['26', '31'])).
% 1.68/1.90  thf('46', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)),
% 1.68/1.90      inference('demod', [status(thm)], ['44', '45'])).
% 1.68/1.90  thf('47', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 1.68/1.90      inference('demod', [status(thm)], ['41', '46'])).
% 1.68/1.90  thf(t9_funct_1, axiom,
% 1.68/1.90    (![A:$i]:
% 1.68/1.90     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.68/1.90       ( ![B:$i]:
% 1.68/1.90         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.68/1.90           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 1.68/1.90               ( ![C:$i]:
% 1.68/1.90                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 1.68/1.90                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 1.68/1.90             ( ( A ) = ( B ) ) ) ) ) ))).
% 1.68/1.90  thf('48', plain,
% 1.68/1.90      (![X12 : $i, X13 : $i]:
% 1.68/1.90         (~ (v1_relat_1 @ X12)
% 1.68/1.90          | ~ (v1_funct_1 @ X12)
% 1.68/1.90          | ((X13) = (X12))
% 1.68/1.90          | (r2_hidden @ (sk_C @ X12 @ X13) @ (k1_relat_1 @ X13))
% 1.68/1.90          | ((k1_relat_1 @ X13) != (k1_relat_1 @ X12))
% 1.68/1.90          | ~ (v1_funct_1 @ X13)
% 1.68/1.90          | ~ (v1_relat_1 @ X13))),
% 1.68/1.90      inference('cnf', [status(esa)], [t9_funct_1])).
% 1.68/1.90  thf('49', plain,
% 1.68/1.90      (![X0 : $i]:
% 1.68/1.90         (((sk_A) != (k1_relat_1 @ X0))
% 1.68/1.90          | ~ (v1_relat_1 @ sk_C_1)
% 1.68/1.90          | ~ (v1_funct_1 @ sk_C_1)
% 1.68/1.90          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 1.68/1.90          | ((sk_C_1) = (X0))
% 1.68/1.90          | ~ (v1_funct_1 @ X0)
% 1.68/1.90          | ~ (v1_relat_1 @ X0))),
% 1.68/1.90      inference('sup-', [status(thm)], ['47', '48'])).
% 1.68/1.90  thf('50', plain,
% 1.68/1.90      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.68/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.90  thf(cc1_relset_1, axiom,
% 1.68/1.90    (![A:$i,B:$i,C:$i]:
% 1.68/1.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.68/1.90       ( v1_relat_1 @ C ) ))).
% 1.68/1.90  thf('51', plain,
% 1.68/1.90      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.68/1.90         ((v1_relat_1 @ X14)
% 1.68/1.90          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.68/1.90      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.68/1.90  thf('52', plain, ((v1_relat_1 @ sk_C_1)),
% 1.68/1.90      inference('sup-', [status(thm)], ['50', '51'])).
% 1.68/1.90  thf('53', plain, ((v1_funct_1 @ sk_C_1)),
% 1.68/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.90  thf('54', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 1.68/1.90      inference('demod', [status(thm)], ['41', '46'])).
% 1.68/1.90  thf('55', plain,
% 1.68/1.90      (![X0 : $i]:
% 1.68/1.90         (((sk_A) != (k1_relat_1 @ X0))
% 1.68/1.90          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_A)
% 1.68/1.90          | ((sk_C_1) = (X0))
% 1.68/1.90          | ~ (v1_funct_1 @ X0)
% 1.68/1.90          | ~ (v1_relat_1 @ X0))),
% 1.68/1.90      inference('demod', [status(thm)], ['49', '52', '53', '54'])).
% 1.68/1.90  thf('56', plain,
% 1.68/1.90      ((((sk_A) != (sk_A))
% 1.68/1.90        | ~ (v1_relat_1 @ sk_D)
% 1.68/1.90        | ~ (v1_funct_1 @ sk_D)
% 1.68/1.90        | ((sk_C_1) = (sk_D))
% 1.68/1.90        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 1.68/1.90      inference('sup-', [status(thm)], ['34', '55'])).
% 1.68/1.90  thf('57', plain,
% 1.68/1.90      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.68/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.90  thf('58', plain,
% 1.68/1.90      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.68/1.90         ((v1_relat_1 @ X14)
% 1.68/1.90          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.68/1.90      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.68/1.90  thf('59', plain, ((v1_relat_1 @ sk_D)),
% 1.68/1.90      inference('sup-', [status(thm)], ['57', '58'])).
% 1.68/1.90  thf('60', plain, ((v1_funct_1 @ sk_D)),
% 1.68/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.90  thf('61', plain,
% 1.68/1.90      ((((sk_A) != (sk_A))
% 1.68/1.90        | ((sk_C_1) = (sk_D))
% 1.68/1.90        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 1.68/1.90      inference('demod', [status(thm)], ['56', '59', '60'])).
% 1.68/1.90  thf('62', plain,
% 1.68/1.90      (((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A) | ((sk_C_1) = (sk_D)))),
% 1.68/1.90      inference('simplify', [status(thm)], ['61'])).
% 1.68/1.90  thf(d2_subset_1, axiom,
% 1.68/1.90    (![A:$i,B:$i]:
% 1.68/1.90     ( ( ( v1_xboole_0 @ A ) =>
% 1.68/1.90         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.68/1.90       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.68/1.90         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.68/1.90  thf('63', plain,
% 1.68/1.90      (![X5 : $i, X6 : $i]:
% 1.68/1.90         (~ (r2_hidden @ X5 @ X6)
% 1.68/1.90          | (m1_subset_1 @ X5 @ X6)
% 1.68/1.90          | (v1_xboole_0 @ X6))),
% 1.68/1.90      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.68/1.90  thf(d1_xboole_0, axiom,
% 1.68/1.90    (![A:$i]:
% 1.68/1.90     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.68/1.90  thf('64', plain,
% 1.68/1.90      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.68/1.90      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.68/1.90  thf('65', plain,
% 1.68/1.90      (![X5 : $i, X6 : $i]: ((m1_subset_1 @ X5 @ X6) | ~ (r2_hidden @ X5 @ X6))),
% 1.68/1.90      inference('clc', [status(thm)], ['63', '64'])).
% 1.68/1.90  thf('66', plain,
% 1.68/1.90      ((((sk_C_1) = (sk_D)) | (m1_subset_1 @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 1.68/1.90      inference('sup-', [status(thm)], ['62', '65'])).
% 1.68/1.90  thf('67', plain,
% 1.68/1.90      (![X35 : $i]:
% 1.68/1.90         (((k1_funct_1 @ sk_C_1 @ X35) = (k1_funct_1 @ sk_D @ X35))
% 1.68/1.90          | ~ (m1_subset_1 @ X35 @ sk_A))),
% 1.68/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.90  thf('68', plain,
% 1.68/1.90      ((((sk_C_1) = (sk_D))
% 1.68/1.90        | ((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 1.68/1.90            = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))))),
% 1.68/1.90      inference('sup-', [status(thm)], ['66', '67'])).
% 1.68/1.90  thf('69', plain,
% 1.68/1.90      (((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 1.68/1.90         = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))),
% 1.68/1.90      inference('condensation', [status(thm)], ['68'])).
% 1.68/1.90  thf('70', plain,
% 1.68/1.90      (![X12 : $i, X13 : $i]:
% 1.68/1.90         (~ (v1_relat_1 @ X12)
% 1.68/1.90          | ~ (v1_funct_1 @ X12)
% 1.68/1.90          | ((X13) = (X12))
% 1.68/1.90          | ((k1_funct_1 @ X13 @ (sk_C @ X12 @ X13))
% 1.68/1.90              != (k1_funct_1 @ X12 @ (sk_C @ X12 @ X13)))
% 1.68/1.90          | ((k1_relat_1 @ X13) != (k1_relat_1 @ X12))
% 1.68/1.90          | ~ (v1_funct_1 @ X13)
% 1.68/1.90          | ~ (v1_relat_1 @ X13))),
% 1.68/1.90      inference('cnf', [status(esa)], [t9_funct_1])).
% 1.68/1.90  thf('71', plain,
% 1.68/1.90      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 1.68/1.90          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 1.68/1.90        | ~ (v1_relat_1 @ sk_C_1)
% 1.68/1.90        | ~ (v1_funct_1 @ sk_C_1)
% 1.68/1.90        | ((k1_relat_1 @ sk_C_1) != (k1_relat_1 @ sk_D))
% 1.68/1.90        | ((sk_C_1) = (sk_D))
% 1.68/1.90        | ~ (v1_funct_1 @ sk_D)
% 1.68/1.90        | ~ (v1_relat_1 @ sk_D))),
% 1.68/1.90      inference('sup-', [status(thm)], ['69', '70'])).
% 1.68/1.90  thf('72', plain, ((v1_relat_1 @ sk_C_1)),
% 1.68/1.90      inference('sup-', [status(thm)], ['50', '51'])).
% 1.68/1.90  thf('73', plain, ((v1_funct_1 @ sk_C_1)),
% 1.68/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.90  thf('74', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 1.68/1.90      inference('demod', [status(thm)], ['41', '46'])).
% 1.68/1.90  thf('75', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 1.68/1.90      inference('demod', [status(thm)], ['7', '33'])).
% 1.68/1.90  thf('76', plain, ((v1_funct_1 @ sk_D)),
% 1.68/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.90  thf('77', plain, ((v1_relat_1 @ sk_D)),
% 1.68/1.90      inference('sup-', [status(thm)], ['57', '58'])).
% 1.68/1.90  thf('78', plain,
% 1.68/1.90      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 1.68/1.90          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 1.68/1.90        | ((sk_A) != (sk_A))
% 1.68/1.90        | ((sk_C_1) = (sk_D)))),
% 1.68/1.90      inference('demod', [status(thm)],
% 1.68/1.90                ['71', '72', '73', '74', '75', '76', '77'])).
% 1.68/1.90  thf('79', plain, (((sk_C_1) = (sk_D))),
% 1.68/1.90      inference('simplify', [status(thm)], ['78'])).
% 1.68/1.90  thf('80', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_C_1)),
% 1.68/1.90      inference('sup-', [status(thm)], ['11', '13'])).
% 1.68/1.90  thf('81', plain, ($false),
% 1.68/1.90      inference('demod', [status(thm)], ['0', '79', '80'])).
% 1.68/1.90  
% 1.68/1.90  % SZS output end Refutation
% 1.68/1.90  
% 1.68/1.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
