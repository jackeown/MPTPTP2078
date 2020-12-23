%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uLLl3ezsQM

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:35 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 392 expanded)
%              Number of leaves         :   34 ( 131 expanded)
%              Depth                    :   21
%              Number of atoms          :  861 (5921 expanded)
%              Number of equality atoms :   64 ( 241 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( r2_relset_1 @ X14 @ X15 @ X13 @ X16 )
      | ( X13 != X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('13',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_relset_1 @ X14 @ X15 @ X16 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X7 ) ) )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X1 )
      | ( sk_D = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ sk_B @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ~ ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['14','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('28',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X7 ) ) )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('30',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference(clc,[status(thm)],['26','31'])).

thf('33',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['10','32'])).

thf('34',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','33'])).

thf('35',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('37',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('40',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('44',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference(clc,[status(thm)],['26','31'])).

thf('46',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ),
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
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( X3 = X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ X3 ) @ ( k1_relat_1 @ X3 ) )
      | ( ( k1_relat_1 @ X3 )
       != ( k1_relat_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
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
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('51',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
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

thf('63',plain,(
    ! [X25: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ X25 )
        = ( k1_funct_1 @ sk_D @ X25 ) )
      | ~ ( r2_hidden @ X25 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( sk_C_1 = sk_D )
    | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ),
    inference(condensation,[status(thm)],['64'])).

thf('66',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( X3 = X2 )
      | ( ( k1_funct_1 @ X3 @ ( sk_C @ X2 @ X3 ) )
       != ( k1_funct_1 @ X2 @ ( sk_C @ X2 @ X3 ) ) )
      | ( ( k1_relat_1 @ X3 )
       != ( k1_relat_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('67',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_1 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['50','51'])).

thf('69',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['41','46'])).

thf('71',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','33'])).

thf('72',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['57','58'])).

thf('74',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(demod,[status(thm)],['67','68','69','70','71','72','73'])).

thf('75',plain,(
    sk_C_1 = sk_D ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['11','13'])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['0','75','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uLLl3ezsQM
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:19:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.41/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.62  % Solved by: fo/fo7.sh
% 0.41/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.62  % done 162 iterations in 0.166s
% 0.41/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.62  % SZS output start Refutation
% 0.41/0.62  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.41/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.41/0.62  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.41/0.62  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.41/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.41/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.41/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.41/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.62  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.41/0.62  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.41/0.62  thf(sk_D_type, type, sk_D: $i).
% 0.41/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.62  thf(t18_funct_2, conjecture,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.41/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.62       ( ![D:$i]:
% 0.41/0.62         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.41/0.62             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.62           ( ( ![E:$i]:
% 0.41/0.62               ( ( r2_hidden @ E @ A ) =>
% 0.41/0.62                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 0.41/0.62             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 0.41/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.62    (~( ![A:$i,B:$i,C:$i]:
% 0.41/0.62        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.41/0.62            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.62          ( ![D:$i]:
% 0.41/0.62            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.41/0.62                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.62              ( ( ![E:$i]:
% 0.41/0.62                  ( ( r2_hidden @ E @ A ) =>
% 0.41/0.62                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 0.41/0.62                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 0.41/0.62    inference('cnf.neg', [status(esa)], [t18_funct_2])).
% 0.41/0.62  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(d1_funct_2, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.62       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.41/0.62           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.41/0.62             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.41/0.62         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.41/0.62           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.41/0.62             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.41/0.62  thf(zf_stmt_1, axiom,
% 0.41/0.62    (![C:$i,B:$i,A:$i]:
% 0.41/0.62     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.41/0.62       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.41/0.62  thf('2', plain,
% 0.41/0.62      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.41/0.62         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 0.41/0.62          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 0.41/0.62          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.41/0.62  thf('3', plain,
% 0.41/0.62      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.41/0.62        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.41/0.62  thf('4', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(redefinition_k1_relset_1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.62       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.41/0.62  thf('5', plain,
% 0.41/0.62      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.41/0.62         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 0.41/0.62          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.41/0.62      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.41/0.62  thf('6', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.41/0.62      inference('sup-', [status(thm)], ['4', '5'])).
% 0.41/0.62  thf('7', plain,
% 0.41/0.62      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.41/0.62      inference('demod', [status(thm)], ['3', '6'])).
% 0.41/0.62  thf('8', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.41/0.62  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.41/0.62  thf(zf_stmt_4, axiom,
% 0.41/0.62    (![B:$i,A:$i]:
% 0.41/0.62     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.41/0.62       ( zip_tseitin_0 @ B @ A ) ))).
% 0.41/0.62  thf(zf_stmt_5, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.62       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.41/0.62         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.41/0.62           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.41/0.62             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.41/0.62  thf('9', plain,
% 0.41/0.62      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.41/0.62         (~ (zip_tseitin_0 @ X22 @ X23)
% 0.41/0.62          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 0.41/0.62          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.41/0.62  thf('10', plain,
% 0.41/0.62      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.41/0.62      inference('sup-', [status(thm)], ['8', '9'])).
% 0.41/0.62  thf('11', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(redefinition_r2_relset_1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.62     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.41/0.62         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.62       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.41/0.62  thf('12', plain,
% 0.41/0.62      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.41/0.62         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.41/0.62          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.41/0.62          | (r2_relset_1 @ X14 @ X15 @ X13 @ X16)
% 0.41/0.62          | ((X13) != (X16)))),
% 0.41/0.62      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.41/0.62  thf('13', plain,
% 0.41/0.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.41/0.62         ((r2_relset_1 @ X14 @ X15 @ X16 @ X16)
% 0.41/0.62          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.41/0.62      inference('simplify', [status(thm)], ['12'])).
% 0.41/0.62  thf('14', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1)),
% 0.41/0.62      inference('sup-', [status(thm)], ['11', '13'])).
% 0.41/0.62  thf('15', plain,
% 0.41/0.62      (![X17 : $i, X18 : $i]:
% 0.41/0.62         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.41/0.62  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.41/0.62  thf('16', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.63      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.41/0.63  thf('17', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.41/0.63      inference('sup+', [status(thm)], ['15', '16'])).
% 0.41/0.63  thf('18', plain,
% 0.41/0.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf(cc4_relset_1, axiom,
% 0.41/0.63    (![A:$i,B:$i]:
% 0.41/0.63     ( ( v1_xboole_0 @ A ) =>
% 0.41/0.63       ( ![C:$i]:
% 0.41/0.63         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.41/0.63           ( v1_xboole_0 @ C ) ) ) ))).
% 0.41/0.63  thf('19', plain,
% 0.41/0.63      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.41/0.63         (~ (v1_xboole_0 @ X7)
% 0.41/0.63          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X7)))
% 0.41/0.63          | (v1_xboole_0 @ X8))),
% 0.41/0.63      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.41/0.63  thf('20', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_B))),
% 0.41/0.63      inference('sup-', [status(thm)], ['18', '19'])).
% 0.41/0.63  thf('21', plain,
% 0.41/0.63      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | (v1_xboole_0 @ sk_D))),
% 0.41/0.63      inference('sup-', [status(thm)], ['17', '20'])).
% 0.41/0.63  thf(t8_boole, axiom,
% 0.41/0.63    (![A:$i,B:$i]:
% 0.41/0.63     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.41/0.63  thf('22', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i]:
% 0.41/0.63         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 0.41/0.63      inference('cnf', [status(esa)], [t8_boole])).
% 0.41/0.63  thf('23', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i]:
% 0.41/0.63         ((zip_tseitin_0 @ sk_B @ X1) | ((sk_D) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.63      inference('sup-', [status(thm)], ['21', '22'])).
% 0.41/0.63  thf('24', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('25', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i]:
% 0.41/0.63         (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0)
% 0.41/0.63          | ~ (v1_xboole_0 @ X0)
% 0.41/0.63          | (zip_tseitin_0 @ sk_B @ X1))),
% 0.41/0.63      inference('sup-', [status(thm)], ['23', '24'])).
% 0.41/0.63  thf('26', plain,
% 0.41/0.63      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | ~ (v1_xboole_0 @ sk_C_1))),
% 0.41/0.63      inference('sup-', [status(thm)], ['14', '25'])).
% 0.41/0.63  thf('27', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.41/0.63      inference('sup+', [status(thm)], ['15', '16'])).
% 0.41/0.63  thf('28', plain,
% 0.41/0.63      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('29', plain,
% 0.41/0.63      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.41/0.63         (~ (v1_xboole_0 @ X7)
% 0.41/0.63          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X7)))
% 0.41/0.63          | (v1_xboole_0 @ X8))),
% 0.41/0.63      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.41/0.63  thf('30', plain, (((v1_xboole_0 @ sk_C_1) | ~ (v1_xboole_0 @ sk_B))),
% 0.41/0.63      inference('sup-', [status(thm)], ['28', '29'])).
% 0.41/0.63  thf('31', plain,
% 0.41/0.63      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | (v1_xboole_0 @ sk_C_1))),
% 0.41/0.63      inference('sup-', [status(thm)], ['27', '30'])).
% 0.41/0.63  thf('32', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 0.41/0.63      inference('clc', [status(thm)], ['26', '31'])).
% 0.41/0.63  thf('33', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 0.41/0.63      inference('demod', [status(thm)], ['10', '32'])).
% 0.41/0.63  thf('34', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.41/0.63      inference('demod', [status(thm)], ['7', '33'])).
% 0.41/0.63  thf('35', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('36', plain,
% 0.41/0.63      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.41/0.63         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 0.41/0.63          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 0.41/0.63          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.41/0.63  thf('37', plain,
% 0.41/0.63      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 0.41/0.63        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['35', '36'])).
% 0.41/0.63  thf('38', plain,
% 0.41/0.63      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('39', plain,
% 0.41/0.63      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.41/0.63         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 0.41/0.63          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.41/0.63      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.41/0.63  thf('40', plain,
% 0.41/0.63      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.41/0.63      inference('sup-', [status(thm)], ['38', '39'])).
% 0.41/0.63  thf('41', plain,
% 0.41/0.63      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 0.41/0.63        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 0.41/0.63      inference('demod', [status(thm)], ['37', '40'])).
% 0.41/0.63  thf('42', plain,
% 0.41/0.63      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('43', plain,
% 0.41/0.63      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.41/0.63         (~ (zip_tseitin_0 @ X22 @ X23)
% 0.41/0.63          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 0.41/0.63          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.41/0.63  thf('44', plain,
% 0.41/0.63      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 0.41/0.63        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.41/0.63      inference('sup-', [status(thm)], ['42', '43'])).
% 0.41/0.63  thf('45', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 0.41/0.63      inference('clc', [status(thm)], ['26', '31'])).
% 0.41/0.63  thf('46', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)),
% 0.41/0.63      inference('demod', [status(thm)], ['44', '45'])).
% 0.41/0.63  thf('47', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.41/0.63      inference('demod', [status(thm)], ['41', '46'])).
% 0.41/0.63  thf(t9_funct_1, axiom,
% 0.41/0.63    (![A:$i]:
% 0.41/0.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.41/0.63       ( ![B:$i]:
% 0.41/0.63         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.41/0.63           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.41/0.63               ( ![C:$i]:
% 0.41/0.63                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 0.41/0.63                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 0.41/0.63             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.41/0.63  thf('48', plain,
% 0.41/0.63      (![X2 : $i, X3 : $i]:
% 0.41/0.63         (~ (v1_relat_1 @ X2)
% 0.41/0.63          | ~ (v1_funct_1 @ X2)
% 0.41/0.63          | ((X3) = (X2))
% 0.41/0.63          | (r2_hidden @ (sk_C @ X2 @ X3) @ (k1_relat_1 @ X3))
% 0.41/0.63          | ((k1_relat_1 @ X3) != (k1_relat_1 @ X2))
% 0.41/0.63          | ~ (v1_funct_1 @ X3)
% 0.41/0.63          | ~ (v1_relat_1 @ X3))),
% 0.41/0.63      inference('cnf', [status(esa)], [t9_funct_1])).
% 0.41/0.63  thf('49', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         (((sk_A) != (k1_relat_1 @ X0))
% 0.41/0.63          | ~ (v1_relat_1 @ sk_C_1)
% 0.41/0.63          | ~ (v1_funct_1 @ sk_C_1)
% 0.41/0.63          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 0.41/0.63          | ((sk_C_1) = (X0))
% 0.41/0.63          | ~ (v1_funct_1 @ X0)
% 0.41/0.63          | ~ (v1_relat_1 @ X0))),
% 0.41/0.63      inference('sup-', [status(thm)], ['47', '48'])).
% 0.41/0.63  thf('50', plain,
% 0.41/0.63      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf(cc1_relset_1, axiom,
% 0.41/0.63    (![A:$i,B:$i,C:$i]:
% 0.41/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.63       ( v1_relat_1 @ C ) ))).
% 0.41/0.63  thf('51', plain,
% 0.41/0.63      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.41/0.63         ((v1_relat_1 @ X4)
% 0.41/0.63          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.41/0.63      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.41/0.63  thf('52', plain, ((v1_relat_1 @ sk_C_1)),
% 0.41/0.63      inference('sup-', [status(thm)], ['50', '51'])).
% 0.41/0.63  thf('53', plain, ((v1_funct_1 @ sk_C_1)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('54', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.41/0.63      inference('demod', [status(thm)], ['41', '46'])).
% 0.41/0.63  thf('55', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         (((sk_A) != (k1_relat_1 @ X0))
% 0.41/0.63          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_A)
% 0.41/0.63          | ((sk_C_1) = (X0))
% 0.41/0.63          | ~ (v1_funct_1 @ X0)
% 0.41/0.63          | ~ (v1_relat_1 @ X0))),
% 0.41/0.63      inference('demod', [status(thm)], ['49', '52', '53', '54'])).
% 0.41/0.63  thf('56', plain,
% 0.41/0.63      ((((sk_A) != (sk_A))
% 0.41/0.63        | ~ (v1_relat_1 @ sk_D)
% 0.41/0.63        | ~ (v1_funct_1 @ sk_D)
% 0.41/0.63        | ((sk_C_1) = (sk_D))
% 0.41/0.63        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 0.41/0.63      inference('sup-', [status(thm)], ['34', '55'])).
% 0.41/0.63  thf('57', plain,
% 0.41/0.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('58', plain,
% 0.41/0.63      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.41/0.63         ((v1_relat_1 @ X4)
% 0.41/0.63          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.41/0.63      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.41/0.63  thf('59', plain, ((v1_relat_1 @ sk_D)),
% 0.41/0.63      inference('sup-', [status(thm)], ['57', '58'])).
% 0.41/0.63  thf('60', plain, ((v1_funct_1 @ sk_D)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('61', plain,
% 0.41/0.63      ((((sk_A) != (sk_A))
% 0.41/0.63        | ((sk_C_1) = (sk_D))
% 0.41/0.63        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 0.41/0.63      inference('demod', [status(thm)], ['56', '59', '60'])).
% 0.41/0.63  thf('62', plain,
% 0.41/0.63      (((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A) | ((sk_C_1) = (sk_D)))),
% 0.41/0.63      inference('simplify', [status(thm)], ['61'])).
% 0.41/0.63  thf('63', plain,
% 0.41/0.63      (![X25 : $i]:
% 0.41/0.63         (((k1_funct_1 @ sk_C_1 @ X25) = (k1_funct_1 @ sk_D @ X25))
% 0.41/0.63          | ~ (r2_hidden @ X25 @ sk_A))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('64', plain,
% 0.41/0.63      ((((sk_C_1) = (sk_D))
% 0.41/0.63        | ((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 0.41/0.63            = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))))),
% 0.41/0.63      inference('sup-', [status(thm)], ['62', '63'])).
% 0.41/0.63  thf('65', plain,
% 0.41/0.63      (((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 0.41/0.63         = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))),
% 0.41/0.63      inference('condensation', [status(thm)], ['64'])).
% 0.41/0.63  thf('66', plain,
% 0.41/0.63      (![X2 : $i, X3 : $i]:
% 0.41/0.63         (~ (v1_relat_1 @ X2)
% 0.41/0.63          | ~ (v1_funct_1 @ X2)
% 0.41/0.63          | ((X3) = (X2))
% 0.41/0.63          | ((k1_funct_1 @ X3 @ (sk_C @ X2 @ X3))
% 0.41/0.63              != (k1_funct_1 @ X2 @ (sk_C @ X2 @ X3)))
% 0.41/0.63          | ((k1_relat_1 @ X3) != (k1_relat_1 @ X2))
% 0.41/0.63          | ~ (v1_funct_1 @ X3)
% 0.41/0.63          | ~ (v1_relat_1 @ X3))),
% 0.41/0.63      inference('cnf', [status(esa)], [t9_funct_1])).
% 0.41/0.63  thf('67', plain,
% 0.41/0.63      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 0.41/0.63          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 0.41/0.63        | ~ (v1_relat_1 @ sk_C_1)
% 0.41/0.63        | ~ (v1_funct_1 @ sk_C_1)
% 0.41/0.63        | ((k1_relat_1 @ sk_C_1) != (k1_relat_1 @ sk_D))
% 0.41/0.63        | ((sk_C_1) = (sk_D))
% 0.41/0.63        | ~ (v1_funct_1 @ sk_D)
% 0.41/0.63        | ~ (v1_relat_1 @ sk_D))),
% 0.41/0.63      inference('sup-', [status(thm)], ['65', '66'])).
% 0.41/0.63  thf('68', plain, ((v1_relat_1 @ sk_C_1)),
% 0.41/0.63      inference('sup-', [status(thm)], ['50', '51'])).
% 0.41/0.63  thf('69', plain, ((v1_funct_1 @ sk_C_1)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('70', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.41/0.63      inference('demod', [status(thm)], ['41', '46'])).
% 0.41/0.63  thf('71', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.41/0.63      inference('demod', [status(thm)], ['7', '33'])).
% 0.41/0.63  thf('72', plain, ((v1_funct_1 @ sk_D)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('73', plain, ((v1_relat_1 @ sk_D)),
% 0.41/0.63      inference('sup-', [status(thm)], ['57', '58'])).
% 0.41/0.63  thf('74', plain,
% 0.41/0.63      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 0.41/0.63          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 0.41/0.63        | ((sk_A) != (sk_A))
% 0.41/0.63        | ((sk_C_1) = (sk_D)))),
% 0.41/0.63      inference('demod', [status(thm)],
% 0.41/0.63                ['67', '68', '69', '70', '71', '72', '73'])).
% 0.41/0.63  thf('75', plain, (((sk_C_1) = (sk_D))),
% 0.41/0.63      inference('simplify', [status(thm)], ['74'])).
% 0.41/0.63  thf('76', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1)),
% 0.41/0.63      inference('sup-', [status(thm)], ['11', '13'])).
% 0.41/0.63  thf('77', plain, ($false),
% 0.41/0.63      inference('demod', [status(thm)], ['0', '75', '76'])).
% 0.41/0.63  
% 0.41/0.63  % SZS output end Refutation
% 0.41/0.63  
% 0.47/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
