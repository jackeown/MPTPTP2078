%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.v1JvUKpyCD

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:35 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 392 expanded)
%              Number of leaves         :   34 ( 131 expanded)
%              Depth                    :   21
%              Number of atoms          :  872 (5885 expanded)
%              Number of equality atoms :   62 ( 229 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

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
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ( X26
        = ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('12',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( r2_relset_1 @ X20 @ X21 @ X22 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['12'])).

thf('14',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
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
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('19',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X14 ) ) )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_C_2 ) ) ),
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
      | ( sk_C_2 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_B @ X0 @ sk_D )
      | ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ sk_B @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ~ ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['14','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X14 ) ) )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('30',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
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
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ( X26
        = ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('37',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('40',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('44',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference(clc,[status(thm)],['26','31'])).

thf('46',plain,(
    zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
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
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( X10 = X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X10 ) @ ( k1_relat_1 @ X10 ) )
      | ( ( k1_relat_1 @ X10 )
       != ( k1_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('51',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('52',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['41','46'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ sk_A )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['49','52','53','54'])).

thf('56',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['34','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('59',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['56','59','60'])).

thf('62',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D @ sk_C_2 ) @ sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X34: $i] :
      ( ( ( k1_funct_1 @ sk_C_2 @ X34 )
        = ( k1_funct_1 @ sk_D @ X34 ) )
      | ~ ( r2_hidden @ X34 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( sk_C_2 = sk_D )
    | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C @ sk_D @ sk_C_2 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( sk_C @ sk_D @ sk_C_2 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_2 ) ) ),
    inference(condensation,[status(thm)],['64'])).

thf('66',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( X10 = X9 )
      | ( ( k1_funct_1 @ X10 @ ( sk_C @ X9 @ X10 ) )
       != ( k1_funct_1 @ X9 @ ( sk_C @ X9 @ X10 ) ) )
      | ( ( k1_relat_1 @ X10 )
       != ( k1_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('67',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C @ sk_D @ sk_C_2 ) ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_2 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['50','51'])).

thf('69',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
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
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C @ sk_D @ sk_C_2 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(demod,[status(thm)],['67','68','69','70','71','72','73'])).

thf('75',plain,(
    sk_C_2 = sk_D ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['12'])).

thf('78',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_C_2 ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    $false ),
    inference(demod,[status(thm)],['0','75','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.v1JvUKpyCD
% 0.13/0.36  % Computer   : n015.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 11:26:53 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 1.60/1.80  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.60/1.80  % Solved by: fo/fo7.sh
% 1.60/1.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.60/1.80  % done 2115 iterations in 1.326s
% 1.60/1.80  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.60/1.80  % SZS output start Refutation
% 1.60/1.80  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.60/1.80  thf(sk_D_type, type, sk_D: $i).
% 1.60/1.80  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.60/1.80  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.60/1.80  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.60/1.80  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.60/1.80  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.60/1.80  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.60/1.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.60/1.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.60/1.80  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.60/1.80  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.60/1.80  thf(sk_A_type, type, sk_A: $i).
% 1.60/1.80  thf(sk_B_type, type, sk_B: $i).
% 1.60/1.80  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.60/1.80  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.60/1.80  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.60/1.80  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.60/1.80  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.60/1.80  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.60/1.80  thf(t18_funct_2, conjecture,
% 1.60/1.80    (![A:$i,B:$i,C:$i]:
% 1.60/1.80     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.60/1.80         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.60/1.80       ( ![D:$i]:
% 1.60/1.80         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.60/1.80             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.60/1.80           ( ( ![E:$i]:
% 1.60/1.80               ( ( r2_hidden @ E @ A ) =>
% 1.60/1.80                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 1.60/1.80             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 1.60/1.80  thf(zf_stmt_0, negated_conjecture,
% 1.60/1.80    (~( ![A:$i,B:$i,C:$i]:
% 1.60/1.80        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.60/1.80            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.60/1.80          ( ![D:$i]:
% 1.60/1.80            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.60/1.80                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.60/1.80              ( ( ![E:$i]:
% 1.60/1.80                  ( ( r2_hidden @ E @ A ) =>
% 1.60/1.80                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 1.60/1.80                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 1.60/1.80    inference('cnf.neg', [status(esa)], [t18_funct_2])).
% 1.60/1.80  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D)),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf(d1_funct_2, axiom,
% 1.60/1.80    (![A:$i,B:$i,C:$i]:
% 1.60/1.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.60/1.80       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.60/1.80           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.60/1.80             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.60/1.80         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.60/1.80           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.60/1.80             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.60/1.80  thf(zf_stmt_1, axiom,
% 1.60/1.80    (![C:$i,B:$i,A:$i]:
% 1.60/1.80     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.60/1.80       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.60/1.80  thf('2', plain,
% 1.60/1.80      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.60/1.80         (~ (v1_funct_2 @ X28 @ X26 @ X27)
% 1.60/1.80          | ((X26) = (k1_relset_1 @ X26 @ X27 @ X28))
% 1.60/1.80          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.60/1.80  thf('3', plain,
% 1.60/1.80      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 1.60/1.80        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 1.60/1.80      inference('sup-', [status(thm)], ['1', '2'])).
% 1.60/1.80  thf('4', plain,
% 1.60/1.80      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf(redefinition_k1_relset_1, axiom,
% 1.60/1.80    (![A:$i,B:$i,C:$i]:
% 1.60/1.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.60/1.80       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.60/1.80  thf('5', plain,
% 1.60/1.80      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.60/1.80         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 1.60/1.80          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.60/1.80      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.60/1.80  thf('6', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.60/1.80      inference('sup-', [status(thm)], ['4', '5'])).
% 1.60/1.80  thf('7', plain,
% 1.60/1.80      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.60/1.80      inference('demod', [status(thm)], ['3', '6'])).
% 1.60/1.80  thf('8', plain,
% 1.60/1.80      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.60/1.80  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.60/1.80  thf(zf_stmt_4, axiom,
% 1.60/1.80    (![B:$i,A:$i]:
% 1.60/1.80     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.60/1.80       ( zip_tseitin_0 @ B @ A ) ))).
% 1.60/1.80  thf(zf_stmt_5, axiom,
% 1.60/1.80    (![A:$i,B:$i,C:$i]:
% 1.60/1.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.60/1.80       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.60/1.80         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.60/1.80           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.60/1.80             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.60/1.80  thf('9', plain,
% 1.60/1.80      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.60/1.80         (~ (zip_tseitin_0 @ X29 @ X30)
% 1.60/1.80          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 1.60/1.80          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.60/1.80  thf('10', plain,
% 1.60/1.80      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.60/1.80      inference('sup-', [status(thm)], ['8', '9'])).
% 1.60/1.80  thf('11', plain,
% 1.60/1.80      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf(reflexivity_r2_relset_1, axiom,
% 1.60/1.80    (![A:$i,B:$i,C:$i,D:$i]:
% 1.60/1.80     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.60/1.80         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.60/1.80       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 1.60/1.80  thf('12', plain,
% 1.60/1.80      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 1.60/1.80         ((r2_relset_1 @ X20 @ X21 @ X22 @ X22)
% 1.60/1.80          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.60/1.80          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 1.60/1.80      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 1.60/1.80  thf('13', plain,
% 1.60/1.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.60/1.80         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 1.60/1.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 1.60/1.80      inference('condensation', [status(thm)], ['12'])).
% 1.60/1.80  thf('14', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D)),
% 1.60/1.80      inference('sup-', [status(thm)], ['11', '13'])).
% 1.60/1.80  thf('15', plain,
% 1.60/1.80      (![X24 : $i, X25 : $i]:
% 1.60/1.80         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.60/1.80  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.60/1.80  thf('16', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.60/1.80      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.60/1.80  thf('17', plain,
% 1.60/1.80      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.60/1.80      inference('sup+', [status(thm)], ['15', '16'])).
% 1.60/1.80  thf('18', plain,
% 1.60/1.80      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf(cc4_relset_1, axiom,
% 1.60/1.80    (![A:$i,B:$i]:
% 1.60/1.80     ( ( v1_xboole_0 @ A ) =>
% 1.60/1.80       ( ![C:$i]:
% 1.60/1.80         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 1.60/1.80           ( v1_xboole_0 @ C ) ) ) ))).
% 1.60/1.80  thf('19', plain,
% 1.60/1.80      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.60/1.80         (~ (v1_xboole_0 @ X14)
% 1.60/1.80          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X14)))
% 1.60/1.80          | (v1_xboole_0 @ X15))),
% 1.60/1.80      inference('cnf', [status(esa)], [cc4_relset_1])).
% 1.60/1.80  thf('20', plain, (((v1_xboole_0 @ sk_C_2) | ~ (v1_xboole_0 @ sk_B))),
% 1.60/1.80      inference('sup-', [status(thm)], ['18', '19'])).
% 1.60/1.80  thf('21', plain,
% 1.60/1.80      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | (v1_xboole_0 @ sk_C_2))),
% 1.60/1.80      inference('sup-', [status(thm)], ['17', '20'])).
% 1.60/1.80  thf(t8_boole, axiom,
% 1.60/1.80    (![A:$i,B:$i]:
% 1.60/1.80     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 1.60/1.80  thf('22', plain,
% 1.60/1.80      (![X0 : $i, X1 : $i]:
% 1.60/1.80         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 1.60/1.80      inference('cnf', [status(esa)], [t8_boole])).
% 1.60/1.80  thf('23', plain,
% 1.60/1.80      (![X0 : $i, X1 : $i]:
% 1.60/1.80         ((zip_tseitin_0 @ sk_B @ X1)
% 1.60/1.80          | ((sk_C_2) = (X0))
% 1.60/1.80          | ~ (v1_xboole_0 @ X0))),
% 1.60/1.80      inference('sup-', [status(thm)], ['21', '22'])).
% 1.60/1.80  thf('24', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D)),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf('25', plain,
% 1.60/1.80      (![X0 : $i, X1 : $i]:
% 1.60/1.80         (~ (r2_relset_1 @ sk_A @ sk_B @ X0 @ sk_D)
% 1.60/1.80          | ~ (v1_xboole_0 @ X0)
% 1.60/1.80          | (zip_tseitin_0 @ sk_B @ X1))),
% 1.60/1.80      inference('sup-', [status(thm)], ['23', '24'])).
% 1.60/1.80  thf('26', plain,
% 1.60/1.80      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | ~ (v1_xboole_0 @ sk_D))),
% 1.60/1.80      inference('sup-', [status(thm)], ['14', '25'])).
% 1.60/1.80  thf('27', plain,
% 1.60/1.80      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.60/1.80      inference('sup+', [status(thm)], ['15', '16'])).
% 1.60/1.80  thf('28', plain,
% 1.60/1.80      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf('29', plain,
% 1.60/1.80      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.60/1.80         (~ (v1_xboole_0 @ X14)
% 1.60/1.80          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X14)))
% 1.60/1.80          | (v1_xboole_0 @ X15))),
% 1.60/1.80      inference('cnf', [status(esa)], [cc4_relset_1])).
% 1.60/1.80  thf('30', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_B))),
% 1.60/1.80      inference('sup-', [status(thm)], ['28', '29'])).
% 1.60/1.80  thf('31', plain,
% 1.60/1.80      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | (v1_xboole_0 @ sk_D))),
% 1.60/1.80      inference('sup-', [status(thm)], ['27', '30'])).
% 1.60/1.80  thf('32', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 1.60/1.80      inference('clc', [status(thm)], ['26', '31'])).
% 1.60/1.80  thf('33', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 1.60/1.80      inference('demod', [status(thm)], ['10', '32'])).
% 1.60/1.80  thf('34', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 1.60/1.80      inference('demod', [status(thm)], ['7', '33'])).
% 1.60/1.80  thf('35', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf('36', plain,
% 1.60/1.80      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.60/1.80         (~ (v1_funct_2 @ X28 @ X26 @ X27)
% 1.60/1.80          | ((X26) = (k1_relset_1 @ X26 @ X27 @ X28))
% 1.60/1.80          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.60/1.80  thf('37', plain,
% 1.60/1.80      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 1.60/1.80        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 1.60/1.80      inference('sup-', [status(thm)], ['35', '36'])).
% 1.60/1.80  thf('38', plain,
% 1.60/1.80      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf('39', plain,
% 1.60/1.80      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.60/1.80         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 1.60/1.80          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.60/1.80      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.60/1.80  thf('40', plain,
% 1.60/1.80      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 1.60/1.80      inference('sup-', [status(thm)], ['38', '39'])).
% 1.60/1.80  thf('41', plain,
% 1.60/1.80      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 1.60/1.80        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 1.60/1.80      inference('demod', [status(thm)], ['37', '40'])).
% 1.60/1.80  thf('42', plain,
% 1.60/1.80      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf('43', plain,
% 1.60/1.80      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.60/1.80         (~ (zip_tseitin_0 @ X29 @ X30)
% 1.60/1.80          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 1.60/1.80          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.60/1.80  thf('44', plain,
% 1.60/1.80      (((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 1.60/1.80        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.60/1.80      inference('sup-', [status(thm)], ['42', '43'])).
% 1.60/1.80  thf('45', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 1.60/1.80      inference('clc', [status(thm)], ['26', '31'])).
% 1.60/1.80  thf('46', plain, ((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)),
% 1.60/1.80      inference('demod', [status(thm)], ['44', '45'])).
% 1.60/1.80  thf('47', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 1.60/1.80      inference('demod', [status(thm)], ['41', '46'])).
% 1.60/1.80  thf(t9_funct_1, axiom,
% 1.60/1.80    (![A:$i]:
% 1.60/1.80     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.60/1.80       ( ![B:$i]:
% 1.60/1.80         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.60/1.80           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 1.60/1.80               ( ![C:$i]:
% 1.60/1.80                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 1.60/1.80                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 1.60/1.80             ( ( A ) = ( B ) ) ) ) ) ))).
% 1.60/1.80  thf('48', plain,
% 1.60/1.80      (![X9 : $i, X10 : $i]:
% 1.60/1.80         (~ (v1_relat_1 @ X9)
% 1.60/1.80          | ~ (v1_funct_1 @ X9)
% 1.60/1.80          | ((X10) = (X9))
% 1.60/1.80          | (r2_hidden @ (sk_C @ X9 @ X10) @ (k1_relat_1 @ X10))
% 1.60/1.80          | ((k1_relat_1 @ X10) != (k1_relat_1 @ X9))
% 1.60/1.80          | ~ (v1_funct_1 @ X10)
% 1.60/1.80          | ~ (v1_relat_1 @ X10))),
% 1.60/1.80      inference('cnf', [status(esa)], [t9_funct_1])).
% 1.60/1.80  thf('49', plain,
% 1.60/1.80      (![X0 : $i]:
% 1.60/1.80         (((sk_A) != (k1_relat_1 @ X0))
% 1.60/1.80          | ~ (v1_relat_1 @ sk_C_2)
% 1.60/1.80          | ~ (v1_funct_1 @ sk_C_2)
% 1.60/1.80          | (r2_hidden @ (sk_C @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 1.60/1.80          | ((sk_C_2) = (X0))
% 1.60/1.80          | ~ (v1_funct_1 @ X0)
% 1.60/1.80          | ~ (v1_relat_1 @ X0))),
% 1.60/1.80      inference('sup-', [status(thm)], ['47', '48'])).
% 1.60/1.80  thf('50', plain,
% 1.60/1.80      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf(cc1_relset_1, axiom,
% 1.60/1.80    (![A:$i,B:$i,C:$i]:
% 1.60/1.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.60/1.80       ( v1_relat_1 @ C ) ))).
% 1.60/1.80  thf('51', plain,
% 1.60/1.80      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.60/1.80         ((v1_relat_1 @ X11)
% 1.60/1.80          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.60/1.80      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.60/1.80  thf('52', plain, ((v1_relat_1 @ sk_C_2)),
% 1.60/1.80      inference('sup-', [status(thm)], ['50', '51'])).
% 1.60/1.80  thf('53', plain, ((v1_funct_1 @ sk_C_2)),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf('54', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 1.60/1.80      inference('demod', [status(thm)], ['41', '46'])).
% 1.60/1.80  thf('55', plain,
% 1.60/1.80      (![X0 : $i]:
% 1.60/1.80         (((sk_A) != (k1_relat_1 @ X0))
% 1.60/1.80          | (r2_hidden @ (sk_C @ X0 @ sk_C_2) @ sk_A)
% 1.60/1.80          | ((sk_C_2) = (X0))
% 1.60/1.80          | ~ (v1_funct_1 @ X0)
% 1.60/1.80          | ~ (v1_relat_1 @ X0))),
% 1.60/1.80      inference('demod', [status(thm)], ['49', '52', '53', '54'])).
% 1.60/1.80  thf('56', plain,
% 1.60/1.80      ((((sk_A) != (sk_A))
% 1.60/1.80        | ~ (v1_relat_1 @ sk_D)
% 1.60/1.80        | ~ (v1_funct_1 @ sk_D)
% 1.60/1.80        | ((sk_C_2) = (sk_D))
% 1.60/1.80        | (r2_hidden @ (sk_C @ sk_D @ sk_C_2) @ sk_A))),
% 1.60/1.80      inference('sup-', [status(thm)], ['34', '55'])).
% 1.60/1.80  thf('57', plain,
% 1.60/1.80      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf('58', plain,
% 1.60/1.80      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.60/1.80         ((v1_relat_1 @ X11)
% 1.60/1.80          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.60/1.80      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.60/1.80  thf('59', plain, ((v1_relat_1 @ sk_D)),
% 1.60/1.80      inference('sup-', [status(thm)], ['57', '58'])).
% 1.60/1.80  thf('60', plain, ((v1_funct_1 @ sk_D)),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf('61', plain,
% 1.60/1.80      ((((sk_A) != (sk_A))
% 1.60/1.80        | ((sk_C_2) = (sk_D))
% 1.60/1.80        | (r2_hidden @ (sk_C @ sk_D @ sk_C_2) @ sk_A))),
% 1.60/1.80      inference('demod', [status(thm)], ['56', '59', '60'])).
% 1.60/1.80  thf('62', plain,
% 1.60/1.80      (((r2_hidden @ (sk_C @ sk_D @ sk_C_2) @ sk_A) | ((sk_C_2) = (sk_D)))),
% 1.60/1.80      inference('simplify', [status(thm)], ['61'])).
% 1.60/1.80  thf('63', plain,
% 1.60/1.80      (![X34 : $i]:
% 1.60/1.80         (((k1_funct_1 @ sk_C_2 @ X34) = (k1_funct_1 @ sk_D @ X34))
% 1.60/1.80          | ~ (r2_hidden @ X34 @ sk_A))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf('64', plain,
% 1.60/1.80      ((((sk_C_2) = (sk_D))
% 1.60/1.80        | ((k1_funct_1 @ sk_C_2 @ (sk_C @ sk_D @ sk_C_2))
% 1.60/1.80            = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_2))))),
% 1.60/1.80      inference('sup-', [status(thm)], ['62', '63'])).
% 1.60/1.80  thf('65', plain,
% 1.60/1.80      (((k1_funct_1 @ sk_C_2 @ (sk_C @ sk_D @ sk_C_2))
% 1.60/1.80         = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_2)))),
% 1.60/1.80      inference('condensation', [status(thm)], ['64'])).
% 1.60/1.80  thf('66', plain,
% 1.60/1.80      (![X9 : $i, X10 : $i]:
% 1.60/1.80         (~ (v1_relat_1 @ X9)
% 1.60/1.80          | ~ (v1_funct_1 @ X9)
% 1.60/1.80          | ((X10) = (X9))
% 1.60/1.80          | ((k1_funct_1 @ X10 @ (sk_C @ X9 @ X10))
% 1.60/1.80              != (k1_funct_1 @ X9 @ (sk_C @ X9 @ X10)))
% 1.60/1.80          | ((k1_relat_1 @ X10) != (k1_relat_1 @ X9))
% 1.60/1.80          | ~ (v1_funct_1 @ X10)
% 1.60/1.80          | ~ (v1_relat_1 @ X10))),
% 1.60/1.80      inference('cnf', [status(esa)], [t9_funct_1])).
% 1.60/1.80  thf('67', plain,
% 1.60/1.80      ((((k1_funct_1 @ sk_C_2 @ (sk_C @ sk_D @ sk_C_2))
% 1.60/1.80          != (k1_funct_1 @ sk_C_2 @ (sk_C @ sk_D @ sk_C_2)))
% 1.60/1.80        | ~ (v1_relat_1 @ sk_C_2)
% 1.60/1.80        | ~ (v1_funct_1 @ sk_C_2)
% 1.60/1.80        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 1.60/1.80        | ((sk_C_2) = (sk_D))
% 1.60/1.80        | ~ (v1_funct_1 @ sk_D)
% 1.60/1.80        | ~ (v1_relat_1 @ sk_D))),
% 1.60/1.80      inference('sup-', [status(thm)], ['65', '66'])).
% 1.60/1.80  thf('68', plain, ((v1_relat_1 @ sk_C_2)),
% 1.60/1.80      inference('sup-', [status(thm)], ['50', '51'])).
% 1.60/1.80  thf('69', plain, ((v1_funct_1 @ sk_C_2)),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf('70', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 1.60/1.80      inference('demod', [status(thm)], ['41', '46'])).
% 1.60/1.80  thf('71', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 1.60/1.80      inference('demod', [status(thm)], ['7', '33'])).
% 1.60/1.80  thf('72', plain, ((v1_funct_1 @ sk_D)),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf('73', plain, ((v1_relat_1 @ sk_D)),
% 1.60/1.80      inference('sup-', [status(thm)], ['57', '58'])).
% 1.60/1.80  thf('74', plain,
% 1.60/1.80      ((((k1_funct_1 @ sk_C_2 @ (sk_C @ sk_D @ sk_C_2))
% 1.60/1.80          != (k1_funct_1 @ sk_C_2 @ (sk_C @ sk_D @ sk_C_2)))
% 1.60/1.80        | ((sk_A) != (sk_A))
% 1.60/1.80        | ((sk_C_2) = (sk_D)))),
% 1.60/1.80      inference('demod', [status(thm)],
% 1.60/1.80                ['67', '68', '69', '70', '71', '72', '73'])).
% 1.60/1.80  thf('75', plain, (((sk_C_2) = (sk_D))),
% 1.60/1.80      inference('simplify', [status(thm)], ['74'])).
% 1.60/1.80  thf('76', plain,
% 1.60/1.80      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf('77', plain,
% 1.60/1.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.60/1.80         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 1.60/1.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 1.60/1.80      inference('condensation', [status(thm)], ['12'])).
% 1.60/1.80  thf('78', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_C_2)),
% 1.60/1.80      inference('sup-', [status(thm)], ['76', '77'])).
% 1.60/1.80  thf('79', plain, ($false),
% 1.60/1.80      inference('demod', [status(thm)], ['0', '75', '78'])).
% 1.60/1.80  
% 1.60/1.80  % SZS output end Refutation
% 1.60/1.80  
% 1.60/1.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
