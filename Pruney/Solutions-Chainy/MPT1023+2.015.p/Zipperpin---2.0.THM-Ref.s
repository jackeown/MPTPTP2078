%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B6wyE1keQI

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:30 EST 2020

% Result     : Theorem 6.03s
% Output     : Refutation 6.03s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 395 expanded)
%              Number of leaves         :   35 ( 132 expanded)
%              Depth                    :   22
%              Number of atoms          :  875 (5905 expanded)
%              Number of equality atoms :   63 ( 230 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('12',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( r2_relset_1 @ X19 @ X20 @ X21 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['12'])).

thf('14',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X13 ) ) )
      | ( v1_xboole_0 @ X14 ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X13 ) ) )
      | ( v1_xboole_0 @ X14 ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( X9 = X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X9 ) @ ( k1_relat_1 @ X9 ) )
      | ( ( k1_relat_1 @ X9 )
       != ( k1_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
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

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('63',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('64',plain,
    ( ( sk_C_1 = sk_D )
    | ( m1_subset_1 @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X31: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ X31 )
        = ( k1_funct_1 @ sk_D @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( sk_C_1 = sk_D )
    | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ),
    inference(condensation,[status(thm)],['66'])).

thf('68',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( X9 = X8 )
      | ( ( k1_funct_1 @ X9 @ ( sk_C @ X8 @ X9 ) )
       != ( k1_funct_1 @ X8 @ ( sk_C @ X8 @ X9 ) ) )
      | ( ( k1_relat_1 @ X9 )
       != ( k1_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('69',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_1 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['50','51'])).

thf('71',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['41','46'])).

thf('73',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','33'])).

thf('74',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['57','58'])).

thf('76',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(demod,[status(thm)],['69','70','71','72','73','74','75'])).

thf('77',plain,(
    sk_C_1 = sk_D ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['11','13'])).

thf('79',plain,(
    $false ),
    inference(demod,[status(thm)],['0','77','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B6wyE1keQI
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:11:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 6.03/6.25  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.03/6.25  % Solved by: fo/fo7.sh
% 6.03/6.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.03/6.25  % done 4949 iterations in 5.799s
% 6.03/6.25  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.03/6.25  % SZS output start Refutation
% 6.03/6.25  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.03/6.25  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.03/6.25  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 6.03/6.25  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 6.03/6.25  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 6.03/6.25  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.03/6.25  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.03/6.25  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 6.03/6.25  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 6.03/6.25  thf(sk_B_type, type, sk_B: $i).
% 6.03/6.25  thf(sk_A_type, type, sk_A: $i).
% 6.03/6.25  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 6.03/6.25  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 6.03/6.25  thf(sk_C_1_type, type, sk_C_1: $i).
% 6.03/6.25  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 6.03/6.25  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.03/6.25  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 6.03/6.25  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 6.03/6.25  thf(sk_D_type, type, sk_D: $i).
% 6.03/6.25  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.03/6.25  thf(t113_funct_2, conjecture,
% 6.03/6.25    (![A:$i,B:$i,C:$i]:
% 6.03/6.25     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.03/6.25         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.03/6.25       ( ![D:$i]:
% 6.03/6.25         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 6.03/6.25             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.03/6.25           ( ( ![E:$i]:
% 6.03/6.25               ( ( m1_subset_1 @ E @ A ) =>
% 6.03/6.25                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 6.03/6.25             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 6.03/6.25  thf(zf_stmt_0, negated_conjecture,
% 6.03/6.25    (~( ![A:$i,B:$i,C:$i]:
% 6.03/6.25        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.03/6.25            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.03/6.25          ( ![D:$i]:
% 6.03/6.25            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 6.03/6.25                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.03/6.25              ( ( ![E:$i]:
% 6.03/6.25                  ( ( m1_subset_1 @ E @ A ) =>
% 6.03/6.25                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 6.03/6.25                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 6.03/6.25    inference('cnf.neg', [status(esa)], [t113_funct_2])).
% 6.03/6.25  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)),
% 6.03/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.25  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 6.03/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.25  thf(d1_funct_2, axiom,
% 6.03/6.25    (![A:$i,B:$i,C:$i]:
% 6.03/6.25     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.03/6.25       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.03/6.25           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 6.03/6.25             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 6.03/6.25         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.03/6.25           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 6.03/6.25             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 6.03/6.25  thf(zf_stmt_1, axiom,
% 6.03/6.25    (![C:$i,B:$i,A:$i]:
% 6.03/6.25     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 6.03/6.25       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 6.03/6.25  thf('2', plain,
% 6.03/6.25      (![X25 : $i, X26 : $i, X27 : $i]:
% 6.03/6.25         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 6.03/6.25          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 6.03/6.25          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 6.03/6.25      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.03/6.25  thf('3', plain,
% 6.03/6.25      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 6.03/6.25        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 6.03/6.25      inference('sup-', [status(thm)], ['1', '2'])).
% 6.03/6.25  thf('4', plain,
% 6.03/6.25      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.03/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.25  thf(redefinition_k1_relset_1, axiom,
% 6.03/6.25    (![A:$i,B:$i,C:$i]:
% 6.03/6.25     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.03/6.25       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 6.03/6.25  thf('5', plain,
% 6.03/6.25      (![X16 : $i, X17 : $i, X18 : $i]:
% 6.03/6.25         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 6.03/6.25          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 6.03/6.25      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.03/6.25  thf('6', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 6.03/6.25      inference('sup-', [status(thm)], ['4', '5'])).
% 6.03/6.25  thf('7', plain,
% 6.03/6.25      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 6.03/6.25      inference('demod', [status(thm)], ['3', '6'])).
% 6.03/6.25  thf('8', plain,
% 6.03/6.25      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.03/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.25  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 6.03/6.25  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 6.03/6.25  thf(zf_stmt_4, axiom,
% 6.03/6.25    (![B:$i,A:$i]:
% 6.03/6.25     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.03/6.25       ( zip_tseitin_0 @ B @ A ) ))).
% 6.03/6.25  thf(zf_stmt_5, axiom,
% 6.03/6.25    (![A:$i,B:$i,C:$i]:
% 6.03/6.25     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.03/6.25       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 6.03/6.25         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.03/6.25           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 6.03/6.25             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 6.03/6.25  thf('9', plain,
% 6.03/6.25      (![X28 : $i, X29 : $i, X30 : $i]:
% 6.03/6.25         (~ (zip_tseitin_0 @ X28 @ X29)
% 6.03/6.25          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 6.03/6.25          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 6.03/6.25      inference('cnf', [status(esa)], [zf_stmt_5])).
% 6.03/6.25  thf('10', plain,
% 6.03/6.25      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 6.03/6.25      inference('sup-', [status(thm)], ['8', '9'])).
% 6.03/6.25  thf('11', plain,
% 6.03/6.25      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.03/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.25  thf(reflexivity_r2_relset_1, axiom,
% 6.03/6.25    (![A:$i,B:$i,C:$i,D:$i]:
% 6.03/6.25     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.03/6.25         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.03/6.25       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 6.03/6.25  thf('12', plain,
% 6.03/6.25      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 6.03/6.25         ((r2_relset_1 @ X19 @ X20 @ X21 @ X21)
% 6.03/6.25          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 6.03/6.25          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 6.03/6.25      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 6.03/6.25  thf('13', plain,
% 6.03/6.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.03/6.25         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 6.03/6.25          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 6.03/6.25      inference('condensation', [status(thm)], ['12'])).
% 6.03/6.25  thf('14', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1)),
% 6.03/6.25      inference('sup-', [status(thm)], ['11', '13'])).
% 6.03/6.25  thf('15', plain,
% 6.03/6.25      (![X23 : $i, X24 : $i]:
% 6.03/6.25         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 6.03/6.25      inference('cnf', [status(esa)], [zf_stmt_4])).
% 6.03/6.25  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 6.03/6.25  thf('16', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.03/6.25      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.03/6.25  thf('17', plain,
% 6.03/6.25      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 6.03/6.25      inference('sup+', [status(thm)], ['15', '16'])).
% 6.03/6.25  thf('18', plain,
% 6.03/6.25      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.03/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.25  thf(cc4_relset_1, axiom,
% 6.03/6.25    (![A:$i,B:$i]:
% 6.03/6.25     ( ( v1_xboole_0 @ A ) =>
% 6.03/6.25       ( ![C:$i]:
% 6.03/6.25         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 6.03/6.25           ( v1_xboole_0 @ C ) ) ) ))).
% 6.03/6.25  thf('19', plain,
% 6.03/6.25      (![X13 : $i, X14 : $i, X15 : $i]:
% 6.03/6.25         (~ (v1_xboole_0 @ X13)
% 6.03/6.25          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X13)))
% 6.03/6.25          | (v1_xboole_0 @ X14))),
% 6.03/6.25      inference('cnf', [status(esa)], [cc4_relset_1])).
% 6.03/6.25  thf('20', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_B))),
% 6.03/6.25      inference('sup-', [status(thm)], ['18', '19'])).
% 6.03/6.25  thf('21', plain,
% 6.03/6.25      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | (v1_xboole_0 @ sk_D))),
% 6.03/6.25      inference('sup-', [status(thm)], ['17', '20'])).
% 6.03/6.25  thf(t8_boole, axiom,
% 6.03/6.25    (![A:$i,B:$i]:
% 6.03/6.25     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 6.03/6.25  thf('22', plain,
% 6.03/6.25      (![X0 : $i, X1 : $i]:
% 6.03/6.25         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 6.03/6.25      inference('cnf', [status(esa)], [t8_boole])).
% 6.03/6.25  thf('23', plain,
% 6.03/6.25      (![X0 : $i, X1 : $i]:
% 6.03/6.25         ((zip_tseitin_0 @ sk_B @ X1) | ((sk_D) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 6.03/6.25      inference('sup-', [status(thm)], ['21', '22'])).
% 6.03/6.25  thf('24', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)),
% 6.03/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.25  thf('25', plain,
% 6.03/6.25      (![X0 : $i, X1 : $i]:
% 6.03/6.25         (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0)
% 6.03/6.25          | ~ (v1_xboole_0 @ X0)
% 6.03/6.25          | (zip_tseitin_0 @ sk_B @ X1))),
% 6.03/6.25      inference('sup-', [status(thm)], ['23', '24'])).
% 6.03/6.25  thf('26', plain,
% 6.03/6.25      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | ~ (v1_xboole_0 @ sk_C_1))),
% 6.03/6.25      inference('sup-', [status(thm)], ['14', '25'])).
% 6.03/6.25  thf('27', plain,
% 6.03/6.25      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 6.03/6.25      inference('sup+', [status(thm)], ['15', '16'])).
% 6.03/6.25  thf('28', plain,
% 6.03/6.25      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.03/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.25  thf('29', plain,
% 6.03/6.25      (![X13 : $i, X14 : $i, X15 : $i]:
% 6.03/6.25         (~ (v1_xboole_0 @ X13)
% 6.03/6.25          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X13)))
% 6.03/6.25          | (v1_xboole_0 @ X14))),
% 6.03/6.25      inference('cnf', [status(esa)], [cc4_relset_1])).
% 6.03/6.25  thf('30', plain, (((v1_xboole_0 @ sk_C_1) | ~ (v1_xboole_0 @ sk_B))),
% 6.03/6.25      inference('sup-', [status(thm)], ['28', '29'])).
% 6.03/6.25  thf('31', plain,
% 6.03/6.25      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | (v1_xboole_0 @ sk_C_1))),
% 6.03/6.25      inference('sup-', [status(thm)], ['27', '30'])).
% 6.03/6.25  thf('32', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 6.03/6.25      inference('clc', [status(thm)], ['26', '31'])).
% 6.03/6.25  thf('33', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 6.03/6.25      inference('demod', [status(thm)], ['10', '32'])).
% 6.03/6.25  thf('34', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 6.03/6.25      inference('demod', [status(thm)], ['7', '33'])).
% 6.03/6.25  thf('35', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 6.03/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.25  thf('36', plain,
% 6.03/6.25      (![X25 : $i, X26 : $i, X27 : $i]:
% 6.03/6.25         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 6.03/6.25          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 6.03/6.25          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 6.03/6.25      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.03/6.25  thf('37', plain,
% 6.03/6.25      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 6.03/6.25        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 6.03/6.25      inference('sup-', [status(thm)], ['35', '36'])).
% 6.03/6.25  thf('38', plain,
% 6.03/6.25      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.03/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.25  thf('39', plain,
% 6.03/6.25      (![X16 : $i, X17 : $i, X18 : $i]:
% 6.03/6.25         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 6.03/6.25          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 6.03/6.25      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.03/6.25  thf('40', plain,
% 6.03/6.25      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 6.03/6.25      inference('sup-', [status(thm)], ['38', '39'])).
% 6.03/6.25  thf('41', plain,
% 6.03/6.25      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 6.03/6.25        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 6.03/6.25      inference('demod', [status(thm)], ['37', '40'])).
% 6.03/6.25  thf('42', plain,
% 6.03/6.25      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.03/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.25  thf('43', plain,
% 6.03/6.25      (![X28 : $i, X29 : $i, X30 : $i]:
% 6.03/6.25         (~ (zip_tseitin_0 @ X28 @ X29)
% 6.03/6.25          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 6.03/6.25          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 6.03/6.25      inference('cnf', [status(esa)], [zf_stmt_5])).
% 6.03/6.25  thf('44', plain,
% 6.03/6.25      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 6.03/6.25        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 6.03/6.25      inference('sup-', [status(thm)], ['42', '43'])).
% 6.03/6.25  thf('45', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 6.03/6.25      inference('clc', [status(thm)], ['26', '31'])).
% 6.03/6.25  thf('46', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)),
% 6.03/6.25      inference('demod', [status(thm)], ['44', '45'])).
% 6.03/6.25  thf('47', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 6.03/6.25      inference('demod', [status(thm)], ['41', '46'])).
% 6.03/6.25  thf(t9_funct_1, axiom,
% 6.03/6.25    (![A:$i]:
% 6.03/6.25     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.03/6.25       ( ![B:$i]:
% 6.03/6.25         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 6.03/6.25           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 6.03/6.25               ( ![C:$i]:
% 6.03/6.25                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 6.03/6.25                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 6.03/6.25             ( ( A ) = ( B ) ) ) ) ) ))).
% 6.03/6.25  thf('48', plain,
% 6.03/6.25      (![X8 : $i, X9 : $i]:
% 6.03/6.25         (~ (v1_relat_1 @ X8)
% 6.03/6.25          | ~ (v1_funct_1 @ X8)
% 6.03/6.25          | ((X9) = (X8))
% 6.03/6.25          | (r2_hidden @ (sk_C @ X8 @ X9) @ (k1_relat_1 @ X9))
% 6.03/6.25          | ((k1_relat_1 @ X9) != (k1_relat_1 @ X8))
% 6.03/6.25          | ~ (v1_funct_1 @ X9)
% 6.03/6.25          | ~ (v1_relat_1 @ X9))),
% 6.03/6.25      inference('cnf', [status(esa)], [t9_funct_1])).
% 6.03/6.25  thf('49', plain,
% 6.03/6.25      (![X0 : $i]:
% 6.03/6.25         (((sk_A) != (k1_relat_1 @ X0))
% 6.03/6.25          | ~ (v1_relat_1 @ sk_C_1)
% 6.03/6.25          | ~ (v1_funct_1 @ sk_C_1)
% 6.03/6.25          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 6.03/6.25          | ((sk_C_1) = (X0))
% 6.03/6.25          | ~ (v1_funct_1 @ X0)
% 6.03/6.25          | ~ (v1_relat_1 @ X0))),
% 6.03/6.25      inference('sup-', [status(thm)], ['47', '48'])).
% 6.03/6.25  thf('50', plain,
% 6.03/6.25      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.03/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.25  thf(cc1_relset_1, axiom,
% 6.03/6.25    (![A:$i,B:$i,C:$i]:
% 6.03/6.25     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.03/6.25       ( v1_relat_1 @ C ) ))).
% 6.03/6.25  thf('51', plain,
% 6.03/6.25      (![X10 : $i, X11 : $i, X12 : $i]:
% 6.03/6.25         ((v1_relat_1 @ X10)
% 6.03/6.25          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 6.03/6.25      inference('cnf', [status(esa)], [cc1_relset_1])).
% 6.03/6.25  thf('52', plain, ((v1_relat_1 @ sk_C_1)),
% 6.03/6.25      inference('sup-', [status(thm)], ['50', '51'])).
% 6.03/6.25  thf('53', plain, ((v1_funct_1 @ sk_C_1)),
% 6.03/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.25  thf('54', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 6.03/6.25      inference('demod', [status(thm)], ['41', '46'])).
% 6.03/6.25  thf('55', plain,
% 6.03/6.25      (![X0 : $i]:
% 6.03/6.25         (((sk_A) != (k1_relat_1 @ X0))
% 6.03/6.25          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_A)
% 6.03/6.25          | ((sk_C_1) = (X0))
% 6.03/6.25          | ~ (v1_funct_1 @ X0)
% 6.03/6.25          | ~ (v1_relat_1 @ X0))),
% 6.03/6.25      inference('demod', [status(thm)], ['49', '52', '53', '54'])).
% 6.03/6.25  thf('56', plain,
% 6.03/6.25      ((((sk_A) != (sk_A))
% 6.03/6.25        | ~ (v1_relat_1 @ sk_D)
% 6.03/6.25        | ~ (v1_funct_1 @ sk_D)
% 6.03/6.25        | ((sk_C_1) = (sk_D))
% 6.03/6.25        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 6.03/6.25      inference('sup-', [status(thm)], ['34', '55'])).
% 6.03/6.25  thf('57', plain,
% 6.03/6.25      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.03/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.25  thf('58', plain,
% 6.03/6.25      (![X10 : $i, X11 : $i, X12 : $i]:
% 6.03/6.25         ((v1_relat_1 @ X10)
% 6.03/6.25          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 6.03/6.25      inference('cnf', [status(esa)], [cc1_relset_1])).
% 6.03/6.25  thf('59', plain, ((v1_relat_1 @ sk_D)),
% 6.03/6.25      inference('sup-', [status(thm)], ['57', '58'])).
% 6.03/6.25  thf('60', plain, ((v1_funct_1 @ sk_D)),
% 6.03/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.25  thf('61', plain,
% 6.03/6.25      ((((sk_A) != (sk_A))
% 6.03/6.25        | ((sk_C_1) = (sk_D))
% 6.03/6.25        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 6.03/6.25      inference('demod', [status(thm)], ['56', '59', '60'])).
% 6.03/6.25  thf('62', plain,
% 6.03/6.25      (((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A) | ((sk_C_1) = (sk_D)))),
% 6.03/6.25      inference('simplify', [status(thm)], ['61'])).
% 6.03/6.25  thf(t1_subset, axiom,
% 6.03/6.25    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 6.03/6.25  thf('63', plain,
% 6.03/6.25      (![X3 : $i, X4 : $i]: ((m1_subset_1 @ X3 @ X4) | ~ (r2_hidden @ X3 @ X4))),
% 6.03/6.25      inference('cnf', [status(esa)], [t1_subset])).
% 6.03/6.25  thf('64', plain,
% 6.03/6.25      ((((sk_C_1) = (sk_D)) | (m1_subset_1 @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 6.03/6.25      inference('sup-', [status(thm)], ['62', '63'])).
% 6.03/6.25  thf('65', plain,
% 6.03/6.25      (![X31 : $i]:
% 6.03/6.25         (((k1_funct_1 @ sk_C_1 @ X31) = (k1_funct_1 @ sk_D @ X31))
% 6.03/6.25          | ~ (m1_subset_1 @ X31 @ sk_A))),
% 6.03/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.25  thf('66', plain,
% 6.03/6.25      ((((sk_C_1) = (sk_D))
% 6.03/6.25        | ((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 6.03/6.25            = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))))),
% 6.03/6.25      inference('sup-', [status(thm)], ['64', '65'])).
% 6.03/6.25  thf('67', plain,
% 6.03/6.25      (((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 6.03/6.25         = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))),
% 6.03/6.25      inference('condensation', [status(thm)], ['66'])).
% 6.03/6.25  thf('68', plain,
% 6.03/6.25      (![X8 : $i, X9 : $i]:
% 6.03/6.25         (~ (v1_relat_1 @ X8)
% 6.03/6.25          | ~ (v1_funct_1 @ X8)
% 6.03/6.25          | ((X9) = (X8))
% 6.03/6.25          | ((k1_funct_1 @ X9 @ (sk_C @ X8 @ X9))
% 6.03/6.25              != (k1_funct_1 @ X8 @ (sk_C @ X8 @ X9)))
% 6.03/6.25          | ((k1_relat_1 @ X9) != (k1_relat_1 @ X8))
% 6.03/6.25          | ~ (v1_funct_1 @ X9)
% 6.03/6.25          | ~ (v1_relat_1 @ X9))),
% 6.03/6.25      inference('cnf', [status(esa)], [t9_funct_1])).
% 6.03/6.25  thf('69', plain,
% 6.03/6.25      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 6.03/6.25          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 6.03/6.25        | ~ (v1_relat_1 @ sk_C_1)
% 6.03/6.25        | ~ (v1_funct_1 @ sk_C_1)
% 6.03/6.25        | ((k1_relat_1 @ sk_C_1) != (k1_relat_1 @ sk_D))
% 6.03/6.25        | ((sk_C_1) = (sk_D))
% 6.03/6.25        | ~ (v1_funct_1 @ sk_D)
% 6.03/6.25        | ~ (v1_relat_1 @ sk_D))),
% 6.03/6.25      inference('sup-', [status(thm)], ['67', '68'])).
% 6.03/6.25  thf('70', plain, ((v1_relat_1 @ sk_C_1)),
% 6.03/6.25      inference('sup-', [status(thm)], ['50', '51'])).
% 6.03/6.25  thf('71', plain, ((v1_funct_1 @ sk_C_1)),
% 6.03/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.25  thf('72', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 6.03/6.25      inference('demod', [status(thm)], ['41', '46'])).
% 6.03/6.25  thf('73', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 6.03/6.25      inference('demod', [status(thm)], ['7', '33'])).
% 6.03/6.25  thf('74', plain, ((v1_funct_1 @ sk_D)),
% 6.03/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.25  thf('75', plain, ((v1_relat_1 @ sk_D)),
% 6.03/6.25      inference('sup-', [status(thm)], ['57', '58'])).
% 6.03/6.25  thf('76', plain,
% 6.03/6.25      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 6.03/6.25          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 6.03/6.25        | ((sk_A) != (sk_A))
% 6.03/6.25        | ((sk_C_1) = (sk_D)))),
% 6.03/6.25      inference('demod', [status(thm)],
% 6.03/6.25                ['69', '70', '71', '72', '73', '74', '75'])).
% 6.03/6.25  thf('77', plain, (((sk_C_1) = (sk_D))),
% 6.03/6.25      inference('simplify', [status(thm)], ['76'])).
% 6.03/6.25  thf('78', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1)),
% 6.03/6.25      inference('sup-', [status(thm)], ['11', '13'])).
% 6.03/6.25  thf('79', plain, ($false),
% 6.03/6.25      inference('demod', [status(thm)], ['0', '77', '78'])).
% 6.03/6.25  
% 6.03/6.25  % SZS output end Refutation
% 6.03/6.25  
% 6.12/6.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
