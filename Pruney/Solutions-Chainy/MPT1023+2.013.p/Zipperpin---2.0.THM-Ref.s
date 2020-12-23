%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bGJZ8HdN7Z

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:30 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 402 expanded)
%              Number of leaves         :   38 ( 135 expanded)
%              Depth                    :   22
%              Number of atoms          :  928 (5941 expanded)
%              Number of equality atoms :   65 ( 232 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('12',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_relset_1 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
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
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('19',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X12 ) ) )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
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
      | ( sk_C_1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X12 ) ) )
      | ( v1_xboole_0 @ X13 ) ) ),
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
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ( X24
        = ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
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

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('63',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X3 ) @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('64',plain,(
    ! [X2: $i] :
      ( ( k2_subset_1 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('65',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('66',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( m1_subset_1 @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( sk_C_1 = sk_D )
    | ( m1_subset_1 @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['62','67'])).

thf('69',plain,(
    ! [X30: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ X30 )
        = ( k1_funct_1 @ sk_D @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( sk_C_1 = sk_D )
    | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ),
    inference(condensation,[status(thm)],['70'])).

thf('72',plain,(
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

thf('73',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_1 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['50','51'])).

thf('75',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['41','46'])).

thf('77',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','33'])).

thf('78',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['57','58'])).

thf('80',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(demod,[status(thm)],['73','74','75','76','77','78','79'])).

thf('81',plain,(
    sk_C_1 = sk_D ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['12'])).

thf('84',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    $false ),
    inference(demod,[status(thm)],['0','81','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bGJZ8HdN7Z
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:58:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.58/0.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.80  % Solved by: fo/fo7.sh
% 0.58/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.80  % done 310 iterations in 0.348s
% 0.58/0.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.80  % SZS output start Refutation
% 0.58/0.80  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.58/0.80  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.58/0.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.80  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.58/0.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.80  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.80  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.58/0.80  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.58/0.80  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.58/0.80  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.58/0.80  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.58/0.80  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.58/0.80  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.58/0.80  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.58/0.80  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.58/0.80  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.80  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.58/0.80  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.80  thf(sk_D_type, type, sk_D: $i).
% 0.58/0.80  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.58/0.80  thf(t113_funct_2, conjecture,
% 0.58/0.80    (![A:$i,B:$i,C:$i]:
% 0.58/0.80     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.58/0.80         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.80       ( ![D:$i]:
% 0.58/0.80         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.58/0.80             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.80           ( ( ![E:$i]:
% 0.58/0.80               ( ( m1_subset_1 @ E @ A ) =>
% 0.58/0.80                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 0.58/0.80             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 0.58/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.80    (~( ![A:$i,B:$i,C:$i]:
% 0.58/0.80        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.58/0.80            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.80          ( ![D:$i]:
% 0.58/0.80            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.58/0.80                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.80              ( ( ![E:$i]:
% 0.58/0.80                  ( ( m1_subset_1 @ E @ A ) =>
% 0.58/0.80                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 0.58/0.80                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 0.58/0.80    inference('cnf.neg', [status(esa)], [t113_funct_2])).
% 0.58/0.80  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf(d1_funct_2, axiom,
% 0.58/0.80    (![A:$i,B:$i,C:$i]:
% 0.58/0.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.80       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.58/0.80           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.58/0.80             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.58/0.80         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.58/0.80           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.58/0.80             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.58/0.80  thf(zf_stmt_1, axiom,
% 0.58/0.80    (![C:$i,B:$i,A:$i]:
% 0.58/0.80     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.58/0.80       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.58/0.80  thf('2', plain,
% 0.58/0.80      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.58/0.80         (~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.58/0.80          | ((X24) = (k1_relset_1 @ X24 @ X25 @ X26))
% 0.58/0.80          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.58/0.80  thf('3', plain,
% 0.58/0.80      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.58/0.80        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['1', '2'])).
% 0.58/0.80  thf('4', plain,
% 0.58/0.80      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf(redefinition_k1_relset_1, axiom,
% 0.58/0.80    (![A:$i,B:$i,C:$i]:
% 0.58/0.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.80       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.58/0.80  thf('5', plain,
% 0.58/0.80      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.58/0.80         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 0.58/0.80          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.58/0.80      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.58/0.80  thf('6', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.58/0.80      inference('sup-', [status(thm)], ['4', '5'])).
% 0.58/0.80  thf('7', plain,
% 0.58/0.80      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.58/0.80      inference('demod', [status(thm)], ['3', '6'])).
% 0.58/0.80  thf('8', plain,
% 0.58/0.80      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.58/0.80  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.58/0.80  thf(zf_stmt_4, axiom,
% 0.58/0.80    (![B:$i,A:$i]:
% 0.58/0.80     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.58/0.80       ( zip_tseitin_0 @ B @ A ) ))).
% 0.58/0.80  thf(zf_stmt_5, axiom,
% 0.58/0.80    (![A:$i,B:$i,C:$i]:
% 0.58/0.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.80       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.58/0.80         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.58/0.80           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.58/0.80             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.58/0.80  thf('9', plain,
% 0.58/0.80      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.58/0.80         (~ (zip_tseitin_0 @ X27 @ X28)
% 0.58/0.80          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 0.58/0.80          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.58/0.80  thf('10', plain,
% 0.58/0.80      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.58/0.80      inference('sup-', [status(thm)], ['8', '9'])).
% 0.58/0.80  thf('11', plain,
% 0.58/0.80      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf(reflexivity_r2_relset_1, axiom,
% 0.58/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.80     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.58/0.80         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.80       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.58/0.80  thf('12', plain,
% 0.58/0.80      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.58/0.80         ((r2_relset_1 @ X18 @ X19 @ X20 @ X20)
% 0.58/0.80          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.58/0.80          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.58/0.80      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.58/0.80  thf('13', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.80         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.58/0.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.58/0.80      inference('condensation', [status(thm)], ['12'])).
% 0.58/0.80  thf('14', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D)),
% 0.58/0.80      inference('sup-', [status(thm)], ['11', '13'])).
% 0.58/0.80  thf('15', plain,
% 0.58/0.80      (![X22 : $i, X23 : $i]:
% 0.58/0.80         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.58/0.80  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.58/0.80  thf('16', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.80      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.58/0.80  thf('17', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.58/0.80      inference('sup+', [status(thm)], ['15', '16'])).
% 0.58/0.80  thf('18', plain,
% 0.58/0.80      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf(cc4_relset_1, axiom,
% 0.58/0.80    (![A:$i,B:$i]:
% 0.58/0.80     ( ( v1_xboole_0 @ A ) =>
% 0.58/0.80       ( ![C:$i]:
% 0.58/0.80         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.58/0.80           ( v1_xboole_0 @ C ) ) ) ))).
% 0.58/0.80  thf('19', plain,
% 0.58/0.80      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.58/0.80         (~ (v1_xboole_0 @ X12)
% 0.58/0.80          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X12)))
% 0.58/0.80          | (v1_xboole_0 @ X13))),
% 0.58/0.80      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.58/0.80  thf('20', plain, (((v1_xboole_0 @ sk_C_1) | ~ (v1_xboole_0 @ sk_B))),
% 0.58/0.80      inference('sup-', [status(thm)], ['18', '19'])).
% 0.58/0.80  thf('21', plain,
% 0.58/0.80      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | (v1_xboole_0 @ sk_C_1))),
% 0.58/0.80      inference('sup-', [status(thm)], ['17', '20'])).
% 0.58/0.80  thf(t8_boole, axiom,
% 0.58/0.80    (![A:$i,B:$i]:
% 0.58/0.80     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.58/0.80  thf('22', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 0.58/0.80      inference('cnf', [status(esa)], [t8_boole])).
% 0.58/0.80  thf('23', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((zip_tseitin_0 @ sk_B @ X1)
% 0.58/0.80          | ((sk_C_1) = (X0))
% 0.58/0.80          | ~ (v1_xboole_0 @ X0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['21', '22'])).
% 0.58/0.80  thf('24', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('25', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         (~ (r2_relset_1 @ sk_A @ sk_B @ X0 @ sk_D)
% 0.58/0.80          | ~ (v1_xboole_0 @ X0)
% 0.58/0.80          | (zip_tseitin_0 @ sk_B @ X1))),
% 0.58/0.80      inference('sup-', [status(thm)], ['23', '24'])).
% 0.58/0.80  thf('26', plain,
% 0.58/0.80      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | ~ (v1_xboole_0 @ sk_D))),
% 0.58/0.80      inference('sup-', [status(thm)], ['14', '25'])).
% 0.58/0.80  thf('27', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.58/0.80      inference('sup+', [status(thm)], ['15', '16'])).
% 0.58/0.80  thf('28', plain,
% 0.58/0.80      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('29', plain,
% 0.58/0.80      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.58/0.80         (~ (v1_xboole_0 @ X12)
% 0.58/0.80          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X12)))
% 0.58/0.80          | (v1_xboole_0 @ X13))),
% 0.58/0.80      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.58/0.80  thf('30', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_B))),
% 0.58/0.80      inference('sup-', [status(thm)], ['28', '29'])).
% 0.58/0.80  thf('31', plain,
% 0.58/0.80      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | (v1_xboole_0 @ sk_D))),
% 0.58/0.80      inference('sup-', [status(thm)], ['27', '30'])).
% 0.58/0.80  thf('32', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 0.58/0.80      inference('clc', [status(thm)], ['26', '31'])).
% 0.58/0.80  thf('33', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 0.58/0.80      inference('demod', [status(thm)], ['10', '32'])).
% 0.58/0.80  thf('34', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.58/0.80      inference('demod', [status(thm)], ['7', '33'])).
% 0.58/0.80  thf('35', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('36', plain,
% 0.58/0.80      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.58/0.80         (~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.58/0.80          | ((X24) = (k1_relset_1 @ X24 @ X25 @ X26))
% 0.58/0.80          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.58/0.80  thf('37', plain,
% 0.58/0.80      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 0.58/0.80        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['35', '36'])).
% 0.58/0.80  thf('38', plain,
% 0.58/0.80      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('39', plain,
% 0.58/0.80      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.58/0.80         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 0.58/0.80          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.58/0.80      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.58/0.80  thf('40', plain,
% 0.58/0.80      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.58/0.80      inference('sup-', [status(thm)], ['38', '39'])).
% 0.58/0.80  thf('41', plain,
% 0.58/0.80      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 0.58/0.80        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 0.58/0.80      inference('demod', [status(thm)], ['37', '40'])).
% 0.58/0.80  thf('42', plain,
% 0.58/0.80      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('43', plain,
% 0.58/0.80      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.58/0.80         (~ (zip_tseitin_0 @ X27 @ X28)
% 0.58/0.80          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 0.58/0.80          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.58/0.80  thf('44', plain,
% 0.58/0.80      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 0.58/0.80        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.58/0.80      inference('sup-', [status(thm)], ['42', '43'])).
% 0.58/0.80  thf('45', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 0.58/0.80      inference('clc', [status(thm)], ['26', '31'])).
% 0.58/0.80  thf('46', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)),
% 0.58/0.80      inference('demod', [status(thm)], ['44', '45'])).
% 0.58/0.80  thf('47', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.58/0.80      inference('demod', [status(thm)], ['41', '46'])).
% 0.58/0.80  thf(t9_funct_1, axiom,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.58/0.80       ( ![B:$i]:
% 0.58/0.80         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.58/0.80           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.58/0.80               ( ![C:$i]:
% 0.58/0.80                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 0.58/0.80                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 0.58/0.80             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.58/0.80  thf('48', plain,
% 0.58/0.80      (![X7 : $i, X8 : $i]:
% 0.58/0.80         (~ (v1_relat_1 @ X7)
% 0.58/0.80          | ~ (v1_funct_1 @ X7)
% 0.58/0.80          | ((X8) = (X7))
% 0.58/0.80          | (r2_hidden @ (sk_C @ X7 @ X8) @ (k1_relat_1 @ X8))
% 0.58/0.80          | ((k1_relat_1 @ X8) != (k1_relat_1 @ X7))
% 0.58/0.80          | ~ (v1_funct_1 @ X8)
% 0.58/0.80          | ~ (v1_relat_1 @ X8))),
% 0.58/0.80      inference('cnf', [status(esa)], [t9_funct_1])).
% 0.58/0.80  thf('49', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (((sk_A) != (k1_relat_1 @ X0))
% 0.58/0.80          | ~ (v1_relat_1 @ sk_C_1)
% 0.58/0.80          | ~ (v1_funct_1 @ sk_C_1)
% 0.58/0.80          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 0.58/0.80          | ((sk_C_1) = (X0))
% 0.58/0.80          | ~ (v1_funct_1 @ X0)
% 0.58/0.80          | ~ (v1_relat_1 @ X0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['47', '48'])).
% 0.58/0.80  thf('50', plain,
% 0.58/0.80      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf(cc1_relset_1, axiom,
% 0.58/0.80    (![A:$i,B:$i,C:$i]:
% 0.58/0.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.80       ( v1_relat_1 @ C ) ))).
% 0.58/0.80  thf('51', plain,
% 0.58/0.80      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.58/0.80         ((v1_relat_1 @ X9)
% 0.58/0.80          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.58/0.80      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.58/0.80  thf('52', plain, ((v1_relat_1 @ sk_C_1)),
% 0.58/0.80      inference('sup-', [status(thm)], ['50', '51'])).
% 0.58/0.80  thf('53', plain, ((v1_funct_1 @ sk_C_1)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('54', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.58/0.80      inference('demod', [status(thm)], ['41', '46'])).
% 0.58/0.80  thf('55', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (((sk_A) != (k1_relat_1 @ X0))
% 0.58/0.80          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_A)
% 0.58/0.80          | ((sk_C_1) = (X0))
% 0.58/0.80          | ~ (v1_funct_1 @ X0)
% 0.58/0.80          | ~ (v1_relat_1 @ X0))),
% 0.58/0.80      inference('demod', [status(thm)], ['49', '52', '53', '54'])).
% 0.58/0.80  thf('56', plain,
% 0.58/0.80      ((((sk_A) != (sk_A))
% 0.58/0.80        | ~ (v1_relat_1 @ sk_D)
% 0.58/0.80        | ~ (v1_funct_1 @ sk_D)
% 0.58/0.80        | ((sk_C_1) = (sk_D))
% 0.58/0.80        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 0.58/0.80      inference('sup-', [status(thm)], ['34', '55'])).
% 0.58/0.80  thf('57', plain,
% 0.58/0.80      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('58', plain,
% 0.58/0.80      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.58/0.80         ((v1_relat_1 @ X9)
% 0.58/0.80          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.58/0.80      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.58/0.80  thf('59', plain, ((v1_relat_1 @ sk_D)),
% 0.58/0.80      inference('sup-', [status(thm)], ['57', '58'])).
% 0.58/0.80  thf('60', plain, ((v1_funct_1 @ sk_D)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('61', plain,
% 0.58/0.80      ((((sk_A) != (sk_A))
% 0.58/0.80        | ((sk_C_1) = (sk_D))
% 0.58/0.80        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 0.58/0.80      inference('demod', [status(thm)], ['56', '59', '60'])).
% 0.58/0.80  thf('62', plain,
% 0.58/0.80      (((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A) | ((sk_C_1) = (sk_D)))),
% 0.58/0.80      inference('simplify', [status(thm)], ['61'])).
% 0.58/0.80  thf(dt_k2_subset_1, axiom,
% 0.58/0.80    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.58/0.80  thf('63', plain,
% 0.58/0.80      (![X3 : $i]: (m1_subset_1 @ (k2_subset_1 @ X3) @ (k1_zfmisc_1 @ X3))),
% 0.58/0.80      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.58/0.80  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.58/0.80  thf('64', plain, (![X2 : $i]: ((k2_subset_1 @ X2) = (X2))),
% 0.58/0.80      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.58/0.80  thf('65', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.58/0.80      inference('demod', [status(thm)], ['63', '64'])).
% 0.58/0.80  thf(t4_subset, axiom,
% 0.58/0.80    (![A:$i,B:$i,C:$i]:
% 0.58/0.80     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.58/0.80       ( m1_subset_1 @ A @ C ) ))).
% 0.58/0.80  thf('66', plain,
% 0.58/0.80      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.58/0.80         (~ (r2_hidden @ X4 @ X5)
% 0.58/0.80          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.58/0.80          | (m1_subset_1 @ X4 @ X6))),
% 0.58/0.80      inference('cnf', [status(esa)], [t4_subset])).
% 0.58/0.80  thf('67', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['65', '66'])).
% 0.58/0.80  thf('68', plain,
% 0.58/0.80      ((((sk_C_1) = (sk_D)) | (m1_subset_1 @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 0.58/0.80      inference('sup-', [status(thm)], ['62', '67'])).
% 0.58/0.80  thf('69', plain,
% 0.58/0.80      (![X30 : $i]:
% 0.58/0.80         (((k1_funct_1 @ sk_C_1 @ X30) = (k1_funct_1 @ sk_D @ X30))
% 0.58/0.80          | ~ (m1_subset_1 @ X30 @ sk_A))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('70', plain,
% 0.58/0.80      ((((sk_C_1) = (sk_D))
% 0.58/0.80        | ((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 0.58/0.80            = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))))),
% 0.58/0.80      inference('sup-', [status(thm)], ['68', '69'])).
% 0.58/0.80  thf('71', plain,
% 0.58/0.80      (((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 0.58/0.80         = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))),
% 0.58/0.80      inference('condensation', [status(thm)], ['70'])).
% 0.58/0.80  thf('72', plain,
% 0.58/0.80      (![X7 : $i, X8 : $i]:
% 0.58/0.80         (~ (v1_relat_1 @ X7)
% 0.58/0.80          | ~ (v1_funct_1 @ X7)
% 0.58/0.80          | ((X8) = (X7))
% 0.58/0.80          | ((k1_funct_1 @ X8 @ (sk_C @ X7 @ X8))
% 0.58/0.80              != (k1_funct_1 @ X7 @ (sk_C @ X7 @ X8)))
% 0.58/0.80          | ((k1_relat_1 @ X8) != (k1_relat_1 @ X7))
% 0.58/0.80          | ~ (v1_funct_1 @ X8)
% 0.58/0.80          | ~ (v1_relat_1 @ X8))),
% 0.58/0.80      inference('cnf', [status(esa)], [t9_funct_1])).
% 0.58/0.80  thf('73', plain,
% 0.58/0.80      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 0.58/0.80          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 0.58/0.80        | ~ (v1_relat_1 @ sk_C_1)
% 0.58/0.80        | ~ (v1_funct_1 @ sk_C_1)
% 0.58/0.80        | ((k1_relat_1 @ sk_C_1) != (k1_relat_1 @ sk_D))
% 0.58/0.80        | ((sk_C_1) = (sk_D))
% 0.58/0.80        | ~ (v1_funct_1 @ sk_D)
% 0.58/0.80        | ~ (v1_relat_1 @ sk_D))),
% 0.58/0.80      inference('sup-', [status(thm)], ['71', '72'])).
% 0.58/0.80  thf('74', plain, ((v1_relat_1 @ sk_C_1)),
% 0.58/0.80      inference('sup-', [status(thm)], ['50', '51'])).
% 0.58/0.80  thf('75', plain, ((v1_funct_1 @ sk_C_1)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('76', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.58/0.80      inference('demod', [status(thm)], ['41', '46'])).
% 0.58/0.80  thf('77', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.58/0.80      inference('demod', [status(thm)], ['7', '33'])).
% 0.58/0.80  thf('78', plain, ((v1_funct_1 @ sk_D)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('79', plain, ((v1_relat_1 @ sk_D)),
% 0.58/0.80      inference('sup-', [status(thm)], ['57', '58'])).
% 0.58/0.80  thf('80', plain,
% 0.58/0.80      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 0.58/0.80          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 0.58/0.80        | ((sk_A) != (sk_A))
% 0.58/0.80        | ((sk_C_1) = (sk_D)))),
% 0.58/0.80      inference('demod', [status(thm)],
% 0.58/0.80                ['73', '74', '75', '76', '77', '78', '79'])).
% 0.58/0.80  thf('81', plain, (((sk_C_1) = (sk_D))),
% 0.58/0.80      inference('simplify', [status(thm)], ['80'])).
% 0.58/0.80  thf('82', plain,
% 0.58/0.80      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('83', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.80         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.58/0.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.58/0.80      inference('condensation', [status(thm)], ['12'])).
% 0.58/0.80  thf('84', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1)),
% 0.58/0.80      inference('sup-', [status(thm)], ['82', '83'])).
% 0.58/0.80  thf('85', plain, ($false),
% 0.58/0.80      inference('demod', [status(thm)], ['0', '81', '84'])).
% 0.58/0.80  
% 0.58/0.80  % SZS output end Refutation
% 0.58/0.80  
% 0.58/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
