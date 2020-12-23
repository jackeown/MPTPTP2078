%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bCBxZow5hV

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:30 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 395 expanded)
%              Number of leaves         :   35 ( 132 expanded)
%              Depth                    :   22
%              Number of atoms          :  881 (5941 expanded)
%              Number of equality atoms :   65 ( 242 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ( X21
        = ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( r2_relset_1 @ X16 @ X17 @ X15 @ X18 )
      | ( X15 != X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('13',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_relset_1 @ X16 @ X17 @ X18 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X9 ) ) )
      | ( v1_xboole_0 @ X10 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X9 ) ) )
      | ( v1_xboole_0 @ X10 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ( X21
        = ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( X5 = X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X5 ) @ ( k1_relat_1 @ X5 ) )
      | ( ( k1_relat_1 @ X5 )
       != ( k1_relat_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
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
    ! [X2: $i,X3: $i] :
      ( ( m1_subset_1 @ X2 @ X3 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('64',plain,
    ( ( sk_C_1 = sk_D )
    | ( m1_subset_1 @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X27: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ X27 )
        = ( k1_funct_1 @ sk_D @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ sk_A ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( X5 = X4 )
      | ( ( k1_funct_1 @ X5 @ ( sk_C @ X4 @ X5 ) )
       != ( k1_funct_1 @ X4 @ ( sk_C @ X4 @ X5 ) ) )
      | ( ( k1_relat_1 @ X5 )
       != ( k1_relat_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
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
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bCBxZow5hV
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:21:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.42/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.63  % Solved by: fo/fo7.sh
% 0.42/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.63  % done 164 iterations in 0.172s
% 0.42/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.63  % SZS output start Refutation
% 0.42/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.42/0.63  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.42/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.42/0.63  thf(sk_D_type, type, sk_D: $i).
% 0.42/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.63  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.42/0.63  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.42/0.63  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.42/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.63  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.42/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.42/0.63  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.42/0.63  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.42/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.42/0.63  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.42/0.63  thf(t113_funct_2, conjecture,
% 0.42/0.63    (![A:$i,B:$i,C:$i]:
% 0.42/0.63     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.42/0.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.63       ( ![D:$i]:
% 0.42/0.63         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.42/0.63             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.63           ( ( ![E:$i]:
% 0.42/0.63               ( ( m1_subset_1 @ E @ A ) =>
% 0.42/0.63                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 0.42/0.63             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 0.42/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.63    (~( ![A:$i,B:$i,C:$i]:
% 0.42/0.63        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.42/0.63            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.63          ( ![D:$i]:
% 0.42/0.63            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.42/0.63                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.63              ( ( ![E:$i]:
% 0.42/0.63                  ( ( m1_subset_1 @ E @ A ) =>
% 0.42/0.63                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 0.42/0.63                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 0.42/0.63    inference('cnf.neg', [status(esa)], [t113_funct_2])).
% 0.42/0.63  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf(d1_funct_2, axiom,
% 0.42/0.63    (![A:$i,B:$i,C:$i]:
% 0.42/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.63       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.42/0.63           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.42/0.63             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.42/0.63         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.63           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.42/0.63             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.42/0.63  thf(zf_stmt_1, axiom,
% 0.42/0.63    (![C:$i,B:$i,A:$i]:
% 0.42/0.63     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.42/0.63       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.42/0.63  thf('2', plain,
% 0.42/0.63      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.42/0.63         (~ (v1_funct_2 @ X23 @ X21 @ X22)
% 0.42/0.63          | ((X21) = (k1_relset_1 @ X21 @ X22 @ X23))
% 0.42/0.63          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.63  thf('3', plain,
% 0.42/0.63      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.42/0.63        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.42/0.63      inference('sup-', [status(thm)], ['1', '2'])).
% 0.42/0.63  thf('4', plain,
% 0.42/0.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf(redefinition_k1_relset_1, axiom,
% 0.42/0.63    (![A:$i,B:$i,C:$i]:
% 0.42/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.63       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.42/0.63  thf('5', plain,
% 0.42/0.63      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.42/0.63         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 0.42/0.63          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.42/0.63      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.42/0.63  thf('6', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.42/0.63      inference('sup-', [status(thm)], ['4', '5'])).
% 0.42/0.63  thf('7', plain,
% 0.42/0.63      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.42/0.63      inference('demod', [status(thm)], ['3', '6'])).
% 0.42/0.63  thf('8', plain,
% 0.42/0.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.42/0.63  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.42/0.63  thf(zf_stmt_4, axiom,
% 0.42/0.63    (![B:$i,A:$i]:
% 0.42/0.63     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.63       ( zip_tseitin_0 @ B @ A ) ))).
% 0.42/0.63  thf(zf_stmt_5, axiom,
% 0.42/0.63    (![A:$i,B:$i,C:$i]:
% 0.42/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.63       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.42/0.63         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.42/0.63           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.42/0.63             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.42/0.63  thf('9', plain,
% 0.42/0.63      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.42/0.63         (~ (zip_tseitin_0 @ X24 @ X25)
% 0.42/0.63          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 0.42/0.63          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.42/0.63  thf('10', plain,
% 0.42/0.63      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.42/0.63      inference('sup-', [status(thm)], ['8', '9'])).
% 0.42/0.63  thf('11', plain,
% 0.42/0.63      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf(redefinition_r2_relset_1, axiom,
% 0.42/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.63     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.42/0.63         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.63       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.42/0.63  thf('12', plain,
% 0.42/0.63      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.42/0.63         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.42/0.63          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.42/0.63          | (r2_relset_1 @ X16 @ X17 @ X15 @ X18)
% 0.42/0.63          | ((X15) != (X18)))),
% 0.42/0.63      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.42/0.63  thf('13', plain,
% 0.42/0.63      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.42/0.63         ((r2_relset_1 @ X16 @ X17 @ X18 @ X18)
% 0.42/0.63          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.42/0.63      inference('simplify', [status(thm)], ['12'])).
% 0.42/0.63  thf('14', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1)),
% 0.42/0.63      inference('sup-', [status(thm)], ['11', '13'])).
% 0.42/0.63  thf('15', plain,
% 0.42/0.63      (![X19 : $i, X20 : $i]:
% 0.42/0.63         ((zip_tseitin_0 @ X19 @ X20) | ((X19) = (k1_xboole_0)))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.42/0.63  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.42/0.63  thf('16', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.42/0.63      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.42/0.63  thf('17', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.42/0.63      inference('sup+', [status(thm)], ['15', '16'])).
% 0.42/0.63  thf('18', plain,
% 0.42/0.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf(cc4_relset_1, axiom,
% 0.42/0.63    (![A:$i,B:$i]:
% 0.42/0.63     ( ( v1_xboole_0 @ A ) =>
% 0.42/0.63       ( ![C:$i]:
% 0.42/0.63         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.42/0.63           ( v1_xboole_0 @ C ) ) ) ))).
% 0.42/0.63  thf('19', plain,
% 0.42/0.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.42/0.63         (~ (v1_xboole_0 @ X9)
% 0.42/0.63          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X9)))
% 0.42/0.63          | (v1_xboole_0 @ X10))),
% 0.42/0.63      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.42/0.63  thf('20', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_B))),
% 0.42/0.63      inference('sup-', [status(thm)], ['18', '19'])).
% 0.42/0.63  thf('21', plain,
% 0.42/0.63      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | (v1_xboole_0 @ sk_D))),
% 0.42/0.63      inference('sup-', [status(thm)], ['17', '20'])).
% 0.42/0.63  thf(t8_boole, axiom,
% 0.42/0.63    (![A:$i,B:$i]:
% 0.42/0.63     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.42/0.63  thf('22', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]:
% 0.42/0.63         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 0.42/0.63      inference('cnf', [status(esa)], [t8_boole])).
% 0.42/0.63  thf('23', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]:
% 0.42/0.63         ((zip_tseitin_0 @ sk_B @ X1) | ((sk_D) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.42/0.63      inference('sup-', [status(thm)], ['21', '22'])).
% 0.42/0.63  thf('24', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('25', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]:
% 0.42/0.63         (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0)
% 0.42/0.63          | ~ (v1_xboole_0 @ X0)
% 0.42/0.63          | (zip_tseitin_0 @ sk_B @ X1))),
% 0.42/0.63      inference('sup-', [status(thm)], ['23', '24'])).
% 0.42/0.63  thf('26', plain,
% 0.42/0.63      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | ~ (v1_xboole_0 @ sk_C_1))),
% 0.42/0.63      inference('sup-', [status(thm)], ['14', '25'])).
% 0.42/0.63  thf('27', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.42/0.63      inference('sup+', [status(thm)], ['15', '16'])).
% 0.42/0.63  thf('28', plain,
% 0.42/0.63      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('29', plain,
% 0.42/0.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.42/0.63         (~ (v1_xboole_0 @ X9)
% 0.42/0.63          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X9)))
% 0.42/0.63          | (v1_xboole_0 @ X10))),
% 0.42/0.63      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.42/0.63  thf('30', plain, (((v1_xboole_0 @ sk_C_1) | ~ (v1_xboole_0 @ sk_B))),
% 0.42/0.63      inference('sup-', [status(thm)], ['28', '29'])).
% 0.42/0.63  thf('31', plain,
% 0.42/0.63      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | (v1_xboole_0 @ sk_C_1))),
% 0.42/0.63      inference('sup-', [status(thm)], ['27', '30'])).
% 0.42/0.63  thf('32', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 0.42/0.63      inference('clc', [status(thm)], ['26', '31'])).
% 0.42/0.63  thf('33', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 0.42/0.63      inference('demod', [status(thm)], ['10', '32'])).
% 0.42/0.63  thf('34', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.42/0.63      inference('demod', [status(thm)], ['7', '33'])).
% 0.42/0.63  thf('35', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('36', plain,
% 0.42/0.63      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.42/0.63         (~ (v1_funct_2 @ X23 @ X21 @ X22)
% 0.42/0.63          | ((X21) = (k1_relset_1 @ X21 @ X22 @ X23))
% 0.42/0.63          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.63  thf('37', plain,
% 0.42/0.63      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 0.42/0.63        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.42/0.63      inference('sup-', [status(thm)], ['35', '36'])).
% 0.42/0.63  thf('38', plain,
% 0.42/0.63      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('39', plain,
% 0.42/0.63      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.42/0.63         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 0.42/0.63          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.42/0.63      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.42/0.63  thf('40', plain,
% 0.42/0.63      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.42/0.63      inference('sup-', [status(thm)], ['38', '39'])).
% 0.42/0.63  thf('41', plain,
% 0.42/0.63      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 0.42/0.63        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 0.42/0.63      inference('demod', [status(thm)], ['37', '40'])).
% 0.42/0.63  thf('42', plain,
% 0.42/0.63      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('43', plain,
% 0.42/0.63      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.42/0.63         (~ (zip_tseitin_0 @ X24 @ X25)
% 0.42/0.63          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 0.42/0.63          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.42/0.63  thf('44', plain,
% 0.42/0.63      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 0.42/0.63        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.42/0.63      inference('sup-', [status(thm)], ['42', '43'])).
% 0.42/0.63  thf('45', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 0.42/0.63      inference('clc', [status(thm)], ['26', '31'])).
% 0.42/0.63  thf('46', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)),
% 0.42/0.63      inference('demod', [status(thm)], ['44', '45'])).
% 0.42/0.63  thf('47', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.42/0.63      inference('demod', [status(thm)], ['41', '46'])).
% 0.42/0.63  thf(t9_funct_1, axiom,
% 0.42/0.63    (![A:$i]:
% 0.42/0.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.42/0.63       ( ![B:$i]:
% 0.42/0.63         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.42/0.63           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.42/0.63               ( ![C:$i]:
% 0.42/0.63                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 0.42/0.63                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 0.42/0.63             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.42/0.63  thf('48', plain,
% 0.42/0.63      (![X4 : $i, X5 : $i]:
% 0.42/0.63         (~ (v1_relat_1 @ X4)
% 0.42/0.63          | ~ (v1_funct_1 @ X4)
% 0.42/0.63          | ((X5) = (X4))
% 0.42/0.63          | (r2_hidden @ (sk_C @ X4 @ X5) @ (k1_relat_1 @ X5))
% 0.42/0.63          | ((k1_relat_1 @ X5) != (k1_relat_1 @ X4))
% 0.42/0.63          | ~ (v1_funct_1 @ X5)
% 0.42/0.63          | ~ (v1_relat_1 @ X5))),
% 0.42/0.63      inference('cnf', [status(esa)], [t9_funct_1])).
% 0.42/0.63  thf('49', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         (((sk_A) != (k1_relat_1 @ X0))
% 0.42/0.63          | ~ (v1_relat_1 @ sk_C_1)
% 0.42/0.63          | ~ (v1_funct_1 @ sk_C_1)
% 0.42/0.63          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 0.42/0.63          | ((sk_C_1) = (X0))
% 0.42/0.63          | ~ (v1_funct_1 @ X0)
% 0.42/0.63          | ~ (v1_relat_1 @ X0))),
% 0.42/0.63      inference('sup-', [status(thm)], ['47', '48'])).
% 0.42/0.63  thf('50', plain,
% 0.42/0.63      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf(cc1_relset_1, axiom,
% 0.42/0.63    (![A:$i,B:$i,C:$i]:
% 0.42/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.63       ( v1_relat_1 @ C ) ))).
% 0.42/0.63  thf('51', plain,
% 0.42/0.63      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.42/0.63         ((v1_relat_1 @ X6)
% 0.42/0.63          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.42/0.63      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.42/0.63  thf('52', plain, ((v1_relat_1 @ sk_C_1)),
% 0.42/0.63      inference('sup-', [status(thm)], ['50', '51'])).
% 0.42/0.63  thf('53', plain, ((v1_funct_1 @ sk_C_1)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('54', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.42/0.63      inference('demod', [status(thm)], ['41', '46'])).
% 0.42/0.63  thf('55', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         (((sk_A) != (k1_relat_1 @ X0))
% 0.42/0.63          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_A)
% 0.42/0.63          | ((sk_C_1) = (X0))
% 0.42/0.63          | ~ (v1_funct_1 @ X0)
% 0.42/0.63          | ~ (v1_relat_1 @ X0))),
% 0.42/0.63      inference('demod', [status(thm)], ['49', '52', '53', '54'])).
% 0.42/0.63  thf('56', plain,
% 0.42/0.63      ((((sk_A) != (sk_A))
% 0.42/0.63        | ~ (v1_relat_1 @ sk_D)
% 0.42/0.63        | ~ (v1_funct_1 @ sk_D)
% 0.42/0.63        | ((sk_C_1) = (sk_D))
% 0.42/0.63        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 0.42/0.63      inference('sup-', [status(thm)], ['34', '55'])).
% 0.42/0.63  thf('57', plain,
% 0.42/0.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('58', plain,
% 0.42/0.63      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.42/0.63         ((v1_relat_1 @ X6)
% 0.42/0.63          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.42/0.63      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.42/0.63  thf('59', plain, ((v1_relat_1 @ sk_D)),
% 0.42/0.63      inference('sup-', [status(thm)], ['57', '58'])).
% 0.42/0.63  thf('60', plain, ((v1_funct_1 @ sk_D)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('61', plain,
% 0.42/0.63      ((((sk_A) != (sk_A))
% 0.42/0.63        | ((sk_C_1) = (sk_D))
% 0.42/0.63        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 0.42/0.63      inference('demod', [status(thm)], ['56', '59', '60'])).
% 0.42/0.63  thf('62', plain,
% 0.42/0.63      (((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A) | ((sk_C_1) = (sk_D)))),
% 0.42/0.63      inference('simplify', [status(thm)], ['61'])).
% 0.42/0.63  thf(t1_subset, axiom,
% 0.42/0.63    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.42/0.63  thf('63', plain,
% 0.42/0.63      (![X2 : $i, X3 : $i]: ((m1_subset_1 @ X2 @ X3) | ~ (r2_hidden @ X2 @ X3))),
% 0.42/0.63      inference('cnf', [status(esa)], [t1_subset])).
% 0.42/0.63  thf('64', plain,
% 0.42/0.63      ((((sk_C_1) = (sk_D)) | (m1_subset_1 @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 0.42/0.63      inference('sup-', [status(thm)], ['62', '63'])).
% 0.42/0.63  thf('65', plain,
% 0.42/0.63      (![X27 : $i]:
% 0.42/0.63         (((k1_funct_1 @ sk_C_1 @ X27) = (k1_funct_1 @ sk_D @ X27))
% 0.42/0.63          | ~ (m1_subset_1 @ X27 @ sk_A))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('66', plain,
% 0.42/0.63      ((((sk_C_1) = (sk_D))
% 0.42/0.63        | ((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 0.42/0.63            = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))))),
% 0.42/0.63      inference('sup-', [status(thm)], ['64', '65'])).
% 0.42/0.63  thf('67', plain,
% 0.42/0.63      (((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 0.42/0.63         = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))),
% 0.42/0.63      inference('condensation', [status(thm)], ['66'])).
% 0.42/0.63  thf('68', plain,
% 0.42/0.63      (![X4 : $i, X5 : $i]:
% 0.42/0.63         (~ (v1_relat_1 @ X4)
% 0.42/0.63          | ~ (v1_funct_1 @ X4)
% 0.42/0.63          | ((X5) = (X4))
% 0.42/0.63          | ((k1_funct_1 @ X5 @ (sk_C @ X4 @ X5))
% 0.42/0.63              != (k1_funct_1 @ X4 @ (sk_C @ X4 @ X5)))
% 0.42/0.63          | ((k1_relat_1 @ X5) != (k1_relat_1 @ X4))
% 0.42/0.63          | ~ (v1_funct_1 @ X5)
% 0.42/0.63          | ~ (v1_relat_1 @ X5))),
% 0.42/0.63      inference('cnf', [status(esa)], [t9_funct_1])).
% 0.42/0.63  thf('69', plain,
% 0.42/0.63      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 0.42/0.63          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 0.42/0.63        | ~ (v1_relat_1 @ sk_C_1)
% 0.42/0.63        | ~ (v1_funct_1 @ sk_C_1)
% 0.42/0.63        | ((k1_relat_1 @ sk_C_1) != (k1_relat_1 @ sk_D))
% 0.42/0.63        | ((sk_C_1) = (sk_D))
% 0.42/0.63        | ~ (v1_funct_1 @ sk_D)
% 0.42/0.63        | ~ (v1_relat_1 @ sk_D))),
% 0.42/0.63      inference('sup-', [status(thm)], ['67', '68'])).
% 0.42/0.63  thf('70', plain, ((v1_relat_1 @ sk_C_1)),
% 0.42/0.63      inference('sup-', [status(thm)], ['50', '51'])).
% 0.42/0.63  thf('71', plain, ((v1_funct_1 @ sk_C_1)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('72', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.42/0.63      inference('demod', [status(thm)], ['41', '46'])).
% 0.42/0.63  thf('73', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.42/0.63      inference('demod', [status(thm)], ['7', '33'])).
% 0.42/0.63  thf('74', plain, ((v1_funct_1 @ sk_D)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('75', plain, ((v1_relat_1 @ sk_D)),
% 0.42/0.63      inference('sup-', [status(thm)], ['57', '58'])).
% 0.42/0.63  thf('76', plain,
% 0.42/0.63      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 0.42/0.63          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 0.42/0.63        | ((sk_A) != (sk_A))
% 0.42/0.63        | ((sk_C_1) = (sk_D)))),
% 0.42/0.63      inference('demod', [status(thm)],
% 0.42/0.63                ['69', '70', '71', '72', '73', '74', '75'])).
% 0.42/0.63  thf('77', plain, (((sk_C_1) = (sk_D))),
% 0.42/0.63      inference('simplify', [status(thm)], ['76'])).
% 0.42/0.63  thf('78', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1)),
% 0.42/0.63      inference('sup-', [status(thm)], ['11', '13'])).
% 0.42/0.63  thf('79', plain, ($false),
% 0.42/0.63      inference('demod', [status(thm)], ['0', '77', '78'])).
% 0.42/0.63  
% 0.42/0.63  % SZS output end Refutation
% 0.42/0.63  
% 0.42/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
