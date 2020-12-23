%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tvGJSudF2o

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:38 EST 2020

% Result     : Theorem 1.97s
% Output     : Refutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 568 expanded)
%              Number of leaves         :   37 ( 182 expanded)
%              Depth                    :   23
%              Number of atoms          : 1076 (8451 expanded)
%              Number of equality atoms :   87 ( 421 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( r2_relset_1 @ X20 @ X21 @ X19 @ X22 )
      | ( X19 != X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('3',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_relset_1 @ X20 @ X21 @ X22 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['1','3'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('5',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

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

thf('6',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('8',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('14',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','15'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('17',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ( sk_C_1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('20',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('21',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_C_1 = X0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('25',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('27',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('28',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf('31',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ X0 @ sk_D )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','32'])).

thf('34',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_D )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','41'])).

thf('43',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('44',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('46',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['33','46'])).

thf('48',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['1','3'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ( sk_C_1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('50',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('52',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_C_1 = X0 )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('56',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('59',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['53','60'])).

thf('62',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ X0 @ sk_D )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['48','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_D )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','41'])).

thf('66',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('67',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('69',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['64','69'])).

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

thf('71',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X12 = X11 )
      | ( r2_hidden @ ( sk_C @ X11 @ X12 ) @ ( k1_relat_1 @ X12 ) )
      | ( ( k1_relat_1 @ X12 )
       != ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('74',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('75',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['64','69'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_A )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['72','75','76','77'])).

thf('79',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['47','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('82',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['79','82','83'])).

thf('85',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X31: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ X31 )
        = ( k1_funct_1 @ sk_D @ X31 ) )
      | ~ ( r2_hidden @ X31 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( sk_C_1 = sk_D )
    | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ),
    inference(condensation,[status(thm)],['87'])).

thf('89',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X12 = X11 )
      | ( ( k1_funct_1 @ X12 @ ( sk_C @ X11 @ X12 ) )
       != ( k1_funct_1 @ X11 @ ( sk_C @ X11 @ X12 ) ) )
      | ( ( k1_relat_1 @ X12 )
       != ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('90',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_1 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['73','74'])).

thf('92',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['64','69'])).

thf('94',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['33','46'])).

thf('95',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['80','81'])).

thf('97',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(demod,[status(thm)],['90','91','92','93','94','95','96'])).

thf('98',plain,(
    sk_C_1 = sk_D ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_relset_1 @ X20 @ X21 @ X22 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('101',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    $false ),
    inference(demod,[status(thm)],['0','98','101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tvGJSudF2o
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:05:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.97/2.19  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.97/2.19  % Solved by: fo/fo7.sh
% 1.97/2.19  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.97/2.19  % done 1737 iterations in 1.721s
% 1.97/2.19  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.97/2.19  % SZS output start Refutation
% 1.97/2.19  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.97/2.19  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.97/2.19  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.97/2.19  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.97/2.19  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.97/2.19  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.97/2.19  thf(sk_A_type, type, sk_A: $i).
% 1.97/2.19  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.97/2.19  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.97/2.19  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.97/2.19  thf(sk_B_type, type, sk_B: $i > $i).
% 1.97/2.19  thf(sk_D_type, type, sk_D: $i).
% 1.97/2.19  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.97/2.19  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.97/2.19  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.97/2.19  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.97/2.19  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.97/2.19  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.97/2.19  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.97/2.19  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.97/2.19  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.97/2.19  thf(t18_funct_2, conjecture,
% 1.97/2.19    (![A:$i,B:$i,C:$i]:
% 1.97/2.19     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.97/2.19         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.97/2.19       ( ![D:$i]:
% 1.97/2.19         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.97/2.19             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.97/2.19           ( ( ![E:$i]:
% 1.97/2.19               ( ( r2_hidden @ E @ A ) =>
% 1.97/2.19                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 1.97/2.19             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 1.97/2.19  thf(zf_stmt_0, negated_conjecture,
% 1.97/2.19    (~( ![A:$i,B:$i,C:$i]:
% 1.97/2.19        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.97/2.19            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.97/2.19          ( ![D:$i]:
% 1.97/2.19            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.97/2.19                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.97/2.19              ( ( ![E:$i]:
% 1.97/2.19                  ( ( r2_hidden @ E @ A ) =>
% 1.97/2.19                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 1.97/2.19                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 1.97/2.19    inference('cnf.neg', [status(esa)], [t18_funct_2])).
% 1.97/2.19  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('1', plain,
% 1.97/2.19      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf(redefinition_r2_relset_1, axiom,
% 1.97/2.19    (![A:$i,B:$i,C:$i,D:$i]:
% 1.97/2.19     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.97/2.19         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.97/2.19       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.97/2.19  thf('2', plain,
% 1.97/2.19      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.97/2.19         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.97/2.19          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.97/2.19          | (r2_relset_1 @ X20 @ X21 @ X19 @ X22)
% 1.97/2.19          | ((X19) != (X22)))),
% 1.97/2.19      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.97/2.19  thf('3', plain,
% 1.97/2.19      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.97/2.19         ((r2_relset_1 @ X20 @ X21 @ X22 @ X22)
% 1.97/2.19          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 1.97/2.19      inference('simplify', [status(thm)], ['2'])).
% 1.97/2.19  thf('4', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_D @ sk_D)),
% 1.97/2.19      inference('sup-', [status(thm)], ['1', '3'])).
% 1.97/2.19  thf(d1_xboole_0, axiom,
% 1.97/2.19    (![A:$i]:
% 1.97/2.19     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.97/2.19  thf('5', plain,
% 1.97/2.19      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.97/2.19      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.97/2.19  thf(d1_funct_2, axiom,
% 1.97/2.19    (![A:$i,B:$i,C:$i]:
% 1.97/2.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.97/2.19       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.97/2.19           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.97/2.19             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.97/2.19         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.97/2.19           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.97/2.19             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.97/2.19  thf(zf_stmt_1, axiom,
% 1.97/2.19    (![B:$i,A:$i]:
% 1.97/2.19     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.97/2.19       ( zip_tseitin_0 @ B @ A ) ))).
% 1.97/2.19  thf('6', plain,
% 1.97/2.19      (![X23 : $i, X24 : $i]:
% 1.97/2.19         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.97/2.19  thf(t113_zfmisc_1, axiom,
% 1.97/2.19    (![A:$i,B:$i]:
% 1.97/2.19     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.97/2.19       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.97/2.19  thf('7', plain,
% 1.97/2.19      (![X6 : $i, X7 : $i]:
% 1.97/2.19         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 1.97/2.19      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.97/2.19  thf('8', plain,
% 1.97/2.19      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 1.97/2.19      inference('simplify', [status(thm)], ['7'])).
% 1.97/2.19  thf('9', plain,
% 1.97/2.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.97/2.19         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 1.97/2.19      inference('sup+', [status(thm)], ['6', '8'])).
% 1.97/2.19  thf('10', plain,
% 1.97/2.19      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf(t5_subset, axiom,
% 1.97/2.19    (![A:$i,B:$i,C:$i]:
% 1.97/2.19     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 1.97/2.19          ( v1_xboole_0 @ C ) ) ))).
% 1.97/2.19  thf('11', plain,
% 1.97/2.19      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.97/2.19         (~ (r2_hidden @ X8 @ X9)
% 1.97/2.19          | ~ (v1_xboole_0 @ X10)
% 1.97/2.19          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 1.97/2.19      inference('cnf', [status(esa)], [t5_subset])).
% 1.97/2.19  thf('12', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 1.97/2.19          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 1.97/2.19      inference('sup-', [status(thm)], ['10', '11'])).
% 1.97/2.19  thf('13', plain,
% 1.97/2.19      (![X0 : $i, X1 : $i]:
% 1.97/2.19         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.97/2.19          | (zip_tseitin_0 @ sk_B_1 @ X1)
% 1.97/2.19          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 1.97/2.19      inference('sup-', [status(thm)], ['9', '12'])).
% 1.97/2.19  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.97/2.19  thf('14', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.97/2.19      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.97/2.19  thf('15', plain,
% 1.97/2.19      (![X0 : $i, X1 : $i]:
% 1.97/2.19         ((zip_tseitin_0 @ sk_B_1 @ X1) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 1.97/2.19      inference('demod', [status(thm)], ['13', '14'])).
% 1.97/2.19  thf('16', plain,
% 1.97/2.19      (![X0 : $i]: ((v1_xboole_0 @ sk_C_1) | (zip_tseitin_0 @ sk_B_1 @ X0))),
% 1.97/2.19      inference('sup-', [status(thm)], ['5', '15'])).
% 1.97/2.19  thf(t8_boole, axiom,
% 1.97/2.19    (![A:$i,B:$i]:
% 1.97/2.19     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 1.97/2.19  thf('17', plain,
% 1.97/2.19      (![X3 : $i, X4 : $i]:
% 1.97/2.19         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 1.97/2.19      inference('cnf', [status(esa)], [t8_boole])).
% 1.97/2.19  thf('18', plain,
% 1.97/2.19      (![X0 : $i, X1 : $i]:
% 1.97/2.19         ((zip_tseitin_0 @ sk_B_1 @ X1)
% 1.97/2.19          | ((sk_C_1) = (X0))
% 1.97/2.19          | ~ (v1_xboole_0 @ X0))),
% 1.97/2.19      inference('sup-', [status(thm)], ['16', '17'])).
% 1.97/2.19  thf('19', plain,
% 1.97/2.19      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.97/2.19  thf(zf_stmt_3, axiom,
% 1.97/2.19    (![C:$i,B:$i,A:$i]:
% 1.97/2.19     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.97/2.19       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.97/2.19  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.97/2.19  thf(zf_stmt_5, axiom,
% 1.97/2.19    (![A:$i,B:$i,C:$i]:
% 1.97/2.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.97/2.19       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.97/2.19         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.97/2.19           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.97/2.19             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.97/2.19  thf('20', plain,
% 1.97/2.19      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.97/2.19         (~ (zip_tseitin_0 @ X28 @ X29)
% 1.97/2.19          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 1.97/2.19          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.97/2.19  thf('21', plain,
% 1.97/2.19      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.97/2.19        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 1.97/2.19      inference('sup-', [status(thm)], ['19', '20'])).
% 1.97/2.19  thf('22', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         (~ (v1_xboole_0 @ X0)
% 1.97/2.19          | ((sk_C_1) = (X0))
% 1.97/2.19          | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 1.97/2.19      inference('sup-', [status(thm)], ['18', '21'])).
% 1.97/2.19  thf('23', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('24', plain,
% 1.97/2.19      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.97/2.19         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 1.97/2.19          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 1.97/2.19          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.97/2.19  thf('25', plain,
% 1.97/2.19      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.97/2.19        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 1.97/2.19      inference('sup-', [status(thm)], ['23', '24'])).
% 1.97/2.19  thf('26', plain,
% 1.97/2.19      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf(redefinition_k1_relset_1, axiom,
% 1.97/2.19    (![A:$i,B:$i,C:$i]:
% 1.97/2.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.97/2.19       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.97/2.19  thf('27', plain,
% 1.97/2.19      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.97/2.19         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 1.97/2.19          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.97/2.19      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.97/2.19  thf('28', plain,
% 1.97/2.19      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.97/2.19      inference('sup-', [status(thm)], ['26', '27'])).
% 1.97/2.19  thf('29', plain,
% 1.97/2.19      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.97/2.19        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.97/2.19      inference('demod', [status(thm)], ['25', '28'])).
% 1.97/2.19  thf('30', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         (((sk_C_1) = (X0))
% 1.97/2.19          | ~ (v1_xboole_0 @ X0)
% 1.97/2.19          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.97/2.19      inference('sup-', [status(thm)], ['22', '29'])).
% 1.97/2.19  thf('31', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('32', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         (~ (r2_relset_1 @ sk_A @ sk_B_1 @ X0 @ sk_D)
% 1.97/2.19          | ((sk_A) = (k1_relat_1 @ sk_D))
% 1.97/2.19          | ~ (v1_xboole_0 @ X0))),
% 1.97/2.19      inference('sup-', [status(thm)], ['30', '31'])).
% 1.97/2.19  thf('33', plain, ((~ (v1_xboole_0 @ sk_D) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.97/2.19      inference('sup-', [status(thm)], ['4', '32'])).
% 1.97/2.19  thf('34', plain,
% 1.97/2.19      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.97/2.19      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.97/2.19  thf('35', plain,
% 1.97/2.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.97/2.19         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 1.97/2.19      inference('sup+', [status(thm)], ['6', '8'])).
% 1.97/2.19  thf('36', plain,
% 1.97/2.19      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('37', plain,
% 1.97/2.19      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.97/2.19         (~ (r2_hidden @ X8 @ X9)
% 1.97/2.19          | ~ (v1_xboole_0 @ X10)
% 1.97/2.19          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 1.97/2.19      inference('cnf', [status(esa)], [t5_subset])).
% 1.97/2.19  thf('38', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 1.97/2.19          | ~ (r2_hidden @ X0 @ sk_D))),
% 1.97/2.19      inference('sup-', [status(thm)], ['36', '37'])).
% 1.97/2.19  thf('39', plain,
% 1.97/2.19      (![X0 : $i, X1 : $i]:
% 1.97/2.19         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.97/2.19          | (zip_tseitin_0 @ sk_B_1 @ X1)
% 1.97/2.19          | ~ (r2_hidden @ X0 @ sk_D))),
% 1.97/2.19      inference('sup-', [status(thm)], ['35', '38'])).
% 1.97/2.19  thf('40', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.97/2.19      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.97/2.19  thf('41', plain,
% 1.97/2.19      (![X0 : $i, X1 : $i]:
% 1.97/2.19         ((zip_tseitin_0 @ sk_B_1 @ X1) | ~ (r2_hidden @ X0 @ sk_D))),
% 1.97/2.19      inference('demod', [status(thm)], ['39', '40'])).
% 1.97/2.19  thf('42', plain,
% 1.97/2.19      (![X0 : $i]: ((v1_xboole_0 @ sk_D) | (zip_tseitin_0 @ sk_B_1 @ X0))),
% 1.97/2.19      inference('sup-', [status(thm)], ['34', '41'])).
% 1.97/2.19  thf('43', plain,
% 1.97/2.19      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.97/2.19        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 1.97/2.19      inference('sup-', [status(thm)], ['19', '20'])).
% 1.97/2.19  thf('44', plain,
% 1.97/2.19      (((v1_xboole_0 @ sk_D) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 1.97/2.19      inference('sup-', [status(thm)], ['42', '43'])).
% 1.97/2.19  thf('45', plain,
% 1.97/2.19      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.97/2.19        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.97/2.19      inference('demod', [status(thm)], ['25', '28'])).
% 1.97/2.19  thf('46', plain, (((v1_xboole_0 @ sk_D) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.97/2.19      inference('sup-', [status(thm)], ['44', '45'])).
% 1.97/2.19  thf('47', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 1.97/2.19      inference('clc', [status(thm)], ['33', '46'])).
% 1.97/2.19  thf('48', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_D @ sk_D)),
% 1.97/2.19      inference('sup-', [status(thm)], ['1', '3'])).
% 1.97/2.19  thf('49', plain,
% 1.97/2.19      (![X0 : $i, X1 : $i]:
% 1.97/2.19         ((zip_tseitin_0 @ sk_B_1 @ X1)
% 1.97/2.19          | ((sk_C_1) = (X0))
% 1.97/2.19          | ~ (v1_xboole_0 @ X0))),
% 1.97/2.19      inference('sup-', [status(thm)], ['16', '17'])).
% 1.97/2.19  thf('50', plain,
% 1.97/2.19      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('51', plain,
% 1.97/2.19      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.97/2.19         (~ (zip_tseitin_0 @ X28 @ X29)
% 1.97/2.19          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 1.97/2.19          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.97/2.19  thf('52', plain,
% 1.97/2.19      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 1.97/2.19        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 1.97/2.19      inference('sup-', [status(thm)], ['50', '51'])).
% 1.97/2.19  thf('53', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         (~ (v1_xboole_0 @ X0)
% 1.97/2.19          | ((sk_C_1) = (X0))
% 1.97/2.19          | (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A))),
% 1.97/2.19      inference('sup-', [status(thm)], ['49', '52'])).
% 1.97/2.19  thf('54', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('55', plain,
% 1.97/2.19      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.97/2.19         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 1.97/2.19          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 1.97/2.19          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.97/2.19  thf('56', plain,
% 1.97/2.19      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 1.97/2.19        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 1.97/2.19      inference('sup-', [status(thm)], ['54', '55'])).
% 1.97/2.19  thf('57', plain,
% 1.97/2.19      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('58', plain,
% 1.97/2.19      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.97/2.19         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 1.97/2.19          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.97/2.19      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.97/2.19  thf('59', plain,
% 1.97/2.19      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 1.97/2.19      inference('sup-', [status(thm)], ['57', '58'])).
% 1.97/2.19  thf('60', plain,
% 1.97/2.19      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 1.97/2.19        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.97/2.19      inference('demod', [status(thm)], ['56', '59'])).
% 1.97/2.19  thf('61', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         (((sk_C_1) = (X0))
% 1.97/2.19          | ~ (v1_xboole_0 @ X0)
% 1.97/2.19          | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.97/2.19      inference('sup-', [status(thm)], ['53', '60'])).
% 1.97/2.19  thf('62', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('63', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         (~ (r2_relset_1 @ sk_A @ sk_B_1 @ X0 @ sk_D)
% 1.97/2.19          | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 1.97/2.19          | ~ (v1_xboole_0 @ X0))),
% 1.97/2.19      inference('sup-', [status(thm)], ['61', '62'])).
% 1.97/2.19  thf('64', plain,
% 1.97/2.19      ((~ (v1_xboole_0 @ sk_D) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.97/2.19      inference('sup-', [status(thm)], ['48', '63'])).
% 1.97/2.19  thf('65', plain,
% 1.97/2.19      (![X0 : $i]: ((v1_xboole_0 @ sk_D) | (zip_tseitin_0 @ sk_B_1 @ X0))),
% 1.97/2.19      inference('sup-', [status(thm)], ['34', '41'])).
% 1.97/2.19  thf('66', plain,
% 1.97/2.19      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 1.97/2.19        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 1.97/2.19      inference('sup-', [status(thm)], ['50', '51'])).
% 1.97/2.19  thf('67', plain,
% 1.97/2.19      (((v1_xboole_0 @ sk_D) | (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A))),
% 1.97/2.19      inference('sup-', [status(thm)], ['65', '66'])).
% 1.97/2.19  thf('68', plain,
% 1.97/2.19      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 1.97/2.19        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.97/2.19      inference('demod', [status(thm)], ['56', '59'])).
% 1.97/2.19  thf('69', plain, (((v1_xboole_0 @ sk_D) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.97/2.19      inference('sup-', [status(thm)], ['67', '68'])).
% 1.97/2.19  thf('70', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 1.97/2.19      inference('clc', [status(thm)], ['64', '69'])).
% 1.97/2.19  thf(t9_funct_1, axiom,
% 1.97/2.19    (![A:$i]:
% 1.97/2.19     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.97/2.19       ( ![B:$i]:
% 1.97/2.19         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.97/2.19           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 1.97/2.19               ( ![C:$i]:
% 1.97/2.19                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 1.97/2.19                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 1.97/2.19             ( ( A ) = ( B ) ) ) ) ) ))).
% 1.97/2.19  thf('71', plain,
% 1.97/2.19      (![X11 : $i, X12 : $i]:
% 1.97/2.19         (~ (v1_relat_1 @ X11)
% 1.97/2.19          | ~ (v1_funct_1 @ X11)
% 1.97/2.19          | ((X12) = (X11))
% 1.97/2.19          | (r2_hidden @ (sk_C @ X11 @ X12) @ (k1_relat_1 @ X12))
% 1.97/2.19          | ((k1_relat_1 @ X12) != (k1_relat_1 @ X11))
% 1.97/2.19          | ~ (v1_funct_1 @ X12)
% 1.97/2.19          | ~ (v1_relat_1 @ X12))),
% 1.97/2.19      inference('cnf', [status(esa)], [t9_funct_1])).
% 1.97/2.19  thf('72', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         (((sk_A) != (k1_relat_1 @ X0))
% 1.97/2.19          | ~ (v1_relat_1 @ sk_C_1)
% 1.97/2.19          | ~ (v1_funct_1 @ sk_C_1)
% 1.97/2.19          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 1.97/2.19          | ((sk_C_1) = (X0))
% 1.97/2.19          | ~ (v1_funct_1 @ X0)
% 1.97/2.19          | ~ (v1_relat_1 @ X0))),
% 1.97/2.19      inference('sup-', [status(thm)], ['70', '71'])).
% 1.97/2.19  thf('73', plain,
% 1.97/2.19      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf(cc1_relset_1, axiom,
% 1.97/2.19    (![A:$i,B:$i,C:$i]:
% 1.97/2.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.97/2.19       ( v1_relat_1 @ C ) ))).
% 1.97/2.19  thf('74', plain,
% 1.97/2.19      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.97/2.19         ((v1_relat_1 @ X13)
% 1.97/2.19          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.97/2.19      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.97/2.19  thf('75', plain, ((v1_relat_1 @ sk_C_1)),
% 1.97/2.19      inference('sup-', [status(thm)], ['73', '74'])).
% 1.97/2.19  thf('76', plain, ((v1_funct_1 @ sk_C_1)),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('77', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 1.97/2.19      inference('clc', [status(thm)], ['64', '69'])).
% 1.97/2.19  thf('78', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         (((sk_A) != (k1_relat_1 @ X0))
% 1.97/2.19          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_A)
% 1.97/2.19          | ((sk_C_1) = (X0))
% 1.97/2.19          | ~ (v1_funct_1 @ X0)
% 1.97/2.19          | ~ (v1_relat_1 @ X0))),
% 1.97/2.19      inference('demod', [status(thm)], ['72', '75', '76', '77'])).
% 1.97/2.19  thf('79', plain,
% 1.97/2.19      ((((sk_A) != (sk_A))
% 1.97/2.19        | ~ (v1_relat_1 @ sk_D)
% 1.97/2.19        | ~ (v1_funct_1 @ sk_D)
% 1.97/2.19        | ((sk_C_1) = (sk_D))
% 1.97/2.19        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 1.97/2.19      inference('sup-', [status(thm)], ['47', '78'])).
% 1.97/2.19  thf('80', plain,
% 1.97/2.19      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('81', plain,
% 1.97/2.19      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.97/2.19         ((v1_relat_1 @ X13)
% 1.97/2.19          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.97/2.19      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.97/2.19  thf('82', plain, ((v1_relat_1 @ sk_D)),
% 1.97/2.19      inference('sup-', [status(thm)], ['80', '81'])).
% 1.97/2.19  thf('83', plain, ((v1_funct_1 @ sk_D)),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('84', plain,
% 1.97/2.19      ((((sk_A) != (sk_A))
% 1.97/2.19        | ((sk_C_1) = (sk_D))
% 1.97/2.19        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 1.97/2.19      inference('demod', [status(thm)], ['79', '82', '83'])).
% 1.97/2.19  thf('85', plain,
% 1.97/2.19      (((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A) | ((sk_C_1) = (sk_D)))),
% 1.97/2.19      inference('simplify', [status(thm)], ['84'])).
% 1.97/2.19  thf('86', plain,
% 1.97/2.19      (![X31 : $i]:
% 1.97/2.19         (((k1_funct_1 @ sk_C_1 @ X31) = (k1_funct_1 @ sk_D @ X31))
% 1.97/2.19          | ~ (r2_hidden @ X31 @ sk_A))),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('87', plain,
% 1.97/2.19      ((((sk_C_1) = (sk_D))
% 1.97/2.19        | ((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 1.97/2.19            = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))))),
% 1.97/2.19      inference('sup-', [status(thm)], ['85', '86'])).
% 1.97/2.19  thf('88', plain,
% 1.97/2.19      (((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 1.97/2.19         = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))),
% 1.97/2.19      inference('condensation', [status(thm)], ['87'])).
% 1.97/2.19  thf('89', plain,
% 1.97/2.19      (![X11 : $i, X12 : $i]:
% 1.97/2.19         (~ (v1_relat_1 @ X11)
% 1.97/2.19          | ~ (v1_funct_1 @ X11)
% 1.97/2.19          | ((X12) = (X11))
% 1.97/2.19          | ((k1_funct_1 @ X12 @ (sk_C @ X11 @ X12))
% 1.97/2.19              != (k1_funct_1 @ X11 @ (sk_C @ X11 @ X12)))
% 1.97/2.19          | ((k1_relat_1 @ X12) != (k1_relat_1 @ X11))
% 1.97/2.19          | ~ (v1_funct_1 @ X12)
% 1.97/2.19          | ~ (v1_relat_1 @ X12))),
% 1.97/2.19      inference('cnf', [status(esa)], [t9_funct_1])).
% 1.97/2.19  thf('90', plain,
% 1.97/2.19      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 1.97/2.19          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 1.97/2.19        | ~ (v1_relat_1 @ sk_C_1)
% 1.97/2.19        | ~ (v1_funct_1 @ sk_C_1)
% 1.97/2.19        | ((k1_relat_1 @ sk_C_1) != (k1_relat_1 @ sk_D))
% 1.97/2.19        | ((sk_C_1) = (sk_D))
% 1.97/2.19        | ~ (v1_funct_1 @ sk_D)
% 1.97/2.19        | ~ (v1_relat_1 @ sk_D))),
% 1.97/2.19      inference('sup-', [status(thm)], ['88', '89'])).
% 1.97/2.19  thf('91', plain, ((v1_relat_1 @ sk_C_1)),
% 1.97/2.19      inference('sup-', [status(thm)], ['73', '74'])).
% 1.97/2.19  thf('92', plain, ((v1_funct_1 @ sk_C_1)),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('93', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 1.97/2.19      inference('clc', [status(thm)], ['64', '69'])).
% 1.97/2.19  thf('94', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 1.97/2.19      inference('clc', [status(thm)], ['33', '46'])).
% 1.97/2.19  thf('95', plain, ((v1_funct_1 @ sk_D)),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('96', plain, ((v1_relat_1 @ sk_D)),
% 1.97/2.19      inference('sup-', [status(thm)], ['80', '81'])).
% 1.97/2.19  thf('97', plain,
% 1.97/2.19      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 1.97/2.19          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 1.97/2.19        | ((sk_A) != (sk_A))
% 1.97/2.19        | ((sk_C_1) = (sk_D)))),
% 1.97/2.19      inference('demod', [status(thm)],
% 1.97/2.19                ['90', '91', '92', '93', '94', '95', '96'])).
% 1.97/2.19  thf('98', plain, (((sk_C_1) = (sk_D))),
% 1.97/2.19      inference('simplify', [status(thm)], ['97'])).
% 1.97/2.19  thf('99', plain,
% 1.97/2.19      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('100', plain,
% 1.97/2.19      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.97/2.19         ((r2_relset_1 @ X20 @ X21 @ X22 @ X22)
% 1.97/2.19          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 1.97/2.19      inference('simplify', [status(thm)], ['2'])).
% 1.97/2.19  thf('101', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_C_1)),
% 1.97/2.19      inference('sup-', [status(thm)], ['99', '100'])).
% 1.97/2.19  thf('102', plain, ($false),
% 1.97/2.19      inference('demod', [status(thm)], ['0', '98', '101'])).
% 1.97/2.19  
% 1.97/2.19  % SZS output end Refutation
% 1.97/2.19  
% 1.97/2.20  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
