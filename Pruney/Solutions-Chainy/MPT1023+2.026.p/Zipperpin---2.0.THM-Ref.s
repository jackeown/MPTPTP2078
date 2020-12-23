%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JxECrBYq8X

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:32 EST 2020

% Result     : Theorem 3.45s
% Output     : Refutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 571 expanded)
%              Number of leaves         :   38 ( 183 expanded)
%              Depth                    :   25
%              Number of atoms          : 1096 (8471 expanded)
%              Number of equality atoms :   88 ( 422 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( r2_relset_1 @ X22 @ X23 @ X21 @ X24 )
      | ( X21 != X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('3',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_relset_1 @ X22 @ X23 @ X24 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
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
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
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

thf('11',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ( X27
        = ( k1_relset_1 @ X27 @ X28 @ X29 ) )
      | ~ ( zip_tseitin_1 @ X29 @ X28 @ X27 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ( X27
        = ( k1_relset_1 @ X27 @ X28 @ X29 ) )
      | ~ ( zip_tseitin_1 @ X29 @ X28 @ X27 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
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

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('86',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('87',plain,
    ( ( sk_C_1 = sk_D )
    | ( m1_subset_1 @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X33: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ X33 )
        = ( k1_funct_1 @ sk_D @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( sk_C_1 = sk_D )
    | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ),
    inference(condensation,[status(thm)],['89'])).

thf('91',plain,(
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

thf('92',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_1 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['73','74'])).

thf('94',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['64','69'])).

thf('96',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['33','46'])).

thf('97',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['80','81'])).

thf('99',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(demod,[status(thm)],['92','93','94','95','96','97','98'])).

thf('100',plain,(
    sk_C_1 = sk_D ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_relset_1 @ X22 @ X23 @ X24 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('103',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    $false ),
    inference(demod,[status(thm)],['0','100','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JxECrBYq8X
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:57:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.45/3.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.45/3.65  % Solved by: fo/fo7.sh
% 3.45/3.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.45/3.65  % done 3409 iterations in 3.164s
% 3.45/3.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.45/3.65  % SZS output start Refutation
% 3.45/3.65  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 3.45/3.65  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.45/3.65  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.45/3.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.45/3.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.45/3.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.45/3.65  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.45/3.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.45/3.65  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.45/3.65  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.45/3.65  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.45/3.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.45/3.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.45/3.65  thf(sk_B_type, type, sk_B: $i > $i).
% 3.45/3.65  thf(sk_D_type, type, sk_D: $i).
% 3.45/3.65  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.45/3.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.45/3.65  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.45/3.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.45/3.65  thf(sk_A_type, type, sk_A: $i).
% 3.45/3.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.45/3.65  thf(t113_funct_2, conjecture,
% 3.45/3.65    (![A:$i,B:$i,C:$i]:
% 3.45/3.65     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.45/3.65         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.45/3.65       ( ![D:$i]:
% 3.45/3.65         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.45/3.65             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.45/3.65           ( ( ![E:$i]:
% 3.45/3.65               ( ( m1_subset_1 @ E @ A ) =>
% 3.45/3.65                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 3.45/3.65             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 3.45/3.65  thf(zf_stmt_0, negated_conjecture,
% 3.45/3.65    (~( ![A:$i,B:$i,C:$i]:
% 3.45/3.65        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.45/3.65            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.45/3.65          ( ![D:$i]:
% 3.45/3.65            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.45/3.65                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.45/3.65              ( ( ![E:$i]:
% 3.45/3.65                  ( ( m1_subset_1 @ E @ A ) =>
% 3.45/3.65                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 3.45/3.65                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 3.45/3.65    inference('cnf.neg', [status(esa)], [t113_funct_2])).
% 3.45/3.65  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.65  thf('1', plain,
% 3.45/3.65      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.65  thf(redefinition_r2_relset_1, axiom,
% 3.45/3.65    (![A:$i,B:$i,C:$i,D:$i]:
% 3.45/3.65     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.45/3.65         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.45/3.65       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.45/3.65  thf('2', plain,
% 3.45/3.65      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 3.45/3.65         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 3.45/3.65          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 3.45/3.65          | (r2_relset_1 @ X22 @ X23 @ X21 @ X24)
% 3.45/3.65          | ((X21) != (X24)))),
% 3.45/3.65      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.45/3.65  thf('3', plain,
% 3.45/3.65      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.45/3.65         ((r2_relset_1 @ X22 @ X23 @ X24 @ X24)
% 3.45/3.65          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 3.45/3.65      inference('simplify', [status(thm)], ['2'])).
% 3.45/3.65  thf('4', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_D @ sk_D)),
% 3.45/3.65      inference('sup-', [status(thm)], ['1', '3'])).
% 3.45/3.65  thf(d1_xboole_0, axiom,
% 3.45/3.65    (![A:$i]:
% 3.45/3.65     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 3.45/3.65  thf('5', plain,
% 3.45/3.65      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 3.45/3.65      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.45/3.65  thf(d1_funct_2, axiom,
% 3.45/3.65    (![A:$i,B:$i,C:$i]:
% 3.45/3.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.45/3.65       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.45/3.65           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.45/3.65             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.45/3.65         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.45/3.65           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.45/3.65             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.45/3.65  thf(zf_stmt_1, axiom,
% 3.45/3.65    (![B:$i,A:$i]:
% 3.45/3.65     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.45/3.65       ( zip_tseitin_0 @ B @ A ) ))).
% 3.45/3.65  thf('6', plain,
% 3.45/3.65      (![X25 : $i, X26 : $i]:
% 3.45/3.65         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.45/3.65  thf(t113_zfmisc_1, axiom,
% 3.45/3.65    (![A:$i,B:$i]:
% 3.45/3.65     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.45/3.65       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.45/3.65  thf('7', plain,
% 3.45/3.65      (![X6 : $i, X7 : $i]:
% 3.45/3.65         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 3.45/3.65      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.45/3.65  thf('8', plain,
% 3.45/3.65      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 3.45/3.65      inference('simplify', [status(thm)], ['7'])).
% 3.45/3.65  thf('9', plain,
% 3.45/3.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.45/3.65         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 3.45/3.65      inference('sup+', [status(thm)], ['6', '8'])).
% 3.45/3.65  thf('10', plain,
% 3.45/3.65      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.65  thf('11', plain,
% 3.45/3.65      (![X0 : $i]:
% 3.45/3.65         ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.45/3.65          | (zip_tseitin_0 @ sk_B_1 @ X0))),
% 3.45/3.65      inference('sup+', [status(thm)], ['9', '10'])).
% 3.45/3.65  thf(t5_subset, axiom,
% 3.45/3.65    (![A:$i,B:$i,C:$i]:
% 3.45/3.65     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 3.45/3.65          ( v1_xboole_0 @ C ) ) ))).
% 3.45/3.65  thf('12', plain,
% 3.45/3.65      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.45/3.65         (~ (r2_hidden @ X10 @ X11)
% 3.45/3.65          | ~ (v1_xboole_0 @ X12)
% 3.45/3.65          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 3.45/3.65      inference('cnf', [status(esa)], [t5_subset])).
% 3.45/3.65  thf('13', plain,
% 3.45/3.65      (![X0 : $i, X1 : $i]:
% 3.45/3.65         ((zip_tseitin_0 @ sk_B_1 @ X1)
% 3.45/3.65          | ~ (v1_xboole_0 @ k1_xboole_0)
% 3.45/3.65          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 3.45/3.65      inference('sup-', [status(thm)], ['11', '12'])).
% 3.45/3.65  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.45/3.65  thf('14', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.45/3.65      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.45/3.65  thf('15', plain,
% 3.45/3.65      (![X0 : $i, X1 : $i]:
% 3.45/3.65         ((zip_tseitin_0 @ sk_B_1 @ X1) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 3.45/3.65      inference('demod', [status(thm)], ['13', '14'])).
% 3.45/3.65  thf('16', plain,
% 3.45/3.65      (![X0 : $i]: ((v1_xboole_0 @ sk_C_1) | (zip_tseitin_0 @ sk_B_1 @ X0))),
% 3.45/3.65      inference('sup-', [status(thm)], ['5', '15'])).
% 3.45/3.65  thf(t8_boole, axiom,
% 3.45/3.65    (![A:$i,B:$i]:
% 3.45/3.65     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 3.45/3.65  thf('17', plain,
% 3.45/3.65      (![X3 : $i, X4 : $i]:
% 3.45/3.65         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 3.45/3.65      inference('cnf', [status(esa)], [t8_boole])).
% 3.45/3.65  thf('18', plain,
% 3.45/3.65      (![X0 : $i, X1 : $i]:
% 3.45/3.65         ((zip_tseitin_0 @ sk_B_1 @ X1)
% 3.45/3.65          | ((sk_C_1) = (X0))
% 3.45/3.65          | ~ (v1_xboole_0 @ X0))),
% 3.45/3.65      inference('sup-', [status(thm)], ['16', '17'])).
% 3.45/3.65  thf('19', plain,
% 3.45/3.65      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.65  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.45/3.65  thf(zf_stmt_3, axiom,
% 3.45/3.65    (![C:$i,B:$i,A:$i]:
% 3.45/3.65     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.45/3.65       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.45/3.65  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 3.45/3.65  thf(zf_stmt_5, axiom,
% 3.45/3.65    (![A:$i,B:$i,C:$i]:
% 3.45/3.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.45/3.65       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.45/3.65         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.45/3.65           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.45/3.65             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.45/3.65  thf('20', plain,
% 3.45/3.65      (![X30 : $i, X31 : $i, X32 : $i]:
% 3.45/3.65         (~ (zip_tseitin_0 @ X30 @ X31)
% 3.45/3.65          | (zip_tseitin_1 @ X32 @ X30 @ X31)
% 3.45/3.65          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.45/3.65  thf('21', plain,
% 3.45/3.65      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 3.45/3.65        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 3.45/3.65      inference('sup-', [status(thm)], ['19', '20'])).
% 3.45/3.65  thf('22', plain,
% 3.45/3.65      (![X0 : $i]:
% 3.45/3.65         (~ (v1_xboole_0 @ X0)
% 3.45/3.65          | ((sk_C_1) = (X0))
% 3.45/3.65          | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 3.45/3.65      inference('sup-', [status(thm)], ['18', '21'])).
% 3.45/3.65  thf('23', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.65  thf('24', plain,
% 3.45/3.65      (![X27 : $i, X28 : $i, X29 : $i]:
% 3.45/3.65         (~ (v1_funct_2 @ X29 @ X27 @ X28)
% 3.45/3.65          | ((X27) = (k1_relset_1 @ X27 @ X28 @ X29))
% 3.45/3.65          | ~ (zip_tseitin_1 @ X29 @ X28 @ X27))),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.45/3.65  thf('25', plain,
% 3.45/3.65      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 3.45/3.65        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 3.45/3.65      inference('sup-', [status(thm)], ['23', '24'])).
% 3.45/3.65  thf('26', plain,
% 3.45/3.65      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.65  thf(redefinition_k1_relset_1, axiom,
% 3.45/3.65    (![A:$i,B:$i,C:$i]:
% 3.45/3.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.45/3.65       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.45/3.65  thf('27', plain,
% 3.45/3.65      (![X18 : $i, X19 : $i, X20 : $i]:
% 3.45/3.65         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 3.45/3.65          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 3.45/3.65      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.45/3.65  thf('28', plain,
% 3.45/3.65      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 3.45/3.65      inference('sup-', [status(thm)], ['26', '27'])).
% 3.45/3.65  thf('29', plain,
% 3.45/3.65      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 3.45/3.65        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.45/3.65      inference('demod', [status(thm)], ['25', '28'])).
% 3.45/3.65  thf('30', plain,
% 3.45/3.65      (![X0 : $i]:
% 3.45/3.65         (((sk_C_1) = (X0))
% 3.45/3.65          | ~ (v1_xboole_0 @ X0)
% 3.45/3.65          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.45/3.65      inference('sup-', [status(thm)], ['22', '29'])).
% 3.45/3.65  thf('31', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.65  thf('32', plain,
% 3.45/3.65      (![X0 : $i]:
% 3.45/3.65         (~ (r2_relset_1 @ sk_A @ sk_B_1 @ X0 @ sk_D)
% 3.45/3.65          | ((sk_A) = (k1_relat_1 @ sk_D))
% 3.45/3.65          | ~ (v1_xboole_0 @ X0))),
% 3.45/3.65      inference('sup-', [status(thm)], ['30', '31'])).
% 3.45/3.65  thf('33', plain, ((~ (v1_xboole_0 @ sk_D) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.45/3.65      inference('sup-', [status(thm)], ['4', '32'])).
% 3.45/3.65  thf('34', plain,
% 3.45/3.65      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 3.45/3.65      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.45/3.65  thf('35', plain,
% 3.45/3.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.45/3.65         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 3.45/3.65      inference('sup+', [status(thm)], ['6', '8'])).
% 3.45/3.65  thf('36', plain,
% 3.45/3.65      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.65  thf('37', plain,
% 3.45/3.65      (![X0 : $i]:
% 3.45/3.65         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.45/3.65          | (zip_tseitin_0 @ sk_B_1 @ X0))),
% 3.45/3.65      inference('sup+', [status(thm)], ['35', '36'])).
% 3.45/3.65  thf('38', plain,
% 3.45/3.65      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.45/3.65         (~ (r2_hidden @ X10 @ X11)
% 3.45/3.65          | ~ (v1_xboole_0 @ X12)
% 3.45/3.65          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 3.45/3.65      inference('cnf', [status(esa)], [t5_subset])).
% 3.45/3.65  thf('39', plain,
% 3.45/3.65      (![X0 : $i, X1 : $i]:
% 3.45/3.65         ((zip_tseitin_0 @ sk_B_1 @ X1)
% 3.45/3.65          | ~ (v1_xboole_0 @ k1_xboole_0)
% 3.45/3.65          | ~ (r2_hidden @ X0 @ sk_D))),
% 3.45/3.65      inference('sup-', [status(thm)], ['37', '38'])).
% 3.45/3.65  thf('40', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.45/3.65      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.45/3.65  thf('41', plain,
% 3.45/3.65      (![X0 : $i, X1 : $i]:
% 3.45/3.65         ((zip_tseitin_0 @ sk_B_1 @ X1) | ~ (r2_hidden @ X0 @ sk_D))),
% 3.45/3.65      inference('demod', [status(thm)], ['39', '40'])).
% 3.45/3.65  thf('42', plain,
% 3.45/3.65      (![X0 : $i]: ((v1_xboole_0 @ sk_D) | (zip_tseitin_0 @ sk_B_1 @ X0))),
% 3.45/3.65      inference('sup-', [status(thm)], ['34', '41'])).
% 3.45/3.65  thf('43', plain,
% 3.45/3.65      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 3.45/3.65        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 3.45/3.65      inference('sup-', [status(thm)], ['19', '20'])).
% 3.45/3.65  thf('44', plain,
% 3.45/3.65      (((v1_xboole_0 @ sk_D) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 3.45/3.65      inference('sup-', [status(thm)], ['42', '43'])).
% 3.45/3.65  thf('45', plain,
% 3.45/3.65      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 3.45/3.65        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.45/3.65      inference('demod', [status(thm)], ['25', '28'])).
% 3.45/3.65  thf('46', plain, (((v1_xboole_0 @ sk_D) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.45/3.65      inference('sup-', [status(thm)], ['44', '45'])).
% 3.45/3.65  thf('47', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 3.45/3.65      inference('clc', [status(thm)], ['33', '46'])).
% 3.45/3.65  thf('48', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_D @ sk_D)),
% 3.45/3.65      inference('sup-', [status(thm)], ['1', '3'])).
% 3.45/3.65  thf('49', plain,
% 3.45/3.65      (![X0 : $i, X1 : $i]:
% 3.45/3.65         ((zip_tseitin_0 @ sk_B_1 @ X1)
% 3.45/3.65          | ((sk_C_1) = (X0))
% 3.45/3.65          | ~ (v1_xboole_0 @ X0))),
% 3.45/3.65      inference('sup-', [status(thm)], ['16', '17'])).
% 3.45/3.65  thf('50', plain,
% 3.45/3.65      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.65  thf('51', plain,
% 3.45/3.65      (![X30 : $i, X31 : $i, X32 : $i]:
% 3.45/3.65         (~ (zip_tseitin_0 @ X30 @ X31)
% 3.45/3.65          | (zip_tseitin_1 @ X32 @ X30 @ X31)
% 3.45/3.65          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.45/3.65  thf('52', plain,
% 3.45/3.65      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 3.45/3.65        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 3.45/3.65      inference('sup-', [status(thm)], ['50', '51'])).
% 3.45/3.65  thf('53', plain,
% 3.45/3.65      (![X0 : $i]:
% 3.45/3.65         (~ (v1_xboole_0 @ X0)
% 3.45/3.65          | ((sk_C_1) = (X0))
% 3.45/3.65          | (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A))),
% 3.45/3.65      inference('sup-', [status(thm)], ['49', '52'])).
% 3.45/3.65  thf('54', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.65  thf('55', plain,
% 3.45/3.65      (![X27 : $i, X28 : $i, X29 : $i]:
% 3.45/3.65         (~ (v1_funct_2 @ X29 @ X27 @ X28)
% 3.45/3.65          | ((X27) = (k1_relset_1 @ X27 @ X28 @ X29))
% 3.45/3.65          | ~ (zip_tseitin_1 @ X29 @ X28 @ X27))),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.45/3.65  thf('56', plain,
% 3.45/3.65      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 3.45/3.65        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 3.45/3.65      inference('sup-', [status(thm)], ['54', '55'])).
% 3.45/3.65  thf('57', plain,
% 3.45/3.65      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.65  thf('58', plain,
% 3.45/3.65      (![X18 : $i, X19 : $i, X20 : $i]:
% 3.45/3.65         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 3.45/3.65          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 3.45/3.65      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.45/3.65  thf('59', plain,
% 3.45/3.65      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 3.45/3.65      inference('sup-', [status(thm)], ['57', '58'])).
% 3.45/3.65  thf('60', plain,
% 3.45/3.65      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 3.45/3.65        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 3.45/3.65      inference('demod', [status(thm)], ['56', '59'])).
% 3.45/3.65  thf('61', plain,
% 3.45/3.65      (![X0 : $i]:
% 3.45/3.65         (((sk_C_1) = (X0))
% 3.45/3.65          | ~ (v1_xboole_0 @ X0)
% 3.45/3.65          | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 3.45/3.65      inference('sup-', [status(thm)], ['53', '60'])).
% 3.45/3.65  thf('62', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.65  thf('63', plain,
% 3.45/3.65      (![X0 : $i]:
% 3.45/3.65         (~ (r2_relset_1 @ sk_A @ sk_B_1 @ X0 @ sk_D)
% 3.45/3.65          | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 3.45/3.65          | ~ (v1_xboole_0 @ X0))),
% 3.45/3.65      inference('sup-', [status(thm)], ['61', '62'])).
% 3.45/3.65  thf('64', plain,
% 3.45/3.65      ((~ (v1_xboole_0 @ sk_D) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 3.45/3.65      inference('sup-', [status(thm)], ['48', '63'])).
% 3.45/3.65  thf('65', plain,
% 3.45/3.65      (![X0 : $i]: ((v1_xboole_0 @ sk_D) | (zip_tseitin_0 @ sk_B_1 @ X0))),
% 3.45/3.65      inference('sup-', [status(thm)], ['34', '41'])).
% 3.45/3.65  thf('66', plain,
% 3.45/3.65      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 3.45/3.65        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 3.45/3.65      inference('sup-', [status(thm)], ['50', '51'])).
% 3.45/3.65  thf('67', plain,
% 3.45/3.65      (((v1_xboole_0 @ sk_D) | (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A))),
% 3.45/3.65      inference('sup-', [status(thm)], ['65', '66'])).
% 3.45/3.65  thf('68', plain,
% 3.45/3.65      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 3.45/3.65        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 3.45/3.65      inference('demod', [status(thm)], ['56', '59'])).
% 3.45/3.65  thf('69', plain, (((v1_xboole_0 @ sk_D) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 3.45/3.65      inference('sup-', [status(thm)], ['67', '68'])).
% 3.45/3.65  thf('70', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 3.45/3.65      inference('clc', [status(thm)], ['64', '69'])).
% 3.45/3.65  thf(t9_funct_1, axiom,
% 3.45/3.65    (![A:$i]:
% 3.45/3.65     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.45/3.65       ( ![B:$i]:
% 3.45/3.65         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.45/3.65           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 3.45/3.65               ( ![C:$i]:
% 3.45/3.65                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 3.45/3.65                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 3.45/3.65             ( ( A ) = ( B ) ) ) ) ) ))).
% 3.45/3.65  thf('71', plain,
% 3.45/3.65      (![X13 : $i, X14 : $i]:
% 3.45/3.65         (~ (v1_relat_1 @ X13)
% 3.45/3.65          | ~ (v1_funct_1 @ X13)
% 3.45/3.65          | ((X14) = (X13))
% 3.45/3.65          | (r2_hidden @ (sk_C @ X13 @ X14) @ (k1_relat_1 @ X14))
% 3.45/3.65          | ((k1_relat_1 @ X14) != (k1_relat_1 @ X13))
% 3.45/3.65          | ~ (v1_funct_1 @ X14)
% 3.45/3.65          | ~ (v1_relat_1 @ X14))),
% 3.45/3.65      inference('cnf', [status(esa)], [t9_funct_1])).
% 3.45/3.65  thf('72', plain,
% 3.45/3.65      (![X0 : $i]:
% 3.45/3.65         (((sk_A) != (k1_relat_1 @ X0))
% 3.45/3.65          | ~ (v1_relat_1 @ sk_C_1)
% 3.45/3.65          | ~ (v1_funct_1 @ sk_C_1)
% 3.45/3.65          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 3.45/3.65          | ((sk_C_1) = (X0))
% 3.45/3.65          | ~ (v1_funct_1 @ X0)
% 3.45/3.65          | ~ (v1_relat_1 @ X0))),
% 3.45/3.65      inference('sup-', [status(thm)], ['70', '71'])).
% 3.45/3.65  thf('73', plain,
% 3.45/3.65      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.65  thf(cc1_relset_1, axiom,
% 3.45/3.65    (![A:$i,B:$i,C:$i]:
% 3.45/3.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.45/3.65       ( v1_relat_1 @ C ) ))).
% 3.45/3.65  thf('74', plain,
% 3.45/3.65      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.45/3.65         ((v1_relat_1 @ X15)
% 3.45/3.65          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 3.45/3.65      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.45/3.65  thf('75', plain, ((v1_relat_1 @ sk_C_1)),
% 3.45/3.65      inference('sup-', [status(thm)], ['73', '74'])).
% 3.45/3.65  thf('76', plain, ((v1_funct_1 @ sk_C_1)),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.65  thf('77', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 3.45/3.65      inference('clc', [status(thm)], ['64', '69'])).
% 3.45/3.65  thf('78', plain,
% 3.45/3.65      (![X0 : $i]:
% 3.45/3.65         (((sk_A) != (k1_relat_1 @ X0))
% 3.45/3.65          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_A)
% 3.45/3.65          | ((sk_C_1) = (X0))
% 3.45/3.65          | ~ (v1_funct_1 @ X0)
% 3.45/3.65          | ~ (v1_relat_1 @ X0))),
% 3.45/3.65      inference('demod', [status(thm)], ['72', '75', '76', '77'])).
% 3.45/3.65  thf('79', plain,
% 3.45/3.65      ((((sk_A) != (sk_A))
% 3.45/3.65        | ~ (v1_relat_1 @ sk_D)
% 3.45/3.65        | ~ (v1_funct_1 @ sk_D)
% 3.45/3.65        | ((sk_C_1) = (sk_D))
% 3.45/3.65        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 3.45/3.65      inference('sup-', [status(thm)], ['47', '78'])).
% 3.45/3.65  thf('80', plain,
% 3.45/3.65      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.65  thf('81', plain,
% 3.45/3.65      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.45/3.65         ((v1_relat_1 @ X15)
% 3.45/3.65          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 3.45/3.65      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.45/3.65  thf('82', plain, ((v1_relat_1 @ sk_D)),
% 3.45/3.65      inference('sup-', [status(thm)], ['80', '81'])).
% 3.45/3.65  thf('83', plain, ((v1_funct_1 @ sk_D)),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.65  thf('84', plain,
% 3.45/3.65      ((((sk_A) != (sk_A))
% 3.45/3.65        | ((sk_C_1) = (sk_D))
% 3.45/3.65        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 3.45/3.65      inference('demod', [status(thm)], ['79', '82', '83'])).
% 3.45/3.65  thf('85', plain,
% 3.45/3.65      (((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A) | ((sk_C_1) = (sk_D)))),
% 3.45/3.65      inference('simplify', [status(thm)], ['84'])).
% 3.45/3.65  thf(t1_subset, axiom,
% 3.45/3.65    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 3.45/3.65  thf('86', plain,
% 3.45/3.65      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 3.45/3.65      inference('cnf', [status(esa)], [t1_subset])).
% 3.45/3.65  thf('87', plain,
% 3.45/3.65      ((((sk_C_1) = (sk_D)) | (m1_subset_1 @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 3.45/3.65      inference('sup-', [status(thm)], ['85', '86'])).
% 3.45/3.65  thf('88', plain,
% 3.45/3.65      (![X33 : $i]:
% 3.45/3.65         (((k1_funct_1 @ sk_C_1 @ X33) = (k1_funct_1 @ sk_D @ X33))
% 3.45/3.65          | ~ (m1_subset_1 @ X33 @ sk_A))),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.65  thf('89', plain,
% 3.45/3.65      ((((sk_C_1) = (sk_D))
% 3.45/3.65        | ((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 3.45/3.65            = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))))),
% 3.45/3.65      inference('sup-', [status(thm)], ['87', '88'])).
% 3.45/3.65  thf('90', plain,
% 3.45/3.65      (((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 3.45/3.65         = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))),
% 3.45/3.65      inference('condensation', [status(thm)], ['89'])).
% 3.45/3.65  thf('91', plain,
% 3.45/3.65      (![X13 : $i, X14 : $i]:
% 3.45/3.65         (~ (v1_relat_1 @ X13)
% 3.45/3.65          | ~ (v1_funct_1 @ X13)
% 3.45/3.65          | ((X14) = (X13))
% 3.45/3.65          | ((k1_funct_1 @ X14 @ (sk_C @ X13 @ X14))
% 3.45/3.65              != (k1_funct_1 @ X13 @ (sk_C @ X13 @ X14)))
% 3.45/3.65          | ((k1_relat_1 @ X14) != (k1_relat_1 @ X13))
% 3.45/3.65          | ~ (v1_funct_1 @ X14)
% 3.45/3.65          | ~ (v1_relat_1 @ X14))),
% 3.45/3.65      inference('cnf', [status(esa)], [t9_funct_1])).
% 3.45/3.65  thf('92', plain,
% 3.45/3.65      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 3.45/3.65          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 3.45/3.65        | ~ (v1_relat_1 @ sk_C_1)
% 3.45/3.65        | ~ (v1_funct_1 @ sk_C_1)
% 3.45/3.65        | ((k1_relat_1 @ sk_C_1) != (k1_relat_1 @ sk_D))
% 3.45/3.65        | ((sk_C_1) = (sk_D))
% 3.45/3.65        | ~ (v1_funct_1 @ sk_D)
% 3.45/3.65        | ~ (v1_relat_1 @ sk_D))),
% 3.45/3.65      inference('sup-', [status(thm)], ['90', '91'])).
% 3.45/3.65  thf('93', plain, ((v1_relat_1 @ sk_C_1)),
% 3.45/3.65      inference('sup-', [status(thm)], ['73', '74'])).
% 3.45/3.65  thf('94', plain, ((v1_funct_1 @ sk_C_1)),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.65  thf('95', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 3.45/3.65      inference('clc', [status(thm)], ['64', '69'])).
% 3.45/3.65  thf('96', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 3.45/3.65      inference('clc', [status(thm)], ['33', '46'])).
% 3.45/3.65  thf('97', plain, ((v1_funct_1 @ sk_D)),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.65  thf('98', plain, ((v1_relat_1 @ sk_D)),
% 3.45/3.65      inference('sup-', [status(thm)], ['80', '81'])).
% 3.45/3.65  thf('99', plain,
% 3.45/3.65      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 3.45/3.65          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 3.45/3.65        | ((sk_A) != (sk_A))
% 3.45/3.65        | ((sk_C_1) = (sk_D)))),
% 3.45/3.65      inference('demod', [status(thm)],
% 3.45/3.65                ['92', '93', '94', '95', '96', '97', '98'])).
% 3.45/3.65  thf('100', plain, (((sk_C_1) = (sk_D))),
% 3.45/3.65      inference('simplify', [status(thm)], ['99'])).
% 3.45/3.65  thf('101', plain,
% 3.45/3.65      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.65  thf('102', plain,
% 3.45/3.65      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.45/3.65         ((r2_relset_1 @ X22 @ X23 @ X24 @ X24)
% 3.45/3.65          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 3.45/3.65      inference('simplify', [status(thm)], ['2'])).
% 3.45/3.65  thf('103', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_C_1)),
% 3.45/3.65      inference('sup-', [status(thm)], ['101', '102'])).
% 3.45/3.65  thf('104', plain, ($false),
% 3.45/3.65      inference('demod', [status(thm)], ['0', '100', '103'])).
% 3.45/3.65  
% 3.45/3.65  % SZS output end Refutation
% 3.45/3.65  
% 3.49/3.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
