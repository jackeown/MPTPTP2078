%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SDDxijnYWQ

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:53 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :  200 (2598 expanded)
%              Number of leaves         :   35 ( 683 expanded)
%              Depth                    :   27
%              Number of atoms          : 1923 (41217 expanded)
%              Number of equality atoms :  204 (4350 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t25_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_2 @ C @ A @ B )
        & ( v1_funct_1 @ C ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( v2_funct_1 @ C )
        <=> ! [D: $i,E: $i] :
              ( ( ( ( k1_funct_1 @ C @ D )
                  = ( k1_funct_1 @ C @ E ) )
                & ( r2_hidden @ E @ A )
                & ( r2_hidden @ D @ A ) )
             => ( D = E ) ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,D: $i,C: $i,A: $i] :
      ( ( zip_tseitin_2 @ E @ D @ C @ A )
    <=> ( ( r2_hidden @ D @ A )
        & ( r2_hidden @ E @ A )
        & ( ( k1_funct_1 @ C @ D )
          = ( k1_funct_1 @ C @ E ) ) ) ) )).

thf(zf_stmt_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( v2_funct_1 @ C )
        <=> ! [D: $i,E: $i] :
              ( ( zip_tseitin_2 @ E @ D @ C @ A )
             => ( D = E ) ) ) ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v2_funct_1 @ C )
          <=> ! [D: $i,E: $i] :
                ( ( zip_tseitin_2 @ E @ D @ C @ A )
               => ( D = E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[zf_stmt_2])).

thf('0',plain,
    ( ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('1',plain,
    ( ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
   <= ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_funct_1 @ X20 @ X17 )
        = ( k1_funct_1 @ X20 @ X19 ) )
      | ~ ( zip_tseitin_2 @ X19 @ X17 @ X20 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ sk_D )
      = ( k1_funct_1 @ sk_C_1 @ sk_E ) )
   <= ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( sk_D != sk_E )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('5',plain,
    ( ( sk_D != sk_E )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('7',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('9',plain,
    ( ( v1_funct_2 @ sk_C_1 @ k1_xboole_0 @ sk_B_1 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

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

thf(zf_stmt_4,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('10',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_funct_2 @ X13 @ X11 @ X12 )
      | ( X11
        = ( k1_relset_1 @ X11 @ X12 @ X13 ) )
      | ~ ( zip_tseitin_1 @ X13 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('11',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('13',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('14',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(zf_stmt_5,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_6,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( zip_tseitin_0 @ X14 @ X15 )
      | ( zip_tseitin_1 @ X16 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('16',plain,
    ( ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_B_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('18',plain,(
    ! [X9: $i] :
      ( zip_tseitin_0 @ X9 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','18'])).

thf('20',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k1_relset_1 @ X7 @ X8 @ X6 )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_1 )
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','19','22'])).

thf(d8_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
      <=> ! [B: $i,C: $i] :
            ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
              & ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
              & ( ( k1_funct_1 @ A @ B )
                = ( k1_funct_1 @ A @ C ) ) )
           => ( B = C ) ) ) ) )).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( sk_C @ X0 ) ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('27',plain,(
    ! [X17: $i,X19: $i,X20: $i,X21: $i] :
      ( ( zip_tseitin_2 @ X19 @ X17 @ X20 @ X21 )
      | ( ( k1_funct_1 @ X20 @ X17 )
       != ( k1_funct_1 @ X20 @ X19 ) )
      | ~ ( r2_hidden @ X19 @ X21 )
      | ~ ( r2_hidden @ X17 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) )
       != ( k1_funct_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ( zip_tseitin_2 @ X1 @ ( sk_C @ X0 ) @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_2 @ ( sk_B @ X1 ) @ ( sk_C @ X1 ) @ X1 @ X0 )
      | ~ ( r2_hidden @ ( sk_B @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X1 ) @ X0 )
      | ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(eq_res,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( zip_tseitin_2 @ ( sk_B @ X0 ) @ ( sk_C @ X0 ) @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ ( sk_B @ X0 ) @ ( sk_C @ X0 ) @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ( zip_tseitin_2 @ ( sk_B @ X0 ) @ ( sk_C @ X0 ) @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ ( sk_B @ X0 ) @ ( sk_C @ X0 ) @ X0 @ ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( ( zip_tseitin_2 @ ( sk_B @ sk_C_1 ) @ ( sk_C @ sk_C_1 ) @ sk_C_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( v2_funct_1 @ sk_C_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('36',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('37',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('39',plain,
    ( ( ( zip_tseitin_2 @ ( sk_B @ sk_C_1 ) @ ( sk_C @ sk_C_1 ) @ sk_C_1 @ k1_xboole_0 )
      | ( v2_funct_1 @ sk_C_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','37','38'])).

thf('40',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('41',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A )
      | ( X23 = X22 )
      | ( v2_funct_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('42',plain,
    ( ! [X22: $i,X23: $i] :
        ( ( X23 = X22 )
        | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) )
   <= ! [X22: $i,X23: $i] :
        ( ( X23 = X22 )
        | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_2 @ X1 @ X0 @ sk_C_1 @ k1_xboole_0 )
        | ( X0 = X1 ) )
   <= ( ! [X22: $i,X23: $i] :
          ( ( X23 = X22 )
          | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,
    ( ( ( v2_funct_1 @ sk_C_1 )
      | ( ( sk_C @ sk_C_1 )
        = ( sk_B @ sk_C_1 ) ) )
   <= ( ! [X22: $i,X23: $i] :
          ( ( X23 = X22 )
          | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','43'])).

thf('45',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('46',plain,
    ( ( ( sk_C @ sk_C_1 )
      = ( sk_B @ sk_C_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_C_1 )
      & ! [X22: $i,X23: $i] :
          ( ( X23 = X22 )
          | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != ( sk_C @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('48',plain,
    ( ( ( ( sk_B @ sk_C_1 )
       != ( sk_B @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( v2_funct_1 @ sk_C_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_C_1 )
      & ! [X22: $i,X23: $i] :
          ( ( X23 = X22 )
          | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('50',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('51',plain,
    ( ( ( ( sk_B @ sk_C_1 )
       != ( sk_B @ sk_C_1 ) )
      | ( v2_funct_1 @ sk_C_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_C_1 )
      & ! [X22: $i,X23: $i] :
          ( ( X23 = X22 )
          | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ( v2_funct_1 @ sk_C_1 )
   <= ( ~ ( v2_funct_1 @ sk_C_1 )
      & ! [X22: $i,X23: $i] :
          ( ( X23 = X22 )
          | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('54',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( v2_funct_1 @ sk_C_1 )
    | ~ ! [X22: $i,X23: $i] :
          ( ( X23 = X22 )
          | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
   <= ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('56',plain,
    ( ! [X22: $i,X23: $i] :
        ( ( X23 = X22 )
        | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) )
   <= ! [X22: $i,X23: $i] :
        ( ( X23 = X22 )
        | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['41'])).

thf('57',plain,
    ( ( sk_D = sk_E )
   <= ( ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
      & ! [X22: $i,X23: $i] :
          ( ( X23 = X22 )
          | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( sk_D != sk_E )
   <= ( sk_D != sk_E ) ),
    inference(split,[status(esa)],['4'])).

thf('59',plain,
    ( ( sk_D != sk_D )
   <= ( ( sk_D != sk_E )
      & ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
      & ! [X22: $i,X23: $i] :
          ( ( X23 = X22 )
          | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ! [X22: $i,X23: $i] :
          ( ( X23 = X22 )
          | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) )
    | ( sk_D = sk_E )
    | ~ ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ sk_D )
      = ( k1_funct_1 @ sk_C_1 @ sk_E ) )
   <= ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('62',plain,
    ( ( v2_funct_1 @ sk_C_1 )
   <= ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['41'])).

thf('63',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','19','22'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ X0 @ X1 )
       != ( k1_funct_1 @ X0 @ X2 ) )
      | ( X1 = X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('65',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
        | ~ ( v1_relat_1 @ sk_C_1 )
        | ~ ( v1_funct_1 @ sk_C_1 )
        | ( X0 = X1 )
        | ( ( k1_funct_1 @ sk_C_1 @ X0 )
         != ( k1_funct_1 @ sk_C_1 @ X1 ) )
        | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_C_1 ) )
        | ~ ( v2_funct_1 @ sk_C_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('67',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('68',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','19','22'])).

thf('69',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
        | ( X0 = X1 )
        | ( ( k1_funct_1 @ sk_C_1 @ X0 )
         != ( k1_funct_1 @ sk_C_1 @ X1 ) )
        | ~ ( r2_hidden @ X1 @ k1_xboole_0 )
        | ~ ( v2_funct_1 @ sk_C_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66','67','68'])).

thf('70',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
        | ( ( k1_funct_1 @ sk_C_1 @ X1 )
         != ( k1_funct_1 @ sk_C_1 @ X0 ) )
        | ( X1 = X0 )
        | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) )
   <= ( ( v2_funct_1 @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['62','69'])).

thf('71',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_C_1 @ sk_D )
         != ( k1_funct_1 @ sk_C_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_E @ k1_xboole_0 )
        | ( sk_E = X0 )
        | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) )
   <= ( ( v2_funct_1 @ sk_C_1 )
      & ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['61','70'])).

thf('72',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('73',plain,
    ( ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
   <= ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('74',plain,
    ( ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ k1_xboole_0 )
   <= ( ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X19 @ X18 )
      | ~ ( zip_tseitin_2 @ X19 @ X17 @ X20 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('76',plain,
    ( ( r2_hidden @ sk_E @ k1_xboole_0 )
   <= ( ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_C_1 @ sk_D )
         != ( k1_funct_1 @ sk_C_1 @ X0 ) )
        | ( sk_E = X0 )
        | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) )
   <= ( ( v2_funct_1 @ sk_C_1 )
      & ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['71','76'])).

thf('78',plain,
    ( ( ~ ( r2_hidden @ sk_D @ k1_xboole_0 )
      | ( sk_E = sk_D ) )
   <= ( ( v2_funct_1 @ sk_C_1 )
      & ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(eq_res,[status(thm)],['77'])).

thf('79',plain,
    ( ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ k1_xboole_0 )
   <= ( ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('80',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X17 @ X18 )
      | ~ ( zip_tseitin_2 @ X19 @ X17 @ X20 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('81',plain,
    ( ( r2_hidden @ sk_D @ k1_xboole_0 )
   <= ( ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( sk_E = sk_D )
   <= ( ( v2_funct_1 @ sk_C_1 )
      & ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['78','81'])).

thf('83',plain,
    ( ( sk_D != sk_E )
   <= ( sk_D != sk_E ) ),
    inference(split,[status(esa)],['4'])).

thf('84',plain,
    ( ( sk_D != sk_D )
   <= ( ( sk_D != sk_E )
      & ( v2_funct_1 @ sk_C_1 )
      & ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
    | ( sk_D = sk_E ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('87',plain,
    ( ( v2_funct_1 @ sk_C_1 )
    | ! [X22: $i,X23: $i] :
        ( ( X23 = X22 )
        | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['41'])).

thf('88',plain,(
    ! [X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('89',plain,(
    ! [X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('90',plain,(
    ! [X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 = X0 )
      | ( zip_tseitin_0 @ X0 @ X3 )
      | ( zip_tseitin_0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('93',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( zip_tseitin_0 @ X14 @ X15 )
      | ( zip_tseitin_1 @ X16 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('94',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( sk_B_1 = X1 )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('96',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('97',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
        | ( zip_tseitin_0 @ X0 @ X1 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ! [X1: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ X1 )
        | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('100',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_funct_2 @ X13 @ X11 @ X12 )
      | ( X11
        = ( k1_relset_1 @ X11 @ X12 @ X13 ) )
      | ~ ( zip_tseitin_1 @ X13 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('101',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('103',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k1_relset_1 @ X7 @ X8 @ X6 )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('104',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['101','104'])).

thf('106',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C_1 ) ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','105'])).

thf('107',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( zip_tseitin_0 @ X0 @ X1 )
        | ( zip_tseitin_0 @ X0 @ X2 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C_1 ) ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['88','106'])).

thf('108',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( sk_A
          = ( k1_relat_1 @ sk_C_1 ) )
        | ( zip_tseitin_0 @ X1 @ X0 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['107'])).

thf('109',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('110',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['101','104'])).

thf('112',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ ( sk_B @ X0 ) @ ( sk_C @ X0 ) @ X0 @ ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('114',plain,
    ( ( ( zip_tseitin_2 @ ( sk_B @ sk_C_1 ) @ ( sk_C @ sk_C_1 ) @ sk_C_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( v2_funct_1 @ sk_C_1 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('116',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('117',plain,
    ( ( ( zip_tseitin_2 @ ( sk_B @ sk_C_1 ) @ ( sk_C @ sk_C_1 ) @ sk_C_1 @ sk_A )
      | ( v2_funct_1 @ sk_C_1 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,
    ( ! [X22: $i,X23: $i] :
        ( ( X23 = X22 )
        | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) )
   <= ! [X22: $i,X23: $i] :
        ( ( X23 = X22 )
        | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['41'])).

thf('119',plain,
    ( ( ( v2_funct_1 @ sk_C_1 )
      | ( ( sk_C @ sk_C_1 )
        = ( sk_B @ sk_C_1 ) ) )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ! [X22: $i,X23: $i] :
          ( ( X23 = X22 )
          | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('121',plain,
    ( ( ( sk_C @ sk_C_1 )
      = ( sk_B @ sk_C_1 ) )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ~ ( v2_funct_1 @ sk_C_1 )
      & ! [X22: $i,X23: $i] :
          ( ( X23 = X22 )
          | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != ( sk_C @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('123',plain,
    ( ( ( ( sk_B @ sk_C_1 )
       != ( sk_B @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( v2_funct_1 @ sk_C_1 ) )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ~ ( v2_funct_1 @ sk_C_1 )
      & ! [X22: $i,X23: $i] :
          ( ( X23 = X22 )
          | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('125',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('126',plain,
    ( ( ( ( sk_B @ sk_C_1 )
       != ( sk_B @ sk_C_1 ) )
      | ( v2_funct_1 @ sk_C_1 ) )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ~ ( v2_funct_1 @ sk_C_1 )
      & ! [X22: $i,X23: $i] :
          ( ( X23 = X22 )
          | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,
    ( ( v2_funct_1 @ sk_C_1 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ~ ( v2_funct_1 @ sk_C_1 )
      & ! [X22: $i,X23: $i] :
          ( ( X23 = X22 )
          | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('129',plain,
    ( ~ ! [X22: $i,X23: $i] :
          ( ( X23 = X22 )
          | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,
    ( ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('131',plain,(
    zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['5','54','60','85','86','87','129','130'])).

thf('132',plain,
    ( ( k1_funct_1 @ sk_C_1 @ sk_D )
    = ( k1_funct_1 @ sk_C_1 @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['3','131'])).

thf('133',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('134',plain,
    ( ( v2_funct_1 @ sk_C_1 )
    | ( sk_A != k1_xboole_0 )
    | ~ ! [X22: $i,X23: $i] :
          ( ( X23 = X22 )
          | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('135',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['87','5','130','134','60','85','86'])).

thf('136',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['133','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ X0 @ X1 )
       != ( k1_funct_1 @ X0 @ X2 ) )
      | ( X1 = X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_C_1 @ X0 )
       != ( k1_funct_1 @ sk_C_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('140',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('141',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['133','135'])).

thf('142',plain,
    ( ( v2_funct_1 @ sk_C_1 )
   <= ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['41'])).

thf('143',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['5','130','54','60','85','86','87','129'])).

thf('144',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(simpl_trail,[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_C_1 @ X0 )
       != ( k1_funct_1 @ sk_C_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['138','139','140','141','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ sk_D )
       != ( k1_funct_1 @ sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_E = X0 )
      | ~ ( r2_hidden @ sk_E @ sk_A ) ) ),
    inference('sup-',[status(thm)],['132','145'])).

thf('147',plain,
    ( ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
   <= ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('148',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X19 @ X18 )
      | ~ ( zip_tseitin_2 @ X19 @ X17 @ X20 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('149',plain,
    ( ( r2_hidden @ sk_E @ sk_A )
   <= ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['5','54','60','85','86','87','129','130'])).

thf('151',plain,(
    r2_hidden @ sk_E @ sk_A ),
    inference(simpl_trail,[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ sk_D )
       != ( k1_funct_1 @ sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_E = X0 ) ) ),
    inference(demod,[status(thm)],['146','151'])).

thf('153',plain,
    ( ( sk_E = sk_D )
    | ~ ( r2_hidden @ sk_D @ sk_A ) ),
    inference(eq_res,[status(thm)],['152'])).

thf('154',plain,
    ( ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
   <= ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('155',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X17 @ X18 )
      | ~ ( zip_tseitin_2 @ X19 @ X17 @ X20 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('156',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
   <= ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['5','54','60','85','86','87','129','130'])).

thf('158',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(simpl_trail,[status(thm)],['156','157'])).

thf('159',plain,(
    sk_E = sk_D ),
    inference(demod,[status(thm)],['153','158'])).

thf('160',plain,
    ( ( sk_D != sk_E )
   <= ( sk_D != sk_E ) ),
    inference(split,[status(esa)],['4'])).

thf('161',plain,(
    sk_D != sk_E ),
    inference('sat_resolution*',[status(thm)],['130','54','60','85','86','87','129','5'])).

thf('162',plain,(
    sk_D != sk_E ),
    inference(simpl_trail,[status(thm)],['160','161'])).

thf('163',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['159','162'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SDDxijnYWQ
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:04:48 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.66/1.83  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.66/1.83  % Solved by: fo/fo7.sh
% 1.66/1.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.66/1.83  % done 1464 iterations in 1.383s
% 1.66/1.83  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.66/1.83  % SZS output start Refutation
% 1.66/1.83  thf(sk_A_type, type, sk_A: $i).
% 1.66/1.83  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.66/1.83  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.66/1.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.66/1.83  thf(sk_B_type, type, sk_B: $i > $i).
% 1.66/1.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.66/1.83  thf(sk_D_type, type, sk_D: $i).
% 1.66/1.83  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.66/1.83  thf(sk_E_type, type, sk_E: $i).
% 1.66/1.83  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.66/1.83  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.66/1.83  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.66/1.83  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.66/1.83  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.66/1.83  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $i > $o).
% 1.66/1.83  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.66/1.83  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.66/1.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.66/1.83  thf(sk_C_type, type, sk_C: $i > $i).
% 1.66/1.83  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.66/1.83  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.66/1.83  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.66/1.83  thf(t25_funct_2, conjecture,
% 1.66/1.83    (![A:$i,B:$i,C:$i]:
% 1.66/1.83     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.66/1.83         ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) =>
% 1.66/1.83       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.66/1.83         ( ( v2_funct_1 @ C ) <=>
% 1.66/1.83           ( ![D:$i,E:$i]:
% 1.66/1.83             ( ( ( ( k1_funct_1 @ C @ D ) = ( k1_funct_1 @ C @ E ) ) & 
% 1.66/1.83                 ( r2_hidden @ E @ A ) & ( r2_hidden @ D @ A ) ) =>
% 1.66/1.83               ( ( D ) = ( E ) ) ) ) ) ) ))).
% 1.66/1.83  thf(zf_stmt_0, type, zip_tseitin_2 : $i > $i > $i > $i > $o).
% 1.66/1.83  thf(zf_stmt_1, axiom,
% 1.66/1.83    (![E:$i,D:$i,C:$i,A:$i]:
% 1.66/1.83     ( ( zip_tseitin_2 @ E @ D @ C @ A ) <=>
% 1.66/1.83       ( ( r2_hidden @ D @ A ) & ( r2_hidden @ E @ A ) & 
% 1.66/1.83         ( ( k1_funct_1 @ C @ D ) = ( k1_funct_1 @ C @ E ) ) ) ))).
% 1.66/1.83  thf(zf_stmt_2, conjecture,
% 1.66/1.83    (![A:$i,B:$i,C:$i]:
% 1.66/1.83     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.66/1.83         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.66/1.83       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.66/1.83         ( ( v2_funct_1 @ C ) <=>
% 1.66/1.83           ( ![D:$i,E:$i]:
% 1.66/1.83             ( ( zip_tseitin_2 @ E @ D @ C @ A ) => ( ( D ) = ( E ) ) ) ) ) ) ))).
% 1.66/1.83  thf(zf_stmt_3, negated_conjecture,
% 1.66/1.83    (~( ![A:$i,B:$i,C:$i]:
% 1.66/1.83        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.66/1.83            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.66/1.83          ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.66/1.83            ( ( v2_funct_1 @ C ) <=>
% 1.66/1.83              ( ![D:$i,E:$i]:
% 1.66/1.83                ( ( zip_tseitin_2 @ E @ D @ C @ A ) => ( ( D ) = ( E ) ) ) ) ) ) ) )),
% 1.66/1.83    inference('cnf.neg', [status(esa)], [zf_stmt_2])).
% 1.66/1.83  thf('0', plain,
% 1.66/1.83      (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A) | ~ (v2_funct_1 @ sk_C_1))),
% 1.66/1.83      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.66/1.83  thf('1', plain,
% 1.66/1.83      (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A))
% 1.66/1.83         <= (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)))),
% 1.66/1.83      inference('split', [status(esa)], ['0'])).
% 1.66/1.83  thf('2', plain,
% 1.66/1.83      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.66/1.83         (((k1_funct_1 @ X20 @ X17) = (k1_funct_1 @ X20 @ X19))
% 1.66/1.83          | ~ (zip_tseitin_2 @ X19 @ X17 @ X20 @ X18))),
% 1.66/1.83      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.66/1.83  thf('3', plain,
% 1.66/1.83      ((((k1_funct_1 @ sk_C_1 @ sk_D) = (k1_funct_1 @ sk_C_1 @ sk_E)))
% 1.66/1.83         <= (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)))),
% 1.66/1.83      inference('sup-', [status(thm)], ['1', '2'])).
% 1.66/1.83  thf('4', plain, ((((sk_D) != (sk_E)) | ~ (v2_funct_1 @ sk_C_1))),
% 1.66/1.83      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.66/1.83  thf('5', plain, (~ (((sk_D) = (sk_E))) | ~ ((v2_funct_1 @ sk_C_1))),
% 1.66/1.83      inference('split', [status(esa)], ['4'])).
% 1.66/1.83  thf('6', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B_1) != (k1_xboole_0)))),
% 1.66/1.83      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.66/1.83  thf('7', plain, ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.66/1.83      inference('split', [status(esa)], ['6'])).
% 1.66/1.83  thf('8', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 1.66/1.83      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.66/1.83  thf('9', plain,
% 1.66/1.83      (((v1_funct_2 @ sk_C_1 @ k1_xboole_0 @ sk_B_1))
% 1.66/1.83         <= ((((sk_A) = (k1_xboole_0))))),
% 1.66/1.83      inference('sup+', [status(thm)], ['7', '8'])).
% 1.66/1.83  thf(d1_funct_2, axiom,
% 1.66/1.83    (![A:$i,B:$i,C:$i]:
% 1.66/1.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.66/1.83       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.66/1.83           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.66/1.83             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.66/1.83         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.66/1.83           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.66/1.83             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.66/1.83  thf(zf_stmt_4, axiom,
% 1.66/1.83    (![C:$i,B:$i,A:$i]:
% 1.66/1.83     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.66/1.83       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.66/1.83  thf('10', plain,
% 1.66/1.83      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.66/1.83         (~ (v1_funct_2 @ X13 @ X11 @ X12)
% 1.66/1.83          | ((X11) = (k1_relset_1 @ X11 @ X12 @ X13))
% 1.66/1.83          | ~ (zip_tseitin_1 @ X13 @ X12 @ X11))),
% 1.66/1.83      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.66/1.83  thf('11', plain,
% 1.66/1.83      (((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ k1_xboole_0)
% 1.66/1.83         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_1))))
% 1.66/1.83         <= ((((sk_A) = (k1_xboole_0))))),
% 1.66/1.83      inference('sup-', [status(thm)], ['9', '10'])).
% 1.66/1.83  thf('12', plain,
% 1.66/1.83      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.66/1.83      inference('split', [status(esa)], ['6'])).
% 1.66/1.83  thf('13', plain,
% 1.66/1.83      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.66/1.83      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.66/1.83  thf('14', plain,
% 1.66/1.83      (((m1_subset_1 @ sk_C_1 @ 
% 1.66/1.83         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 1.66/1.83         <= ((((sk_A) = (k1_xboole_0))))),
% 1.66/1.83      inference('sup+', [status(thm)], ['12', '13'])).
% 1.66/1.83  thf(zf_stmt_5, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.66/1.83  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $o).
% 1.66/1.83  thf(zf_stmt_7, axiom,
% 1.66/1.83    (![B:$i,A:$i]:
% 1.66/1.83     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.66/1.83       ( zip_tseitin_0 @ B @ A ) ))).
% 1.66/1.83  thf(zf_stmt_8, axiom,
% 1.66/1.83    (![A:$i,B:$i,C:$i]:
% 1.66/1.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.66/1.83       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.66/1.83         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.66/1.83           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.66/1.83             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.66/1.83  thf('15', plain,
% 1.66/1.83      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.66/1.83         (~ (zip_tseitin_0 @ X14 @ X15)
% 1.66/1.83          | (zip_tseitin_1 @ X16 @ X14 @ X15)
% 1.66/1.83          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X14))))),
% 1.66/1.83      inference('cnf', [status(esa)], [zf_stmt_8])).
% 1.66/1.83  thf('16', plain,
% 1.66/1.83      ((((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ k1_xboole_0)
% 1.66/1.83         | ~ (zip_tseitin_0 @ sk_B_1 @ k1_xboole_0)))
% 1.66/1.83         <= ((((sk_A) = (k1_xboole_0))))),
% 1.66/1.83      inference('sup-', [status(thm)], ['14', '15'])).
% 1.66/1.83  thf('17', plain,
% 1.66/1.83      (![X9 : $i, X10 : $i]:
% 1.66/1.83         ((zip_tseitin_0 @ X9 @ X10) | ((X10) != (k1_xboole_0)))),
% 1.66/1.83      inference('cnf', [status(esa)], [zf_stmt_7])).
% 1.66/1.83  thf('18', plain, (![X9 : $i]: (zip_tseitin_0 @ X9 @ k1_xboole_0)),
% 1.66/1.83      inference('simplify', [status(thm)], ['17'])).
% 1.66/1.83  thf('19', plain,
% 1.66/1.83      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ k1_xboole_0))
% 1.66/1.83         <= ((((sk_A) = (k1_xboole_0))))),
% 1.66/1.83      inference('demod', [status(thm)], ['16', '18'])).
% 1.66/1.83  thf('20', plain,
% 1.66/1.83      (((m1_subset_1 @ sk_C_1 @ 
% 1.66/1.83         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 1.66/1.83         <= ((((sk_A) = (k1_xboole_0))))),
% 1.66/1.83      inference('sup+', [status(thm)], ['12', '13'])).
% 1.66/1.83  thf(redefinition_k1_relset_1, axiom,
% 1.66/1.83    (![A:$i,B:$i,C:$i]:
% 1.66/1.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.66/1.83       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.66/1.83  thf('21', plain,
% 1.66/1.83      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.66/1.83         (((k1_relset_1 @ X7 @ X8 @ X6) = (k1_relat_1 @ X6))
% 1.66/1.83          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 1.66/1.83      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.66/1.83  thf('22', plain,
% 1.66/1.83      ((((k1_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1)))
% 1.66/1.83         <= ((((sk_A) = (k1_xboole_0))))),
% 1.66/1.83      inference('sup-', [status(thm)], ['20', '21'])).
% 1.66/1.83  thf('23', plain,
% 1.66/1.83      ((((k1_xboole_0) = (k1_relat_1 @ sk_C_1)))
% 1.66/1.83         <= ((((sk_A) = (k1_xboole_0))))),
% 1.66/1.83      inference('demod', [status(thm)], ['11', '19', '22'])).
% 1.66/1.83  thf(d8_funct_1, axiom,
% 1.66/1.83    (![A:$i]:
% 1.66/1.83     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.66/1.83       ( ( v2_funct_1 @ A ) <=>
% 1.66/1.83         ( ![B:$i,C:$i]:
% 1.66/1.83           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 1.66/1.83               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 1.66/1.83               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 1.66/1.83             ( ( B ) = ( C ) ) ) ) ) ))).
% 1.66/1.83  thf('24', plain,
% 1.66/1.83      (![X0 : $i]:
% 1.66/1.83         ((r2_hidden @ (sk_C @ X0) @ (k1_relat_1 @ X0))
% 1.66/1.83          | (v2_funct_1 @ X0)
% 1.66/1.83          | ~ (v1_funct_1 @ X0)
% 1.66/1.83          | ~ (v1_relat_1 @ X0))),
% 1.66/1.83      inference('cnf', [status(esa)], [d8_funct_1])).
% 1.66/1.83  thf('25', plain,
% 1.66/1.83      (![X0 : $i]:
% 1.66/1.83         ((r2_hidden @ (sk_B @ X0) @ (k1_relat_1 @ X0))
% 1.66/1.83          | (v2_funct_1 @ X0)
% 1.66/1.83          | ~ (v1_funct_1 @ X0)
% 1.66/1.83          | ~ (v1_relat_1 @ X0))),
% 1.66/1.83      inference('cnf', [status(esa)], [d8_funct_1])).
% 1.66/1.83  thf('26', plain,
% 1.66/1.83      (![X0 : $i]:
% 1.66/1.83         (((k1_funct_1 @ X0 @ (sk_B @ X0)) = (k1_funct_1 @ X0 @ (sk_C @ X0)))
% 1.66/1.83          | (v2_funct_1 @ X0)
% 1.66/1.83          | ~ (v1_funct_1 @ X0)
% 1.66/1.83          | ~ (v1_relat_1 @ X0))),
% 1.66/1.83      inference('cnf', [status(esa)], [d8_funct_1])).
% 1.66/1.83  thf('27', plain,
% 1.66/1.83      (![X17 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.66/1.83         ((zip_tseitin_2 @ X19 @ X17 @ X20 @ X21)
% 1.66/1.83          | ((k1_funct_1 @ X20 @ X17) != (k1_funct_1 @ X20 @ X19))
% 1.66/1.83          | ~ (r2_hidden @ X19 @ X21)
% 1.66/1.83          | ~ (r2_hidden @ X17 @ X21))),
% 1.66/1.83      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.66/1.83  thf('28', plain,
% 1.66/1.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.83         (((k1_funct_1 @ X0 @ (sk_B @ X0)) != (k1_funct_1 @ X0 @ X1))
% 1.66/1.83          | ~ (v1_relat_1 @ X0)
% 1.66/1.83          | ~ (v1_funct_1 @ X0)
% 1.66/1.83          | (v2_funct_1 @ X0)
% 1.66/1.83          | ~ (r2_hidden @ (sk_C @ X0) @ X2)
% 1.66/1.83          | ~ (r2_hidden @ X1 @ X2)
% 1.66/1.83          | (zip_tseitin_2 @ X1 @ (sk_C @ X0) @ X0 @ X2))),
% 1.66/1.83      inference('sup-', [status(thm)], ['26', '27'])).
% 1.66/1.83  thf('29', plain,
% 1.66/1.83      (![X0 : $i, X1 : $i]:
% 1.66/1.83         ((zip_tseitin_2 @ (sk_B @ X1) @ (sk_C @ X1) @ X1 @ X0)
% 1.66/1.83          | ~ (r2_hidden @ (sk_B @ X1) @ X0)
% 1.66/1.83          | ~ (r2_hidden @ (sk_C @ X1) @ X0)
% 1.66/1.83          | (v2_funct_1 @ X1)
% 1.66/1.83          | ~ (v1_funct_1 @ X1)
% 1.66/1.83          | ~ (v1_relat_1 @ X1))),
% 1.66/1.83      inference('eq_res', [status(thm)], ['28'])).
% 1.66/1.83  thf('30', plain,
% 1.66/1.83      (![X0 : $i]:
% 1.66/1.83         (~ (v1_relat_1 @ X0)
% 1.66/1.83          | ~ (v1_funct_1 @ X0)
% 1.66/1.83          | (v2_funct_1 @ X0)
% 1.66/1.83          | ~ (v1_relat_1 @ X0)
% 1.66/1.83          | ~ (v1_funct_1 @ X0)
% 1.66/1.83          | (v2_funct_1 @ X0)
% 1.66/1.83          | ~ (r2_hidden @ (sk_C @ X0) @ (k1_relat_1 @ X0))
% 1.66/1.83          | (zip_tseitin_2 @ (sk_B @ X0) @ (sk_C @ X0) @ X0 @ (k1_relat_1 @ X0)))),
% 1.66/1.83      inference('sup-', [status(thm)], ['25', '29'])).
% 1.66/1.83  thf('31', plain,
% 1.66/1.83      (![X0 : $i]:
% 1.66/1.83         ((zip_tseitin_2 @ (sk_B @ X0) @ (sk_C @ X0) @ X0 @ (k1_relat_1 @ X0))
% 1.66/1.83          | ~ (r2_hidden @ (sk_C @ X0) @ (k1_relat_1 @ X0))
% 1.66/1.83          | (v2_funct_1 @ X0)
% 1.66/1.83          | ~ (v1_funct_1 @ X0)
% 1.66/1.83          | ~ (v1_relat_1 @ X0))),
% 1.66/1.83      inference('simplify', [status(thm)], ['30'])).
% 1.66/1.83  thf('32', plain,
% 1.66/1.83      (![X0 : $i]:
% 1.66/1.83         (~ (v1_relat_1 @ X0)
% 1.66/1.83          | ~ (v1_funct_1 @ X0)
% 1.66/1.83          | (v2_funct_1 @ X0)
% 1.66/1.83          | ~ (v1_relat_1 @ X0)
% 1.66/1.83          | ~ (v1_funct_1 @ X0)
% 1.66/1.83          | (v2_funct_1 @ X0)
% 1.66/1.83          | (zip_tseitin_2 @ (sk_B @ X0) @ (sk_C @ X0) @ X0 @ (k1_relat_1 @ X0)))),
% 1.66/1.83      inference('sup-', [status(thm)], ['24', '31'])).
% 1.66/1.83  thf('33', plain,
% 1.66/1.83      (![X0 : $i]:
% 1.66/1.83         ((zip_tseitin_2 @ (sk_B @ X0) @ (sk_C @ X0) @ X0 @ (k1_relat_1 @ X0))
% 1.66/1.83          | (v2_funct_1 @ X0)
% 1.66/1.83          | ~ (v1_funct_1 @ X0)
% 1.66/1.83          | ~ (v1_relat_1 @ X0))),
% 1.66/1.83      inference('simplify', [status(thm)], ['32'])).
% 1.66/1.83  thf('34', plain,
% 1.66/1.83      ((((zip_tseitin_2 @ (sk_B @ sk_C_1) @ (sk_C @ sk_C_1) @ sk_C_1 @ 
% 1.66/1.83          k1_xboole_0)
% 1.66/1.83         | ~ (v1_relat_1 @ sk_C_1)
% 1.66/1.83         | ~ (v1_funct_1 @ sk_C_1)
% 1.66/1.83         | (v2_funct_1 @ sk_C_1))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.66/1.83      inference('sup+', [status(thm)], ['23', '33'])).
% 1.66/1.83  thf('35', plain,
% 1.66/1.83      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.66/1.83      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.66/1.83  thf(cc1_relset_1, axiom,
% 1.66/1.83    (![A:$i,B:$i,C:$i]:
% 1.66/1.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.66/1.83       ( v1_relat_1 @ C ) ))).
% 1.66/1.83  thf('36', plain,
% 1.66/1.83      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.66/1.83         ((v1_relat_1 @ X3)
% 1.66/1.83          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 1.66/1.83      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.66/1.83  thf('37', plain, ((v1_relat_1 @ sk_C_1)),
% 1.66/1.83      inference('sup-', [status(thm)], ['35', '36'])).
% 1.66/1.83  thf('38', plain, ((v1_funct_1 @ sk_C_1)),
% 1.66/1.83      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.66/1.83  thf('39', plain,
% 1.66/1.83      ((((zip_tseitin_2 @ (sk_B @ sk_C_1) @ (sk_C @ sk_C_1) @ sk_C_1 @ 
% 1.66/1.83          k1_xboole_0)
% 1.66/1.83         | (v2_funct_1 @ sk_C_1))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.66/1.83      inference('demod', [status(thm)], ['34', '37', '38'])).
% 1.66/1.83  thf('40', plain,
% 1.66/1.83      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.66/1.83      inference('split', [status(esa)], ['6'])).
% 1.66/1.83  thf('41', plain,
% 1.66/1.83      (![X22 : $i, X23 : $i]:
% 1.66/1.83         (~ (zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A)
% 1.66/1.83          | ((X23) = (X22))
% 1.66/1.83          | (v2_funct_1 @ sk_C_1))),
% 1.66/1.83      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.66/1.83  thf('42', plain,
% 1.66/1.83      ((![X22 : $i, X23 : $i]:
% 1.66/1.83          (((X23) = (X22)) | ~ (zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A)))
% 1.66/1.83         <= ((![X22 : $i, X23 : $i]:
% 1.66/1.83                (((X23) = (X22))
% 1.66/1.83                 | ~ (zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A))))),
% 1.66/1.83      inference('split', [status(esa)], ['41'])).
% 1.66/1.83  thf('43', plain,
% 1.66/1.83      ((![X0 : $i, X1 : $i]:
% 1.66/1.83          (~ (zip_tseitin_2 @ X1 @ X0 @ sk_C_1 @ k1_xboole_0) | ((X0) = (X1))))
% 1.66/1.83         <= ((![X22 : $i, X23 : $i]:
% 1.66/1.83                (((X23) = (X22))
% 1.66/1.83                 | ~ (zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A))) & 
% 1.66/1.83             (((sk_A) = (k1_xboole_0))))),
% 1.66/1.83      inference('sup-', [status(thm)], ['40', '42'])).
% 1.66/1.83  thf('44', plain,
% 1.66/1.83      ((((v2_funct_1 @ sk_C_1) | ((sk_C @ sk_C_1) = (sk_B @ sk_C_1))))
% 1.66/1.84         <= ((![X22 : $i, X23 : $i]:
% 1.66/1.84                (((X23) = (X22))
% 1.66/1.84                 | ~ (zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A))) & 
% 1.66/1.84             (((sk_A) = (k1_xboole_0))))),
% 1.66/1.84      inference('sup-', [status(thm)], ['39', '43'])).
% 1.66/1.84  thf('45', plain, ((~ (v2_funct_1 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 1.66/1.84      inference('split', [status(esa)], ['4'])).
% 1.66/1.84  thf('46', plain,
% 1.66/1.84      ((((sk_C @ sk_C_1) = (sk_B @ sk_C_1)))
% 1.66/1.84         <= (~ ((v2_funct_1 @ sk_C_1)) & 
% 1.66/1.84             (![X22 : $i, X23 : $i]:
% 1.66/1.84                (((X23) = (X22))
% 1.66/1.84                 | ~ (zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A))) & 
% 1.66/1.84             (((sk_A) = (k1_xboole_0))))),
% 1.66/1.84      inference('sup-', [status(thm)], ['44', '45'])).
% 1.66/1.84  thf('47', plain,
% 1.66/1.84      (![X0 : $i]:
% 1.66/1.84         (((sk_B @ X0) != (sk_C @ X0))
% 1.66/1.84          | (v2_funct_1 @ X0)
% 1.66/1.84          | ~ (v1_funct_1 @ X0)
% 1.66/1.84          | ~ (v1_relat_1 @ X0))),
% 1.66/1.84      inference('cnf', [status(esa)], [d8_funct_1])).
% 1.66/1.84  thf('48', plain,
% 1.66/1.84      (((((sk_B @ sk_C_1) != (sk_B @ sk_C_1))
% 1.66/1.84         | ~ (v1_relat_1 @ sk_C_1)
% 1.66/1.84         | ~ (v1_funct_1 @ sk_C_1)
% 1.66/1.84         | (v2_funct_1 @ sk_C_1)))
% 1.66/1.84         <= (~ ((v2_funct_1 @ sk_C_1)) & 
% 1.66/1.84             (![X22 : $i, X23 : $i]:
% 1.66/1.84                (((X23) = (X22))
% 1.66/1.84                 | ~ (zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A))) & 
% 1.66/1.84             (((sk_A) = (k1_xboole_0))))),
% 1.66/1.84      inference('sup-', [status(thm)], ['46', '47'])).
% 1.66/1.84  thf('49', plain, ((v1_relat_1 @ sk_C_1)),
% 1.66/1.84      inference('sup-', [status(thm)], ['35', '36'])).
% 1.66/1.84  thf('50', plain, ((v1_funct_1 @ sk_C_1)),
% 1.66/1.84      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.66/1.84  thf('51', plain,
% 1.66/1.84      (((((sk_B @ sk_C_1) != (sk_B @ sk_C_1)) | (v2_funct_1 @ sk_C_1)))
% 1.66/1.84         <= (~ ((v2_funct_1 @ sk_C_1)) & 
% 1.66/1.84             (![X22 : $i, X23 : $i]:
% 1.66/1.84                (((X23) = (X22))
% 1.66/1.84                 | ~ (zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A))) & 
% 1.66/1.84             (((sk_A) = (k1_xboole_0))))),
% 1.66/1.84      inference('demod', [status(thm)], ['48', '49', '50'])).
% 1.66/1.84  thf('52', plain,
% 1.66/1.84      (((v2_funct_1 @ sk_C_1))
% 1.66/1.84         <= (~ ((v2_funct_1 @ sk_C_1)) & 
% 1.66/1.84             (![X22 : $i, X23 : $i]:
% 1.66/1.84                (((X23) = (X22))
% 1.66/1.84                 | ~ (zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A))) & 
% 1.66/1.84             (((sk_A) = (k1_xboole_0))))),
% 1.66/1.84      inference('simplify', [status(thm)], ['51'])).
% 1.66/1.84  thf('53', plain, ((~ (v2_funct_1 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 1.66/1.84      inference('split', [status(esa)], ['4'])).
% 1.66/1.84  thf('54', plain,
% 1.66/1.84      (~ (((sk_A) = (k1_xboole_0))) | ((v2_funct_1 @ sk_C_1)) | 
% 1.66/1.84       ~
% 1.66/1.84       (![X22 : $i, X23 : $i]:
% 1.66/1.84          (((X23) = (X22)) | ~ (zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A)))),
% 1.66/1.84      inference('sup-', [status(thm)], ['52', '53'])).
% 1.66/1.84  thf('55', plain,
% 1.66/1.84      (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A))
% 1.66/1.84         <= (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)))),
% 1.66/1.84      inference('split', [status(esa)], ['0'])).
% 1.66/1.84  thf('56', plain,
% 1.66/1.84      ((![X22 : $i, X23 : $i]:
% 1.66/1.84          (((X23) = (X22)) | ~ (zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A)))
% 1.66/1.84         <= ((![X22 : $i, X23 : $i]:
% 1.66/1.84                (((X23) = (X22))
% 1.66/1.84                 | ~ (zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A))))),
% 1.66/1.84      inference('split', [status(esa)], ['41'])).
% 1.66/1.84  thf('57', plain,
% 1.66/1.84      ((((sk_D) = (sk_E)))
% 1.66/1.84         <= (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)) & 
% 1.66/1.84             (![X22 : $i, X23 : $i]:
% 1.66/1.84                (((X23) = (X22))
% 1.66/1.84                 | ~ (zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A))))),
% 1.66/1.84      inference('sup-', [status(thm)], ['55', '56'])).
% 1.66/1.84  thf('58', plain, ((((sk_D) != (sk_E))) <= (~ (((sk_D) = (sk_E))))),
% 1.66/1.84      inference('split', [status(esa)], ['4'])).
% 1.66/1.84  thf('59', plain,
% 1.66/1.84      ((((sk_D) != (sk_D)))
% 1.66/1.84         <= (~ (((sk_D) = (sk_E))) & 
% 1.66/1.84             ((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)) & 
% 1.66/1.84             (![X22 : $i, X23 : $i]:
% 1.66/1.84                (((X23) = (X22))
% 1.66/1.84                 | ~ (zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A))))),
% 1.66/1.84      inference('sup-', [status(thm)], ['57', '58'])).
% 1.66/1.84  thf('60', plain,
% 1.66/1.84      (~
% 1.66/1.84       (![X22 : $i, X23 : $i]:
% 1.66/1.84          (((X23) = (X22)) | ~ (zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A))) | 
% 1.66/1.84       (((sk_D) = (sk_E))) | ~ ((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A))),
% 1.66/1.84      inference('simplify', [status(thm)], ['59'])).
% 1.66/1.84  thf('61', plain,
% 1.66/1.84      ((((k1_funct_1 @ sk_C_1 @ sk_D) = (k1_funct_1 @ sk_C_1 @ sk_E)))
% 1.66/1.84         <= (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)))),
% 1.66/1.84      inference('sup-', [status(thm)], ['1', '2'])).
% 1.66/1.84  thf('62', plain, (((v2_funct_1 @ sk_C_1)) <= (((v2_funct_1 @ sk_C_1)))),
% 1.66/1.84      inference('split', [status(esa)], ['41'])).
% 1.66/1.84  thf('63', plain,
% 1.66/1.84      ((((k1_xboole_0) = (k1_relat_1 @ sk_C_1)))
% 1.66/1.84         <= ((((sk_A) = (k1_xboole_0))))),
% 1.66/1.84      inference('demod', [status(thm)], ['11', '19', '22'])).
% 1.66/1.84  thf('64', plain,
% 1.66/1.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.84         (~ (v2_funct_1 @ X0)
% 1.66/1.84          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 1.66/1.84          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ X0))
% 1.66/1.84          | ((k1_funct_1 @ X0 @ X1) != (k1_funct_1 @ X0 @ X2))
% 1.66/1.84          | ((X1) = (X2))
% 1.66/1.84          | ~ (v1_funct_1 @ X0)
% 1.66/1.84          | ~ (v1_relat_1 @ X0))),
% 1.66/1.84      inference('cnf', [status(esa)], [d8_funct_1])).
% 1.66/1.84  thf('65', plain,
% 1.66/1.84      ((![X0 : $i, X1 : $i]:
% 1.66/1.84          (~ (r2_hidden @ X0 @ k1_xboole_0)
% 1.66/1.84           | ~ (v1_relat_1 @ sk_C_1)
% 1.66/1.84           | ~ (v1_funct_1 @ sk_C_1)
% 1.66/1.84           | ((X0) = (X1))
% 1.66/1.84           | ((k1_funct_1 @ sk_C_1 @ X0) != (k1_funct_1 @ sk_C_1 @ X1))
% 1.66/1.84           | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_C_1))
% 1.66/1.84           | ~ (v2_funct_1 @ sk_C_1)))
% 1.66/1.84         <= ((((sk_A) = (k1_xboole_0))))),
% 1.66/1.84      inference('sup-', [status(thm)], ['63', '64'])).
% 1.66/1.84  thf('66', plain, ((v1_relat_1 @ sk_C_1)),
% 1.66/1.84      inference('sup-', [status(thm)], ['35', '36'])).
% 1.66/1.84  thf('67', plain, ((v1_funct_1 @ sk_C_1)),
% 1.66/1.84      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.66/1.84  thf('68', plain,
% 1.66/1.84      ((((k1_xboole_0) = (k1_relat_1 @ sk_C_1)))
% 1.66/1.84         <= ((((sk_A) = (k1_xboole_0))))),
% 1.66/1.84      inference('demod', [status(thm)], ['11', '19', '22'])).
% 1.66/1.84  thf('69', plain,
% 1.66/1.84      ((![X0 : $i, X1 : $i]:
% 1.66/1.84          (~ (r2_hidden @ X0 @ k1_xboole_0)
% 1.66/1.84           | ((X0) = (X1))
% 1.66/1.84           | ((k1_funct_1 @ sk_C_1 @ X0) != (k1_funct_1 @ sk_C_1 @ X1))
% 1.66/1.84           | ~ (r2_hidden @ X1 @ k1_xboole_0)
% 1.66/1.84           | ~ (v2_funct_1 @ sk_C_1)))
% 1.66/1.84         <= ((((sk_A) = (k1_xboole_0))))),
% 1.66/1.84      inference('demod', [status(thm)], ['65', '66', '67', '68'])).
% 1.66/1.84  thf('70', plain,
% 1.66/1.84      ((![X0 : $i, X1 : $i]:
% 1.66/1.84          (~ (r2_hidden @ X0 @ k1_xboole_0)
% 1.66/1.84           | ((k1_funct_1 @ sk_C_1 @ X1) != (k1_funct_1 @ sk_C_1 @ X0))
% 1.66/1.84           | ((X1) = (X0))
% 1.66/1.84           | ~ (r2_hidden @ X1 @ k1_xboole_0)))
% 1.66/1.84         <= (((v2_funct_1 @ sk_C_1)) & (((sk_A) = (k1_xboole_0))))),
% 1.66/1.84      inference('sup-', [status(thm)], ['62', '69'])).
% 1.66/1.84  thf('71', plain,
% 1.66/1.84      ((![X0 : $i]:
% 1.66/1.84          (((k1_funct_1 @ sk_C_1 @ sk_D) != (k1_funct_1 @ sk_C_1 @ X0))
% 1.66/1.84           | ~ (r2_hidden @ sk_E @ k1_xboole_0)
% 1.66/1.84           | ((sk_E) = (X0))
% 1.66/1.84           | ~ (r2_hidden @ X0 @ k1_xboole_0)))
% 1.66/1.84         <= (((v2_funct_1 @ sk_C_1)) & 
% 1.66/1.84             ((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)) & 
% 1.66/1.84             (((sk_A) = (k1_xboole_0))))),
% 1.66/1.84      inference('sup-', [status(thm)], ['61', '70'])).
% 1.66/1.84  thf('72', plain,
% 1.66/1.84      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.66/1.84      inference('split', [status(esa)], ['6'])).
% 1.66/1.84  thf('73', plain,
% 1.66/1.84      (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A))
% 1.66/1.84         <= (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)))),
% 1.66/1.84      inference('split', [status(esa)], ['0'])).
% 1.66/1.84  thf('74', plain,
% 1.66/1.84      (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ k1_xboole_0))
% 1.66/1.84         <= (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)) & 
% 1.66/1.84             (((sk_A) = (k1_xboole_0))))),
% 1.66/1.84      inference('sup+', [status(thm)], ['72', '73'])).
% 1.66/1.84  thf('75', plain,
% 1.66/1.84      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.66/1.84         ((r2_hidden @ X19 @ X18) | ~ (zip_tseitin_2 @ X19 @ X17 @ X20 @ X18))),
% 1.66/1.84      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.66/1.84  thf('76', plain,
% 1.66/1.84      (((r2_hidden @ sk_E @ k1_xboole_0))
% 1.66/1.84         <= (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)) & 
% 1.66/1.84             (((sk_A) = (k1_xboole_0))))),
% 1.66/1.84      inference('sup-', [status(thm)], ['74', '75'])).
% 1.66/1.84  thf('77', plain,
% 1.66/1.84      ((![X0 : $i]:
% 1.66/1.84          (((k1_funct_1 @ sk_C_1 @ sk_D) != (k1_funct_1 @ sk_C_1 @ X0))
% 1.66/1.84           | ((sk_E) = (X0))
% 1.66/1.84           | ~ (r2_hidden @ X0 @ k1_xboole_0)))
% 1.66/1.84         <= (((v2_funct_1 @ sk_C_1)) & 
% 1.66/1.84             ((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)) & 
% 1.66/1.84             (((sk_A) = (k1_xboole_0))))),
% 1.66/1.84      inference('demod', [status(thm)], ['71', '76'])).
% 1.66/1.84  thf('78', plain,
% 1.66/1.84      (((~ (r2_hidden @ sk_D @ k1_xboole_0) | ((sk_E) = (sk_D))))
% 1.66/1.84         <= (((v2_funct_1 @ sk_C_1)) & 
% 1.66/1.84             ((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)) & 
% 1.66/1.84             (((sk_A) = (k1_xboole_0))))),
% 1.66/1.84      inference('eq_res', [status(thm)], ['77'])).
% 1.66/1.84  thf('79', plain,
% 1.66/1.84      (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ k1_xboole_0))
% 1.66/1.84         <= (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)) & 
% 1.66/1.84             (((sk_A) = (k1_xboole_0))))),
% 1.66/1.84      inference('sup+', [status(thm)], ['72', '73'])).
% 1.66/1.84  thf('80', plain,
% 1.66/1.84      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.66/1.84         ((r2_hidden @ X17 @ X18) | ~ (zip_tseitin_2 @ X19 @ X17 @ X20 @ X18))),
% 1.66/1.84      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.66/1.84  thf('81', plain,
% 1.66/1.84      (((r2_hidden @ sk_D @ k1_xboole_0))
% 1.66/1.84         <= (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)) & 
% 1.66/1.84             (((sk_A) = (k1_xboole_0))))),
% 1.66/1.84      inference('sup-', [status(thm)], ['79', '80'])).
% 1.66/1.84  thf('82', plain,
% 1.66/1.84      ((((sk_E) = (sk_D)))
% 1.66/1.84         <= (((v2_funct_1 @ sk_C_1)) & 
% 1.66/1.84             ((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)) & 
% 1.66/1.84             (((sk_A) = (k1_xboole_0))))),
% 1.66/1.84      inference('demod', [status(thm)], ['78', '81'])).
% 1.66/1.84  thf('83', plain, ((((sk_D) != (sk_E))) <= (~ (((sk_D) = (sk_E))))),
% 1.66/1.84      inference('split', [status(esa)], ['4'])).
% 1.66/1.84  thf('84', plain,
% 1.66/1.84      ((((sk_D) != (sk_D)))
% 1.66/1.84         <= (~ (((sk_D) = (sk_E))) & 
% 1.66/1.84             ((v2_funct_1 @ sk_C_1)) & 
% 1.66/1.84             ((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)) & 
% 1.66/1.84             (((sk_A) = (k1_xboole_0))))),
% 1.66/1.84      inference('sup-', [status(thm)], ['82', '83'])).
% 1.66/1.84  thf('85', plain,
% 1.66/1.84      (~ (((sk_A) = (k1_xboole_0))) | ~ ((v2_funct_1 @ sk_C_1)) | 
% 1.66/1.84       ~ ((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)) | (((sk_D) = (sk_E)))),
% 1.66/1.84      inference('simplify', [status(thm)], ['84'])).
% 1.66/1.84  thf('86', plain,
% 1.66/1.84      (~ (((sk_B_1) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 1.66/1.84      inference('split', [status(esa)], ['6'])).
% 1.66/1.84  thf('87', plain,
% 1.66/1.84      (((v2_funct_1 @ sk_C_1)) | 
% 1.66/1.84       (![X22 : $i, X23 : $i]:
% 1.66/1.84          (((X23) = (X22)) | ~ (zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A)))),
% 1.66/1.84      inference('split', [status(esa)], ['41'])).
% 1.66/1.84  thf('88', plain,
% 1.66/1.84      (![X9 : $i, X10 : $i]:
% 1.66/1.84         ((zip_tseitin_0 @ X9 @ X10) | ((X9) = (k1_xboole_0)))),
% 1.66/1.84      inference('cnf', [status(esa)], [zf_stmt_7])).
% 1.66/1.84  thf('89', plain,
% 1.66/1.84      (![X9 : $i, X10 : $i]:
% 1.66/1.84         ((zip_tseitin_0 @ X9 @ X10) | ((X9) = (k1_xboole_0)))),
% 1.66/1.84      inference('cnf', [status(esa)], [zf_stmt_7])).
% 1.66/1.84  thf('90', plain,
% 1.66/1.84      (![X9 : $i, X10 : $i]:
% 1.66/1.84         ((zip_tseitin_0 @ X9 @ X10) | ((X9) = (k1_xboole_0)))),
% 1.66/1.84      inference('cnf', [status(esa)], [zf_stmt_7])).
% 1.66/1.84  thf('91', plain,
% 1.66/1.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.66/1.84         (((X1) = (X0)) | (zip_tseitin_0 @ X0 @ X3) | (zip_tseitin_0 @ X1 @ X2))),
% 1.66/1.84      inference('sup+', [status(thm)], ['89', '90'])).
% 1.66/1.84  thf('92', plain,
% 1.66/1.84      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.66/1.84      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.66/1.84  thf('93', plain,
% 1.66/1.84      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.66/1.84         (~ (zip_tseitin_0 @ X14 @ X15)
% 1.66/1.84          | (zip_tseitin_1 @ X16 @ X14 @ X15)
% 1.66/1.84          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X14))))),
% 1.66/1.84      inference('cnf', [status(esa)], [zf_stmt_8])).
% 1.66/1.84  thf('94', plain,
% 1.66/1.84      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 1.66/1.84        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 1.66/1.84      inference('sup-', [status(thm)], ['92', '93'])).
% 1.66/1.84  thf('95', plain,
% 1.66/1.84      (![X0 : $i, X1 : $i]:
% 1.66/1.84         ((zip_tseitin_0 @ X1 @ X0)
% 1.66/1.84          | ((sk_B_1) = (X1))
% 1.66/1.84          | (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A))),
% 1.66/1.84      inference('sup-', [status(thm)], ['91', '94'])).
% 1.66/1.84  thf('96', plain,
% 1.66/1.84      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.66/1.84      inference('split', [status(esa)], ['6'])).
% 1.66/1.84  thf('97', plain,
% 1.66/1.84      ((![X0 : $i, X1 : $i]:
% 1.66/1.84          (((X0) != (k1_xboole_0))
% 1.66/1.84           | (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 1.66/1.84           | (zip_tseitin_0 @ X0 @ X1)))
% 1.66/1.84         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.66/1.84      inference('sup-', [status(thm)], ['95', '96'])).
% 1.66/1.84  thf('98', plain,
% 1.66/1.84      ((![X1 : $i]:
% 1.66/1.84          ((zip_tseitin_0 @ k1_xboole_0 @ X1)
% 1.66/1.84           | (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)))
% 1.66/1.84         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.66/1.84      inference('simplify', [status(thm)], ['97'])).
% 1.66/1.84  thf('99', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 1.66/1.84      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.66/1.84  thf('100', plain,
% 1.66/1.84      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.66/1.84         (~ (v1_funct_2 @ X13 @ X11 @ X12)
% 1.66/1.84          | ((X11) = (k1_relset_1 @ X11 @ X12 @ X13))
% 1.66/1.84          | ~ (zip_tseitin_1 @ X13 @ X12 @ X11))),
% 1.66/1.84      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.66/1.84  thf('101', plain,
% 1.66/1.84      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 1.66/1.84        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 1.66/1.84      inference('sup-', [status(thm)], ['99', '100'])).
% 1.66/1.84  thf('102', plain,
% 1.66/1.84      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.66/1.84      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.66/1.84  thf('103', plain,
% 1.66/1.84      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.66/1.84         (((k1_relset_1 @ X7 @ X8 @ X6) = (k1_relat_1 @ X6))
% 1.66/1.84          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 1.66/1.84      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.66/1.84  thf('104', plain,
% 1.66/1.84      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 1.66/1.84      inference('sup-', [status(thm)], ['102', '103'])).
% 1.66/1.84  thf('105', plain,
% 1.66/1.84      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 1.66/1.84        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.66/1.84      inference('demod', [status(thm)], ['101', '104'])).
% 1.66/1.84  thf('106', plain,
% 1.66/1.84      ((![X0 : $i]:
% 1.66/1.84          ((zip_tseitin_0 @ k1_xboole_0 @ X0)
% 1.66/1.84           | ((sk_A) = (k1_relat_1 @ sk_C_1))))
% 1.66/1.84         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.66/1.84      inference('sup-', [status(thm)], ['98', '105'])).
% 1.66/1.84  thf('107', plain,
% 1.66/1.84      ((![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.84          ((zip_tseitin_0 @ X0 @ X1)
% 1.66/1.84           | (zip_tseitin_0 @ X0 @ X2)
% 1.66/1.84           | ((sk_A) = (k1_relat_1 @ sk_C_1))))
% 1.66/1.84         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.66/1.84      inference('sup+', [status(thm)], ['88', '106'])).
% 1.66/1.84  thf('108', plain,
% 1.66/1.84      ((![X0 : $i, X1 : $i]:
% 1.66/1.84          (((sk_A) = (k1_relat_1 @ sk_C_1)) | (zip_tseitin_0 @ X1 @ X0)))
% 1.66/1.84         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.66/1.84      inference('condensation', [status(thm)], ['107'])).
% 1.66/1.84  thf('109', plain,
% 1.66/1.84      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 1.66/1.84        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 1.66/1.84      inference('sup-', [status(thm)], ['92', '93'])).
% 1.66/1.84  thf('110', plain,
% 1.66/1.84      (((((sk_A) = (k1_relat_1 @ sk_C_1))
% 1.66/1.84         | (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)))
% 1.66/1.84         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.66/1.84      inference('sup-', [status(thm)], ['108', '109'])).
% 1.66/1.84  thf('111', plain,
% 1.66/1.84      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 1.66/1.84        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.66/1.84      inference('demod', [status(thm)], ['101', '104'])).
% 1.66/1.84  thf('112', plain,
% 1.66/1.84      ((((sk_A) = (k1_relat_1 @ sk_C_1))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.66/1.84      inference('clc', [status(thm)], ['110', '111'])).
% 1.66/1.84  thf('113', plain,
% 1.66/1.84      (![X0 : $i]:
% 1.66/1.84         ((zip_tseitin_2 @ (sk_B @ X0) @ (sk_C @ X0) @ X0 @ (k1_relat_1 @ X0))
% 1.66/1.84          | (v2_funct_1 @ X0)
% 1.66/1.84          | ~ (v1_funct_1 @ X0)
% 1.66/1.84          | ~ (v1_relat_1 @ X0))),
% 1.66/1.84      inference('simplify', [status(thm)], ['32'])).
% 1.66/1.84  thf('114', plain,
% 1.66/1.84      ((((zip_tseitin_2 @ (sk_B @ sk_C_1) @ (sk_C @ sk_C_1) @ sk_C_1 @ sk_A)
% 1.66/1.84         | ~ (v1_relat_1 @ sk_C_1)
% 1.66/1.84         | ~ (v1_funct_1 @ sk_C_1)
% 1.66/1.84         | (v2_funct_1 @ sk_C_1))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.66/1.84      inference('sup+', [status(thm)], ['112', '113'])).
% 1.66/1.84  thf('115', plain, ((v1_relat_1 @ sk_C_1)),
% 1.66/1.84      inference('sup-', [status(thm)], ['35', '36'])).
% 1.66/1.84  thf('116', plain, ((v1_funct_1 @ sk_C_1)),
% 1.66/1.84      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.66/1.84  thf('117', plain,
% 1.66/1.84      ((((zip_tseitin_2 @ (sk_B @ sk_C_1) @ (sk_C @ sk_C_1) @ sk_C_1 @ sk_A)
% 1.66/1.84         | (v2_funct_1 @ sk_C_1))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.66/1.84      inference('demod', [status(thm)], ['114', '115', '116'])).
% 1.66/1.84  thf('118', plain,
% 1.66/1.84      ((![X22 : $i, X23 : $i]:
% 1.66/1.84          (((X23) = (X22)) | ~ (zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A)))
% 1.66/1.84         <= ((![X22 : $i, X23 : $i]:
% 1.66/1.84                (((X23) = (X22))
% 1.66/1.84                 | ~ (zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A))))),
% 1.66/1.84      inference('split', [status(esa)], ['41'])).
% 1.66/1.84  thf('119', plain,
% 1.66/1.84      ((((v2_funct_1 @ sk_C_1) | ((sk_C @ sk_C_1) = (sk_B @ sk_C_1))))
% 1.66/1.84         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 1.66/1.84             (![X22 : $i, X23 : $i]:
% 1.66/1.84                (((X23) = (X22))
% 1.66/1.84                 | ~ (zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A))))),
% 1.66/1.84      inference('sup-', [status(thm)], ['117', '118'])).
% 1.66/1.84  thf('120', plain, ((~ (v2_funct_1 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 1.66/1.84      inference('split', [status(esa)], ['4'])).
% 1.66/1.84  thf('121', plain,
% 1.66/1.84      ((((sk_C @ sk_C_1) = (sk_B @ sk_C_1)))
% 1.66/1.84         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 1.66/1.84             ~ ((v2_funct_1 @ sk_C_1)) & 
% 1.66/1.84             (![X22 : $i, X23 : $i]:
% 1.66/1.84                (((X23) = (X22))
% 1.66/1.84                 | ~ (zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A))))),
% 1.66/1.84      inference('sup-', [status(thm)], ['119', '120'])).
% 1.66/1.84  thf('122', plain,
% 1.66/1.84      (![X0 : $i]:
% 1.66/1.84         (((sk_B @ X0) != (sk_C @ X0))
% 1.66/1.84          | (v2_funct_1 @ X0)
% 1.66/1.84          | ~ (v1_funct_1 @ X0)
% 1.66/1.84          | ~ (v1_relat_1 @ X0))),
% 1.66/1.84      inference('cnf', [status(esa)], [d8_funct_1])).
% 1.66/1.84  thf('123', plain,
% 1.66/1.84      (((((sk_B @ sk_C_1) != (sk_B @ sk_C_1))
% 1.66/1.84         | ~ (v1_relat_1 @ sk_C_1)
% 1.66/1.84         | ~ (v1_funct_1 @ sk_C_1)
% 1.66/1.84         | (v2_funct_1 @ sk_C_1)))
% 1.66/1.84         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 1.66/1.84             ~ ((v2_funct_1 @ sk_C_1)) & 
% 1.66/1.84             (![X22 : $i, X23 : $i]:
% 1.66/1.84                (((X23) = (X22))
% 1.66/1.84                 | ~ (zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A))))),
% 1.66/1.84      inference('sup-', [status(thm)], ['121', '122'])).
% 1.66/1.84  thf('124', plain, ((v1_relat_1 @ sk_C_1)),
% 1.66/1.84      inference('sup-', [status(thm)], ['35', '36'])).
% 1.66/1.84  thf('125', plain, ((v1_funct_1 @ sk_C_1)),
% 1.66/1.84      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.66/1.84  thf('126', plain,
% 1.66/1.84      (((((sk_B @ sk_C_1) != (sk_B @ sk_C_1)) | (v2_funct_1 @ sk_C_1)))
% 1.66/1.84         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 1.66/1.84             ~ ((v2_funct_1 @ sk_C_1)) & 
% 1.66/1.84             (![X22 : $i, X23 : $i]:
% 1.66/1.84                (((X23) = (X22))
% 1.66/1.84                 | ~ (zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A))))),
% 1.66/1.84      inference('demod', [status(thm)], ['123', '124', '125'])).
% 1.66/1.84  thf('127', plain,
% 1.66/1.84      (((v2_funct_1 @ sk_C_1))
% 1.66/1.84         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 1.66/1.84             ~ ((v2_funct_1 @ sk_C_1)) & 
% 1.66/1.84             (![X22 : $i, X23 : $i]:
% 1.66/1.84                (((X23) = (X22))
% 1.66/1.84                 | ~ (zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A))))),
% 1.66/1.84      inference('simplify', [status(thm)], ['126'])).
% 1.66/1.84  thf('128', plain, ((~ (v2_funct_1 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 1.66/1.84      inference('split', [status(esa)], ['4'])).
% 1.66/1.84  thf('129', plain,
% 1.66/1.84      (~
% 1.66/1.84       (![X22 : $i, X23 : $i]:
% 1.66/1.84          (((X23) = (X22)) | ~ (zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A))) | 
% 1.66/1.84       ((v2_funct_1 @ sk_C_1)) | (((sk_B_1) = (k1_xboole_0)))),
% 1.66/1.84      inference('sup-', [status(thm)], ['127', '128'])).
% 1.66/1.84  thf('130', plain,
% 1.66/1.84      (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)) | 
% 1.66/1.84       ~ ((v2_funct_1 @ sk_C_1))),
% 1.66/1.84      inference('split', [status(esa)], ['0'])).
% 1.66/1.84  thf('131', plain, (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A))),
% 1.66/1.84      inference('sat_resolution*', [status(thm)],
% 1.66/1.84                ['5', '54', '60', '85', '86', '87', '129', '130'])).
% 1.66/1.84  thf('132', plain,
% 1.66/1.84      (((k1_funct_1 @ sk_C_1 @ sk_D) = (k1_funct_1 @ sk_C_1 @ sk_E))),
% 1.66/1.84      inference('simpl_trail', [status(thm)], ['3', '131'])).
% 1.66/1.84  thf('133', plain,
% 1.66/1.84      ((((sk_A) = (k1_relat_1 @ sk_C_1))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.66/1.84      inference('clc', [status(thm)], ['110', '111'])).
% 1.66/1.84  thf('134', plain,
% 1.66/1.84      (((v2_funct_1 @ sk_C_1)) | ~ (((sk_A) = (k1_xboole_0))) | 
% 1.66/1.84       ~
% 1.66/1.84       (![X22 : $i, X23 : $i]:
% 1.66/1.84          (((X23) = (X22)) | ~ (zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A)))),
% 1.66/1.84      inference('sup-', [status(thm)], ['52', '53'])).
% 1.66/1.84  thf('135', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 1.66/1.84      inference('sat_resolution*', [status(thm)],
% 1.66/1.84                ['87', '5', '130', '134', '60', '85', '86'])).
% 1.66/1.84  thf('136', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 1.66/1.84      inference('simpl_trail', [status(thm)], ['133', '135'])).
% 1.66/1.84  thf('137', plain,
% 1.66/1.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.84         (~ (v2_funct_1 @ X0)
% 1.66/1.84          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 1.66/1.84          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ X0))
% 1.66/1.84          | ((k1_funct_1 @ X0 @ X1) != (k1_funct_1 @ X0 @ X2))
% 1.66/1.84          | ((X1) = (X2))
% 1.66/1.84          | ~ (v1_funct_1 @ X0)
% 1.66/1.84          | ~ (v1_relat_1 @ X0))),
% 1.66/1.84      inference('cnf', [status(esa)], [d8_funct_1])).
% 1.66/1.84  thf('138', plain,
% 1.66/1.84      (![X0 : $i, X1 : $i]:
% 1.66/1.84         (~ (r2_hidden @ X0 @ sk_A)
% 1.66/1.84          | ~ (v1_relat_1 @ sk_C_1)
% 1.66/1.84          | ~ (v1_funct_1 @ sk_C_1)
% 1.66/1.84          | ((X0) = (X1))
% 1.66/1.84          | ((k1_funct_1 @ sk_C_1 @ X0) != (k1_funct_1 @ sk_C_1 @ X1))
% 1.66/1.84          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_C_1))
% 1.66/1.84          | ~ (v2_funct_1 @ sk_C_1))),
% 1.66/1.84      inference('sup-', [status(thm)], ['136', '137'])).
% 1.66/1.84  thf('139', plain, ((v1_relat_1 @ sk_C_1)),
% 1.66/1.84      inference('sup-', [status(thm)], ['35', '36'])).
% 1.66/1.84  thf('140', plain, ((v1_funct_1 @ sk_C_1)),
% 1.66/1.84      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.66/1.84  thf('141', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 1.66/1.84      inference('simpl_trail', [status(thm)], ['133', '135'])).
% 1.66/1.84  thf('142', plain, (((v2_funct_1 @ sk_C_1)) <= (((v2_funct_1 @ sk_C_1)))),
% 1.66/1.84      inference('split', [status(esa)], ['41'])).
% 1.66/1.84  thf('143', plain, (((v2_funct_1 @ sk_C_1))),
% 1.66/1.84      inference('sat_resolution*', [status(thm)],
% 1.66/1.84                ['5', '130', '54', '60', '85', '86', '87', '129'])).
% 1.66/1.84  thf('144', plain, ((v2_funct_1 @ sk_C_1)),
% 1.66/1.84      inference('simpl_trail', [status(thm)], ['142', '143'])).
% 1.66/1.84  thf('145', plain,
% 1.66/1.84      (![X0 : $i, X1 : $i]:
% 1.66/1.84         (~ (r2_hidden @ X0 @ sk_A)
% 1.66/1.84          | ((X0) = (X1))
% 1.66/1.84          | ((k1_funct_1 @ sk_C_1 @ X0) != (k1_funct_1 @ sk_C_1 @ X1))
% 1.66/1.84          | ~ (r2_hidden @ X1 @ sk_A))),
% 1.66/1.84      inference('demod', [status(thm)], ['138', '139', '140', '141', '144'])).
% 1.66/1.84  thf('146', plain,
% 1.66/1.84      (![X0 : $i]:
% 1.66/1.84         (((k1_funct_1 @ sk_C_1 @ sk_D) != (k1_funct_1 @ sk_C_1 @ X0))
% 1.66/1.84          | ~ (r2_hidden @ X0 @ sk_A)
% 1.66/1.84          | ((sk_E) = (X0))
% 1.66/1.84          | ~ (r2_hidden @ sk_E @ sk_A))),
% 1.66/1.84      inference('sup-', [status(thm)], ['132', '145'])).
% 1.66/1.84  thf('147', plain,
% 1.66/1.84      (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A))
% 1.66/1.84         <= (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)))),
% 1.66/1.84      inference('split', [status(esa)], ['0'])).
% 1.66/1.84  thf('148', plain,
% 1.66/1.84      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.66/1.84         ((r2_hidden @ X19 @ X18) | ~ (zip_tseitin_2 @ X19 @ X17 @ X20 @ X18))),
% 1.66/1.84      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.66/1.84  thf('149', plain,
% 1.66/1.84      (((r2_hidden @ sk_E @ sk_A))
% 1.66/1.84         <= (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)))),
% 1.66/1.84      inference('sup-', [status(thm)], ['147', '148'])).
% 1.66/1.84  thf('150', plain, (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A))),
% 1.66/1.84      inference('sat_resolution*', [status(thm)],
% 1.66/1.84                ['5', '54', '60', '85', '86', '87', '129', '130'])).
% 1.66/1.84  thf('151', plain, ((r2_hidden @ sk_E @ sk_A)),
% 1.66/1.84      inference('simpl_trail', [status(thm)], ['149', '150'])).
% 1.66/1.84  thf('152', plain,
% 1.66/1.84      (![X0 : $i]:
% 1.66/1.84         (((k1_funct_1 @ sk_C_1 @ sk_D) != (k1_funct_1 @ sk_C_1 @ X0))
% 1.66/1.84          | ~ (r2_hidden @ X0 @ sk_A)
% 1.66/1.84          | ((sk_E) = (X0)))),
% 1.66/1.84      inference('demod', [status(thm)], ['146', '151'])).
% 1.66/1.84  thf('153', plain, ((((sk_E) = (sk_D)) | ~ (r2_hidden @ sk_D @ sk_A))),
% 1.66/1.84      inference('eq_res', [status(thm)], ['152'])).
% 1.66/1.84  thf('154', plain,
% 1.66/1.84      (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A))
% 1.66/1.84         <= (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)))),
% 1.66/1.84      inference('split', [status(esa)], ['0'])).
% 1.66/1.84  thf('155', plain,
% 1.66/1.84      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.66/1.84         ((r2_hidden @ X17 @ X18) | ~ (zip_tseitin_2 @ X19 @ X17 @ X20 @ X18))),
% 1.66/1.84      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.66/1.84  thf('156', plain,
% 1.66/1.84      (((r2_hidden @ sk_D @ sk_A))
% 1.66/1.84         <= (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)))),
% 1.66/1.84      inference('sup-', [status(thm)], ['154', '155'])).
% 1.66/1.84  thf('157', plain, (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A))),
% 1.66/1.84      inference('sat_resolution*', [status(thm)],
% 1.66/1.84                ['5', '54', '60', '85', '86', '87', '129', '130'])).
% 1.66/1.84  thf('158', plain, ((r2_hidden @ sk_D @ sk_A)),
% 1.66/1.84      inference('simpl_trail', [status(thm)], ['156', '157'])).
% 1.66/1.84  thf('159', plain, (((sk_E) = (sk_D))),
% 1.66/1.84      inference('demod', [status(thm)], ['153', '158'])).
% 1.66/1.84  thf('160', plain, ((((sk_D) != (sk_E))) <= (~ (((sk_D) = (sk_E))))),
% 1.66/1.84      inference('split', [status(esa)], ['4'])).
% 1.66/1.84  thf('161', plain, (~ (((sk_D) = (sk_E)))),
% 1.66/1.84      inference('sat_resolution*', [status(thm)],
% 1.66/1.84                ['130', '54', '60', '85', '86', '87', '129', '5'])).
% 1.66/1.84  thf('162', plain, (((sk_D) != (sk_E))),
% 1.66/1.84      inference('simpl_trail', [status(thm)], ['160', '161'])).
% 1.66/1.84  thf('163', plain, ($false),
% 1.66/1.84      inference('simplify_reflect-', [status(thm)], ['159', '162'])).
% 1.66/1.84  
% 1.66/1.84  % SZS output end Refutation
% 1.66/1.84  
% 1.66/1.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
