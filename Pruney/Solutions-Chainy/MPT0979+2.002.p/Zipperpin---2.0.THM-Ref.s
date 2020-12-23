%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wkN84BMHbe

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:53 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  203 (2694 expanded)
%              Number of leaves         :   36 ( 715 expanded)
%              Depth                    :   27
%              Number of atoms          : 1937 (41665 expanded)
%              Number of equality atoms :  202 (4336 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_funct_1 @ X21 @ X18 )
        = ( k1_funct_1 @ X21 @ X20 ) )
      | ~ ( zip_tseitin_2 @ X20 @ X18 @ X21 @ X19 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_funct_2 @ X14 @ X12 @ X13 )
      | ( X12
        = ( k1_relset_1 @ X12 @ X13 @ X14 ) )
      | ~ ( zip_tseitin_1 @ X14 @ X13 @ X12 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( zip_tseitin_0 @ X15 @ X16 )
      | ( zip_tseitin_1 @ X17 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('16',plain,
    ( ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_B_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X10 @ X11 )
      | ( X11 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('18',plain,(
    ! [X10: $i] :
      ( zip_tseitin_0 @ X10 @ k1_xboole_0 ) ),
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
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
    ! [X4: $i] :
      ( ( r2_hidden @ ( sk_C @ X4 ) @ ( k1_relat_1 @ X4 ) )
      | ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('25',plain,(
    ! [X4: $i] :
      ( ( r2_hidden @ ( sk_B @ X4 ) @ ( k1_relat_1 @ X4 ) )
      | ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('26',plain,(
    ! [X4: $i] :
      ( ( ( k1_funct_1 @ X4 @ ( sk_B @ X4 ) )
        = ( k1_funct_1 @ X4 @ ( sk_C @ X4 ) ) )
      | ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('27',plain,(
    ! [X18: $i,X20: $i,X21: $i,X22: $i] :
      ( ( zip_tseitin_2 @ X20 @ X18 @ X21 @ X22 )
      | ( ( k1_funct_1 @ X21 @ X18 )
       != ( k1_funct_1 @ X21 @ X20 ) )
      | ~ ( r2_hidden @ X20 @ X22 )
      | ~ ( r2_hidden @ X18 @ X22 ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('39',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('41',plain,
    ( ( ( zip_tseitin_2 @ ( sk_B @ sk_C_1 ) @ ( sk_C @ sk_C_1 ) @ sk_C_1 @ k1_xboole_0 )
      | ( v2_funct_1 @ sk_C_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','39','40'])).

thf('42',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('43',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A )
      | ( X24 = X23 )
      | ( v2_funct_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('44',plain,
    ( ! [X23: $i,X24: $i] :
        ( ( X24 = X23 )
        | ~ ( zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A ) )
   <= ! [X23: $i,X24: $i] :
        ( ( X24 = X23 )
        | ~ ( zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['43'])).

thf('45',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_2 @ X1 @ X0 @ sk_C_1 @ k1_xboole_0 )
        | ( X0 = X1 ) )
   <= ( ! [X23: $i,X24: $i] :
          ( ( X24 = X23 )
          | ~ ( zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,
    ( ( ( v2_funct_1 @ sk_C_1 )
      | ( ( sk_C @ sk_C_1 )
        = ( sk_B @ sk_C_1 ) ) )
   <= ( ! [X23: $i,X24: $i] :
          ( ( X24 = X23 )
          | ~ ( zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','45'])).

thf('47',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('48',plain,
    ( ( ( sk_C @ sk_C_1 )
      = ( sk_B @ sk_C_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_C_1 )
      & ! [X23: $i,X24: $i] :
          ( ( X24 = X23 )
          | ~ ( zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X4: $i] :
      ( ( ( sk_B @ X4 )
       != ( sk_C @ X4 ) )
      | ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('50',plain,
    ( ( ( ( sk_B @ sk_C_1 )
       != ( sk_B @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( v2_funct_1 @ sk_C_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_C_1 )
      & ! [X23: $i,X24: $i] :
          ( ( X24 = X23 )
          | ~ ( zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['37','38'])).

thf('52',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('53',plain,
    ( ( ( ( sk_B @ sk_C_1 )
       != ( sk_B @ sk_C_1 ) )
      | ( v2_funct_1 @ sk_C_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_C_1 )
      & ! [X23: $i,X24: $i] :
          ( ( X24 = X23 )
          | ~ ( zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ( v2_funct_1 @ sk_C_1 )
   <= ( ~ ( v2_funct_1 @ sk_C_1 )
      & ! [X23: $i,X24: $i] :
          ( ( X24 = X23 )
          | ~ ( zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('56',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( v2_funct_1 @ sk_C_1 )
    | ~ ! [X23: $i,X24: $i] :
          ( ( X24 = X23 )
          | ~ ( zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
   <= ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('58',plain,
    ( ! [X23: $i,X24: $i] :
        ( ( X24 = X23 )
        | ~ ( zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A ) )
   <= ! [X23: $i,X24: $i] :
        ( ( X24 = X23 )
        | ~ ( zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['43'])).

thf('59',plain,
    ( ( sk_D = sk_E )
   <= ( ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
      & ! [X23: $i,X24: $i] :
          ( ( X24 = X23 )
          | ~ ( zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( sk_D != sk_E )
   <= ( sk_D != sk_E ) ),
    inference(split,[status(esa)],['4'])).

thf('61',plain,
    ( ( sk_D != sk_D )
   <= ( ( sk_D != sk_E )
      & ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
      & ! [X23: $i,X24: $i] :
          ( ( X24 = X23 )
          | ~ ( zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ! [X23: $i,X24: $i] :
          ( ( X24 = X23 )
          | ~ ( zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A ) )
    | ( sk_D = sk_E )
    | ~ ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ sk_D )
      = ( k1_funct_1 @ sk_C_1 @ sk_E ) )
   <= ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('64',plain,
    ( ( v2_funct_1 @ sk_C_1 )
   <= ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['43'])).

thf('65',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','19','22'])).

thf('66',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ~ ( r2_hidden @ X5 @ ( k1_relat_1 @ X4 ) )
      | ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ X4 ) )
      | ( ( k1_funct_1 @ X4 @ X5 )
       != ( k1_funct_1 @ X4 @ X6 ) )
      | ( X5 = X6 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('67',plain,
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
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['37','38'])).

thf('69',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('70',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','19','22'])).

thf('71',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
        | ( X0 = X1 )
        | ( ( k1_funct_1 @ sk_C_1 @ X0 )
         != ( k1_funct_1 @ sk_C_1 @ X1 ) )
        | ~ ( r2_hidden @ X1 @ k1_xboole_0 )
        | ~ ( v2_funct_1 @ sk_C_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','68','69','70'])).

thf('72',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
        | ( ( k1_funct_1 @ sk_C_1 @ X1 )
         != ( k1_funct_1 @ sk_C_1 @ X0 ) )
        | ( X1 = X0 )
        | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) )
   <= ( ( v2_funct_1 @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['64','71'])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_C_1 @ sk_D )
         != ( k1_funct_1 @ sk_C_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_E @ k1_xboole_0 )
        | ( sk_E = X0 )
        | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) )
   <= ( ( v2_funct_1 @ sk_C_1 )
      & ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','72'])).

thf('74',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('75',plain,
    ( ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
   <= ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('76',plain,
    ( ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ k1_xboole_0 )
   <= ( ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X20 @ X19 )
      | ~ ( zip_tseitin_2 @ X20 @ X18 @ X21 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('78',plain,
    ( ( r2_hidden @ sk_E @ k1_xboole_0 )
   <= ( ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_C_1 @ sk_D )
         != ( k1_funct_1 @ sk_C_1 @ X0 ) )
        | ( sk_E = X0 )
        | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) )
   <= ( ( v2_funct_1 @ sk_C_1 )
      & ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['73','78'])).

thf('80',plain,
    ( ( ~ ( r2_hidden @ sk_D @ k1_xboole_0 )
      | ( sk_E = sk_D ) )
   <= ( ( v2_funct_1 @ sk_C_1 )
      & ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(eq_res,[status(thm)],['79'])).

thf('81',plain,
    ( ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ k1_xboole_0 )
   <= ( ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('82',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X18 @ X19 )
      | ~ ( zip_tseitin_2 @ X20 @ X18 @ X21 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('83',plain,
    ( ( r2_hidden @ sk_D @ k1_xboole_0 )
   <= ( ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( sk_E = sk_D )
   <= ( ( v2_funct_1 @ sk_C_1 )
      & ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['80','83'])).

thf('85',plain,
    ( ( sk_D != sk_E )
   <= ( sk_D != sk_E ) ),
    inference(split,[status(esa)],['4'])).

thf('86',plain,
    ( ( sk_D != sk_D )
   <= ( ( sk_D != sk_E )
      & ( v2_funct_1 @ sk_C_1 )
      & ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
    | ( sk_D = sk_E ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('89',plain,
    ( ( v2_funct_1 @ sk_C_1 )
    | ! [X23: $i,X24: $i] :
        ( ( X24 = X23 )
        | ~ ( zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['43'])).

thf('90',plain,(
    ! [X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X10 @ X11 )
      | ( X10 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('91',plain,(
    ! [X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X10 @ X11 )
      | ( X10 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('92',plain,(
    ! [X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X10 @ X11 )
      | ( X10 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 = X0 )
      | ( zip_tseitin_0 @ X0 @ X3 )
      | ( zip_tseitin_0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('95',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( zip_tseitin_0 @ X15 @ X16 )
      | ( zip_tseitin_1 @ X17 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('96',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( sk_B_1 = X1 )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('99',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
        | ( zip_tseitin_0 @ X0 @ X1 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ! [X1: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ X1 )
        | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( zip_tseitin_0 @ X0 @ X1 )
        | ( zip_tseitin_0 @ X0 @ X2 )
        | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['90','100'])).

thf('102',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
        | ( zip_tseitin_0 @ X1 @ X0 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['101'])).

thf('103',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('104',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_funct_2 @ X14 @ X12 @ X13 )
      | ( X12
        = ( k1_relset_1 @ X12 @ X13 @ X14 ) )
      | ~ ( zip_tseitin_1 @ X14 @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('105',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('107',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('108',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['105','108'])).

thf('110',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_0 @ X1 @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C_1 ) ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['102','109'])).

thf('111',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('112',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['105','108'])).

thf('114',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ ( sk_B @ X0 ) @ ( sk_C @ X0 ) @ X0 @ ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('116',plain,
    ( ( ( zip_tseitin_2 @ ( sk_B @ sk_C_1 ) @ ( sk_C @ sk_C_1 ) @ sk_C_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( v2_funct_1 @ sk_C_1 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['37','38'])).

thf('118',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('119',plain,
    ( ( ( zip_tseitin_2 @ ( sk_B @ sk_C_1 ) @ ( sk_C @ sk_C_1 ) @ sk_C_1 @ sk_A )
      | ( v2_funct_1 @ sk_C_1 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,
    ( ! [X23: $i,X24: $i] :
        ( ( X24 = X23 )
        | ~ ( zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A ) )
   <= ! [X23: $i,X24: $i] :
        ( ( X24 = X23 )
        | ~ ( zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['43'])).

thf('121',plain,
    ( ( ( v2_funct_1 @ sk_C_1 )
      | ( ( sk_C @ sk_C_1 )
        = ( sk_B @ sk_C_1 ) ) )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ! [X23: $i,X24: $i] :
          ( ( X24 = X23 )
          | ~ ( zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('123',plain,
    ( ( ( sk_C @ sk_C_1 )
      = ( sk_B @ sk_C_1 ) )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ~ ( v2_funct_1 @ sk_C_1 )
      & ! [X23: $i,X24: $i] :
          ( ( X24 = X23 )
          | ~ ( zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X4: $i] :
      ( ( ( sk_B @ X4 )
       != ( sk_C @ X4 ) )
      | ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('125',plain,
    ( ( ( ( sk_B @ sk_C_1 )
       != ( sk_B @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( v2_funct_1 @ sk_C_1 ) )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ~ ( v2_funct_1 @ sk_C_1 )
      & ! [X23: $i,X24: $i] :
          ( ( X24 = X23 )
          | ~ ( zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['37','38'])).

thf('127',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('128',plain,
    ( ( ( ( sk_B @ sk_C_1 )
       != ( sk_B @ sk_C_1 ) )
      | ( v2_funct_1 @ sk_C_1 ) )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ~ ( v2_funct_1 @ sk_C_1 )
      & ! [X23: $i,X24: $i] :
          ( ( X24 = X23 )
          | ~ ( zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['125','126','127'])).

thf('129',plain,
    ( ( v2_funct_1 @ sk_C_1 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ~ ( v2_funct_1 @ sk_C_1 )
      & ! [X23: $i,X24: $i] :
          ( ( X24 = X23 )
          | ~ ( zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('131',plain,
    ( ~ ! [X23: $i,X24: $i] :
          ( ( X24 = X23 )
          | ~ ( zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('133',plain,(
    zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['5','56','62','87','88','89','131','132'])).

thf('134',plain,
    ( ( k1_funct_1 @ sk_C_1 @ sk_D )
    = ( k1_funct_1 @ sk_C_1 @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['3','133'])).

thf('135',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('136',plain,
    ( ( v2_funct_1 @ sk_C_1 )
    | ( sk_A != k1_xboole_0 )
    | ~ ! [X23: $i,X24: $i] :
          ( ( X24 = X23 )
          | ~ ( zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('137',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['89','5','132','136','62','87','88'])).

thf('138',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['135','137'])).

thf('139',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ~ ( r2_hidden @ X5 @ ( k1_relat_1 @ X4 ) )
      | ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ X4 ) )
      | ( ( k1_funct_1 @ X4 @ X5 )
       != ( k1_funct_1 @ X4 @ X6 ) )
      | ( X5 = X6 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_C_1 @ X0 )
       != ( k1_funct_1 @ sk_C_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['37','38'])).

thf('142',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('143',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['135','137'])).

thf('144',plain,
    ( ( v2_funct_1 @ sk_C_1 )
   <= ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['43'])).

thf('145',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['5','132','56','62','87','88','89','131'])).

thf('146',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(simpl_trail,[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_C_1 @ X0 )
       != ( k1_funct_1 @ sk_C_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['140','141','142','143','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ sk_D )
       != ( k1_funct_1 @ sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_E = X0 )
      | ~ ( r2_hidden @ sk_E @ sk_A ) ) ),
    inference('sup-',[status(thm)],['134','147'])).

thf('149',plain,
    ( ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
   <= ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('150',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X20 @ X19 )
      | ~ ( zip_tseitin_2 @ X20 @ X18 @ X21 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('151',plain,
    ( ( r2_hidden @ sk_E @ sk_A )
   <= ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['5','56','62','87','88','89','131','132'])).

thf('153',plain,(
    r2_hidden @ sk_E @ sk_A ),
    inference(simpl_trail,[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ sk_D )
       != ( k1_funct_1 @ sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_E = X0 ) ) ),
    inference(demod,[status(thm)],['148','153'])).

thf('155',plain,
    ( ( sk_E = sk_D )
    | ~ ( r2_hidden @ sk_D @ sk_A ) ),
    inference(eq_res,[status(thm)],['154'])).

thf('156',plain,
    ( ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
   <= ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('157',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X18 @ X19 )
      | ~ ( zip_tseitin_2 @ X20 @ X18 @ X21 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('158',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
   <= ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['5','56','62','87','88','89','131','132'])).

thf('160',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(simpl_trail,[status(thm)],['158','159'])).

thf('161',plain,(
    sk_E = sk_D ),
    inference(demod,[status(thm)],['155','160'])).

thf('162',plain,
    ( ( sk_D != sk_E )
   <= ( sk_D != sk_E ) ),
    inference(split,[status(esa)],['4'])).

thf('163',plain,(
    sk_D != sk_E ),
    inference('sat_resolution*',[status(thm)],['132','56','62','87','88','89','131','5'])).

thf('164',plain,(
    sk_D != sk_E ),
    inference(simpl_trail,[status(thm)],['162','163'])).

thf('165',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['161','164'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wkN84BMHbe
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:04:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.65/1.83  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.65/1.83  % Solved by: fo/fo7.sh
% 1.65/1.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.65/1.83  % done 1483 iterations in 1.371s
% 1.65/1.83  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.65/1.83  % SZS output start Refutation
% 1.65/1.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.65/1.83  thf(sk_E_type, type, sk_E: $i).
% 1.65/1.83  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.65/1.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.65/1.83  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.65/1.83  thf(sk_C_type, type, sk_C: $i > $i).
% 1.65/1.83  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $i > $o).
% 1.65/1.83  thf(sk_A_type, type, sk_A: $i).
% 1.65/1.83  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.65/1.83  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.65/1.83  thf(sk_D_type, type, sk_D: $i).
% 1.65/1.83  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.65/1.83  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.65/1.83  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.65/1.83  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.65/1.83  thf(sk_B_type, type, sk_B: $i > $i).
% 1.65/1.83  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.65/1.83  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.65/1.83  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.65/1.83  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.65/1.83  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.65/1.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.65/1.83  thf(t25_funct_2, conjecture,
% 1.65/1.83    (![A:$i,B:$i,C:$i]:
% 1.65/1.83     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.65/1.83         ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) =>
% 1.65/1.83       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.65/1.83         ( ( v2_funct_1 @ C ) <=>
% 1.65/1.83           ( ![D:$i,E:$i]:
% 1.65/1.83             ( ( ( ( k1_funct_1 @ C @ D ) = ( k1_funct_1 @ C @ E ) ) & 
% 1.65/1.83                 ( r2_hidden @ E @ A ) & ( r2_hidden @ D @ A ) ) =>
% 1.65/1.83               ( ( D ) = ( E ) ) ) ) ) ) ))).
% 1.65/1.83  thf(zf_stmt_0, type, zip_tseitin_2 : $i > $i > $i > $i > $o).
% 1.65/1.83  thf(zf_stmt_1, axiom,
% 1.65/1.83    (![E:$i,D:$i,C:$i,A:$i]:
% 1.65/1.83     ( ( zip_tseitin_2 @ E @ D @ C @ A ) <=>
% 1.65/1.83       ( ( r2_hidden @ D @ A ) & ( r2_hidden @ E @ A ) & 
% 1.65/1.83         ( ( k1_funct_1 @ C @ D ) = ( k1_funct_1 @ C @ E ) ) ) ))).
% 1.65/1.83  thf(zf_stmt_2, conjecture,
% 1.65/1.83    (![A:$i,B:$i,C:$i]:
% 1.65/1.83     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.65/1.83         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.65/1.83       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.65/1.83         ( ( v2_funct_1 @ C ) <=>
% 1.65/1.83           ( ![D:$i,E:$i]:
% 1.65/1.83             ( ( zip_tseitin_2 @ E @ D @ C @ A ) => ( ( D ) = ( E ) ) ) ) ) ) ))).
% 1.65/1.83  thf(zf_stmt_3, negated_conjecture,
% 1.65/1.83    (~( ![A:$i,B:$i,C:$i]:
% 1.65/1.83        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.65/1.83            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.65/1.83          ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.65/1.83            ( ( v2_funct_1 @ C ) <=>
% 1.65/1.83              ( ![D:$i,E:$i]:
% 1.65/1.83                ( ( zip_tseitin_2 @ E @ D @ C @ A ) => ( ( D ) = ( E ) ) ) ) ) ) ) )),
% 1.65/1.83    inference('cnf.neg', [status(esa)], [zf_stmt_2])).
% 1.65/1.83  thf('0', plain,
% 1.65/1.83      (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A) | ~ (v2_funct_1 @ sk_C_1))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.65/1.83  thf('1', plain,
% 1.65/1.83      (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A))
% 1.65/1.83         <= (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)))),
% 1.65/1.83      inference('split', [status(esa)], ['0'])).
% 1.65/1.83  thf('2', plain,
% 1.65/1.83      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.65/1.83         (((k1_funct_1 @ X21 @ X18) = (k1_funct_1 @ X21 @ X20))
% 1.65/1.83          | ~ (zip_tseitin_2 @ X20 @ X18 @ X21 @ X19))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.65/1.83  thf('3', plain,
% 1.65/1.83      ((((k1_funct_1 @ sk_C_1 @ sk_D) = (k1_funct_1 @ sk_C_1 @ sk_E)))
% 1.65/1.83         <= (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['1', '2'])).
% 1.65/1.83  thf('4', plain, ((((sk_D) != (sk_E)) | ~ (v2_funct_1 @ sk_C_1))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.65/1.83  thf('5', plain, (~ (((sk_D) = (sk_E))) | ~ ((v2_funct_1 @ sk_C_1))),
% 1.65/1.83      inference('split', [status(esa)], ['4'])).
% 1.65/1.83  thf('6', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B_1) != (k1_xboole_0)))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.65/1.83  thf('7', plain, ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('split', [status(esa)], ['6'])).
% 1.65/1.83  thf('8', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.65/1.83  thf('9', plain,
% 1.65/1.83      (((v1_funct_2 @ sk_C_1 @ k1_xboole_0 @ sk_B_1))
% 1.65/1.83         <= ((((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('sup+', [status(thm)], ['7', '8'])).
% 1.65/1.83  thf(d1_funct_2, axiom,
% 1.65/1.83    (![A:$i,B:$i,C:$i]:
% 1.65/1.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.65/1.83       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.65/1.83           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.65/1.83             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.65/1.83         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.65/1.83           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.65/1.83             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.65/1.83  thf(zf_stmt_4, axiom,
% 1.65/1.83    (![C:$i,B:$i,A:$i]:
% 1.65/1.83     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.65/1.83       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.65/1.83  thf('10', plain,
% 1.65/1.83      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.65/1.83         (~ (v1_funct_2 @ X14 @ X12 @ X13)
% 1.65/1.83          | ((X12) = (k1_relset_1 @ X12 @ X13 @ X14))
% 1.65/1.83          | ~ (zip_tseitin_1 @ X14 @ X13 @ X12))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.65/1.83  thf('11', plain,
% 1.65/1.83      (((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ k1_xboole_0)
% 1.65/1.83         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_1))))
% 1.65/1.83         <= ((((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['9', '10'])).
% 1.65/1.83  thf('12', plain,
% 1.65/1.83      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('split', [status(esa)], ['6'])).
% 1.65/1.83  thf('13', plain,
% 1.65/1.83      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.65/1.83  thf('14', plain,
% 1.65/1.83      (((m1_subset_1 @ sk_C_1 @ 
% 1.65/1.83         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 1.65/1.83         <= ((((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('sup+', [status(thm)], ['12', '13'])).
% 1.65/1.83  thf(zf_stmt_5, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.65/1.83  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $o).
% 1.65/1.83  thf(zf_stmt_7, axiom,
% 1.65/1.83    (![B:$i,A:$i]:
% 1.65/1.83     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.65/1.83       ( zip_tseitin_0 @ B @ A ) ))).
% 1.65/1.83  thf(zf_stmt_8, axiom,
% 1.65/1.83    (![A:$i,B:$i,C:$i]:
% 1.65/1.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.65/1.83       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.65/1.83         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.65/1.83           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.65/1.83             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.65/1.83  thf('15', plain,
% 1.65/1.83      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.65/1.83         (~ (zip_tseitin_0 @ X15 @ X16)
% 1.65/1.83          | (zip_tseitin_1 @ X17 @ X15 @ X16)
% 1.65/1.83          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X15))))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_8])).
% 1.65/1.83  thf('16', plain,
% 1.65/1.83      ((((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ k1_xboole_0)
% 1.65/1.83         | ~ (zip_tseitin_0 @ sk_B_1 @ k1_xboole_0)))
% 1.65/1.83         <= ((((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['14', '15'])).
% 1.65/1.83  thf('17', plain,
% 1.65/1.83      (![X10 : $i, X11 : $i]:
% 1.65/1.83         ((zip_tseitin_0 @ X10 @ X11) | ((X11) != (k1_xboole_0)))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_7])).
% 1.65/1.83  thf('18', plain, (![X10 : $i]: (zip_tseitin_0 @ X10 @ k1_xboole_0)),
% 1.65/1.83      inference('simplify', [status(thm)], ['17'])).
% 1.65/1.83  thf('19', plain,
% 1.65/1.83      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ k1_xboole_0))
% 1.65/1.83         <= ((((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('demod', [status(thm)], ['16', '18'])).
% 1.65/1.83  thf('20', plain,
% 1.65/1.83      (((m1_subset_1 @ sk_C_1 @ 
% 1.65/1.83         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 1.65/1.83         <= ((((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('sup+', [status(thm)], ['12', '13'])).
% 1.65/1.83  thf(redefinition_k1_relset_1, axiom,
% 1.65/1.83    (![A:$i,B:$i,C:$i]:
% 1.65/1.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.65/1.83       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.65/1.83  thf('21', plain,
% 1.65/1.83      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.65/1.83         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 1.65/1.83          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 1.65/1.83      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.65/1.83  thf('22', plain,
% 1.65/1.83      ((((k1_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1)))
% 1.65/1.83         <= ((((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['20', '21'])).
% 1.65/1.83  thf('23', plain,
% 1.65/1.83      ((((k1_xboole_0) = (k1_relat_1 @ sk_C_1)))
% 1.65/1.83         <= ((((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('demod', [status(thm)], ['11', '19', '22'])).
% 1.65/1.83  thf(d8_funct_1, axiom,
% 1.65/1.83    (![A:$i]:
% 1.65/1.83     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.65/1.83       ( ( v2_funct_1 @ A ) <=>
% 1.65/1.83         ( ![B:$i,C:$i]:
% 1.65/1.83           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 1.65/1.83               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 1.65/1.83               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 1.65/1.83             ( ( B ) = ( C ) ) ) ) ) ))).
% 1.65/1.83  thf('24', plain,
% 1.65/1.83      (![X4 : $i]:
% 1.65/1.83         ((r2_hidden @ (sk_C @ X4) @ (k1_relat_1 @ X4))
% 1.65/1.83          | (v2_funct_1 @ X4)
% 1.65/1.83          | ~ (v1_funct_1 @ X4)
% 1.65/1.83          | ~ (v1_relat_1 @ X4))),
% 1.65/1.83      inference('cnf', [status(esa)], [d8_funct_1])).
% 1.65/1.83  thf('25', plain,
% 1.65/1.83      (![X4 : $i]:
% 1.65/1.83         ((r2_hidden @ (sk_B @ X4) @ (k1_relat_1 @ X4))
% 1.65/1.83          | (v2_funct_1 @ X4)
% 1.65/1.83          | ~ (v1_funct_1 @ X4)
% 1.65/1.83          | ~ (v1_relat_1 @ X4))),
% 1.65/1.83      inference('cnf', [status(esa)], [d8_funct_1])).
% 1.65/1.83  thf('26', plain,
% 1.65/1.83      (![X4 : $i]:
% 1.65/1.83         (((k1_funct_1 @ X4 @ (sk_B @ X4)) = (k1_funct_1 @ X4 @ (sk_C @ X4)))
% 1.65/1.83          | (v2_funct_1 @ X4)
% 1.65/1.83          | ~ (v1_funct_1 @ X4)
% 1.65/1.83          | ~ (v1_relat_1 @ X4))),
% 1.65/1.83      inference('cnf', [status(esa)], [d8_funct_1])).
% 1.65/1.83  thf('27', plain,
% 1.65/1.83      (![X18 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.65/1.83         ((zip_tseitin_2 @ X20 @ X18 @ X21 @ X22)
% 1.65/1.83          | ((k1_funct_1 @ X21 @ X18) != (k1_funct_1 @ X21 @ X20))
% 1.65/1.83          | ~ (r2_hidden @ X20 @ X22)
% 1.65/1.83          | ~ (r2_hidden @ X18 @ X22))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.65/1.83  thf('28', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.83         (((k1_funct_1 @ X0 @ (sk_B @ X0)) != (k1_funct_1 @ X0 @ X1))
% 1.65/1.83          | ~ (v1_relat_1 @ X0)
% 1.65/1.83          | ~ (v1_funct_1 @ X0)
% 1.65/1.83          | (v2_funct_1 @ X0)
% 1.65/1.83          | ~ (r2_hidden @ (sk_C @ X0) @ X2)
% 1.65/1.83          | ~ (r2_hidden @ X1 @ X2)
% 1.65/1.83          | (zip_tseitin_2 @ X1 @ (sk_C @ X0) @ X0 @ X2))),
% 1.65/1.83      inference('sup-', [status(thm)], ['26', '27'])).
% 1.65/1.83  thf('29', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         ((zip_tseitin_2 @ (sk_B @ X1) @ (sk_C @ X1) @ X1 @ X0)
% 1.65/1.83          | ~ (r2_hidden @ (sk_B @ X1) @ X0)
% 1.65/1.83          | ~ (r2_hidden @ (sk_C @ X1) @ X0)
% 1.65/1.83          | (v2_funct_1 @ X1)
% 1.65/1.83          | ~ (v1_funct_1 @ X1)
% 1.65/1.83          | ~ (v1_relat_1 @ X1))),
% 1.65/1.83      inference('eq_res', [status(thm)], ['28'])).
% 1.65/1.83  thf('30', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         (~ (v1_relat_1 @ X0)
% 1.65/1.83          | ~ (v1_funct_1 @ X0)
% 1.65/1.83          | (v2_funct_1 @ X0)
% 1.65/1.83          | ~ (v1_relat_1 @ X0)
% 1.65/1.83          | ~ (v1_funct_1 @ X0)
% 1.65/1.83          | (v2_funct_1 @ X0)
% 1.65/1.83          | ~ (r2_hidden @ (sk_C @ X0) @ (k1_relat_1 @ X0))
% 1.65/1.83          | (zip_tseitin_2 @ (sk_B @ X0) @ (sk_C @ X0) @ X0 @ (k1_relat_1 @ X0)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['25', '29'])).
% 1.65/1.83  thf('31', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         ((zip_tseitin_2 @ (sk_B @ X0) @ (sk_C @ X0) @ X0 @ (k1_relat_1 @ X0))
% 1.65/1.83          | ~ (r2_hidden @ (sk_C @ X0) @ (k1_relat_1 @ X0))
% 1.65/1.83          | (v2_funct_1 @ X0)
% 1.65/1.83          | ~ (v1_funct_1 @ X0)
% 1.65/1.83          | ~ (v1_relat_1 @ X0))),
% 1.65/1.83      inference('simplify', [status(thm)], ['30'])).
% 1.65/1.83  thf('32', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         (~ (v1_relat_1 @ X0)
% 1.65/1.83          | ~ (v1_funct_1 @ X0)
% 1.65/1.83          | (v2_funct_1 @ X0)
% 1.65/1.83          | ~ (v1_relat_1 @ X0)
% 1.65/1.83          | ~ (v1_funct_1 @ X0)
% 1.65/1.83          | (v2_funct_1 @ X0)
% 1.65/1.83          | (zip_tseitin_2 @ (sk_B @ X0) @ (sk_C @ X0) @ X0 @ (k1_relat_1 @ X0)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['24', '31'])).
% 1.65/1.83  thf('33', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         ((zip_tseitin_2 @ (sk_B @ X0) @ (sk_C @ X0) @ X0 @ (k1_relat_1 @ X0))
% 1.65/1.83          | (v2_funct_1 @ X0)
% 1.65/1.83          | ~ (v1_funct_1 @ X0)
% 1.65/1.83          | ~ (v1_relat_1 @ X0))),
% 1.65/1.83      inference('simplify', [status(thm)], ['32'])).
% 1.65/1.83  thf('34', plain,
% 1.65/1.83      ((((zip_tseitin_2 @ (sk_B @ sk_C_1) @ (sk_C @ sk_C_1) @ sk_C_1 @ 
% 1.65/1.83          k1_xboole_0)
% 1.65/1.83         | ~ (v1_relat_1 @ sk_C_1)
% 1.65/1.83         | ~ (v1_funct_1 @ sk_C_1)
% 1.65/1.83         | (v2_funct_1 @ sk_C_1))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('sup+', [status(thm)], ['23', '33'])).
% 1.65/1.83  thf('35', plain,
% 1.65/1.83      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.65/1.83  thf(cc2_relat_1, axiom,
% 1.65/1.83    (![A:$i]:
% 1.65/1.83     ( ( v1_relat_1 @ A ) =>
% 1.65/1.83       ( ![B:$i]:
% 1.65/1.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.65/1.83  thf('36', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.65/1.83          | (v1_relat_1 @ X0)
% 1.65/1.83          | ~ (v1_relat_1 @ X1))),
% 1.65/1.83      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.65/1.83  thf('37', plain,
% 1.65/1.83      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_C_1))),
% 1.65/1.83      inference('sup-', [status(thm)], ['35', '36'])).
% 1.65/1.83  thf(fc6_relat_1, axiom,
% 1.65/1.83    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.65/1.83  thf('38', plain,
% 1.65/1.83      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.65/1.83      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.65/1.83  thf('39', plain, ((v1_relat_1 @ sk_C_1)),
% 1.65/1.83      inference('demod', [status(thm)], ['37', '38'])).
% 1.65/1.83  thf('40', plain, ((v1_funct_1 @ sk_C_1)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.65/1.83  thf('41', plain,
% 1.65/1.83      ((((zip_tseitin_2 @ (sk_B @ sk_C_1) @ (sk_C @ sk_C_1) @ sk_C_1 @ 
% 1.65/1.83          k1_xboole_0)
% 1.65/1.83         | (v2_funct_1 @ sk_C_1))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('demod', [status(thm)], ['34', '39', '40'])).
% 1.65/1.83  thf('42', plain,
% 1.65/1.83      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('split', [status(esa)], ['6'])).
% 1.65/1.83  thf('43', plain,
% 1.65/1.83      (![X23 : $i, X24 : $i]:
% 1.65/1.83         (~ (zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A)
% 1.65/1.83          | ((X24) = (X23))
% 1.65/1.83          | (v2_funct_1 @ sk_C_1))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.65/1.83  thf('44', plain,
% 1.65/1.83      ((![X23 : $i, X24 : $i]:
% 1.65/1.83          (((X24) = (X23)) | ~ (zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A)))
% 1.65/1.83         <= ((![X23 : $i, X24 : $i]:
% 1.65/1.83                (((X24) = (X23))
% 1.65/1.83                 | ~ (zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A))))),
% 1.65/1.83      inference('split', [status(esa)], ['43'])).
% 1.65/1.83  thf('45', plain,
% 1.65/1.83      ((![X0 : $i, X1 : $i]:
% 1.65/1.83          (~ (zip_tseitin_2 @ X1 @ X0 @ sk_C_1 @ k1_xboole_0) | ((X0) = (X1))))
% 1.65/1.83         <= ((![X23 : $i, X24 : $i]:
% 1.65/1.83                (((X24) = (X23))
% 1.65/1.83                 | ~ (zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A))) & 
% 1.65/1.83             (((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['42', '44'])).
% 1.65/1.83  thf('46', plain,
% 1.65/1.83      ((((v2_funct_1 @ sk_C_1) | ((sk_C @ sk_C_1) = (sk_B @ sk_C_1))))
% 1.65/1.83         <= ((![X23 : $i, X24 : $i]:
% 1.65/1.83                (((X24) = (X23))
% 1.65/1.83                 | ~ (zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A))) & 
% 1.65/1.83             (((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['41', '45'])).
% 1.65/1.83  thf('47', plain, ((~ (v2_funct_1 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 1.65/1.83      inference('split', [status(esa)], ['4'])).
% 1.65/1.83  thf('48', plain,
% 1.65/1.83      ((((sk_C @ sk_C_1) = (sk_B @ sk_C_1)))
% 1.65/1.83         <= (~ ((v2_funct_1 @ sk_C_1)) & 
% 1.65/1.83             (![X23 : $i, X24 : $i]:
% 1.65/1.83                (((X24) = (X23))
% 1.65/1.83                 | ~ (zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A))) & 
% 1.65/1.83             (((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['46', '47'])).
% 1.65/1.83  thf('49', plain,
% 1.65/1.83      (![X4 : $i]:
% 1.65/1.83         (((sk_B @ X4) != (sk_C @ X4))
% 1.65/1.83          | (v2_funct_1 @ X4)
% 1.65/1.83          | ~ (v1_funct_1 @ X4)
% 1.65/1.83          | ~ (v1_relat_1 @ X4))),
% 1.65/1.83      inference('cnf', [status(esa)], [d8_funct_1])).
% 1.65/1.83  thf('50', plain,
% 1.65/1.83      (((((sk_B @ sk_C_1) != (sk_B @ sk_C_1))
% 1.65/1.83         | ~ (v1_relat_1 @ sk_C_1)
% 1.65/1.83         | ~ (v1_funct_1 @ sk_C_1)
% 1.65/1.83         | (v2_funct_1 @ sk_C_1)))
% 1.65/1.83         <= (~ ((v2_funct_1 @ sk_C_1)) & 
% 1.65/1.83             (![X23 : $i, X24 : $i]:
% 1.65/1.83                (((X24) = (X23))
% 1.65/1.83                 | ~ (zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A))) & 
% 1.65/1.83             (((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['48', '49'])).
% 1.65/1.83  thf('51', plain, ((v1_relat_1 @ sk_C_1)),
% 1.65/1.83      inference('demod', [status(thm)], ['37', '38'])).
% 1.65/1.83  thf('52', plain, ((v1_funct_1 @ sk_C_1)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.65/1.83  thf('53', plain,
% 1.65/1.83      (((((sk_B @ sk_C_1) != (sk_B @ sk_C_1)) | (v2_funct_1 @ sk_C_1)))
% 1.65/1.83         <= (~ ((v2_funct_1 @ sk_C_1)) & 
% 1.65/1.83             (![X23 : $i, X24 : $i]:
% 1.65/1.83                (((X24) = (X23))
% 1.65/1.83                 | ~ (zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A))) & 
% 1.65/1.83             (((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('demod', [status(thm)], ['50', '51', '52'])).
% 1.65/1.83  thf('54', plain,
% 1.65/1.83      (((v2_funct_1 @ sk_C_1))
% 1.65/1.83         <= (~ ((v2_funct_1 @ sk_C_1)) & 
% 1.65/1.83             (![X23 : $i, X24 : $i]:
% 1.65/1.83                (((X24) = (X23))
% 1.65/1.83                 | ~ (zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A))) & 
% 1.65/1.83             (((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('simplify', [status(thm)], ['53'])).
% 1.65/1.83  thf('55', plain, ((~ (v2_funct_1 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 1.65/1.83      inference('split', [status(esa)], ['4'])).
% 1.65/1.83  thf('56', plain,
% 1.65/1.83      (~ (((sk_A) = (k1_xboole_0))) | ((v2_funct_1 @ sk_C_1)) | 
% 1.65/1.83       ~
% 1.65/1.83       (![X23 : $i, X24 : $i]:
% 1.65/1.83          (((X24) = (X23)) | ~ (zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['54', '55'])).
% 1.65/1.83  thf('57', plain,
% 1.65/1.83      (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A))
% 1.65/1.83         <= (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)))),
% 1.65/1.83      inference('split', [status(esa)], ['0'])).
% 1.65/1.83  thf('58', plain,
% 1.65/1.83      ((![X23 : $i, X24 : $i]:
% 1.65/1.83          (((X24) = (X23)) | ~ (zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A)))
% 1.65/1.83         <= ((![X23 : $i, X24 : $i]:
% 1.65/1.83                (((X24) = (X23))
% 1.65/1.83                 | ~ (zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A))))),
% 1.65/1.83      inference('split', [status(esa)], ['43'])).
% 1.65/1.83  thf('59', plain,
% 1.65/1.83      ((((sk_D) = (sk_E)))
% 1.65/1.83         <= (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)) & 
% 1.65/1.83             (![X23 : $i, X24 : $i]:
% 1.65/1.83                (((X24) = (X23))
% 1.65/1.83                 | ~ (zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['57', '58'])).
% 1.65/1.83  thf('60', plain, ((((sk_D) != (sk_E))) <= (~ (((sk_D) = (sk_E))))),
% 1.65/1.83      inference('split', [status(esa)], ['4'])).
% 1.65/1.83  thf('61', plain,
% 1.65/1.83      ((((sk_D) != (sk_D)))
% 1.65/1.83         <= (~ (((sk_D) = (sk_E))) & 
% 1.65/1.83             ((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)) & 
% 1.65/1.83             (![X23 : $i, X24 : $i]:
% 1.65/1.83                (((X24) = (X23))
% 1.65/1.83                 | ~ (zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['59', '60'])).
% 1.65/1.83  thf('62', plain,
% 1.65/1.83      (~
% 1.65/1.83       (![X23 : $i, X24 : $i]:
% 1.65/1.83          (((X24) = (X23)) | ~ (zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A))) | 
% 1.65/1.83       (((sk_D) = (sk_E))) | ~ ((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A))),
% 1.65/1.83      inference('simplify', [status(thm)], ['61'])).
% 1.65/1.83  thf('63', plain,
% 1.65/1.83      ((((k1_funct_1 @ sk_C_1 @ sk_D) = (k1_funct_1 @ sk_C_1 @ sk_E)))
% 1.65/1.83         <= (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['1', '2'])).
% 1.65/1.83  thf('64', plain, (((v2_funct_1 @ sk_C_1)) <= (((v2_funct_1 @ sk_C_1)))),
% 1.65/1.83      inference('split', [status(esa)], ['43'])).
% 1.65/1.83  thf('65', plain,
% 1.65/1.83      ((((k1_xboole_0) = (k1_relat_1 @ sk_C_1)))
% 1.65/1.83         <= ((((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('demod', [status(thm)], ['11', '19', '22'])).
% 1.65/1.83  thf('66', plain,
% 1.65/1.83      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.65/1.83         (~ (v2_funct_1 @ X4)
% 1.65/1.83          | ~ (r2_hidden @ X5 @ (k1_relat_1 @ X4))
% 1.65/1.83          | ~ (r2_hidden @ X6 @ (k1_relat_1 @ X4))
% 1.65/1.83          | ((k1_funct_1 @ X4 @ X5) != (k1_funct_1 @ X4 @ X6))
% 1.65/1.83          | ((X5) = (X6))
% 1.65/1.83          | ~ (v1_funct_1 @ X4)
% 1.65/1.83          | ~ (v1_relat_1 @ X4))),
% 1.65/1.83      inference('cnf', [status(esa)], [d8_funct_1])).
% 1.65/1.83  thf('67', plain,
% 1.65/1.83      ((![X0 : $i, X1 : $i]:
% 1.65/1.83          (~ (r2_hidden @ X0 @ k1_xboole_0)
% 1.65/1.83           | ~ (v1_relat_1 @ sk_C_1)
% 1.65/1.83           | ~ (v1_funct_1 @ sk_C_1)
% 1.65/1.83           | ((X0) = (X1))
% 1.65/1.83           | ((k1_funct_1 @ sk_C_1 @ X0) != (k1_funct_1 @ sk_C_1 @ X1))
% 1.65/1.83           | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_C_1))
% 1.65/1.83           | ~ (v2_funct_1 @ sk_C_1)))
% 1.65/1.83         <= ((((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['65', '66'])).
% 1.65/1.83  thf('68', plain, ((v1_relat_1 @ sk_C_1)),
% 1.65/1.83      inference('demod', [status(thm)], ['37', '38'])).
% 1.65/1.83  thf('69', plain, ((v1_funct_1 @ sk_C_1)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.65/1.83  thf('70', plain,
% 1.65/1.83      ((((k1_xboole_0) = (k1_relat_1 @ sk_C_1)))
% 1.65/1.83         <= ((((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('demod', [status(thm)], ['11', '19', '22'])).
% 1.65/1.83  thf('71', plain,
% 1.65/1.83      ((![X0 : $i, X1 : $i]:
% 1.65/1.83          (~ (r2_hidden @ X0 @ k1_xboole_0)
% 1.65/1.83           | ((X0) = (X1))
% 1.65/1.83           | ((k1_funct_1 @ sk_C_1 @ X0) != (k1_funct_1 @ sk_C_1 @ X1))
% 1.65/1.83           | ~ (r2_hidden @ X1 @ k1_xboole_0)
% 1.65/1.83           | ~ (v2_funct_1 @ sk_C_1)))
% 1.65/1.83         <= ((((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('demod', [status(thm)], ['67', '68', '69', '70'])).
% 1.65/1.83  thf('72', plain,
% 1.65/1.83      ((![X0 : $i, X1 : $i]:
% 1.65/1.83          (~ (r2_hidden @ X0 @ k1_xboole_0)
% 1.65/1.83           | ((k1_funct_1 @ sk_C_1 @ X1) != (k1_funct_1 @ sk_C_1 @ X0))
% 1.65/1.83           | ((X1) = (X0))
% 1.65/1.83           | ~ (r2_hidden @ X1 @ k1_xboole_0)))
% 1.65/1.83         <= (((v2_funct_1 @ sk_C_1)) & (((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['64', '71'])).
% 1.65/1.83  thf('73', plain,
% 1.65/1.83      ((![X0 : $i]:
% 1.65/1.83          (((k1_funct_1 @ sk_C_1 @ sk_D) != (k1_funct_1 @ sk_C_1 @ X0))
% 1.65/1.83           | ~ (r2_hidden @ sk_E @ k1_xboole_0)
% 1.65/1.83           | ((sk_E) = (X0))
% 1.65/1.83           | ~ (r2_hidden @ X0 @ k1_xboole_0)))
% 1.65/1.83         <= (((v2_funct_1 @ sk_C_1)) & 
% 1.65/1.83             ((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)) & 
% 1.65/1.83             (((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['63', '72'])).
% 1.65/1.83  thf('74', plain,
% 1.65/1.83      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('split', [status(esa)], ['6'])).
% 1.65/1.83  thf('75', plain,
% 1.65/1.83      (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A))
% 1.65/1.83         <= (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)))),
% 1.65/1.83      inference('split', [status(esa)], ['0'])).
% 1.65/1.83  thf('76', plain,
% 1.65/1.83      (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ k1_xboole_0))
% 1.65/1.83         <= (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)) & 
% 1.65/1.83             (((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('sup+', [status(thm)], ['74', '75'])).
% 1.65/1.83  thf('77', plain,
% 1.65/1.83      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.65/1.83         ((r2_hidden @ X20 @ X19) | ~ (zip_tseitin_2 @ X20 @ X18 @ X21 @ X19))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.65/1.83  thf('78', plain,
% 1.65/1.83      (((r2_hidden @ sk_E @ k1_xboole_0))
% 1.65/1.83         <= (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)) & 
% 1.65/1.83             (((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['76', '77'])).
% 1.65/1.83  thf('79', plain,
% 1.65/1.83      ((![X0 : $i]:
% 1.65/1.83          (((k1_funct_1 @ sk_C_1 @ sk_D) != (k1_funct_1 @ sk_C_1 @ X0))
% 1.65/1.83           | ((sk_E) = (X0))
% 1.65/1.83           | ~ (r2_hidden @ X0 @ k1_xboole_0)))
% 1.65/1.83         <= (((v2_funct_1 @ sk_C_1)) & 
% 1.65/1.83             ((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)) & 
% 1.65/1.83             (((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('demod', [status(thm)], ['73', '78'])).
% 1.65/1.83  thf('80', plain,
% 1.65/1.83      (((~ (r2_hidden @ sk_D @ k1_xboole_0) | ((sk_E) = (sk_D))))
% 1.65/1.83         <= (((v2_funct_1 @ sk_C_1)) & 
% 1.65/1.83             ((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)) & 
% 1.65/1.83             (((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('eq_res', [status(thm)], ['79'])).
% 1.65/1.83  thf('81', plain,
% 1.65/1.83      (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ k1_xboole_0))
% 1.65/1.83         <= (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)) & 
% 1.65/1.83             (((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('sup+', [status(thm)], ['74', '75'])).
% 1.65/1.83  thf('82', plain,
% 1.65/1.83      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.65/1.83         ((r2_hidden @ X18 @ X19) | ~ (zip_tseitin_2 @ X20 @ X18 @ X21 @ X19))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.65/1.83  thf('83', plain,
% 1.65/1.83      (((r2_hidden @ sk_D @ k1_xboole_0))
% 1.65/1.83         <= (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)) & 
% 1.65/1.83             (((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['81', '82'])).
% 1.65/1.83  thf('84', plain,
% 1.65/1.83      ((((sk_E) = (sk_D)))
% 1.65/1.83         <= (((v2_funct_1 @ sk_C_1)) & 
% 1.65/1.83             ((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)) & 
% 1.65/1.83             (((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('demod', [status(thm)], ['80', '83'])).
% 1.65/1.83  thf('85', plain, ((((sk_D) != (sk_E))) <= (~ (((sk_D) = (sk_E))))),
% 1.65/1.83      inference('split', [status(esa)], ['4'])).
% 1.65/1.83  thf('86', plain,
% 1.65/1.83      ((((sk_D) != (sk_D)))
% 1.65/1.83         <= (~ (((sk_D) = (sk_E))) & 
% 1.65/1.83             ((v2_funct_1 @ sk_C_1)) & 
% 1.65/1.83             ((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)) & 
% 1.65/1.83             (((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['84', '85'])).
% 1.65/1.83  thf('87', plain,
% 1.65/1.83      (~ (((sk_A) = (k1_xboole_0))) | ~ ((v2_funct_1 @ sk_C_1)) | 
% 1.65/1.83       ~ ((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)) | (((sk_D) = (sk_E)))),
% 1.65/1.83      inference('simplify', [status(thm)], ['86'])).
% 1.65/1.83  thf('88', plain,
% 1.65/1.83      (~ (((sk_B_1) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 1.65/1.83      inference('split', [status(esa)], ['6'])).
% 1.65/1.83  thf('89', plain,
% 1.65/1.83      (((v2_funct_1 @ sk_C_1)) | 
% 1.65/1.83       (![X23 : $i, X24 : $i]:
% 1.65/1.83          (((X24) = (X23)) | ~ (zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A)))),
% 1.65/1.83      inference('split', [status(esa)], ['43'])).
% 1.65/1.83  thf('90', plain,
% 1.65/1.83      (![X10 : $i, X11 : $i]:
% 1.65/1.83         ((zip_tseitin_0 @ X10 @ X11) | ((X10) = (k1_xboole_0)))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_7])).
% 1.65/1.83  thf('91', plain,
% 1.65/1.83      (![X10 : $i, X11 : $i]:
% 1.65/1.83         ((zip_tseitin_0 @ X10 @ X11) | ((X10) = (k1_xboole_0)))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_7])).
% 1.65/1.83  thf('92', plain,
% 1.65/1.83      (![X10 : $i, X11 : $i]:
% 1.65/1.83         ((zip_tseitin_0 @ X10 @ X11) | ((X10) = (k1_xboole_0)))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_7])).
% 1.65/1.83  thf('93', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.65/1.83         (((X1) = (X0)) | (zip_tseitin_0 @ X0 @ X3) | (zip_tseitin_0 @ X1 @ X2))),
% 1.65/1.83      inference('sup+', [status(thm)], ['91', '92'])).
% 1.65/1.83  thf('94', plain,
% 1.65/1.83      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.65/1.83  thf('95', plain,
% 1.65/1.83      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.65/1.83         (~ (zip_tseitin_0 @ X15 @ X16)
% 1.65/1.83          | (zip_tseitin_1 @ X17 @ X15 @ X16)
% 1.65/1.83          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X15))))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_8])).
% 1.65/1.83  thf('96', plain,
% 1.65/1.83      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 1.65/1.83        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 1.65/1.83      inference('sup-', [status(thm)], ['94', '95'])).
% 1.65/1.83  thf('97', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         ((zip_tseitin_0 @ X1 @ X0)
% 1.65/1.83          | ((sk_B_1) = (X1))
% 1.65/1.83          | (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A))),
% 1.65/1.83      inference('sup-', [status(thm)], ['93', '96'])).
% 1.65/1.83  thf('98', plain,
% 1.65/1.83      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.65/1.83      inference('split', [status(esa)], ['6'])).
% 1.65/1.83  thf('99', plain,
% 1.65/1.83      ((![X0 : $i, X1 : $i]:
% 1.65/1.83          (((X0) != (k1_xboole_0))
% 1.65/1.83           | (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 1.65/1.83           | (zip_tseitin_0 @ X0 @ X1)))
% 1.65/1.83         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['97', '98'])).
% 1.65/1.83  thf('100', plain,
% 1.65/1.83      ((![X1 : $i]:
% 1.65/1.83          ((zip_tseitin_0 @ k1_xboole_0 @ X1)
% 1.65/1.83           | (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)))
% 1.65/1.83         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.65/1.83      inference('simplify', [status(thm)], ['99'])).
% 1.65/1.83  thf('101', plain,
% 1.65/1.83      ((![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.83          ((zip_tseitin_0 @ X0 @ X1)
% 1.65/1.83           | (zip_tseitin_0 @ X0 @ X2)
% 1.65/1.83           | (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)))
% 1.65/1.83         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.65/1.83      inference('sup+', [status(thm)], ['90', '100'])).
% 1.65/1.83  thf('102', plain,
% 1.65/1.83      ((![X0 : $i, X1 : $i]:
% 1.65/1.83          ((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A) | (zip_tseitin_0 @ X1 @ X0)))
% 1.65/1.83         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.65/1.83      inference('condensation', [status(thm)], ['101'])).
% 1.65/1.83  thf('103', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.65/1.83  thf('104', plain,
% 1.65/1.83      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.65/1.83         (~ (v1_funct_2 @ X14 @ X12 @ X13)
% 1.65/1.83          | ((X12) = (k1_relset_1 @ X12 @ X13 @ X14))
% 1.65/1.83          | ~ (zip_tseitin_1 @ X14 @ X13 @ X12))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.65/1.83  thf('105', plain,
% 1.65/1.83      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 1.65/1.83        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['103', '104'])).
% 1.65/1.83  thf('106', plain,
% 1.65/1.83      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.65/1.83  thf('107', plain,
% 1.65/1.83      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.65/1.83         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 1.65/1.83          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 1.65/1.83      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.65/1.83  thf('108', plain,
% 1.65/1.83      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 1.65/1.83      inference('sup-', [status(thm)], ['106', '107'])).
% 1.65/1.83  thf('109', plain,
% 1.65/1.83      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 1.65/1.83        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.65/1.83      inference('demod', [status(thm)], ['105', '108'])).
% 1.65/1.83  thf('110', plain,
% 1.65/1.83      ((![X0 : $i, X1 : $i]:
% 1.65/1.83          ((zip_tseitin_0 @ X1 @ X0) | ((sk_A) = (k1_relat_1 @ sk_C_1))))
% 1.65/1.83         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['102', '109'])).
% 1.65/1.83  thf('111', plain,
% 1.65/1.83      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 1.65/1.83        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 1.65/1.83      inference('sup-', [status(thm)], ['94', '95'])).
% 1.65/1.83  thf('112', plain,
% 1.65/1.83      (((((sk_A) = (k1_relat_1 @ sk_C_1))
% 1.65/1.83         | (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)))
% 1.65/1.83         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['110', '111'])).
% 1.65/1.83  thf('113', plain,
% 1.65/1.83      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 1.65/1.83        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.65/1.83      inference('demod', [status(thm)], ['105', '108'])).
% 1.65/1.83  thf('114', plain,
% 1.65/1.83      ((((sk_A) = (k1_relat_1 @ sk_C_1))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.65/1.83      inference('clc', [status(thm)], ['112', '113'])).
% 1.65/1.83  thf('115', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         ((zip_tseitin_2 @ (sk_B @ X0) @ (sk_C @ X0) @ X0 @ (k1_relat_1 @ X0))
% 1.65/1.83          | (v2_funct_1 @ X0)
% 1.65/1.83          | ~ (v1_funct_1 @ X0)
% 1.65/1.83          | ~ (v1_relat_1 @ X0))),
% 1.65/1.83      inference('simplify', [status(thm)], ['32'])).
% 1.65/1.83  thf('116', plain,
% 1.65/1.83      ((((zip_tseitin_2 @ (sk_B @ sk_C_1) @ (sk_C @ sk_C_1) @ sk_C_1 @ sk_A)
% 1.65/1.83         | ~ (v1_relat_1 @ sk_C_1)
% 1.65/1.83         | ~ (v1_funct_1 @ sk_C_1)
% 1.65/1.83         | (v2_funct_1 @ sk_C_1))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.65/1.83      inference('sup+', [status(thm)], ['114', '115'])).
% 1.65/1.83  thf('117', plain, ((v1_relat_1 @ sk_C_1)),
% 1.65/1.83      inference('demod', [status(thm)], ['37', '38'])).
% 1.65/1.83  thf('118', plain, ((v1_funct_1 @ sk_C_1)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.65/1.83  thf('119', plain,
% 1.65/1.83      ((((zip_tseitin_2 @ (sk_B @ sk_C_1) @ (sk_C @ sk_C_1) @ sk_C_1 @ sk_A)
% 1.65/1.83         | (v2_funct_1 @ sk_C_1))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.65/1.83      inference('demod', [status(thm)], ['116', '117', '118'])).
% 1.65/1.83  thf('120', plain,
% 1.65/1.83      ((![X23 : $i, X24 : $i]:
% 1.65/1.83          (((X24) = (X23)) | ~ (zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A)))
% 1.65/1.83         <= ((![X23 : $i, X24 : $i]:
% 1.65/1.83                (((X24) = (X23))
% 1.65/1.83                 | ~ (zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A))))),
% 1.65/1.83      inference('split', [status(esa)], ['43'])).
% 1.65/1.83  thf('121', plain,
% 1.65/1.83      ((((v2_funct_1 @ sk_C_1) | ((sk_C @ sk_C_1) = (sk_B @ sk_C_1))))
% 1.65/1.83         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 1.65/1.83             (![X23 : $i, X24 : $i]:
% 1.65/1.83                (((X24) = (X23))
% 1.65/1.83                 | ~ (zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['119', '120'])).
% 1.65/1.83  thf('122', plain, ((~ (v2_funct_1 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 1.65/1.83      inference('split', [status(esa)], ['4'])).
% 1.65/1.83  thf('123', plain,
% 1.65/1.83      ((((sk_C @ sk_C_1) = (sk_B @ sk_C_1)))
% 1.65/1.83         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 1.65/1.83             ~ ((v2_funct_1 @ sk_C_1)) & 
% 1.65/1.83             (![X23 : $i, X24 : $i]:
% 1.65/1.83                (((X24) = (X23))
% 1.65/1.83                 | ~ (zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['121', '122'])).
% 1.65/1.83  thf('124', plain,
% 1.65/1.83      (![X4 : $i]:
% 1.65/1.83         (((sk_B @ X4) != (sk_C @ X4))
% 1.65/1.83          | (v2_funct_1 @ X4)
% 1.65/1.83          | ~ (v1_funct_1 @ X4)
% 1.65/1.83          | ~ (v1_relat_1 @ X4))),
% 1.65/1.83      inference('cnf', [status(esa)], [d8_funct_1])).
% 1.65/1.83  thf('125', plain,
% 1.65/1.83      (((((sk_B @ sk_C_1) != (sk_B @ sk_C_1))
% 1.65/1.83         | ~ (v1_relat_1 @ sk_C_1)
% 1.65/1.83         | ~ (v1_funct_1 @ sk_C_1)
% 1.65/1.83         | (v2_funct_1 @ sk_C_1)))
% 1.65/1.83         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 1.65/1.83             ~ ((v2_funct_1 @ sk_C_1)) & 
% 1.65/1.83             (![X23 : $i, X24 : $i]:
% 1.65/1.83                (((X24) = (X23))
% 1.65/1.83                 | ~ (zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['123', '124'])).
% 1.65/1.83  thf('126', plain, ((v1_relat_1 @ sk_C_1)),
% 1.65/1.83      inference('demod', [status(thm)], ['37', '38'])).
% 1.65/1.83  thf('127', plain, ((v1_funct_1 @ sk_C_1)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.65/1.83  thf('128', plain,
% 1.65/1.83      (((((sk_B @ sk_C_1) != (sk_B @ sk_C_1)) | (v2_funct_1 @ sk_C_1)))
% 1.65/1.83         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 1.65/1.83             ~ ((v2_funct_1 @ sk_C_1)) & 
% 1.65/1.83             (![X23 : $i, X24 : $i]:
% 1.65/1.83                (((X24) = (X23))
% 1.65/1.83                 | ~ (zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A))))),
% 1.65/1.83      inference('demod', [status(thm)], ['125', '126', '127'])).
% 1.65/1.83  thf('129', plain,
% 1.65/1.83      (((v2_funct_1 @ sk_C_1))
% 1.65/1.83         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 1.65/1.83             ~ ((v2_funct_1 @ sk_C_1)) & 
% 1.65/1.83             (![X23 : $i, X24 : $i]:
% 1.65/1.83                (((X24) = (X23))
% 1.65/1.83                 | ~ (zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A))))),
% 1.65/1.83      inference('simplify', [status(thm)], ['128'])).
% 1.65/1.83  thf('130', plain, ((~ (v2_funct_1 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 1.65/1.83      inference('split', [status(esa)], ['4'])).
% 1.65/1.83  thf('131', plain,
% 1.65/1.83      (~
% 1.65/1.83       (![X23 : $i, X24 : $i]:
% 1.65/1.83          (((X24) = (X23)) | ~ (zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A))) | 
% 1.65/1.83       ((v2_funct_1 @ sk_C_1)) | (((sk_B_1) = (k1_xboole_0)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['129', '130'])).
% 1.65/1.83  thf('132', plain,
% 1.65/1.83      (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)) | 
% 1.65/1.83       ~ ((v2_funct_1 @ sk_C_1))),
% 1.65/1.83      inference('split', [status(esa)], ['0'])).
% 1.65/1.83  thf('133', plain, (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A))),
% 1.65/1.83      inference('sat_resolution*', [status(thm)],
% 1.65/1.83                ['5', '56', '62', '87', '88', '89', '131', '132'])).
% 1.65/1.83  thf('134', plain,
% 1.65/1.83      (((k1_funct_1 @ sk_C_1 @ sk_D) = (k1_funct_1 @ sk_C_1 @ sk_E))),
% 1.65/1.83      inference('simpl_trail', [status(thm)], ['3', '133'])).
% 1.65/1.83  thf('135', plain,
% 1.65/1.83      ((((sk_A) = (k1_relat_1 @ sk_C_1))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.65/1.83      inference('clc', [status(thm)], ['112', '113'])).
% 1.65/1.83  thf('136', plain,
% 1.65/1.83      (((v2_funct_1 @ sk_C_1)) | ~ (((sk_A) = (k1_xboole_0))) | 
% 1.65/1.83       ~
% 1.65/1.83       (![X23 : $i, X24 : $i]:
% 1.65/1.83          (((X24) = (X23)) | ~ (zip_tseitin_2 @ X23 @ X24 @ sk_C_1 @ sk_A)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['54', '55'])).
% 1.65/1.83  thf('137', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 1.65/1.83      inference('sat_resolution*', [status(thm)],
% 1.65/1.83                ['89', '5', '132', '136', '62', '87', '88'])).
% 1.65/1.83  thf('138', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 1.65/1.83      inference('simpl_trail', [status(thm)], ['135', '137'])).
% 1.65/1.83  thf('139', plain,
% 1.65/1.83      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.65/1.83         (~ (v2_funct_1 @ X4)
% 1.65/1.83          | ~ (r2_hidden @ X5 @ (k1_relat_1 @ X4))
% 1.65/1.83          | ~ (r2_hidden @ X6 @ (k1_relat_1 @ X4))
% 1.65/1.83          | ((k1_funct_1 @ X4 @ X5) != (k1_funct_1 @ X4 @ X6))
% 1.65/1.83          | ((X5) = (X6))
% 1.65/1.83          | ~ (v1_funct_1 @ X4)
% 1.65/1.83          | ~ (v1_relat_1 @ X4))),
% 1.65/1.83      inference('cnf', [status(esa)], [d8_funct_1])).
% 1.65/1.83  thf('140', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         (~ (r2_hidden @ X0 @ sk_A)
% 1.65/1.83          | ~ (v1_relat_1 @ sk_C_1)
% 1.65/1.83          | ~ (v1_funct_1 @ sk_C_1)
% 1.65/1.83          | ((X0) = (X1))
% 1.65/1.83          | ((k1_funct_1 @ sk_C_1 @ X0) != (k1_funct_1 @ sk_C_1 @ X1))
% 1.65/1.83          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_C_1))
% 1.65/1.83          | ~ (v2_funct_1 @ sk_C_1))),
% 1.65/1.83      inference('sup-', [status(thm)], ['138', '139'])).
% 1.65/1.83  thf('141', plain, ((v1_relat_1 @ sk_C_1)),
% 1.65/1.83      inference('demod', [status(thm)], ['37', '38'])).
% 1.65/1.83  thf('142', plain, ((v1_funct_1 @ sk_C_1)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.65/1.83  thf('143', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 1.65/1.83      inference('simpl_trail', [status(thm)], ['135', '137'])).
% 1.65/1.83  thf('144', plain, (((v2_funct_1 @ sk_C_1)) <= (((v2_funct_1 @ sk_C_1)))),
% 1.65/1.83      inference('split', [status(esa)], ['43'])).
% 1.65/1.83  thf('145', plain, (((v2_funct_1 @ sk_C_1))),
% 1.65/1.83      inference('sat_resolution*', [status(thm)],
% 1.65/1.83                ['5', '132', '56', '62', '87', '88', '89', '131'])).
% 1.65/1.83  thf('146', plain, ((v2_funct_1 @ sk_C_1)),
% 1.65/1.83      inference('simpl_trail', [status(thm)], ['144', '145'])).
% 1.65/1.83  thf('147', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         (~ (r2_hidden @ X0 @ sk_A)
% 1.65/1.83          | ((X0) = (X1))
% 1.65/1.83          | ((k1_funct_1 @ sk_C_1 @ X0) != (k1_funct_1 @ sk_C_1 @ X1))
% 1.65/1.83          | ~ (r2_hidden @ X1 @ sk_A))),
% 1.65/1.83      inference('demod', [status(thm)], ['140', '141', '142', '143', '146'])).
% 1.65/1.83  thf('148', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         (((k1_funct_1 @ sk_C_1 @ sk_D) != (k1_funct_1 @ sk_C_1 @ X0))
% 1.65/1.83          | ~ (r2_hidden @ X0 @ sk_A)
% 1.65/1.83          | ((sk_E) = (X0))
% 1.65/1.83          | ~ (r2_hidden @ sk_E @ sk_A))),
% 1.65/1.83      inference('sup-', [status(thm)], ['134', '147'])).
% 1.65/1.83  thf('149', plain,
% 1.65/1.83      (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A))
% 1.65/1.83         <= (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)))),
% 1.65/1.83      inference('split', [status(esa)], ['0'])).
% 1.65/1.83  thf('150', plain,
% 1.65/1.83      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.65/1.83         ((r2_hidden @ X20 @ X19) | ~ (zip_tseitin_2 @ X20 @ X18 @ X21 @ X19))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.65/1.83  thf('151', plain,
% 1.65/1.83      (((r2_hidden @ sk_E @ sk_A))
% 1.65/1.83         <= (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['149', '150'])).
% 1.65/1.83  thf('152', plain, (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A))),
% 1.65/1.83      inference('sat_resolution*', [status(thm)],
% 1.65/1.83                ['5', '56', '62', '87', '88', '89', '131', '132'])).
% 1.65/1.83  thf('153', plain, ((r2_hidden @ sk_E @ sk_A)),
% 1.65/1.83      inference('simpl_trail', [status(thm)], ['151', '152'])).
% 1.65/1.83  thf('154', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         (((k1_funct_1 @ sk_C_1 @ sk_D) != (k1_funct_1 @ sk_C_1 @ X0))
% 1.65/1.83          | ~ (r2_hidden @ X0 @ sk_A)
% 1.65/1.83          | ((sk_E) = (X0)))),
% 1.65/1.83      inference('demod', [status(thm)], ['148', '153'])).
% 1.65/1.83  thf('155', plain, ((((sk_E) = (sk_D)) | ~ (r2_hidden @ sk_D @ sk_A))),
% 1.65/1.83      inference('eq_res', [status(thm)], ['154'])).
% 1.65/1.83  thf('156', plain,
% 1.65/1.83      (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A))
% 1.65/1.83         <= (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)))),
% 1.65/1.83      inference('split', [status(esa)], ['0'])).
% 1.65/1.83  thf('157', plain,
% 1.65/1.83      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.65/1.83         ((r2_hidden @ X18 @ X19) | ~ (zip_tseitin_2 @ X20 @ X18 @ X21 @ X19))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.65/1.83  thf('158', plain,
% 1.65/1.83      (((r2_hidden @ sk_D @ sk_A))
% 1.65/1.83         <= (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['156', '157'])).
% 1.65/1.83  thf('159', plain, (((zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A))),
% 1.65/1.83      inference('sat_resolution*', [status(thm)],
% 1.65/1.83                ['5', '56', '62', '87', '88', '89', '131', '132'])).
% 1.65/1.83  thf('160', plain, ((r2_hidden @ sk_D @ sk_A)),
% 1.65/1.83      inference('simpl_trail', [status(thm)], ['158', '159'])).
% 1.65/1.83  thf('161', plain, (((sk_E) = (sk_D))),
% 1.65/1.83      inference('demod', [status(thm)], ['155', '160'])).
% 1.65/1.83  thf('162', plain, ((((sk_D) != (sk_E))) <= (~ (((sk_D) = (sk_E))))),
% 1.65/1.83      inference('split', [status(esa)], ['4'])).
% 1.65/1.83  thf('163', plain, (~ (((sk_D) = (sk_E)))),
% 1.65/1.83      inference('sat_resolution*', [status(thm)],
% 1.65/1.83                ['132', '56', '62', '87', '88', '89', '131', '5'])).
% 1.65/1.83  thf('164', plain, (((sk_D) != (sk_E))),
% 1.65/1.83      inference('simpl_trail', [status(thm)], ['162', '163'])).
% 1.65/1.83  thf('165', plain, ($false),
% 1.65/1.83      inference('simplify_reflect-', [status(thm)], ['161', '164'])).
% 1.65/1.83  
% 1.65/1.83  % SZS output end Refutation
% 1.65/1.83  
% 1.65/1.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
