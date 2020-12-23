%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.josNryTobw

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:33 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 186 expanded)
%              Number of leaves         :   46 (  76 expanded)
%              Depth                    :   16
%              Number of atoms          :  754 (2177 expanded)
%              Number of equality atoms :   36 (  81 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t115_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
            & ! [F: $i] :
                ~ ( ( r2_hidden @ F @ A )
                  & ( r2_hidden @ F @ C )
                  & ( E
                    = ( k1_funct_1 @ D @ F ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
              & ! [F: $i] :
                  ~ ( ( r2_hidden @ F @ A )
                    & ( r2_hidden @ F @ C )
                    & ( E
                      = ( k1_funct_1 @ D @ F ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t115_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_3 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( ( k7_relset_1 @ X31 @ X32 @ X30 @ X33 )
        = ( k9_relat_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_3 @ X0 )
      = ( k9_relat_1 @ sk_D_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_3 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ ( k9_relat_1 @ X20 @ X18 ) )
      | ( r2_hidden @ ( sk_D_2 @ X20 @ X18 @ X19 ) @ ( k1_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_D_3 )
    | ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) @ ( k1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('8',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v1_relat_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('9',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) @ ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    v1_funct_2 @ sk_D_3 @ sk_A @ sk_B_1 ),
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

thf('12',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_funct_2 @ X41 @ X39 @ X40 )
      | ( X39
        = ( k1_relset_1 @ X39 @ X40 @ X41 ) )
      | ~ ( zip_tseitin_1 @ X41 @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('13',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('15',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('16',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_3 )
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('19',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( zip_tseitin_0 @ X42 @ X43 )
      | ( zip_tseitin_1 @ X44 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('20',plain,
    ( ( zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X37: $i,X38: $i] :
      ( ( zip_tseitin_0 @ X37 @ X38 )
      | ( X37 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('22',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ( r2_hidden @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('27',plain,(
    ! [X13: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('28',plain,(
    r2_hidden @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('29',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('30',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r2_hidden @ X7 @ X5 )
      | ( r2_hidden @ X7 @ X8 )
      | ( X8
       != ( k3_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('31',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ ( k3_tarski @ X6 ) )
      | ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,
    ( ( r2_hidden @ ( sk_B @ sk_D_3 ) @ ( k3_tarski @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) )
    | ( v1_xboole_0 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['28','32'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('34',plain,(
    ! [X12: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('35',plain,
    ( ( r2_hidden @ ( sk_B @ sk_D_3 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('36',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X34 ) @ X36 )
      | ~ ( r2_hidden @ X34 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('37',plain,
    ( ( v1_xboole_0 @ sk_D_3 )
    | ( r2_hidden @ ( k2_mcart_1 @ ( sk_B @ sk_D_3 ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('39',plain,
    ( ( v1_xboole_0 @ sk_D_3 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['23','39'])).

thf('41',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_3 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('42',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ ( k9_relat_1 @ X20 @ X18 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X20 @ X18 @ X19 ) @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_D_3 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_E ) @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('45',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_E ) @ sk_D_3 ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('47',plain,(
    ~ ( v1_xboole_0 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference('sup-',[status(thm)],['40','47'])).

thf('49',plain,(
    zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['20','48'])).

thf('50',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['17','49'])).

thf('51',plain,(
    r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_A ),
    inference(demod,[status(thm)],['10','50'])).

thf('52',plain,(
    ! [X45: $i] :
      ( ~ ( r2_hidden @ X45 @ sk_A )
      | ~ ( r2_hidden @ X45 @ sk_C_1 )
      | ( sk_E
       != ( k1_funct_1 @ sk_D_3 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( sk_E
     != ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) ) )
    | ~ ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_E ) @ sk_D_3 ),
    inference(demod,[status(thm)],['43','44'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('55',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X21 @ X23 ) @ X22 )
      | ( X23
        = ( k1_funct_1 @ X22 @ X21 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('56',plain,
    ( ~ ( v1_relat_1 @ sk_D_3 )
    | ~ ( v1_funct_1 @ sk_D_3 )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('58',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( sk_E
    = ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_3 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('61',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ ( k9_relat_1 @ X20 @ X18 ) )
      | ( r2_hidden @ ( sk_D_2 @ X20 @ X18 @ X19 ) @ X18 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ sk_D_3 )
    | ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('64',plain,(
    r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_C_1 ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    sk_E != sk_E ),
    inference(demod,[status(thm)],['53','59','64'])).

thf('66',plain,(
    $false ),
    inference(simplify,[status(thm)],['65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.josNryTobw
% 0.15/0.37  % Computer   : n021.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 20:40:35 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.89/1.14  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.89/1.14  % Solved by: fo/fo7.sh
% 0.89/1.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.89/1.14  % done 366 iterations in 0.671s
% 0.89/1.14  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.89/1.14  % SZS output start Refutation
% 0.89/1.14  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.89/1.14  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.89/1.14  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.89/1.14  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.89/1.14  thf(sk_E_type, type, sk_E: $i).
% 0.89/1.14  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.89/1.14  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.89/1.14  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.89/1.14  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.89/1.14  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.89/1.14  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.89/1.14  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 0.89/1.14  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.89/1.14  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.89/1.14  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.89/1.14  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.89/1.14  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.89/1.14  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.89/1.14  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.89/1.14  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.89/1.14  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.89/1.14  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.89/1.14  thf(sk_B_type, type, sk_B: $i > $i).
% 0.89/1.14  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.89/1.14  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.89/1.14  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.89/1.14  thf(sk_A_type, type, sk_A: $i).
% 0.89/1.14  thf(t115_funct_2, conjecture,
% 0.89/1.14    (![A:$i,B:$i,C:$i,D:$i]:
% 0.89/1.14     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.89/1.14         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.89/1.14       ( ![E:$i]:
% 0.89/1.14         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.89/1.14              ( ![F:$i]:
% 0.89/1.14                ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.89/1.14                     ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ))).
% 0.89/1.14  thf(zf_stmt_0, negated_conjecture,
% 0.89/1.14    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.89/1.14        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.89/1.14            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.89/1.14          ( ![E:$i]:
% 0.89/1.14            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.89/1.14                 ( ![F:$i]:
% 0.89/1.14                   ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.89/1.14                        ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )),
% 0.89/1.14    inference('cnf.neg', [status(esa)], [t115_funct_2])).
% 0.89/1.14  thf('0', plain,
% 0.89/1.14      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_3 @ sk_C_1))),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('1', plain,
% 0.89/1.14      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf(redefinition_k7_relset_1, axiom,
% 0.89/1.14    (![A:$i,B:$i,C:$i,D:$i]:
% 0.89/1.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.14       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.89/1.14  thf('2', plain,
% 0.89/1.14      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.89/1.14         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.89/1.14          | ((k7_relset_1 @ X31 @ X32 @ X30 @ X33) = (k9_relat_1 @ X30 @ X33)))),
% 0.89/1.14      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.89/1.14  thf('3', plain,
% 0.89/1.14      (![X0 : $i]:
% 0.89/1.14         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_3 @ X0)
% 0.89/1.14           = (k9_relat_1 @ sk_D_3 @ X0))),
% 0.89/1.14      inference('sup-', [status(thm)], ['1', '2'])).
% 0.89/1.14  thf('4', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_3 @ sk_C_1))),
% 0.89/1.14      inference('demod', [status(thm)], ['0', '3'])).
% 0.89/1.14  thf(t143_relat_1, axiom,
% 0.89/1.14    (![A:$i,B:$i,C:$i]:
% 0.89/1.14     ( ( v1_relat_1 @ C ) =>
% 0.89/1.14       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.89/1.14         ( ?[D:$i]:
% 0.89/1.14           ( ( r2_hidden @ D @ B ) & 
% 0.89/1.14             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.89/1.14             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.89/1.14  thf('5', plain,
% 0.89/1.14      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.89/1.14         (~ (r2_hidden @ X19 @ (k9_relat_1 @ X20 @ X18))
% 0.89/1.14          | (r2_hidden @ (sk_D_2 @ X20 @ X18 @ X19) @ (k1_relat_1 @ X20))
% 0.89/1.14          | ~ (v1_relat_1 @ X20))),
% 0.89/1.14      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.89/1.14  thf('6', plain,
% 0.89/1.14      ((~ (v1_relat_1 @ sk_D_3)
% 0.89/1.14        | (r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E) @ 
% 0.89/1.14           (k1_relat_1 @ sk_D_3)))),
% 0.89/1.14      inference('sup-', [status(thm)], ['4', '5'])).
% 0.89/1.14  thf('7', plain,
% 0.89/1.14      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf(cc1_relset_1, axiom,
% 0.89/1.14    (![A:$i,B:$i,C:$i]:
% 0.89/1.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.14       ( v1_relat_1 @ C ) ))).
% 0.89/1.14  thf('8', plain,
% 0.89/1.14      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.89/1.14         ((v1_relat_1 @ X24)
% 0.89/1.14          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.89/1.14      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.89/1.14  thf('9', plain, ((v1_relat_1 @ sk_D_3)),
% 0.89/1.14      inference('sup-', [status(thm)], ['7', '8'])).
% 0.89/1.14  thf('10', plain,
% 0.89/1.14      ((r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E) @ (k1_relat_1 @ sk_D_3))),
% 0.89/1.14      inference('demod', [status(thm)], ['6', '9'])).
% 0.89/1.14  thf('11', plain, ((v1_funct_2 @ sk_D_3 @ sk_A @ sk_B_1)),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf(d1_funct_2, axiom,
% 0.89/1.14    (![A:$i,B:$i,C:$i]:
% 0.89/1.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.14       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.89/1.14           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.89/1.14             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.89/1.14         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.89/1.14           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.89/1.14             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.89/1.14  thf(zf_stmt_1, axiom,
% 0.89/1.14    (![C:$i,B:$i,A:$i]:
% 0.89/1.14     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.89/1.14       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.89/1.14  thf('12', plain,
% 0.89/1.14      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.89/1.14         (~ (v1_funct_2 @ X41 @ X39 @ X40)
% 0.89/1.14          | ((X39) = (k1_relset_1 @ X39 @ X40 @ X41))
% 0.89/1.14          | ~ (zip_tseitin_1 @ X41 @ X40 @ X39))),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.14  thf('13', plain,
% 0.89/1.14      ((~ (zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A)
% 0.89/1.14        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_3)))),
% 0.89/1.14      inference('sup-', [status(thm)], ['11', '12'])).
% 0.89/1.14  thf('14', plain,
% 0.89/1.14      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf(redefinition_k1_relset_1, axiom,
% 0.89/1.14    (![A:$i,B:$i,C:$i]:
% 0.89/1.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.14       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.89/1.14  thf('15', plain,
% 0.89/1.14      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.89/1.14         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 0.89/1.14          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.89/1.14      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.89/1.14  thf('16', plain,
% 0.89/1.14      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_3) = (k1_relat_1 @ sk_D_3))),
% 0.89/1.14      inference('sup-', [status(thm)], ['14', '15'])).
% 0.89/1.14  thf('17', plain,
% 0.89/1.14      ((~ (zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A)
% 0.89/1.14        | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 0.89/1.14      inference('demod', [status(thm)], ['13', '16'])).
% 0.89/1.14  thf('18', plain,
% 0.89/1.14      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.89/1.14  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.89/1.14  thf(zf_stmt_4, axiom,
% 0.89/1.14    (![B:$i,A:$i]:
% 0.89/1.14     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.89/1.14       ( zip_tseitin_0 @ B @ A ) ))).
% 0.89/1.14  thf(zf_stmt_5, axiom,
% 0.89/1.14    (![A:$i,B:$i,C:$i]:
% 0.89/1.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.14       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.89/1.14         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.89/1.14           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.89/1.14             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.89/1.14  thf('19', plain,
% 0.89/1.14      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.89/1.14         (~ (zip_tseitin_0 @ X42 @ X43)
% 0.89/1.14          | (zip_tseitin_1 @ X44 @ X42 @ X43)
% 0.89/1.14          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42))))),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.89/1.14  thf('20', plain,
% 0.89/1.14      (((zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A)
% 0.89/1.14        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.89/1.14      inference('sup-', [status(thm)], ['18', '19'])).
% 0.89/1.14  thf('21', plain,
% 0.89/1.14      (![X37 : $i, X38 : $i]:
% 0.89/1.14         ((zip_tseitin_0 @ X37 @ X38) | ((X37) = (k1_xboole_0)))),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.89/1.14  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.89/1.14  thf('22', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.89/1.14      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.89/1.14  thf('23', plain,
% 0.89/1.14      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.89/1.14      inference('sup+', [status(thm)], ['21', '22'])).
% 0.89/1.14  thf('24', plain,
% 0.89/1.14      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf(t2_subset, axiom,
% 0.89/1.14    (![A:$i,B:$i]:
% 0.89/1.14     ( ( m1_subset_1 @ A @ B ) =>
% 0.89/1.14       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.89/1.14  thf('25', plain,
% 0.89/1.14      (![X14 : $i, X15 : $i]:
% 0.89/1.14         ((r2_hidden @ X14 @ X15)
% 0.89/1.14          | (v1_xboole_0 @ X15)
% 0.89/1.14          | ~ (m1_subset_1 @ X14 @ X15))),
% 0.89/1.14      inference('cnf', [status(esa)], [t2_subset])).
% 0.89/1.14  thf('26', plain,
% 0.89/1.14      (((v1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.89/1.14        | (r2_hidden @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))),
% 0.89/1.14      inference('sup-', [status(thm)], ['24', '25'])).
% 0.89/1.14  thf(fc1_subset_1, axiom,
% 0.89/1.14    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.89/1.14  thf('27', plain, (![X13 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.89/1.14      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.89/1.14  thf('28', plain,
% 0.89/1.14      ((r2_hidden @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.89/1.14      inference('clc', [status(thm)], ['26', '27'])).
% 0.89/1.14  thf(d1_xboole_0, axiom,
% 0.89/1.14    (![A:$i]:
% 0.89/1.14     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.89/1.14  thf('29', plain,
% 0.89/1.14      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.89/1.14      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.89/1.14  thf(d4_tarski, axiom,
% 0.89/1.14    (![A:$i,B:$i]:
% 0.89/1.14     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 0.89/1.14       ( ![C:$i]:
% 0.89/1.14         ( ( r2_hidden @ C @ B ) <=>
% 0.89/1.14           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 0.89/1.14  thf('30', plain,
% 0.89/1.14      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.89/1.14         (~ (r2_hidden @ X5 @ X6)
% 0.89/1.14          | ~ (r2_hidden @ X7 @ X5)
% 0.89/1.14          | (r2_hidden @ X7 @ X8)
% 0.89/1.14          | ((X8) != (k3_tarski @ X6)))),
% 0.89/1.14      inference('cnf', [status(esa)], [d4_tarski])).
% 0.89/1.14  thf('31', plain,
% 0.89/1.14      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.89/1.14         ((r2_hidden @ X7 @ (k3_tarski @ X6))
% 0.89/1.14          | ~ (r2_hidden @ X7 @ X5)
% 0.89/1.14          | ~ (r2_hidden @ X5 @ X6))),
% 0.89/1.14      inference('simplify', [status(thm)], ['30'])).
% 0.89/1.14  thf('32', plain,
% 0.89/1.14      (![X0 : $i, X1 : $i]:
% 0.89/1.14         ((v1_xboole_0 @ X0)
% 0.89/1.14          | ~ (r2_hidden @ X0 @ X1)
% 0.89/1.14          | (r2_hidden @ (sk_B @ X0) @ (k3_tarski @ X1)))),
% 0.89/1.14      inference('sup-', [status(thm)], ['29', '31'])).
% 0.89/1.14  thf('33', plain,
% 0.89/1.14      (((r2_hidden @ (sk_B @ sk_D_3) @ 
% 0.89/1.14         (k3_tarski @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))
% 0.89/1.14        | (v1_xboole_0 @ sk_D_3))),
% 0.89/1.14      inference('sup-', [status(thm)], ['28', '32'])).
% 0.89/1.14  thf(t99_zfmisc_1, axiom,
% 0.89/1.14    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.89/1.14  thf('34', plain, (![X12 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X12)) = (X12))),
% 0.89/1.14      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.89/1.14  thf('35', plain,
% 0.89/1.14      (((r2_hidden @ (sk_B @ sk_D_3) @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.89/1.14        | (v1_xboole_0 @ sk_D_3))),
% 0.89/1.14      inference('demod', [status(thm)], ['33', '34'])).
% 0.89/1.14  thf(t10_mcart_1, axiom,
% 0.89/1.14    (![A:$i,B:$i,C:$i]:
% 0.89/1.14     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.89/1.14       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.89/1.14         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.89/1.14  thf('36', plain,
% 0.89/1.14      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.89/1.14         ((r2_hidden @ (k2_mcart_1 @ X34) @ X36)
% 0.89/1.14          | ~ (r2_hidden @ X34 @ (k2_zfmisc_1 @ X35 @ X36)))),
% 0.89/1.14      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.89/1.14  thf('37', plain,
% 0.89/1.14      (((v1_xboole_0 @ sk_D_3)
% 0.89/1.14        | (r2_hidden @ (k2_mcart_1 @ (sk_B @ sk_D_3)) @ sk_B_1))),
% 0.89/1.14      inference('sup-', [status(thm)], ['35', '36'])).
% 0.89/1.14  thf('38', plain,
% 0.89/1.14      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.89/1.14      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.89/1.14  thf('39', plain, (((v1_xboole_0 @ sk_D_3) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.89/1.14      inference('sup-', [status(thm)], ['37', '38'])).
% 0.89/1.14  thf('40', plain,
% 0.89/1.14      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_D_3))),
% 0.89/1.14      inference('sup-', [status(thm)], ['23', '39'])).
% 0.89/1.14  thf('41', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_3 @ sk_C_1))),
% 0.89/1.14      inference('demod', [status(thm)], ['0', '3'])).
% 0.89/1.14  thf('42', plain,
% 0.89/1.14      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.89/1.14         (~ (r2_hidden @ X19 @ (k9_relat_1 @ X20 @ X18))
% 0.89/1.14          | (r2_hidden @ (k4_tarski @ (sk_D_2 @ X20 @ X18 @ X19) @ X19) @ X20)
% 0.89/1.14          | ~ (v1_relat_1 @ X20))),
% 0.89/1.14      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.89/1.14  thf('43', plain,
% 0.89/1.14      ((~ (v1_relat_1 @ sk_D_3)
% 0.89/1.14        | (r2_hidden @ 
% 0.89/1.14           (k4_tarski @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_E) @ sk_D_3))),
% 0.89/1.14      inference('sup-', [status(thm)], ['41', '42'])).
% 0.89/1.14  thf('44', plain, ((v1_relat_1 @ sk_D_3)),
% 0.89/1.14      inference('sup-', [status(thm)], ['7', '8'])).
% 0.89/1.14  thf('45', plain,
% 0.89/1.14      ((r2_hidden @ (k4_tarski @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_E) @ 
% 0.89/1.14        sk_D_3)),
% 0.89/1.14      inference('demod', [status(thm)], ['43', '44'])).
% 0.89/1.14  thf('46', plain,
% 0.89/1.14      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.89/1.14      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.89/1.14  thf('47', plain, (~ (v1_xboole_0 @ sk_D_3)),
% 0.89/1.14      inference('sup-', [status(thm)], ['45', '46'])).
% 0.89/1.14  thf('48', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 0.89/1.14      inference('sup-', [status(thm)], ['40', '47'])).
% 0.89/1.14  thf('49', plain, ((zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A)),
% 0.89/1.14      inference('demod', [status(thm)], ['20', '48'])).
% 0.89/1.14  thf('50', plain, (((sk_A) = (k1_relat_1 @ sk_D_3))),
% 0.89/1.14      inference('demod', [status(thm)], ['17', '49'])).
% 0.89/1.14  thf('51', plain, ((r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_A)),
% 0.89/1.14      inference('demod', [status(thm)], ['10', '50'])).
% 0.89/1.14  thf('52', plain,
% 0.89/1.14      (![X45 : $i]:
% 0.89/1.14         (~ (r2_hidden @ X45 @ sk_A)
% 0.89/1.14          | ~ (r2_hidden @ X45 @ sk_C_1)
% 0.89/1.14          | ((sk_E) != (k1_funct_1 @ sk_D_3 @ X45)))),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('53', plain,
% 0.89/1.14      ((((sk_E) != (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E)))
% 0.89/1.14        | ~ (r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_C_1))),
% 0.89/1.14      inference('sup-', [status(thm)], ['51', '52'])).
% 0.89/1.14  thf('54', plain,
% 0.89/1.14      ((r2_hidden @ (k4_tarski @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_E) @ 
% 0.89/1.14        sk_D_3)),
% 0.89/1.14      inference('demod', [status(thm)], ['43', '44'])).
% 0.89/1.14  thf(t8_funct_1, axiom,
% 0.89/1.14    (![A:$i,B:$i,C:$i]:
% 0.89/1.14     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.89/1.14       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.89/1.14         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.89/1.14           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.89/1.14  thf('55', plain,
% 0.89/1.14      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.89/1.14         (~ (r2_hidden @ (k4_tarski @ X21 @ X23) @ X22)
% 0.89/1.14          | ((X23) = (k1_funct_1 @ X22 @ X21))
% 0.89/1.14          | ~ (v1_funct_1 @ X22)
% 0.89/1.14          | ~ (v1_relat_1 @ X22))),
% 0.89/1.14      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.89/1.14  thf('56', plain,
% 0.89/1.14      ((~ (v1_relat_1 @ sk_D_3)
% 0.89/1.14        | ~ (v1_funct_1 @ sk_D_3)
% 0.89/1.14        | ((sk_E) = (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E))))),
% 0.89/1.14      inference('sup-', [status(thm)], ['54', '55'])).
% 0.89/1.14  thf('57', plain, ((v1_relat_1 @ sk_D_3)),
% 0.89/1.14      inference('sup-', [status(thm)], ['7', '8'])).
% 0.89/1.14  thf('58', plain, ((v1_funct_1 @ sk_D_3)),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('59', plain,
% 0.89/1.14      (((sk_E) = (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E)))),
% 0.89/1.14      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.89/1.14  thf('60', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_3 @ sk_C_1))),
% 0.89/1.14      inference('demod', [status(thm)], ['0', '3'])).
% 0.89/1.14  thf('61', plain,
% 0.89/1.14      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.89/1.14         (~ (r2_hidden @ X19 @ (k9_relat_1 @ X20 @ X18))
% 0.89/1.14          | (r2_hidden @ (sk_D_2 @ X20 @ X18 @ X19) @ X18)
% 0.89/1.14          | ~ (v1_relat_1 @ X20))),
% 0.89/1.14      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.89/1.14  thf('62', plain,
% 0.89/1.14      ((~ (v1_relat_1 @ sk_D_3)
% 0.89/1.14        | (r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_C_1))),
% 0.89/1.14      inference('sup-', [status(thm)], ['60', '61'])).
% 0.89/1.14  thf('63', plain, ((v1_relat_1 @ sk_D_3)),
% 0.89/1.14      inference('sup-', [status(thm)], ['7', '8'])).
% 0.89/1.14  thf('64', plain, ((r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_C_1)),
% 0.89/1.14      inference('demod', [status(thm)], ['62', '63'])).
% 0.89/1.14  thf('65', plain, (((sk_E) != (sk_E))),
% 0.89/1.14      inference('demod', [status(thm)], ['53', '59', '64'])).
% 0.89/1.14  thf('66', plain, ($false), inference('simplify', [status(thm)], ['65'])).
% 0.89/1.14  
% 0.89/1.14  % SZS output end Refutation
% 0.89/1.14  
% 0.89/1.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
