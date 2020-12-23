%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0W8PvjoJyM

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:58 EST 2020

% Result     : Theorem 8.77s
% Output     : Refutation 8.77s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 247 expanded)
%              Number of leaves         :   42 (  88 expanded)
%              Depth                    :   15
%              Number of atoms          :  851 (2618 expanded)
%              Number of equality atoms :  104 ( 291 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

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

thf(zf_stmt_0,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X38: $i,X39: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 )
      | ( X38 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( k8_relset_1 @ A @ B @ C @ B )
          = A ) ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( k8_relset_1 @ A @ B @ C @ B )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_funct_2])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

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

thf('2',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( zip_tseitin_0 @ X43 @ X44 )
      | ( zip_tseitin_1 @ X45 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('3',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_funct_2 @ X42 @ X40 @ X41 )
      | ( X40
        = ( k1_relset_1 @ X40 @ X41 @ X42 ) )
      | ~ ( zip_tseitin_1 @ X42 @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('7',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('9',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X32 @ X33 @ X31 )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('10',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_B_1 )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('14',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('15',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( ( k8_relset_1 @ X35 @ X36 @ X34 @ X37 )
        = ( k10_relat_1 @ X34 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ X0 )
      = ( k10_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ( k10_relat_1 @ sk_C_1 @ sk_B_1 )
 != sk_A ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v5_relat_1 @ X28 @ X30 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('20',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('21',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v5_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('24',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('26',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('27',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['22','27'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('29',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X24 ) @ X25 )
      | ( ( k5_relat_1 @ X24 @ ( k6_relat_1 @ X25 ) )
        = X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B_1 ) )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['25','26'])).

thf('32',plain,
    ( ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B_1 ) )
    = sk_C_1 ),
    inference(demod,[status(thm)],['30','31'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('33',plain,(
    ! [X22: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('34',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X21 @ X20 ) )
        = ( k10_relat_1 @ X21 @ ( k1_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('36',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = ( k10_relat_1 @ sk_C_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['32','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['25','26'])).

thf('40',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k10_relat_1 @ sk_C_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ( k1_relat_1 @ sk_C_1 )
 != sk_A ),
    inference(demod,[status(thm)],['17','40'])).

thf('42',plain,
    ( ( sk_A != sk_A )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','41'])).

thf('43',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('45',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('46',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k10_relat_1 @ sk_C_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ X0 )
      = ( k10_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('48',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('49',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('50',plain,(
    ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_B_1 )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('51',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_1 @ sk_B_1 )
     != sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('53',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_1 @ sk_B_1 )
     != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ( ( k8_relset_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_B_1 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,
    ( ( ( ( k10_relat_1 @ sk_C_1 @ sk_B_1 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_A ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','54'])).

thf('56',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('57',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('58',plain,
    ( ( ( k10_relat_1 @ sk_C_1 @ sk_B_1 )
     != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
     != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','58'])).

thf('60',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('61',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('62',plain,
    ( ( v1_funct_2 @ sk_C_1 @ k1_xboole_0 @ sk_B_1 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_funct_2 @ X42 @ X40 @ X41 )
      | ( X40
        = ( k1_relset_1 @ X40 @ X41 @ X42 ) )
      | ~ ( zip_tseitin_1 @ X42 @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('64',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('66',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('67',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X32 @ X33 @ X31 )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('69',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_1 )
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ sk_C_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','69'])).

thf('71',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('72',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( zip_tseitin_0 @ X43 @ X44 )
      | ( zip_tseitin_1 @ X45 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('73',plain,
    ( ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_B_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X38: $i,X39: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 )
      | ( X39 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X38: $i] :
      ( zip_tseitin_0 @ X38 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','75'])).

thf('77',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','76'])).

thf('78',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','77'])).

thf('79',plain,(
    sk_A != k1_xboole_0 ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('81',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['79','80'])).

thf('82',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['45','81'])).

thf('83',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['43','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0W8PvjoJyM
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:51:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 8.77/8.95  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 8.77/8.95  % Solved by: fo/fo7.sh
% 8.77/8.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.77/8.95  % done 7525 iterations in 8.486s
% 8.77/8.95  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 8.77/8.95  % SZS output start Refutation
% 8.77/8.95  thf(sk_B_1_type, type, sk_B_1: $i).
% 8.77/8.95  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 8.77/8.95  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 8.77/8.95  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 8.77/8.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.77/8.95  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 8.77/8.95  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 8.77/8.95  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 8.77/8.95  thf(sk_A_type, type, sk_A: $i).
% 8.77/8.95  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 8.77/8.95  thf(sk_C_1_type, type, sk_C_1: $i).
% 8.77/8.95  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 8.77/8.95  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 8.77/8.95  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 8.77/8.95  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 8.77/8.95  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 8.77/8.95  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 8.77/8.95  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 8.77/8.95  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.77/8.95  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 8.77/8.95  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 8.77/8.95  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 8.77/8.95  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 8.77/8.95  thf(d1_funct_2, axiom,
% 8.77/8.95    (![A:$i,B:$i,C:$i]:
% 8.77/8.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.77/8.95       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 8.77/8.95           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 8.77/8.95             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 8.77/8.95         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 8.77/8.95           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 8.77/8.95             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 8.77/8.95  thf(zf_stmt_0, axiom,
% 8.77/8.95    (![B:$i,A:$i]:
% 8.77/8.95     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 8.77/8.95       ( zip_tseitin_0 @ B @ A ) ))).
% 8.77/8.95  thf('0', plain,
% 8.77/8.95      (![X38 : $i, X39 : $i]:
% 8.77/8.95         ((zip_tseitin_0 @ X38 @ X39) | ((X38) = (k1_xboole_0)))),
% 8.77/8.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.77/8.95  thf(t48_funct_2, conjecture,
% 8.77/8.95    (![A:$i,B:$i,C:$i]:
% 8.77/8.95     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 8.77/8.95         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 8.77/8.95       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 8.77/8.95         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( A ) ) ) ))).
% 8.77/8.95  thf(zf_stmt_1, negated_conjecture,
% 8.77/8.95    (~( ![A:$i,B:$i,C:$i]:
% 8.77/8.95        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 8.77/8.95            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 8.77/8.95          ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 8.77/8.95            ( ( k8_relset_1 @ A @ B @ C @ B ) = ( A ) ) ) ) )),
% 8.77/8.95    inference('cnf.neg', [status(esa)], [t48_funct_2])).
% 8.77/8.95  thf('1', plain,
% 8.77/8.95      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 8.77/8.95      inference('cnf', [status(esa)], [zf_stmt_1])).
% 8.77/8.95  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 8.77/8.95  thf(zf_stmt_3, axiom,
% 8.77/8.95    (![C:$i,B:$i,A:$i]:
% 8.77/8.95     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 8.77/8.95       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 8.77/8.95  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 8.77/8.95  thf(zf_stmt_5, axiom,
% 8.77/8.95    (![A:$i,B:$i,C:$i]:
% 8.77/8.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.77/8.95       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 8.77/8.95         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 8.77/8.95           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 8.77/8.95             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 8.77/8.95  thf('2', plain,
% 8.77/8.95      (![X43 : $i, X44 : $i, X45 : $i]:
% 8.77/8.95         (~ (zip_tseitin_0 @ X43 @ X44)
% 8.77/8.95          | (zip_tseitin_1 @ X45 @ X43 @ X44)
% 8.77/8.95          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43))))),
% 8.77/8.95      inference('cnf', [status(esa)], [zf_stmt_5])).
% 8.77/8.95  thf('3', plain,
% 8.77/8.95      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 8.77/8.95        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 8.77/8.95      inference('sup-', [status(thm)], ['1', '2'])).
% 8.77/8.95  thf('4', plain,
% 8.77/8.95      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A))),
% 8.77/8.95      inference('sup-', [status(thm)], ['0', '3'])).
% 8.77/8.95  thf('5', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 8.77/8.95      inference('cnf', [status(esa)], [zf_stmt_1])).
% 8.77/8.95  thf('6', plain,
% 8.77/8.95      (![X40 : $i, X41 : $i, X42 : $i]:
% 8.77/8.95         (~ (v1_funct_2 @ X42 @ X40 @ X41)
% 8.77/8.95          | ((X40) = (k1_relset_1 @ X40 @ X41 @ X42))
% 8.77/8.95          | ~ (zip_tseitin_1 @ X42 @ X41 @ X40))),
% 8.77/8.95      inference('cnf', [status(esa)], [zf_stmt_3])).
% 8.77/8.95  thf('7', plain,
% 8.77/8.95      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 8.77/8.95        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 8.77/8.95      inference('sup-', [status(thm)], ['5', '6'])).
% 8.77/8.95  thf('8', plain,
% 8.77/8.95      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 8.77/8.95      inference('cnf', [status(esa)], [zf_stmt_1])).
% 8.77/8.95  thf(redefinition_k1_relset_1, axiom,
% 8.77/8.95    (![A:$i,B:$i,C:$i]:
% 8.77/8.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.77/8.95       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 8.77/8.95  thf('9', plain,
% 8.77/8.95      (![X31 : $i, X32 : $i, X33 : $i]:
% 8.77/8.95         (((k1_relset_1 @ X32 @ X33 @ X31) = (k1_relat_1 @ X31))
% 8.77/8.95          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 8.77/8.95      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 8.77/8.95  thf('10', plain,
% 8.77/8.95      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 8.77/8.95      inference('sup-', [status(thm)], ['8', '9'])).
% 8.77/8.95  thf('11', plain,
% 8.77/8.95      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 8.77/8.95        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 8.77/8.95      inference('demod', [status(thm)], ['7', '10'])).
% 8.77/8.95  thf('12', plain,
% 8.77/8.95      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 8.77/8.95      inference('sup-', [status(thm)], ['4', '11'])).
% 8.77/8.95  thf('13', plain,
% 8.77/8.95      (((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_B_1) != (sk_A))),
% 8.77/8.95      inference('cnf', [status(esa)], [zf_stmt_1])).
% 8.77/8.95  thf('14', plain,
% 8.77/8.95      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 8.77/8.95      inference('cnf', [status(esa)], [zf_stmt_1])).
% 8.77/8.95  thf(redefinition_k8_relset_1, axiom,
% 8.77/8.95    (![A:$i,B:$i,C:$i,D:$i]:
% 8.77/8.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.77/8.95       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 8.77/8.95  thf('15', plain,
% 8.77/8.95      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 8.77/8.95         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 8.77/8.95          | ((k8_relset_1 @ X35 @ X36 @ X34 @ X37) = (k10_relat_1 @ X34 @ X37)))),
% 8.77/8.95      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 8.77/8.95  thf('16', plain,
% 8.77/8.95      (![X0 : $i]:
% 8.77/8.95         ((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ X0)
% 8.77/8.95           = (k10_relat_1 @ sk_C_1 @ X0))),
% 8.77/8.95      inference('sup-', [status(thm)], ['14', '15'])).
% 8.77/8.95  thf('17', plain, (((k10_relat_1 @ sk_C_1 @ sk_B_1) != (sk_A))),
% 8.77/8.95      inference('demod', [status(thm)], ['13', '16'])).
% 8.77/8.95  thf('18', plain,
% 8.77/8.95      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 8.77/8.95      inference('cnf', [status(esa)], [zf_stmt_1])).
% 8.77/8.95  thf(cc2_relset_1, axiom,
% 8.77/8.95    (![A:$i,B:$i,C:$i]:
% 8.77/8.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.77/8.95       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 8.77/8.95  thf('19', plain,
% 8.77/8.95      (![X28 : $i, X29 : $i, X30 : $i]:
% 8.77/8.95         ((v5_relat_1 @ X28 @ X30)
% 8.77/8.95          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 8.77/8.95      inference('cnf', [status(esa)], [cc2_relset_1])).
% 8.77/8.95  thf('20', plain, ((v5_relat_1 @ sk_C_1 @ sk_B_1)),
% 8.77/8.95      inference('sup-', [status(thm)], ['18', '19'])).
% 8.77/8.95  thf(d19_relat_1, axiom,
% 8.77/8.95    (![A:$i,B:$i]:
% 8.77/8.95     ( ( v1_relat_1 @ B ) =>
% 8.77/8.95       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 8.77/8.95  thf('21', plain,
% 8.77/8.95      (![X15 : $i, X16 : $i]:
% 8.77/8.95         (~ (v5_relat_1 @ X15 @ X16)
% 8.77/8.95          | (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 8.77/8.95          | ~ (v1_relat_1 @ X15))),
% 8.77/8.95      inference('cnf', [status(esa)], [d19_relat_1])).
% 8.77/8.95  thf('22', plain,
% 8.77/8.95      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))),
% 8.77/8.95      inference('sup-', [status(thm)], ['20', '21'])).
% 8.77/8.95  thf('23', plain,
% 8.77/8.95      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 8.77/8.95      inference('cnf', [status(esa)], [zf_stmt_1])).
% 8.77/8.95  thf(cc2_relat_1, axiom,
% 8.77/8.95    (![A:$i]:
% 8.77/8.95     ( ( v1_relat_1 @ A ) =>
% 8.77/8.95       ( ![B:$i]:
% 8.77/8.95         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 8.77/8.95  thf('24', plain,
% 8.77/8.95      (![X13 : $i, X14 : $i]:
% 8.77/8.95         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 8.77/8.95          | (v1_relat_1 @ X13)
% 8.77/8.95          | ~ (v1_relat_1 @ X14))),
% 8.77/8.95      inference('cnf', [status(esa)], [cc2_relat_1])).
% 8.77/8.95  thf('25', plain,
% 8.77/8.95      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_C_1))),
% 8.77/8.95      inference('sup-', [status(thm)], ['23', '24'])).
% 8.77/8.95  thf(fc6_relat_1, axiom,
% 8.77/8.95    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 8.77/8.95  thf('26', plain,
% 8.77/8.95      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 8.77/8.95      inference('cnf', [status(esa)], [fc6_relat_1])).
% 8.77/8.95  thf('27', plain, ((v1_relat_1 @ sk_C_1)),
% 8.77/8.95      inference('demod', [status(thm)], ['25', '26'])).
% 8.77/8.95  thf('28', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)),
% 8.77/8.95      inference('demod', [status(thm)], ['22', '27'])).
% 8.77/8.95  thf(t79_relat_1, axiom,
% 8.77/8.95    (![A:$i,B:$i]:
% 8.77/8.95     ( ( v1_relat_1 @ B ) =>
% 8.77/8.95       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 8.77/8.95         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 8.77/8.95  thf('29', plain,
% 8.77/8.95      (![X24 : $i, X25 : $i]:
% 8.77/8.95         (~ (r1_tarski @ (k2_relat_1 @ X24) @ X25)
% 8.77/8.95          | ((k5_relat_1 @ X24 @ (k6_relat_1 @ X25)) = (X24))
% 8.77/8.95          | ~ (v1_relat_1 @ X24))),
% 8.77/8.95      inference('cnf', [status(esa)], [t79_relat_1])).
% 8.77/8.95  thf('30', plain,
% 8.77/8.95      ((~ (v1_relat_1 @ sk_C_1)
% 8.77/8.95        | ((k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B_1)) = (sk_C_1)))),
% 8.77/8.95      inference('sup-', [status(thm)], ['28', '29'])).
% 8.77/8.95  thf('31', plain, ((v1_relat_1 @ sk_C_1)),
% 8.77/8.95      inference('demod', [status(thm)], ['25', '26'])).
% 8.77/8.95  thf('32', plain,
% 8.77/8.95      (((k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B_1)) = (sk_C_1))),
% 8.77/8.95      inference('demod', [status(thm)], ['30', '31'])).
% 8.77/8.95  thf(t71_relat_1, axiom,
% 8.77/8.95    (![A:$i]:
% 8.77/8.95     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 8.77/8.95       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 8.77/8.95  thf('33', plain, (![X22 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 8.77/8.95      inference('cnf', [status(esa)], [t71_relat_1])).
% 8.77/8.95  thf(t182_relat_1, axiom,
% 8.77/8.95    (![A:$i]:
% 8.77/8.95     ( ( v1_relat_1 @ A ) =>
% 8.77/8.95       ( ![B:$i]:
% 8.77/8.95         ( ( v1_relat_1 @ B ) =>
% 8.77/8.95           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 8.77/8.95             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 8.77/8.95  thf('34', plain,
% 8.77/8.95      (![X20 : $i, X21 : $i]:
% 8.77/8.95         (~ (v1_relat_1 @ X20)
% 8.77/8.95          | ((k1_relat_1 @ (k5_relat_1 @ X21 @ X20))
% 8.77/8.95              = (k10_relat_1 @ X21 @ (k1_relat_1 @ X20)))
% 8.77/8.95          | ~ (v1_relat_1 @ X21))),
% 8.77/8.95      inference('cnf', [status(esa)], [t182_relat_1])).
% 8.77/8.95  thf('35', plain,
% 8.77/8.95      (![X0 : $i, X1 : $i]:
% 8.77/8.95         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 8.77/8.95            = (k10_relat_1 @ X1 @ X0))
% 8.77/8.95          | ~ (v1_relat_1 @ X1)
% 8.77/8.95          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 8.77/8.95      inference('sup+', [status(thm)], ['33', '34'])).
% 8.77/8.95  thf(fc3_funct_1, axiom,
% 8.77/8.95    (![A:$i]:
% 8.77/8.95     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 8.77/8.95       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 8.77/8.95  thf('36', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 8.77/8.95      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.77/8.95  thf('37', plain,
% 8.77/8.95      (![X0 : $i, X1 : $i]:
% 8.77/8.95         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 8.77/8.95            = (k10_relat_1 @ X1 @ X0))
% 8.77/8.95          | ~ (v1_relat_1 @ X1))),
% 8.77/8.95      inference('demod', [status(thm)], ['35', '36'])).
% 8.77/8.95  thf('38', plain,
% 8.77/8.95      ((((k1_relat_1 @ sk_C_1) = (k10_relat_1 @ sk_C_1 @ sk_B_1))
% 8.77/8.95        | ~ (v1_relat_1 @ sk_C_1))),
% 8.77/8.95      inference('sup+', [status(thm)], ['32', '37'])).
% 8.77/8.95  thf('39', plain, ((v1_relat_1 @ sk_C_1)),
% 8.77/8.95      inference('demod', [status(thm)], ['25', '26'])).
% 8.77/8.95  thf('40', plain, (((k1_relat_1 @ sk_C_1) = (k10_relat_1 @ sk_C_1 @ sk_B_1))),
% 8.77/8.95      inference('demod', [status(thm)], ['38', '39'])).
% 8.77/8.95  thf('41', plain, (((k1_relat_1 @ sk_C_1) != (sk_A))),
% 8.77/8.95      inference('demod', [status(thm)], ['17', '40'])).
% 8.77/8.95  thf('42', plain, ((((sk_A) != (sk_A)) | ((sk_B_1) = (k1_xboole_0)))),
% 8.77/8.95      inference('sup-', [status(thm)], ['12', '41'])).
% 8.77/8.95  thf('43', plain, (((sk_B_1) = (k1_xboole_0))),
% 8.77/8.95      inference('simplify', [status(thm)], ['42'])).
% 8.77/8.95  thf('44', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B_1) != (k1_xboole_0)))),
% 8.77/8.95      inference('cnf', [status(esa)], [zf_stmt_1])).
% 8.77/8.95  thf('45', plain,
% 8.77/8.95      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 8.77/8.95      inference('split', [status(esa)], ['44'])).
% 8.77/8.95  thf('46', plain, (((k1_relat_1 @ sk_C_1) = (k10_relat_1 @ sk_C_1 @ sk_B_1))),
% 8.77/8.95      inference('demod', [status(thm)], ['38', '39'])).
% 8.77/8.95  thf('47', plain,
% 8.77/8.95      (![X0 : $i]:
% 8.77/8.95         ((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ X0)
% 8.77/8.95           = (k10_relat_1 @ sk_C_1 @ X0))),
% 8.77/8.95      inference('sup-', [status(thm)], ['14', '15'])).
% 8.77/8.95  thf(l13_xboole_0, axiom,
% 8.77/8.95    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 8.77/8.95  thf('48', plain,
% 8.77/8.95      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 8.77/8.95      inference('cnf', [status(esa)], [l13_xboole_0])).
% 8.77/8.95  thf('49', plain,
% 8.77/8.95      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 8.77/8.95      inference('split', [status(esa)], ['44'])).
% 8.77/8.95  thf('50', plain,
% 8.77/8.95      (((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_B_1) != (sk_A))),
% 8.77/8.95      inference('cnf', [status(esa)], [zf_stmt_1])).
% 8.77/8.95  thf('51', plain,
% 8.77/8.95      ((((k8_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_1 @ sk_B_1) != (sk_A)))
% 8.77/8.95         <= ((((sk_A) = (k1_xboole_0))))),
% 8.77/8.95      inference('sup-', [status(thm)], ['49', '50'])).
% 8.77/8.95  thf('52', plain,
% 8.77/8.95      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 8.77/8.95      inference('split', [status(esa)], ['44'])).
% 8.77/8.95  thf('53', plain,
% 8.77/8.95      ((((k8_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_1 @ sk_B_1)
% 8.77/8.95          != (k1_xboole_0)))
% 8.77/8.95         <= ((((sk_A) = (k1_xboole_0))))),
% 8.77/8.95      inference('demod', [status(thm)], ['51', '52'])).
% 8.77/8.95  thf('54', plain,
% 8.77/8.95      ((![X0 : $i]:
% 8.77/8.95          (((k8_relset_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_B_1) != (k1_xboole_0))
% 8.77/8.95           | ~ (v1_xboole_0 @ X0)))
% 8.77/8.95         <= ((((sk_A) = (k1_xboole_0))))),
% 8.77/8.95      inference('sup-', [status(thm)], ['48', '53'])).
% 8.77/8.95  thf('55', plain,
% 8.77/8.95      (((((k10_relat_1 @ sk_C_1 @ sk_B_1) != (k1_xboole_0))
% 8.77/8.95         | ~ (v1_xboole_0 @ sk_A))) <= ((((sk_A) = (k1_xboole_0))))),
% 8.77/8.95      inference('sup-', [status(thm)], ['47', '54'])).
% 8.77/8.95  thf('56', plain,
% 8.77/8.95      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 8.77/8.95      inference('split', [status(esa)], ['44'])).
% 8.77/8.95  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 8.77/8.95  thf('57', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 8.77/8.95      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 8.77/8.95  thf('58', plain,
% 8.77/8.95      ((((k10_relat_1 @ sk_C_1 @ sk_B_1) != (k1_xboole_0)))
% 8.77/8.95         <= ((((sk_A) = (k1_xboole_0))))),
% 8.77/8.95      inference('demod', [status(thm)], ['55', '56', '57'])).
% 8.77/8.95  thf('59', plain,
% 8.77/8.95      ((((k1_relat_1 @ sk_C_1) != (k1_xboole_0)))
% 8.77/8.95         <= ((((sk_A) = (k1_xboole_0))))),
% 8.77/8.95      inference('sup-', [status(thm)], ['46', '58'])).
% 8.77/8.95  thf('60', plain,
% 8.77/8.95      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 8.77/8.95      inference('split', [status(esa)], ['44'])).
% 8.77/8.95  thf('61', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 8.77/8.95      inference('cnf', [status(esa)], [zf_stmt_1])).
% 8.77/8.95  thf('62', plain,
% 8.77/8.95      (((v1_funct_2 @ sk_C_1 @ k1_xboole_0 @ sk_B_1))
% 8.77/8.95         <= ((((sk_A) = (k1_xboole_0))))),
% 8.77/8.95      inference('sup+', [status(thm)], ['60', '61'])).
% 8.77/8.95  thf('63', plain,
% 8.77/8.95      (![X40 : $i, X41 : $i, X42 : $i]:
% 8.77/8.95         (~ (v1_funct_2 @ X42 @ X40 @ X41)
% 8.77/8.95          | ((X40) = (k1_relset_1 @ X40 @ X41 @ X42))
% 8.77/8.95          | ~ (zip_tseitin_1 @ X42 @ X41 @ X40))),
% 8.77/8.95      inference('cnf', [status(esa)], [zf_stmt_3])).
% 8.77/8.95  thf('64', plain,
% 8.77/8.95      (((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ k1_xboole_0)
% 8.77/8.95         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_1))))
% 8.77/8.95         <= ((((sk_A) = (k1_xboole_0))))),
% 8.77/8.95      inference('sup-', [status(thm)], ['62', '63'])).
% 8.77/8.95  thf('65', plain,
% 8.77/8.95      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 8.77/8.95      inference('split', [status(esa)], ['44'])).
% 8.77/8.95  thf('66', plain,
% 8.77/8.95      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 8.77/8.95      inference('cnf', [status(esa)], [zf_stmt_1])).
% 8.77/8.95  thf('67', plain,
% 8.77/8.95      (((m1_subset_1 @ sk_C_1 @ 
% 8.77/8.95         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 8.77/8.95         <= ((((sk_A) = (k1_xboole_0))))),
% 8.77/8.95      inference('sup+', [status(thm)], ['65', '66'])).
% 8.77/8.95  thf('68', plain,
% 8.77/8.95      (![X31 : $i, X32 : $i, X33 : $i]:
% 8.77/8.95         (((k1_relset_1 @ X32 @ X33 @ X31) = (k1_relat_1 @ X31))
% 8.77/8.95          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 8.77/8.95      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 8.77/8.95  thf('69', plain,
% 8.77/8.95      ((((k1_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1)))
% 8.77/8.95         <= ((((sk_A) = (k1_xboole_0))))),
% 8.77/8.95      inference('sup-', [status(thm)], ['67', '68'])).
% 8.77/8.95  thf('70', plain,
% 8.77/8.95      (((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ k1_xboole_0)
% 8.77/8.95         | ((k1_xboole_0) = (k1_relat_1 @ sk_C_1))))
% 8.77/8.95         <= ((((sk_A) = (k1_xboole_0))))),
% 8.77/8.95      inference('demod', [status(thm)], ['64', '69'])).
% 8.77/8.95  thf('71', plain,
% 8.77/8.95      (((m1_subset_1 @ sk_C_1 @ 
% 8.77/8.95         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 8.77/8.95         <= ((((sk_A) = (k1_xboole_0))))),
% 8.77/8.95      inference('sup+', [status(thm)], ['65', '66'])).
% 8.77/8.95  thf('72', plain,
% 8.77/8.95      (![X43 : $i, X44 : $i, X45 : $i]:
% 8.77/8.95         (~ (zip_tseitin_0 @ X43 @ X44)
% 8.77/8.95          | (zip_tseitin_1 @ X45 @ X43 @ X44)
% 8.77/8.95          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43))))),
% 8.77/8.95      inference('cnf', [status(esa)], [zf_stmt_5])).
% 8.77/8.95  thf('73', plain,
% 8.77/8.95      ((((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ k1_xboole_0)
% 8.77/8.95         | ~ (zip_tseitin_0 @ sk_B_1 @ k1_xboole_0)))
% 8.77/8.95         <= ((((sk_A) = (k1_xboole_0))))),
% 8.77/8.95      inference('sup-', [status(thm)], ['71', '72'])).
% 8.77/8.95  thf('74', plain,
% 8.77/8.95      (![X38 : $i, X39 : $i]:
% 8.77/8.95         ((zip_tseitin_0 @ X38 @ X39) | ((X39) != (k1_xboole_0)))),
% 8.77/8.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.77/8.95  thf('75', plain, (![X38 : $i]: (zip_tseitin_0 @ X38 @ k1_xboole_0)),
% 8.77/8.95      inference('simplify', [status(thm)], ['74'])).
% 8.77/8.95  thf('76', plain,
% 8.77/8.95      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ k1_xboole_0))
% 8.77/8.95         <= ((((sk_A) = (k1_xboole_0))))),
% 8.77/8.95      inference('demod', [status(thm)], ['73', '75'])).
% 8.77/8.95  thf('77', plain,
% 8.77/8.95      ((((k1_xboole_0) = (k1_relat_1 @ sk_C_1)))
% 8.77/8.95         <= ((((sk_A) = (k1_xboole_0))))),
% 8.77/8.95      inference('demod', [status(thm)], ['70', '76'])).
% 8.77/8.95  thf('78', plain,
% 8.77/8.95      ((((k1_xboole_0) != (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 8.77/8.95      inference('demod', [status(thm)], ['59', '77'])).
% 8.77/8.95  thf('79', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 8.77/8.95      inference('simplify', [status(thm)], ['78'])).
% 8.77/8.95  thf('80', plain,
% 8.77/8.95      (~ (((sk_B_1) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 8.77/8.95      inference('split', [status(esa)], ['44'])).
% 8.77/8.95  thf('81', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 8.77/8.95      inference('sat_resolution*', [status(thm)], ['79', '80'])).
% 8.77/8.95  thf('82', plain, (((sk_B_1) != (k1_xboole_0))),
% 8.77/8.95      inference('simpl_trail', [status(thm)], ['45', '81'])).
% 8.77/8.95  thf('83', plain, ($false),
% 8.77/8.95      inference('simplify_reflect-', [status(thm)], ['43', '82'])).
% 8.77/8.95  
% 8.77/8.95  % SZS output end Refutation
% 8.77/8.95  
% 8.77/8.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
