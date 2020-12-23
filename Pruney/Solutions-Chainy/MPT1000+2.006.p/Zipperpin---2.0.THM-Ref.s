%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.baky3r9JQY

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:58 EST 2020

% Result     : Theorem 4.80s
% Output     : Refutation 4.80s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 247 expanded)
%              Number of leaves         :   42 (  88 expanded)
%              Depth                    :   15
%              Number of atoms          :  848 (2612 expanded)
%              Number of equality atoms :  104 ( 291 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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
    ! [X37: $i,X38: $i] :
      ( ( zip_tseitin_0 @ X37 @ X38 )
      | ( X37 = k1_xboole_0 ) ) ),
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
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( zip_tseitin_0 @ X42 @ X43 )
      | ( zip_tseitin_1 @ X44 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) ) ) ),
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
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_funct_2 @ X41 @ X39 @ X40 )
      | ( X39
        = ( k1_relset_1 @ X39 @ X40 @ X41 ) )
      | ~ ( zip_tseitin_1 @ X41 @ X40 @ X39 ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( ( k8_relset_1 @ X34 @ X35 @ X33 @ X36 )
        = ( k10_relat_1 @ X33 @ X36 ) ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v5_relat_1 @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ),
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
    ! [X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X25 ) @ X26 )
      | ( ( k5_relat_1 @ X25 @ ( k6_relat_1 @ X26 ) )
        = X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
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
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('34',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X22 @ X21 ) )
        = ( k10_relat_1 @ X22 @ ( k1_relat_1 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('36',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

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
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_funct_2 @ X41 @ X39 @ X40 )
      | ( X39
        = ( k1_relset_1 @ X39 @ X40 @ X41 ) )
      | ~ ( zip_tseitin_1 @ X41 @ X40 @ X39 ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
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
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( zip_tseitin_0 @ X42 @ X43 )
      | ( zip_tseitin_1 @ X44 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('73',plain,
    ( ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_B_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X37: $i,X38: $i] :
      ( ( zip_tseitin_0 @ X37 @ X38 )
      | ( X38 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X37: $i] :
      ( zip_tseitin_0 @ X37 @ k1_xboole_0 ) ),
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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.baky3r9JQY
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:42:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 4.80/5.02  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.80/5.02  % Solved by: fo/fo7.sh
% 4.80/5.02  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.80/5.02  % done 4409 iterations in 4.569s
% 4.80/5.02  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.80/5.02  % SZS output start Refutation
% 4.80/5.02  thf(sk_C_1_type, type, sk_C_1: $i).
% 4.80/5.02  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.80/5.02  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 4.80/5.02  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 4.80/5.02  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.80/5.02  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.80/5.02  thf(sk_A_type, type, sk_A: $i).
% 4.80/5.02  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 4.80/5.02  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.80/5.02  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.80/5.02  thf(sk_B_1_type, type, sk_B_1: $i).
% 4.80/5.02  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 4.80/5.02  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.80/5.02  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.80/5.02  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 4.80/5.02  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 4.80/5.02  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.80/5.02  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 4.80/5.02  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.80/5.02  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 4.80/5.02  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.80/5.02  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.80/5.02  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 4.80/5.02  thf(d1_funct_2, axiom,
% 4.80/5.02    (![A:$i,B:$i,C:$i]:
% 4.80/5.02     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.80/5.02       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.80/5.02           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 4.80/5.02             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 4.80/5.02         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.80/5.02           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 4.80/5.02             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 4.80/5.02  thf(zf_stmt_0, axiom,
% 4.80/5.02    (![B:$i,A:$i]:
% 4.80/5.02     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.80/5.02       ( zip_tseitin_0 @ B @ A ) ))).
% 4.80/5.02  thf('0', plain,
% 4.80/5.02      (![X37 : $i, X38 : $i]:
% 4.80/5.02         ((zip_tseitin_0 @ X37 @ X38) | ((X37) = (k1_xboole_0)))),
% 4.80/5.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/5.02  thf(t48_funct_2, conjecture,
% 4.80/5.02    (![A:$i,B:$i,C:$i]:
% 4.80/5.02     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.80/5.02         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.80/5.02       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.80/5.02         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( A ) ) ) ))).
% 4.80/5.02  thf(zf_stmt_1, negated_conjecture,
% 4.80/5.02    (~( ![A:$i,B:$i,C:$i]:
% 4.80/5.02        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.80/5.02            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.80/5.02          ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.80/5.02            ( ( k8_relset_1 @ A @ B @ C @ B ) = ( A ) ) ) ) )),
% 4.80/5.02    inference('cnf.neg', [status(esa)], [t48_funct_2])).
% 4.80/5.02  thf('1', plain,
% 4.80/5.02      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.80/5.02      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.80/5.02  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 4.80/5.02  thf(zf_stmt_3, axiom,
% 4.80/5.02    (![C:$i,B:$i,A:$i]:
% 4.80/5.02     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 4.80/5.02       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 4.80/5.02  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 4.80/5.02  thf(zf_stmt_5, axiom,
% 4.80/5.02    (![A:$i,B:$i,C:$i]:
% 4.80/5.02     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.80/5.02       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 4.80/5.02         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.80/5.02           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 4.80/5.02             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 4.80/5.02  thf('2', plain,
% 4.80/5.02      (![X42 : $i, X43 : $i, X44 : $i]:
% 4.80/5.02         (~ (zip_tseitin_0 @ X42 @ X43)
% 4.80/5.02          | (zip_tseitin_1 @ X44 @ X42 @ X43)
% 4.80/5.02          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42))))),
% 4.80/5.02      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.80/5.02  thf('3', plain,
% 4.80/5.02      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 4.80/5.02        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 4.80/5.02      inference('sup-', [status(thm)], ['1', '2'])).
% 4.80/5.02  thf('4', plain,
% 4.80/5.02      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A))),
% 4.80/5.02      inference('sup-', [status(thm)], ['0', '3'])).
% 4.80/5.02  thf('5', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 4.80/5.02      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.80/5.02  thf('6', plain,
% 4.80/5.02      (![X39 : $i, X40 : $i, X41 : $i]:
% 4.80/5.02         (~ (v1_funct_2 @ X41 @ X39 @ X40)
% 4.80/5.02          | ((X39) = (k1_relset_1 @ X39 @ X40 @ X41))
% 4.80/5.02          | ~ (zip_tseitin_1 @ X41 @ X40 @ X39))),
% 4.80/5.02      inference('cnf', [status(esa)], [zf_stmt_3])).
% 4.80/5.02  thf('7', plain,
% 4.80/5.02      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 4.80/5.02        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 4.80/5.02      inference('sup-', [status(thm)], ['5', '6'])).
% 4.80/5.02  thf('8', plain,
% 4.80/5.02      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.80/5.02      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.80/5.02  thf(redefinition_k1_relset_1, axiom,
% 4.80/5.02    (![A:$i,B:$i,C:$i]:
% 4.80/5.02     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.80/5.02       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 4.80/5.02  thf('9', plain,
% 4.80/5.02      (![X30 : $i, X31 : $i, X32 : $i]:
% 4.80/5.02         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 4.80/5.02          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 4.80/5.02      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.80/5.02  thf('10', plain,
% 4.80/5.02      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 4.80/5.02      inference('sup-', [status(thm)], ['8', '9'])).
% 4.80/5.02  thf('11', plain,
% 4.80/5.02      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 4.80/5.02        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 4.80/5.02      inference('demod', [status(thm)], ['7', '10'])).
% 4.80/5.02  thf('12', plain,
% 4.80/5.02      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 4.80/5.02      inference('sup-', [status(thm)], ['4', '11'])).
% 4.80/5.02  thf('13', plain,
% 4.80/5.02      (((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_B_1) != (sk_A))),
% 4.80/5.02      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.80/5.02  thf('14', plain,
% 4.80/5.02      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.80/5.02      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.80/5.02  thf(redefinition_k8_relset_1, axiom,
% 4.80/5.02    (![A:$i,B:$i,C:$i,D:$i]:
% 4.80/5.02     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.80/5.02       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 4.80/5.02  thf('15', plain,
% 4.80/5.02      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 4.80/5.02         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 4.80/5.02          | ((k8_relset_1 @ X34 @ X35 @ X33 @ X36) = (k10_relat_1 @ X33 @ X36)))),
% 4.80/5.02      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 4.80/5.02  thf('16', plain,
% 4.80/5.02      (![X0 : $i]:
% 4.80/5.02         ((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ X0)
% 4.80/5.02           = (k10_relat_1 @ sk_C_1 @ X0))),
% 4.80/5.02      inference('sup-', [status(thm)], ['14', '15'])).
% 4.80/5.02  thf('17', plain, (((k10_relat_1 @ sk_C_1 @ sk_B_1) != (sk_A))),
% 4.80/5.02      inference('demod', [status(thm)], ['13', '16'])).
% 4.80/5.02  thf('18', plain,
% 4.80/5.02      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.80/5.02      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.80/5.02  thf(cc2_relset_1, axiom,
% 4.80/5.02    (![A:$i,B:$i,C:$i]:
% 4.80/5.02     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.80/5.02       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 4.80/5.02  thf('19', plain,
% 4.80/5.02      (![X27 : $i, X28 : $i, X29 : $i]:
% 4.80/5.02         ((v5_relat_1 @ X27 @ X29)
% 4.80/5.02          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 4.80/5.02      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.80/5.02  thf('20', plain, ((v5_relat_1 @ sk_C_1 @ sk_B_1)),
% 4.80/5.02      inference('sup-', [status(thm)], ['18', '19'])).
% 4.80/5.02  thf(d19_relat_1, axiom,
% 4.80/5.02    (![A:$i,B:$i]:
% 4.80/5.02     ( ( v1_relat_1 @ B ) =>
% 4.80/5.02       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 4.80/5.02  thf('21', plain,
% 4.80/5.02      (![X15 : $i, X16 : $i]:
% 4.80/5.02         (~ (v5_relat_1 @ X15 @ X16)
% 4.80/5.02          | (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 4.80/5.02          | ~ (v1_relat_1 @ X15))),
% 4.80/5.02      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.80/5.02  thf('22', plain,
% 4.80/5.02      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))),
% 4.80/5.02      inference('sup-', [status(thm)], ['20', '21'])).
% 4.80/5.02  thf('23', plain,
% 4.80/5.02      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.80/5.02      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.80/5.02  thf(cc2_relat_1, axiom,
% 4.80/5.02    (![A:$i]:
% 4.80/5.02     ( ( v1_relat_1 @ A ) =>
% 4.80/5.02       ( ![B:$i]:
% 4.80/5.02         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 4.80/5.02  thf('24', plain,
% 4.80/5.02      (![X13 : $i, X14 : $i]:
% 4.80/5.02         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 4.80/5.02          | (v1_relat_1 @ X13)
% 4.80/5.02          | ~ (v1_relat_1 @ X14))),
% 4.80/5.02      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.80/5.02  thf('25', plain,
% 4.80/5.02      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_C_1))),
% 4.80/5.02      inference('sup-', [status(thm)], ['23', '24'])).
% 4.80/5.02  thf(fc6_relat_1, axiom,
% 4.80/5.02    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 4.80/5.02  thf('26', plain,
% 4.80/5.02      (![X19 : $i, X20 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X19 @ X20))),
% 4.80/5.02      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.80/5.02  thf('27', plain, ((v1_relat_1 @ sk_C_1)),
% 4.80/5.02      inference('demod', [status(thm)], ['25', '26'])).
% 4.80/5.02  thf('28', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)),
% 4.80/5.02      inference('demod', [status(thm)], ['22', '27'])).
% 4.80/5.02  thf(t79_relat_1, axiom,
% 4.80/5.02    (![A:$i,B:$i]:
% 4.80/5.02     ( ( v1_relat_1 @ B ) =>
% 4.80/5.02       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 4.80/5.02         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 4.80/5.02  thf('29', plain,
% 4.80/5.02      (![X25 : $i, X26 : $i]:
% 4.80/5.02         (~ (r1_tarski @ (k2_relat_1 @ X25) @ X26)
% 4.80/5.02          | ((k5_relat_1 @ X25 @ (k6_relat_1 @ X26)) = (X25))
% 4.80/5.02          | ~ (v1_relat_1 @ X25))),
% 4.80/5.02      inference('cnf', [status(esa)], [t79_relat_1])).
% 4.80/5.02  thf('30', plain,
% 4.80/5.02      ((~ (v1_relat_1 @ sk_C_1)
% 4.80/5.02        | ((k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B_1)) = (sk_C_1)))),
% 4.80/5.02      inference('sup-', [status(thm)], ['28', '29'])).
% 4.80/5.02  thf('31', plain, ((v1_relat_1 @ sk_C_1)),
% 4.80/5.02      inference('demod', [status(thm)], ['25', '26'])).
% 4.80/5.02  thf('32', plain,
% 4.80/5.02      (((k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B_1)) = (sk_C_1))),
% 4.80/5.02      inference('demod', [status(thm)], ['30', '31'])).
% 4.80/5.02  thf(t71_relat_1, axiom,
% 4.80/5.02    (![A:$i]:
% 4.80/5.02     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 4.80/5.02       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 4.80/5.02  thf('33', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 4.80/5.02      inference('cnf', [status(esa)], [t71_relat_1])).
% 4.80/5.02  thf(t182_relat_1, axiom,
% 4.80/5.02    (![A:$i]:
% 4.80/5.02     ( ( v1_relat_1 @ A ) =>
% 4.80/5.02       ( ![B:$i]:
% 4.80/5.02         ( ( v1_relat_1 @ B ) =>
% 4.80/5.02           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 4.80/5.02             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 4.80/5.02  thf('34', plain,
% 4.80/5.02      (![X21 : $i, X22 : $i]:
% 4.80/5.02         (~ (v1_relat_1 @ X21)
% 4.80/5.02          | ((k1_relat_1 @ (k5_relat_1 @ X22 @ X21))
% 4.80/5.02              = (k10_relat_1 @ X22 @ (k1_relat_1 @ X21)))
% 4.80/5.02          | ~ (v1_relat_1 @ X22))),
% 4.80/5.02      inference('cnf', [status(esa)], [t182_relat_1])).
% 4.80/5.02  thf('35', plain,
% 4.80/5.02      (![X0 : $i, X1 : $i]:
% 4.80/5.02         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 4.80/5.02            = (k10_relat_1 @ X1 @ X0))
% 4.80/5.02          | ~ (v1_relat_1 @ X1)
% 4.80/5.02          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 4.80/5.02      inference('sup+', [status(thm)], ['33', '34'])).
% 4.80/5.02  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 4.80/5.02  thf('36', plain, (![X17 : $i]: (v1_relat_1 @ (k6_relat_1 @ X17))),
% 4.80/5.02      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 4.80/5.02  thf('37', plain,
% 4.80/5.02      (![X0 : $i, X1 : $i]:
% 4.80/5.02         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 4.80/5.02            = (k10_relat_1 @ X1 @ X0))
% 4.80/5.02          | ~ (v1_relat_1 @ X1))),
% 4.80/5.02      inference('demod', [status(thm)], ['35', '36'])).
% 4.80/5.02  thf('38', plain,
% 4.80/5.02      ((((k1_relat_1 @ sk_C_1) = (k10_relat_1 @ sk_C_1 @ sk_B_1))
% 4.80/5.02        | ~ (v1_relat_1 @ sk_C_1))),
% 4.80/5.02      inference('sup+', [status(thm)], ['32', '37'])).
% 4.80/5.02  thf('39', plain, ((v1_relat_1 @ sk_C_1)),
% 4.80/5.02      inference('demod', [status(thm)], ['25', '26'])).
% 4.80/5.02  thf('40', plain, (((k1_relat_1 @ sk_C_1) = (k10_relat_1 @ sk_C_1 @ sk_B_1))),
% 4.80/5.02      inference('demod', [status(thm)], ['38', '39'])).
% 4.80/5.02  thf('41', plain, (((k1_relat_1 @ sk_C_1) != (sk_A))),
% 4.80/5.02      inference('demod', [status(thm)], ['17', '40'])).
% 4.80/5.02  thf('42', plain, ((((sk_A) != (sk_A)) | ((sk_B_1) = (k1_xboole_0)))),
% 4.80/5.02      inference('sup-', [status(thm)], ['12', '41'])).
% 4.80/5.02  thf('43', plain, (((sk_B_1) = (k1_xboole_0))),
% 4.80/5.02      inference('simplify', [status(thm)], ['42'])).
% 4.80/5.02  thf('44', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B_1) != (k1_xboole_0)))),
% 4.80/5.02      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.80/5.02  thf('45', plain,
% 4.80/5.02      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 4.80/5.02      inference('split', [status(esa)], ['44'])).
% 4.80/5.02  thf('46', plain, (((k1_relat_1 @ sk_C_1) = (k10_relat_1 @ sk_C_1 @ sk_B_1))),
% 4.80/5.02      inference('demod', [status(thm)], ['38', '39'])).
% 4.80/5.02  thf('47', plain,
% 4.80/5.02      (![X0 : $i]:
% 4.80/5.02         ((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ X0)
% 4.80/5.02           = (k10_relat_1 @ sk_C_1 @ X0))),
% 4.80/5.02      inference('sup-', [status(thm)], ['14', '15'])).
% 4.80/5.02  thf(l13_xboole_0, axiom,
% 4.80/5.02    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 4.80/5.02  thf('48', plain,
% 4.80/5.02      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 4.80/5.02      inference('cnf', [status(esa)], [l13_xboole_0])).
% 4.80/5.02  thf('49', plain,
% 4.80/5.02      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 4.80/5.02      inference('split', [status(esa)], ['44'])).
% 4.80/5.02  thf('50', plain,
% 4.80/5.02      (((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_B_1) != (sk_A))),
% 4.80/5.02      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.80/5.02  thf('51', plain,
% 4.80/5.02      ((((k8_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_1 @ sk_B_1) != (sk_A)))
% 4.80/5.02         <= ((((sk_A) = (k1_xboole_0))))),
% 4.80/5.02      inference('sup-', [status(thm)], ['49', '50'])).
% 4.80/5.02  thf('52', plain,
% 4.80/5.02      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 4.80/5.02      inference('split', [status(esa)], ['44'])).
% 4.80/5.02  thf('53', plain,
% 4.80/5.02      ((((k8_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_1 @ sk_B_1)
% 4.80/5.02          != (k1_xboole_0)))
% 4.80/5.02         <= ((((sk_A) = (k1_xboole_0))))),
% 4.80/5.02      inference('demod', [status(thm)], ['51', '52'])).
% 4.80/5.02  thf('54', plain,
% 4.80/5.02      ((![X0 : $i]:
% 4.80/5.02          (((k8_relset_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_B_1) != (k1_xboole_0))
% 4.80/5.02           | ~ (v1_xboole_0 @ X0)))
% 4.80/5.02         <= ((((sk_A) = (k1_xboole_0))))),
% 4.80/5.02      inference('sup-', [status(thm)], ['48', '53'])).
% 4.80/5.02  thf('55', plain,
% 4.80/5.02      (((((k10_relat_1 @ sk_C_1 @ sk_B_1) != (k1_xboole_0))
% 4.80/5.02         | ~ (v1_xboole_0 @ sk_A))) <= ((((sk_A) = (k1_xboole_0))))),
% 4.80/5.02      inference('sup-', [status(thm)], ['47', '54'])).
% 4.80/5.02  thf('56', plain,
% 4.80/5.02      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 4.80/5.02      inference('split', [status(esa)], ['44'])).
% 4.80/5.02  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 4.80/5.02  thf('57', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.80/5.02      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.80/5.02  thf('58', plain,
% 4.80/5.02      ((((k10_relat_1 @ sk_C_1 @ sk_B_1) != (k1_xboole_0)))
% 4.80/5.02         <= ((((sk_A) = (k1_xboole_0))))),
% 4.80/5.02      inference('demod', [status(thm)], ['55', '56', '57'])).
% 4.80/5.02  thf('59', plain,
% 4.80/5.02      ((((k1_relat_1 @ sk_C_1) != (k1_xboole_0)))
% 4.80/5.02         <= ((((sk_A) = (k1_xboole_0))))),
% 4.80/5.02      inference('sup-', [status(thm)], ['46', '58'])).
% 4.80/5.02  thf('60', plain,
% 4.80/5.02      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 4.80/5.02      inference('split', [status(esa)], ['44'])).
% 4.80/5.02  thf('61', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 4.80/5.02      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.80/5.02  thf('62', plain,
% 4.80/5.02      (((v1_funct_2 @ sk_C_1 @ k1_xboole_0 @ sk_B_1))
% 4.80/5.02         <= ((((sk_A) = (k1_xboole_0))))),
% 4.80/5.02      inference('sup+', [status(thm)], ['60', '61'])).
% 4.80/5.02  thf('63', plain,
% 4.80/5.02      (![X39 : $i, X40 : $i, X41 : $i]:
% 4.80/5.02         (~ (v1_funct_2 @ X41 @ X39 @ X40)
% 4.80/5.02          | ((X39) = (k1_relset_1 @ X39 @ X40 @ X41))
% 4.80/5.02          | ~ (zip_tseitin_1 @ X41 @ X40 @ X39))),
% 4.80/5.02      inference('cnf', [status(esa)], [zf_stmt_3])).
% 4.80/5.02  thf('64', plain,
% 4.80/5.02      (((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ k1_xboole_0)
% 4.80/5.02         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_1))))
% 4.80/5.02         <= ((((sk_A) = (k1_xboole_0))))),
% 4.80/5.02      inference('sup-', [status(thm)], ['62', '63'])).
% 4.80/5.02  thf('65', plain,
% 4.80/5.02      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 4.80/5.02      inference('split', [status(esa)], ['44'])).
% 4.80/5.02  thf('66', plain,
% 4.80/5.02      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.80/5.02      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.80/5.02  thf('67', plain,
% 4.80/5.02      (((m1_subset_1 @ sk_C_1 @ 
% 4.80/5.02         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 4.80/5.02         <= ((((sk_A) = (k1_xboole_0))))),
% 4.80/5.02      inference('sup+', [status(thm)], ['65', '66'])).
% 4.80/5.02  thf('68', plain,
% 4.80/5.02      (![X30 : $i, X31 : $i, X32 : $i]:
% 4.80/5.02         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 4.80/5.02          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 4.80/5.02      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.80/5.02  thf('69', plain,
% 4.80/5.02      ((((k1_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1)))
% 4.80/5.02         <= ((((sk_A) = (k1_xboole_0))))),
% 4.80/5.02      inference('sup-', [status(thm)], ['67', '68'])).
% 4.80/5.02  thf('70', plain,
% 4.80/5.02      (((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ k1_xboole_0)
% 4.80/5.02         | ((k1_xboole_0) = (k1_relat_1 @ sk_C_1))))
% 4.80/5.02         <= ((((sk_A) = (k1_xboole_0))))),
% 4.80/5.02      inference('demod', [status(thm)], ['64', '69'])).
% 4.80/5.02  thf('71', plain,
% 4.80/5.02      (((m1_subset_1 @ sk_C_1 @ 
% 4.80/5.02         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 4.80/5.02         <= ((((sk_A) = (k1_xboole_0))))),
% 4.80/5.02      inference('sup+', [status(thm)], ['65', '66'])).
% 4.80/5.02  thf('72', plain,
% 4.80/5.02      (![X42 : $i, X43 : $i, X44 : $i]:
% 4.80/5.02         (~ (zip_tseitin_0 @ X42 @ X43)
% 4.80/5.02          | (zip_tseitin_1 @ X44 @ X42 @ X43)
% 4.80/5.02          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42))))),
% 4.80/5.02      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.80/5.02  thf('73', plain,
% 4.80/5.02      ((((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ k1_xboole_0)
% 4.80/5.02         | ~ (zip_tseitin_0 @ sk_B_1 @ k1_xboole_0)))
% 4.80/5.02         <= ((((sk_A) = (k1_xboole_0))))),
% 4.80/5.02      inference('sup-', [status(thm)], ['71', '72'])).
% 4.80/5.02  thf('74', plain,
% 4.80/5.02      (![X37 : $i, X38 : $i]:
% 4.80/5.02         ((zip_tseitin_0 @ X37 @ X38) | ((X38) != (k1_xboole_0)))),
% 4.80/5.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/5.02  thf('75', plain, (![X37 : $i]: (zip_tseitin_0 @ X37 @ k1_xboole_0)),
% 4.80/5.02      inference('simplify', [status(thm)], ['74'])).
% 4.80/5.02  thf('76', plain,
% 4.80/5.02      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ k1_xboole_0))
% 4.80/5.02         <= ((((sk_A) = (k1_xboole_0))))),
% 4.80/5.02      inference('demod', [status(thm)], ['73', '75'])).
% 4.80/5.02  thf('77', plain,
% 4.80/5.02      ((((k1_xboole_0) = (k1_relat_1 @ sk_C_1)))
% 4.80/5.02         <= ((((sk_A) = (k1_xboole_0))))),
% 4.80/5.02      inference('demod', [status(thm)], ['70', '76'])).
% 4.80/5.02  thf('78', plain,
% 4.80/5.02      ((((k1_xboole_0) != (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 4.80/5.02      inference('demod', [status(thm)], ['59', '77'])).
% 4.80/5.02  thf('79', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 4.80/5.02      inference('simplify', [status(thm)], ['78'])).
% 4.80/5.02  thf('80', plain,
% 4.80/5.02      (~ (((sk_B_1) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 4.80/5.02      inference('split', [status(esa)], ['44'])).
% 4.80/5.02  thf('81', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 4.80/5.02      inference('sat_resolution*', [status(thm)], ['79', '80'])).
% 4.80/5.02  thf('82', plain, (((sk_B_1) != (k1_xboole_0))),
% 4.80/5.02      inference('simpl_trail', [status(thm)], ['45', '81'])).
% 4.80/5.02  thf('83', plain, ($false),
% 4.80/5.02      inference('simplify_reflect-', [status(thm)], ['43', '82'])).
% 4.80/5.02  
% 4.80/5.02  % SZS output end Refutation
% 4.80/5.02  
% 4.80/5.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
