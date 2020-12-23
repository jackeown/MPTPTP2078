%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uX9TVZhCdl

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:58 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 240 expanded)
%              Number of leaves         :   39 (  85 expanded)
%              Depth                    :   15
%              Number of atoms          :  822 (2577 expanded)
%              Number of equality atoms :   97 ( 285 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

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
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('3',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('7',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('9',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('10',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_B_1 )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('15',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k8_relset_1 @ X26 @ X27 @ X25 @ X28 )
        = ( k10_relat_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ( k10_relat_1 @ sk_C @ sk_B_1 )
 != sk_A ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v5_relat_1 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('20',plain,(
    v5_relat_1 @ sk_C @ sk_B_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v5_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('24',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('26',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ),
    inference(demod,[status(thm)],['22','27'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('29',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ X18 )
      | ( ( k5_relat_1 @ X17 @ ( k6_relat_1 @ X18 ) )
        = X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B_1 ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['25','26'])).

thf('32',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B_1 ) )
    = sk_C ),
    inference(demod,[status(thm)],['30','31'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('33',plain,(
    ! [X15: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('34',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) )
        = ( k10_relat_1 @ X14 @ ( k1_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['32','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['25','26'])).

thf('40',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ sk_B_1 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ( k1_relat_1 @ sk_C )
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
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ sk_B_1 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('47',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('48',plain,(
    ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_B_1 )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('49',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C @ sk_B_1 )
     != sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('51',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C @ sk_B_1 )
     != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('54',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k8_relset_1 @ X26 @ X27 @ X25 @ X28 )
        = ( k10_relat_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( k8_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C @ X0 )
        = ( k10_relat_1 @ sk_C @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_B_1 )
     != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','56'])).

thf('58',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','57'])).

thf('59',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('60',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('61',plain,
    ( ( v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_B_1 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('63',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('65',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('66',plain,
    ( ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_B_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X30 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X29: $i] :
      ( zip_tseitin_0 @ X29 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','68'])).

thf('70',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('71',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('72',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C )
      = ( k1_relat_1 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','69','72'])).

thf('74',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','73'])).

thf('75',plain,(
    sk_A != k1_xboole_0 ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('77',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['75','76'])).

thf('78',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['45','77'])).

thf('79',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['43','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uX9TVZhCdl
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 21:02:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.46/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.70  % Solved by: fo/fo7.sh
% 0.46/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.70  % done 327 iterations in 0.251s
% 0.46/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.70  % SZS output start Refutation
% 0.46/0.70  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.46/0.70  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.70  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.46/0.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.70  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.46/0.70  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.46/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.70  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.70  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.46/0.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.70  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.46/0.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.70  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.46/0.70  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.46/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.70  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.46/0.70  thf(d1_funct_2, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.70       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.70           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.46/0.70             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.46/0.70         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.70           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.46/0.70             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.46/0.70  thf(zf_stmt_0, axiom,
% 0.46/0.70    (![B:$i,A:$i]:
% 0.46/0.70     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.70       ( zip_tseitin_0 @ B @ A ) ))).
% 0.46/0.70  thf('0', plain,
% 0.46/0.70      (![X29 : $i, X30 : $i]:
% 0.46/0.70         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(t48_funct_2, conjecture,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.70       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.70         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( A ) ) ) ))).
% 0.46/0.70  thf(zf_stmt_1, negated_conjecture,
% 0.46/0.70    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.70        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.70            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.70          ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.70            ( ( k8_relset_1 @ A @ B @ C @ B ) = ( A ) ) ) ) )),
% 0.46/0.70    inference('cnf.neg', [status(esa)], [t48_funct_2])).
% 0.46/0.70  thf('1', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.70  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.46/0.70  thf(zf_stmt_3, axiom,
% 0.46/0.70    (![C:$i,B:$i,A:$i]:
% 0.46/0.70     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.46/0.70       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.46/0.70  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.46/0.70  thf(zf_stmt_5, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.70       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.46/0.70         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.70           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.46/0.70             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.46/0.70  thf('2', plain,
% 0.46/0.70      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.46/0.70         (~ (zip_tseitin_0 @ X34 @ X35)
% 0.46/0.70          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 0.46/0.70          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.46/0.70  thf('3', plain,
% 0.46/0.70      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.46/0.70        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.46/0.70      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.70  thf('4', plain,
% 0.46/0.70      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A))),
% 0.46/0.70      inference('sup-', [status(thm)], ['0', '3'])).
% 0.46/0.70  thf('5', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.70  thf('6', plain,
% 0.46/0.70      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.46/0.70         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 0.46/0.70          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 0.46/0.70          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.70  thf('7', plain,
% 0.46/0.70      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.46/0.70        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.70  thf('8', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.70  thf(redefinition_k1_relset_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.70       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.46/0.70  thf('9', plain,
% 0.46/0.70      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.46/0.70         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 0.46/0.70          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.46/0.70      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.46/0.70  thf('10', plain,
% 0.46/0.70      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.46/0.70      inference('sup-', [status(thm)], ['8', '9'])).
% 0.46/0.70  thf('11', plain,
% 0.46/0.70      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.46/0.70        | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['7', '10'])).
% 0.46/0.70  thf('12', plain,
% 0.46/0.70      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['4', '11'])).
% 0.46/0.70  thf('13', plain, (((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_B_1) != (sk_A))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.70  thf('14', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.70  thf(redefinition_k8_relset_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.70       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.46/0.70  thf('15', plain,
% 0.46/0.70      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.46/0.70          | ((k8_relset_1 @ X26 @ X27 @ X25 @ X28) = (k10_relat_1 @ X25 @ X28)))),
% 0.46/0.70      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.46/0.70  thf('16', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.70  thf('17', plain, (((k10_relat_1 @ sk_C @ sk_B_1) != (sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['13', '16'])).
% 0.46/0.70  thf('18', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.70  thf(cc2_relset_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.70       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.46/0.70  thf('19', plain,
% 0.46/0.70      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.70         ((v5_relat_1 @ X19 @ X21)
% 0.46/0.70          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.46/0.70      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.70  thf('20', plain, ((v5_relat_1 @ sk_C @ sk_B_1)),
% 0.46/0.70      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.70  thf(d19_relat_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( v1_relat_1 @ B ) =>
% 0.46/0.70       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.46/0.70  thf('21', plain,
% 0.46/0.70      (![X8 : $i, X9 : $i]:
% 0.46/0.70         (~ (v5_relat_1 @ X8 @ X9)
% 0.46/0.70          | (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 0.46/0.70          | ~ (v1_relat_1 @ X8))),
% 0.46/0.70      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.46/0.70  thf('22', plain,
% 0.46/0.70      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))),
% 0.46/0.70      inference('sup-', [status(thm)], ['20', '21'])).
% 0.46/0.70  thf('23', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.70  thf(cc2_relat_1, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( v1_relat_1 @ A ) =>
% 0.46/0.70       ( ![B:$i]:
% 0.46/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.46/0.70  thf('24', plain,
% 0.46/0.70      (![X6 : $i, X7 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.46/0.70          | (v1_relat_1 @ X6)
% 0.46/0.70          | ~ (v1_relat_1 @ X7))),
% 0.46/0.70      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.46/0.70  thf('25', plain,
% 0.46/0.70      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_C))),
% 0.46/0.70      inference('sup-', [status(thm)], ['23', '24'])).
% 0.46/0.70  thf(fc6_relat_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.46/0.70  thf('26', plain,
% 0.46/0.70      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 0.46/0.70      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.46/0.70  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.70      inference('demod', [status(thm)], ['25', '26'])).
% 0.46/0.70  thf('28', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)),
% 0.46/0.70      inference('demod', [status(thm)], ['22', '27'])).
% 0.46/0.70  thf(t79_relat_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( v1_relat_1 @ B ) =>
% 0.46/0.70       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.46/0.70         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.46/0.70  thf('29', plain,
% 0.46/0.70      (![X17 : $i, X18 : $i]:
% 0.46/0.70         (~ (r1_tarski @ (k2_relat_1 @ X17) @ X18)
% 0.46/0.70          | ((k5_relat_1 @ X17 @ (k6_relat_1 @ X18)) = (X17))
% 0.46/0.70          | ~ (v1_relat_1 @ X17))),
% 0.46/0.70      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.46/0.70  thf('30', plain,
% 0.46/0.70      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.70        | ((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B_1)) = (sk_C)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['28', '29'])).
% 0.46/0.70  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.70      inference('demod', [status(thm)], ['25', '26'])).
% 0.46/0.70  thf('32', plain, (((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B_1)) = (sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['30', '31'])).
% 0.46/0.70  thf(t71_relat_1, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.46/0.70       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.46/0.70  thf('33', plain, (![X15 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X15)) = (X15))),
% 0.46/0.70      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.46/0.70  thf(t182_relat_1, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( v1_relat_1 @ A ) =>
% 0.46/0.70       ( ![B:$i]:
% 0.46/0.70         ( ( v1_relat_1 @ B ) =>
% 0.46/0.70           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.46/0.70             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.46/0.70  thf('34', plain,
% 0.46/0.70      (![X13 : $i, X14 : $i]:
% 0.46/0.70         (~ (v1_relat_1 @ X13)
% 0.46/0.70          | ((k1_relat_1 @ (k5_relat_1 @ X14 @ X13))
% 0.46/0.70              = (k10_relat_1 @ X14 @ (k1_relat_1 @ X13)))
% 0.46/0.70          | ~ (v1_relat_1 @ X14))),
% 0.46/0.70      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.46/0.70  thf('35', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.46/0.70            = (k10_relat_1 @ X1 @ X0))
% 0.46/0.70          | ~ (v1_relat_1 @ X1)
% 0.46/0.70          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.46/0.70      inference('sup+', [status(thm)], ['33', '34'])).
% 0.46/0.70  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.46/0.70  thf('36', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 0.46/0.70      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.46/0.70  thf('37', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.46/0.70            = (k10_relat_1 @ X1 @ X0))
% 0.46/0.70          | ~ (v1_relat_1 @ X1))),
% 0.46/0.70      inference('demod', [status(thm)], ['35', '36'])).
% 0.46/0.70  thf('38', plain,
% 0.46/0.70      ((((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_B_1))
% 0.46/0.70        | ~ (v1_relat_1 @ sk_C))),
% 0.46/0.70      inference('sup+', [status(thm)], ['32', '37'])).
% 0.46/0.70  thf('39', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.70      inference('demod', [status(thm)], ['25', '26'])).
% 0.46/0.70  thf('40', plain, (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_B_1))),
% 0.46/0.70      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.70  thf('41', plain, (((k1_relat_1 @ sk_C) != (sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['17', '40'])).
% 0.46/0.70  thf('42', plain, ((((sk_A) != (sk_A)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['12', '41'])).
% 0.46/0.70  thf('43', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.46/0.70      inference('simplify', [status(thm)], ['42'])).
% 0.46/0.70  thf('44', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B_1) != (k1_xboole_0)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.70  thf('45', plain,
% 0.46/0.70      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.46/0.70      inference('split', [status(esa)], ['44'])).
% 0.46/0.70  thf('46', plain, (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_B_1))),
% 0.46/0.70      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.70  thf('47', plain,
% 0.46/0.70      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.70      inference('split', [status(esa)], ['44'])).
% 0.46/0.70  thf('48', plain, (((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_B_1) != (sk_A))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.70  thf('49', plain,
% 0.46/0.70      ((((k8_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C @ sk_B_1) != (sk_A)))
% 0.46/0.70         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['47', '48'])).
% 0.46/0.70  thf('50', plain,
% 0.46/0.70      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.70      inference('split', [status(esa)], ['44'])).
% 0.46/0.70  thf('51', plain,
% 0.46/0.70      ((((k8_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C @ sk_B_1) != (k1_xboole_0)))
% 0.46/0.70         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.70      inference('demod', [status(thm)], ['49', '50'])).
% 0.46/0.70  thf('52', plain,
% 0.46/0.70      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.70      inference('split', [status(esa)], ['44'])).
% 0.46/0.70  thf('53', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.70  thf('54', plain,
% 0.46/0.70      (((m1_subset_1 @ sk_C @ 
% 0.46/0.70         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 0.46/0.70         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.70      inference('sup+', [status(thm)], ['52', '53'])).
% 0.46/0.70  thf('55', plain,
% 0.46/0.70      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.46/0.70          | ((k8_relset_1 @ X26 @ X27 @ X25 @ X28) = (k10_relat_1 @ X25 @ X28)))),
% 0.46/0.70      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.46/0.70  thf('56', plain,
% 0.46/0.70      ((![X0 : $i]:
% 0.46/0.70          ((k8_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C @ X0)
% 0.46/0.70            = (k10_relat_1 @ sk_C @ X0)))
% 0.46/0.70         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['54', '55'])).
% 0.46/0.70  thf('57', plain,
% 0.46/0.70      ((((k10_relat_1 @ sk_C @ sk_B_1) != (k1_xboole_0)))
% 0.46/0.70         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.70      inference('demod', [status(thm)], ['51', '56'])).
% 0.46/0.70  thf('58', plain,
% 0.46/0.70      ((((k1_relat_1 @ sk_C) != (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['46', '57'])).
% 0.46/0.70  thf('59', plain,
% 0.46/0.70      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.70      inference('split', [status(esa)], ['44'])).
% 0.46/0.70  thf('60', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.70  thf('61', plain,
% 0.46/0.70      (((v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_B_1))
% 0.46/0.70         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.70      inference('sup+', [status(thm)], ['59', '60'])).
% 0.46/0.70  thf('62', plain,
% 0.46/0.70      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.46/0.70         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 0.46/0.70          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 0.46/0.70          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.70  thf('63', plain,
% 0.46/0.70      (((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ k1_xboole_0)
% 0.46/0.70         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C))))
% 0.46/0.70         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['61', '62'])).
% 0.46/0.70  thf('64', plain,
% 0.46/0.70      (((m1_subset_1 @ sk_C @ 
% 0.46/0.70         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 0.46/0.70         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.70      inference('sup+', [status(thm)], ['52', '53'])).
% 0.46/0.70  thf('65', plain,
% 0.46/0.70      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.46/0.70         (~ (zip_tseitin_0 @ X34 @ X35)
% 0.46/0.70          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 0.46/0.70          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.46/0.70  thf('66', plain,
% 0.46/0.70      ((((zip_tseitin_1 @ sk_C @ sk_B_1 @ k1_xboole_0)
% 0.46/0.70         | ~ (zip_tseitin_0 @ sk_B_1 @ k1_xboole_0)))
% 0.46/0.70         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['64', '65'])).
% 0.46/0.70  thf('67', plain,
% 0.46/0.70      (![X29 : $i, X30 : $i]:
% 0.46/0.70         ((zip_tseitin_0 @ X29 @ X30) | ((X30) != (k1_xboole_0)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('68', plain, (![X29 : $i]: (zip_tseitin_0 @ X29 @ k1_xboole_0)),
% 0.46/0.70      inference('simplify', [status(thm)], ['67'])).
% 0.46/0.70  thf('69', plain,
% 0.46/0.70      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ k1_xboole_0))
% 0.46/0.70         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.70      inference('demod', [status(thm)], ['66', '68'])).
% 0.46/0.70  thf('70', plain,
% 0.46/0.70      (((m1_subset_1 @ sk_C @ 
% 0.46/0.70         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 0.46/0.70         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.70      inference('sup+', [status(thm)], ['52', '53'])).
% 0.46/0.70  thf('71', plain,
% 0.46/0.70      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.46/0.70         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 0.46/0.70          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.46/0.70      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.46/0.70  thf('72', plain,
% 0.46/0.70      ((((k1_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C) = (k1_relat_1 @ sk_C)))
% 0.46/0.70         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['70', '71'])).
% 0.46/0.70  thf('73', plain,
% 0.46/0.70      ((((k1_xboole_0) = (k1_relat_1 @ sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.70      inference('demod', [status(thm)], ['63', '69', '72'])).
% 0.46/0.70  thf('74', plain,
% 0.46/0.70      ((((k1_xboole_0) != (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.70      inference('demod', [status(thm)], ['58', '73'])).
% 0.46/0.70  thf('75', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.46/0.70      inference('simplify', [status(thm)], ['74'])).
% 0.46/0.70  thf('76', plain,
% 0.46/0.70      (~ (((sk_B_1) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.46/0.70      inference('split', [status(esa)], ['44'])).
% 0.46/0.70  thf('77', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.46/0.70      inference('sat_resolution*', [status(thm)], ['75', '76'])).
% 0.46/0.70  thf('78', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.46/0.70      inference('simpl_trail', [status(thm)], ['45', '77'])).
% 0.46/0.70  thf('79', plain, ($false),
% 0.46/0.70      inference('simplify_reflect-', [status(thm)], ['43', '78'])).
% 0.46/0.70  
% 0.46/0.70  % SZS output end Refutation
% 0.46/0.70  
% 0.55/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
