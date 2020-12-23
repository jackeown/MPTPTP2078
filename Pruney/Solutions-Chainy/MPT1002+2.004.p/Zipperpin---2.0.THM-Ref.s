%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KG20MpyiBp

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:00 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 164 expanded)
%              Number of leaves         :   32 (  61 expanded)
%              Depth                    :   15
%              Number of atoms          :  730 (2323 expanded)
%              Number of equality atoms :   68 ( 177 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t50_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ C @ A )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( r1_tarski @ C @ ( k8_relset_1 @ A @ B @ D @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r1_tarski @ C @ A )
         => ( ( ( B = k1_xboole_0 )
              & ( A != k1_xboole_0 ) )
            | ( r1_tarski @ C @ ( k8_relset_1 @ A @ B @ D @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_C @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ( ( k7_relset_1 @ X9 @ X10 @ X8 @ X11 )
        = ( k9_relat_1 @ X8 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ sk_C @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D @ ( k9_relat_1 @ sk_D @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( ( k8_relset_1 @ X13 @ X14 @ X12 @ X15 )
        = ( k10_relat_1 @ X12 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k10_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_D @ ( k9_relat_1 @ sk_D @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,(
    r1_tarski @ sk_C @ sk_A ),
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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('12',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( zip_tseitin_0 @ X21 @ X22 )
      | ( zip_tseitin_1 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('13',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ( X18
        = ( k1_relset_1 @ X18 @ X19 @ X20 ) )
      | ~ ( zip_tseitin_1 @ X20 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('17',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('19',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k1_relset_1 @ X6 @ X7 @ X5 )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('20',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( r1_tarski @ X0 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ( r1_tarski @ X0 @ ( k10_relat_1 @ sk_D @ ( k9_relat_1 @ sk_D @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('26',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('27',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k10_relat_1 @ sk_D @ ( k9_relat_1 @ sk_D @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,
    ( ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_D @ ( k9_relat_1 @ sk_D @ sk_C ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','28'])).

thf('30',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('32',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('33',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('36',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ( X18
        = ( k1_relset_1 @ X18 @ X19 @ X20 ) )
      | ~ ( zip_tseitin_1 @ X20 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('39',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('41',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( zip_tseitin_0 @ X21 @ X22 )
      | ( zip_tseitin_1 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('44',plain,
    ( ( ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 )
      | ( X17 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('46',plain,(
    ! [X16: $i] :
      ( zip_tseitin_0 @ X16 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','46'])).

thf('48',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('49',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k1_relset_1 @ X6 @ X7 @ X5 )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('50',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D )
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','47','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( r1_tarski @ X0 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
        | ~ ( v1_relat_1 @ sk_D )
        | ( r1_tarski @ X0 @ ( k10_relat_1 @ sk_D @ ( k9_relat_1 @ sk_D @ X0 ) ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['25','26'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
        | ( r1_tarski @ X0 @ ( k10_relat_1 @ sk_D @ ( k9_relat_1 @ sk_D @ X0 ) ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_D @ ( k9_relat_1 @ sk_D @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','55'])).

thf('57',plain,(
    ~ ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_D @ ( k9_relat_1 @ sk_D @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('58',plain,(
    sk_A != k1_xboole_0 ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('60',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['58','59'])).

thf('61',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['31','60'])).

thf('62',plain,(
    r1_tarski @ sk_C @ ( k10_relat_1 @ sk_D @ ( k9_relat_1 @ sk_D @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['29','61'])).

thf('63',plain,(
    $false ),
    inference(demod,[status(thm)],['8','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KG20MpyiBp
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:03:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.35/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.57  % Solved by: fo/fo7.sh
% 0.35/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.57  % done 139 iterations in 0.109s
% 0.35/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.57  % SZS output start Refutation
% 0.35/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.35/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.35/0.57  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.35/0.57  thf(sk_D_type, type, sk_D: $i).
% 0.35/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.57  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.35/0.57  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.35/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.35/0.57  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.35/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.57  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.35/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.57  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.35/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.57  thf(t50_funct_2, conjecture,
% 0.35/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.57     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.35/0.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.57       ( ( r1_tarski @ C @ A ) =>
% 0.35/0.57         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.35/0.57           ( r1_tarski @
% 0.35/0.57             C @ ( k8_relset_1 @ A @ B @ D @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ))).
% 0.35/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.57    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.57        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.35/0.57            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.57          ( ( r1_tarski @ C @ A ) =>
% 0.35/0.57            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.35/0.57              ( r1_tarski @
% 0.35/0.57                C @ 
% 0.35/0.57                ( k8_relset_1 @ A @ B @ D @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ) )),
% 0.35/0.57    inference('cnf.neg', [status(esa)], [t50_funct_2])).
% 0.35/0.57  thf('0', plain,
% 0.35/0.57      (~ (r1_tarski @ sk_C @ 
% 0.35/0.57          (k8_relset_1 @ sk_A @ sk_B @ sk_D @ 
% 0.35/0.57           (k7_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('1', plain,
% 0.35/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf(redefinition_k7_relset_1, axiom,
% 0.35/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.57       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.35/0.57  thf('2', plain,
% 0.35/0.57      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.35/0.57         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.35/0.57          | ((k7_relset_1 @ X9 @ X10 @ X8 @ X11) = (k9_relat_1 @ X8 @ X11)))),
% 0.35/0.57      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.35/0.57  thf('3', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         ((k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0) = (k9_relat_1 @ sk_D @ X0))),
% 0.35/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.35/0.57  thf('4', plain,
% 0.35/0.57      (~ (r1_tarski @ sk_C @ 
% 0.35/0.57          (k8_relset_1 @ sk_A @ sk_B @ sk_D @ (k9_relat_1 @ sk_D @ sk_C)))),
% 0.35/0.57      inference('demod', [status(thm)], ['0', '3'])).
% 0.35/0.57  thf('5', plain,
% 0.35/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf(redefinition_k8_relset_1, axiom,
% 0.35/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.57       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.35/0.57  thf('6', plain,
% 0.35/0.57      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.35/0.57         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.35/0.57          | ((k8_relset_1 @ X13 @ X14 @ X12 @ X15) = (k10_relat_1 @ X12 @ X15)))),
% 0.35/0.57      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.35/0.57  thf('7', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         ((k8_relset_1 @ sk_A @ sk_B @ sk_D @ X0) = (k10_relat_1 @ sk_D @ X0))),
% 0.35/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.35/0.57  thf('8', plain,
% 0.35/0.57      (~ (r1_tarski @ sk_C @ (k10_relat_1 @ sk_D @ (k9_relat_1 @ sk_D @ sk_C)))),
% 0.35/0.57      inference('demod', [status(thm)], ['4', '7'])).
% 0.35/0.57  thf('9', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf(d1_funct_2, axiom,
% 0.35/0.57    (![A:$i,B:$i,C:$i]:
% 0.35/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.57       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.35/0.57           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.35/0.57             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.35/0.57         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.35/0.57           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.35/0.57             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.35/0.57  thf(zf_stmt_1, axiom,
% 0.35/0.57    (![B:$i,A:$i]:
% 0.35/0.57     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.35/0.57       ( zip_tseitin_0 @ B @ A ) ))).
% 0.35/0.57  thf('10', plain,
% 0.35/0.57      (![X16 : $i, X17 : $i]:
% 0.35/0.57         ((zip_tseitin_0 @ X16 @ X17) | ((X16) = (k1_xboole_0)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.35/0.57  thf('11', plain,
% 0.35/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.35/0.57  thf(zf_stmt_3, axiom,
% 0.35/0.57    (![C:$i,B:$i,A:$i]:
% 0.35/0.57     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.35/0.57       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.35/0.57  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.35/0.57  thf(zf_stmt_5, axiom,
% 0.35/0.57    (![A:$i,B:$i,C:$i]:
% 0.35/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.57       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.35/0.57         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.35/0.57           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.35/0.57             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.35/0.57  thf('12', plain,
% 0.35/0.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.35/0.57         (~ (zip_tseitin_0 @ X21 @ X22)
% 0.35/0.57          | (zip_tseitin_1 @ X23 @ X21 @ X22)
% 0.35/0.57          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21))))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.35/0.57  thf('13', plain,
% 0.35/0.57      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.35/0.57      inference('sup-', [status(thm)], ['11', '12'])).
% 0.35/0.57  thf('14', plain,
% 0.35/0.57      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.35/0.57      inference('sup-', [status(thm)], ['10', '13'])).
% 0.35/0.57  thf('15', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('16', plain,
% 0.35/0.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.35/0.57         (~ (v1_funct_2 @ X20 @ X18 @ X19)
% 0.35/0.57          | ((X18) = (k1_relset_1 @ X18 @ X19 @ X20))
% 0.35/0.57          | ~ (zip_tseitin_1 @ X20 @ X19 @ X18))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.35/0.57  thf('17', plain,
% 0.35/0.57      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.35/0.57        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.35/0.57      inference('sup-', [status(thm)], ['15', '16'])).
% 0.35/0.57  thf('18', plain,
% 0.35/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf(redefinition_k1_relset_1, axiom,
% 0.35/0.57    (![A:$i,B:$i,C:$i]:
% 0.35/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.57       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.35/0.57  thf('19', plain,
% 0.35/0.57      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.35/0.57         (((k1_relset_1 @ X6 @ X7 @ X5) = (k1_relat_1 @ X5))
% 0.35/0.57          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.35/0.57      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.35/0.57  thf('20', plain,
% 0.35/0.57      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.35/0.57      inference('sup-', [status(thm)], ['18', '19'])).
% 0.35/0.57  thf('21', plain,
% 0.35/0.57      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.35/0.57      inference('demod', [status(thm)], ['17', '20'])).
% 0.35/0.57  thf('22', plain,
% 0.35/0.57      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.35/0.57      inference('sup-', [status(thm)], ['14', '21'])).
% 0.35/0.57  thf(t146_funct_1, axiom,
% 0.35/0.57    (![A:$i,B:$i]:
% 0.35/0.57     ( ( v1_relat_1 @ B ) =>
% 0.35/0.57       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.35/0.57         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.35/0.57  thf('23', plain,
% 0.35/0.57      (![X0 : $i, X1 : $i]:
% 0.35/0.57         (~ (r1_tarski @ X0 @ (k1_relat_1 @ X1))
% 0.35/0.57          | (r1_tarski @ X0 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)))
% 0.35/0.57          | ~ (v1_relat_1 @ X1))),
% 0.35/0.57      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.35/0.57  thf('24', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         (~ (r1_tarski @ X0 @ sk_A)
% 0.35/0.57          | ((sk_B) = (k1_xboole_0))
% 0.35/0.57          | ~ (v1_relat_1 @ sk_D)
% 0.35/0.57          | (r1_tarski @ X0 @ (k10_relat_1 @ sk_D @ (k9_relat_1 @ sk_D @ X0))))),
% 0.35/0.57      inference('sup-', [status(thm)], ['22', '23'])).
% 0.35/0.57  thf('25', plain,
% 0.35/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf(cc1_relset_1, axiom,
% 0.35/0.57    (![A:$i,B:$i,C:$i]:
% 0.35/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.57       ( v1_relat_1 @ C ) ))).
% 0.35/0.57  thf('26', plain,
% 0.35/0.57      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.35/0.57         ((v1_relat_1 @ X2)
% 0.35/0.57          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.35/0.57      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.35/0.57  thf('27', plain, ((v1_relat_1 @ sk_D)),
% 0.35/0.57      inference('sup-', [status(thm)], ['25', '26'])).
% 0.35/0.57  thf('28', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         (~ (r1_tarski @ X0 @ sk_A)
% 0.35/0.57          | ((sk_B) = (k1_xboole_0))
% 0.35/0.57          | (r1_tarski @ X0 @ (k10_relat_1 @ sk_D @ (k9_relat_1 @ sk_D @ X0))))),
% 0.35/0.57      inference('demod', [status(thm)], ['24', '27'])).
% 0.35/0.57  thf('29', plain,
% 0.35/0.57      (((r1_tarski @ sk_C @ (k10_relat_1 @ sk_D @ (k9_relat_1 @ sk_D @ sk_C)))
% 0.35/0.57        | ((sk_B) = (k1_xboole_0)))),
% 0.35/0.57      inference('sup-', [status(thm)], ['9', '28'])).
% 0.35/0.57  thf('30', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('31', plain,
% 0.35/0.57      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.35/0.57      inference('split', [status(esa)], ['30'])).
% 0.35/0.57  thf('32', plain,
% 0.35/0.57      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('split', [status(esa)], ['30'])).
% 0.35/0.57  thf('33', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('34', plain,
% 0.35/0.57      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('sup+', [status(thm)], ['32', '33'])).
% 0.35/0.57  thf('35', plain,
% 0.35/0.57      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('split', [status(esa)], ['30'])).
% 0.35/0.57  thf('36', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('37', plain,
% 0.35/0.57      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B))
% 0.35/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('sup+', [status(thm)], ['35', '36'])).
% 0.35/0.57  thf('38', plain,
% 0.35/0.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.35/0.57         (~ (v1_funct_2 @ X20 @ X18 @ X19)
% 0.35/0.57          | ((X18) = (k1_relset_1 @ X18 @ X19 @ X20))
% 0.35/0.57          | ~ (zip_tseitin_1 @ X20 @ X19 @ X18))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.35/0.57  thf('39', plain,
% 0.35/0.57      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 0.35/0.57         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D))))
% 0.35/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('sup-', [status(thm)], ['37', '38'])).
% 0.35/0.57  thf('40', plain,
% 0.35/0.57      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('split', [status(esa)], ['30'])).
% 0.35/0.57  thf('41', plain,
% 0.35/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('42', plain,
% 0.35/0.57      (((m1_subset_1 @ sk_D @ 
% 0.35/0.57         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.35/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('sup+', [status(thm)], ['40', '41'])).
% 0.35/0.57  thf('43', plain,
% 0.35/0.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.35/0.57         (~ (zip_tseitin_0 @ X21 @ X22)
% 0.35/0.57          | (zip_tseitin_1 @ X23 @ X21 @ X22)
% 0.35/0.57          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21))))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.35/0.57  thf('44', plain,
% 0.35/0.57      ((((zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 0.35/0.57         | ~ (zip_tseitin_0 @ sk_B @ k1_xboole_0)))
% 0.35/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('sup-', [status(thm)], ['42', '43'])).
% 0.35/0.57  thf('45', plain,
% 0.35/0.57      (![X16 : $i, X17 : $i]:
% 0.35/0.57         ((zip_tseitin_0 @ X16 @ X17) | ((X17) != (k1_xboole_0)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.35/0.57  thf('46', plain, (![X16 : $i]: (zip_tseitin_0 @ X16 @ k1_xboole_0)),
% 0.35/0.57      inference('simplify', [status(thm)], ['45'])).
% 0.35/0.57  thf('47', plain,
% 0.35/0.57      (((zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0))
% 0.35/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('demod', [status(thm)], ['44', '46'])).
% 0.35/0.57  thf('48', plain,
% 0.35/0.57      (((m1_subset_1 @ sk_D @ 
% 0.35/0.57         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.35/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('sup+', [status(thm)], ['40', '41'])).
% 0.35/0.57  thf('49', plain,
% 0.35/0.57      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.35/0.57         (((k1_relset_1 @ X6 @ X7 @ X5) = (k1_relat_1 @ X5))
% 0.35/0.57          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.35/0.57      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.35/0.57  thf('50', plain,
% 0.35/0.57      ((((k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D) = (k1_relat_1 @ sk_D)))
% 0.35/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('sup-', [status(thm)], ['48', '49'])).
% 0.35/0.57  thf('51', plain,
% 0.35/0.57      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('demod', [status(thm)], ['39', '47', '50'])).
% 0.35/0.57  thf('52', plain,
% 0.35/0.57      (![X0 : $i, X1 : $i]:
% 0.35/0.57         (~ (r1_tarski @ X0 @ (k1_relat_1 @ X1))
% 0.35/0.57          | (r1_tarski @ X0 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)))
% 0.35/0.57          | ~ (v1_relat_1 @ X1))),
% 0.35/0.57      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.35/0.57  thf('53', plain,
% 0.35/0.57      ((![X0 : $i]:
% 0.35/0.57          (~ (r1_tarski @ X0 @ k1_xboole_0)
% 0.35/0.57           | ~ (v1_relat_1 @ sk_D)
% 0.35/0.57           | (r1_tarski @ X0 @ (k10_relat_1 @ sk_D @ (k9_relat_1 @ sk_D @ X0)))))
% 0.35/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('sup-', [status(thm)], ['51', '52'])).
% 0.35/0.57  thf('54', plain, ((v1_relat_1 @ sk_D)),
% 0.35/0.57      inference('sup-', [status(thm)], ['25', '26'])).
% 0.35/0.57  thf('55', plain,
% 0.35/0.57      ((![X0 : $i]:
% 0.35/0.57          (~ (r1_tarski @ X0 @ k1_xboole_0)
% 0.35/0.57           | (r1_tarski @ X0 @ (k10_relat_1 @ sk_D @ (k9_relat_1 @ sk_D @ X0)))))
% 0.35/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('demod', [status(thm)], ['53', '54'])).
% 0.35/0.57  thf('56', plain,
% 0.35/0.57      (((r1_tarski @ sk_C @ (k10_relat_1 @ sk_D @ (k9_relat_1 @ sk_D @ sk_C))))
% 0.35/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('sup-', [status(thm)], ['34', '55'])).
% 0.35/0.57  thf('57', plain,
% 0.35/0.57      (~ (r1_tarski @ sk_C @ (k10_relat_1 @ sk_D @ (k9_relat_1 @ sk_D @ sk_C)))),
% 0.35/0.57      inference('demod', [status(thm)], ['4', '7'])).
% 0.35/0.57  thf('58', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.35/0.57      inference('sup-', [status(thm)], ['56', '57'])).
% 0.35/0.57  thf('59', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.35/0.57      inference('split', [status(esa)], ['30'])).
% 0.35/0.57  thf('60', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.35/0.57      inference('sat_resolution*', [status(thm)], ['58', '59'])).
% 0.35/0.57  thf('61', plain, (((sk_B) != (k1_xboole_0))),
% 0.35/0.57      inference('simpl_trail', [status(thm)], ['31', '60'])).
% 0.35/0.57  thf('62', plain,
% 0.35/0.57      ((r1_tarski @ sk_C @ (k10_relat_1 @ sk_D @ (k9_relat_1 @ sk_D @ sk_C)))),
% 0.35/0.57      inference('simplify_reflect-', [status(thm)], ['29', '61'])).
% 0.35/0.57  thf('63', plain, ($false), inference('demod', [status(thm)], ['8', '62'])).
% 0.35/0.57  
% 0.35/0.57  % SZS output end Refutation
% 0.35/0.57  
% 0.35/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
