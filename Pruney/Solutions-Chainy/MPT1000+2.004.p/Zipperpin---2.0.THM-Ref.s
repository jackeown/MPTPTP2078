%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DC07AgCJdS

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:58 EST 2020

% Result     : Theorem 3.98s
% Output     : Refutation 3.98s
% Verified   : 
% Statistics : Number of formulae       :  198 ( 467 expanded)
%              Number of leaves         :   51 ( 161 expanded)
%              Depth                    :   28
%              Number of atoms          : 1204 (3500 expanded)
%              Number of equality atoms :  127 ( 356 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t48_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( k8_relset_1 @ A @ B @ C @ B )
          = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( k8_relset_1 @ A @ B @ C @ B )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_funct_2])).

thf('0',plain,(
    ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_B_1 )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( ( k8_relset_1 @ X38 @ X39 @ X37 @ X40 )
        = ( k10_relat_1 @ X37 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ X0 )
      = ( k10_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ( k10_relat_1 @ sk_C_1 @ sk_B_1 )
 != sk_A ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v5_relat_1 @ X31 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('7',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('8',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v5_relat_1 @ X19 @ X20 )
      | ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('13',plain,(
    ! [X23: $i,X24: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('14',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['9','14'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('16',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X29 ) @ X30 )
      | ( ( k5_relat_1 @ X29 @ ( k6_relat_1 @ X30 ) )
        = X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B_1 ) )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('19',plain,
    ( ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B_1 ) )
    = sk_C_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('20',plain,(
    ! [X27: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('21',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X26 @ X25 ) )
        = ( k10_relat_1 @ X26 @ ( k1_relat_1 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('23',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = ( k10_relat_1 @ sk_C_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['19','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('27',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k10_relat_1 @ sk_C_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ( k1_relat_1 @ sk_C_1 )
 != sk_A ),
    inference(demod,[status(thm)],['4','27'])).

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

thf('29',plain,(
    ! [X41: $i,X42: $i] :
      ( ( zip_tseitin_0 @ X41 @ X42 )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('30',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('33',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( zip_tseitin_0 @ X46 @ X47 )
      | ( zip_tseitin_1 @ X48 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('34',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_2 @ X45 @ X43 @ X44 )
      | ( X43
        = ( k1_relset_1 @ X43 @ X44 @ X45 ) )
      | ~ ( zip_tseitin_1 @ X45 @ X44 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('38',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('40',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k1_relset_1 @ X35 @ X36 @ X34 )
        = ( k1_relat_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('41',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['35','42'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('44',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('45',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_B_1 = X0 ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('50',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('51',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['50'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('52',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('53',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('54',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_zfmisc_1 @ X12 @ X13 )
        = k1_xboole_0 )
      | ( X13 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('55',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v5_relat_1 @ X31 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('57',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v5_relat_1 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','57'])).

thf('59',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v5_relat_1 @ X19 @ X20 )
      | ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('60',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_zfmisc_1 @ X12 @ X13 )
        = k1_xboole_0 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('62',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X13 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X23: $i,X24: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('64',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['60','64'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('66',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','70'])).

thf('72',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('73',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X29 ) @ X30 )
      | ( ( k5_relat_1 @ X29 @ ( k6_relat_1 @ X30 ) )
        = X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ ( k6_relat_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['62','63'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ ( k6_relat_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('79',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['71','72'])).

thf('80',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ( v5_relat_1 @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v5_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['62','63'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( v5_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v5_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','83'])).

thf('85',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v5_relat_1 @ X19 @ X20 )
      | ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['62','63'])).

thf('90',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['71','72'])).

thf('91',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ k1_xboole_0 @ ( k6_relat_1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ k1_xboole_0 )
        = ( k10_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(fc10_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('96',plain,(
    ! [X22: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X22 ) )
      | ~ ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf('97',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['62','63'])).

thf('101',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['94','99','100'])).

thf('102',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('104',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('105',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( ( k8_relset_1 @ X38 @ X39 @ X37 @ X40 )
        = ( k10_relat_1 @ X37 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = ( k10_relat_1 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('109',plain,(
    ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_B_1 )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_1 @ sk_B_1 )
     != sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('112',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_1 @ sk_B_1 )
     != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('114',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X13 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('115',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('116',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['114','117'])).

thf('119',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('120',plain,
    ( ( r1_tarski @ sk_C_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('122',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_C_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( r2_hidden @ ( sk_B @ sk_C_1 ) @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['113','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('125',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('127',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('129',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0 @ sk_B_1 )
     != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['112','129'])).

thf('131',plain,
    ( ( ( k10_relat_1 @ k1_xboole_0 @ sk_B_1 )
     != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['107','130'])).

thf('132',plain,
    ( ! [X0: $i] :
        ( ( ( k10_relat_1 @ X0 @ sk_B_1 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['102','131'])).

thf('133',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['101','132'])).

thf('134',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('135',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    sk_A != k1_xboole_0 ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('138',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['136','137'])).

thf('139',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['49','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['47','139'])).

thf('141',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('143',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('simplify_reflect+',[status(thm)],['141','142'])).

thf('144',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['28','143'])).

thf('145',plain,(
    $false ),
    inference(simplify,[status(thm)],['144'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DC07AgCJdS
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:46:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 3.98/4.21  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.98/4.21  % Solved by: fo/fo7.sh
% 3.98/4.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.98/4.21  % done 4370 iterations in 3.757s
% 3.98/4.21  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.98/4.21  % SZS output start Refutation
% 3.98/4.21  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.98/4.21  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.98/4.21  thf(sk_A_type, type, sk_A: $i).
% 3.98/4.21  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.98/4.21  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.98/4.21  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.98/4.21  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.98/4.21  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.98/4.21  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.98/4.21  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.98/4.21  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.98/4.21  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.98/4.21  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 3.98/4.21  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.98/4.21  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.98/4.21  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.98/4.21  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.98/4.21  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.98/4.21  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.98/4.21  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.98/4.21  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.98/4.21  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.98/4.21  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.98/4.21  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 3.98/4.21  thf(sk_B_type, type, sk_B: $i > $i).
% 3.98/4.21  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.98/4.21  thf(t48_funct_2, conjecture,
% 3.98/4.21    (![A:$i,B:$i,C:$i]:
% 3.98/4.21     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.98/4.21         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.98/4.21       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.98/4.21         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( A ) ) ) ))).
% 3.98/4.21  thf(zf_stmt_0, negated_conjecture,
% 3.98/4.21    (~( ![A:$i,B:$i,C:$i]:
% 3.98/4.21        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.98/4.21            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.98/4.21          ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.98/4.21            ( ( k8_relset_1 @ A @ B @ C @ B ) = ( A ) ) ) ) )),
% 3.98/4.21    inference('cnf.neg', [status(esa)], [t48_funct_2])).
% 3.98/4.21  thf('0', plain,
% 3.98/4.21      (((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_B_1) != (sk_A))),
% 3.98/4.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.98/4.21  thf('1', plain,
% 3.98/4.21      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.98/4.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.98/4.21  thf(redefinition_k8_relset_1, axiom,
% 3.98/4.21    (![A:$i,B:$i,C:$i,D:$i]:
% 3.98/4.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.98/4.21       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 3.98/4.21  thf('2', plain,
% 3.98/4.21      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 3.98/4.21         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 3.98/4.21          | ((k8_relset_1 @ X38 @ X39 @ X37 @ X40) = (k10_relat_1 @ X37 @ X40)))),
% 3.98/4.21      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 3.98/4.21  thf('3', plain,
% 3.98/4.21      (![X0 : $i]:
% 3.98/4.21         ((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ X0)
% 3.98/4.21           = (k10_relat_1 @ sk_C_1 @ X0))),
% 3.98/4.21      inference('sup-', [status(thm)], ['1', '2'])).
% 3.98/4.21  thf('4', plain, (((k10_relat_1 @ sk_C_1 @ sk_B_1) != (sk_A))),
% 3.98/4.21      inference('demod', [status(thm)], ['0', '3'])).
% 3.98/4.21  thf('5', plain,
% 3.98/4.21      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.98/4.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.98/4.21  thf(cc2_relset_1, axiom,
% 3.98/4.21    (![A:$i,B:$i,C:$i]:
% 3.98/4.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.98/4.21       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.98/4.21  thf('6', plain,
% 3.98/4.21      (![X31 : $i, X32 : $i, X33 : $i]:
% 3.98/4.21         ((v5_relat_1 @ X31 @ X33)
% 3.98/4.21          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 3.98/4.21      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.98/4.21  thf('7', plain, ((v5_relat_1 @ sk_C_1 @ sk_B_1)),
% 3.98/4.21      inference('sup-', [status(thm)], ['5', '6'])).
% 3.98/4.21  thf(d19_relat_1, axiom,
% 3.98/4.21    (![A:$i,B:$i]:
% 3.98/4.21     ( ( v1_relat_1 @ B ) =>
% 3.98/4.21       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 3.98/4.21  thf('8', plain,
% 3.98/4.21      (![X19 : $i, X20 : $i]:
% 3.98/4.21         (~ (v5_relat_1 @ X19 @ X20)
% 3.98/4.21          | (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 3.98/4.21          | ~ (v1_relat_1 @ X19))),
% 3.98/4.21      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.98/4.21  thf('9', plain,
% 3.98/4.21      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))),
% 3.98/4.21      inference('sup-', [status(thm)], ['7', '8'])).
% 3.98/4.21  thf('10', plain,
% 3.98/4.21      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.98/4.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.98/4.21  thf(cc2_relat_1, axiom,
% 3.98/4.21    (![A:$i]:
% 3.98/4.21     ( ( v1_relat_1 @ A ) =>
% 3.98/4.21       ( ![B:$i]:
% 3.98/4.21         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 3.98/4.21  thf('11', plain,
% 3.98/4.21      (![X17 : $i, X18 : $i]:
% 3.98/4.21         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 3.98/4.21          | (v1_relat_1 @ X17)
% 3.98/4.21          | ~ (v1_relat_1 @ X18))),
% 3.98/4.21      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.98/4.21  thf('12', plain,
% 3.98/4.21      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_C_1))),
% 3.98/4.21      inference('sup-', [status(thm)], ['10', '11'])).
% 3.98/4.21  thf(fc6_relat_1, axiom,
% 3.98/4.21    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 3.98/4.21  thf('13', plain,
% 3.98/4.21      (![X23 : $i, X24 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X23 @ X24))),
% 3.98/4.21      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.98/4.21  thf('14', plain, ((v1_relat_1 @ sk_C_1)),
% 3.98/4.21      inference('demod', [status(thm)], ['12', '13'])).
% 3.98/4.21  thf('15', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)),
% 3.98/4.21      inference('demod', [status(thm)], ['9', '14'])).
% 3.98/4.21  thf(t79_relat_1, axiom,
% 3.98/4.21    (![A:$i,B:$i]:
% 3.98/4.21     ( ( v1_relat_1 @ B ) =>
% 3.98/4.21       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 3.98/4.21         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 3.98/4.21  thf('16', plain,
% 3.98/4.21      (![X29 : $i, X30 : $i]:
% 3.98/4.21         (~ (r1_tarski @ (k2_relat_1 @ X29) @ X30)
% 3.98/4.21          | ((k5_relat_1 @ X29 @ (k6_relat_1 @ X30)) = (X29))
% 3.98/4.21          | ~ (v1_relat_1 @ X29))),
% 3.98/4.21      inference('cnf', [status(esa)], [t79_relat_1])).
% 3.98/4.21  thf('17', plain,
% 3.98/4.21      ((~ (v1_relat_1 @ sk_C_1)
% 3.98/4.21        | ((k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B_1)) = (sk_C_1)))),
% 3.98/4.21      inference('sup-', [status(thm)], ['15', '16'])).
% 3.98/4.21  thf('18', plain, ((v1_relat_1 @ sk_C_1)),
% 3.98/4.21      inference('demod', [status(thm)], ['12', '13'])).
% 3.98/4.21  thf('19', plain,
% 3.98/4.21      (((k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B_1)) = (sk_C_1))),
% 3.98/4.21      inference('demod', [status(thm)], ['17', '18'])).
% 3.98/4.21  thf(t71_relat_1, axiom,
% 3.98/4.21    (![A:$i]:
% 3.98/4.21     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 3.98/4.21       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 3.98/4.21  thf('20', plain, (![X27 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 3.98/4.21      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.98/4.21  thf(t182_relat_1, axiom,
% 3.98/4.21    (![A:$i]:
% 3.98/4.21     ( ( v1_relat_1 @ A ) =>
% 3.98/4.21       ( ![B:$i]:
% 3.98/4.21         ( ( v1_relat_1 @ B ) =>
% 3.98/4.21           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 3.98/4.21             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 3.98/4.21  thf('21', plain,
% 3.98/4.21      (![X25 : $i, X26 : $i]:
% 3.98/4.21         (~ (v1_relat_1 @ X25)
% 3.98/4.21          | ((k1_relat_1 @ (k5_relat_1 @ X26 @ X25))
% 3.98/4.21              = (k10_relat_1 @ X26 @ (k1_relat_1 @ X25)))
% 3.98/4.21          | ~ (v1_relat_1 @ X26))),
% 3.98/4.21      inference('cnf', [status(esa)], [t182_relat_1])).
% 3.98/4.21  thf('22', plain,
% 3.98/4.21      (![X0 : $i, X1 : $i]:
% 3.98/4.21         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 3.98/4.21            = (k10_relat_1 @ X1 @ X0))
% 3.98/4.21          | ~ (v1_relat_1 @ X1)
% 3.98/4.21          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 3.98/4.21      inference('sup+', [status(thm)], ['20', '21'])).
% 3.98/4.21  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 3.98/4.21  thf('23', plain, (![X21 : $i]: (v1_relat_1 @ (k6_relat_1 @ X21))),
% 3.98/4.21      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.98/4.21  thf('24', plain,
% 3.98/4.21      (![X0 : $i, X1 : $i]:
% 3.98/4.21         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 3.98/4.21            = (k10_relat_1 @ X1 @ X0))
% 3.98/4.21          | ~ (v1_relat_1 @ X1))),
% 3.98/4.21      inference('demod', [status(thm)], ['22', '23'])).
% 3.98/4.21  thf('25', plain,
% 3.98/4.21      ((((k1_relat_1 @ sk_C_1) = (k10_relat_1 @ sk_C_1 @ sk_B_1))
% 3.98/4.21        | ~ (v1_relat_1 @ sk_C_1))),
% 3.98/4.21      inference('sup+', [status(thm)], ['19', '24'])).
% 3.98/4.21  thf('26', plain, ((v1_relat_1 @ sk_C_1)),
% 3.98/4.21      inference('demod', [status(thm)], ['12', '13'])).
% 3.98/4.21  thf('27', plain, (((k1_relat_1 @ sk_C_1) = (k10_relat_1 @ sk_C_1 @ sk_B_1))),
% 3.98/4.21      inference('demod', [status(thm)], ['25', '26'])).
% 3.98/4.21  thf('28', plain, (((k1_relat_1 @ sk_C_1) != (sk_A))),
% 3.98/4.21      inference('demod', [status(thm)], ['4', '27'])).
% 3.98/4.21  thf(d1_funct_2, axiom,
% 3.98/4.21    (![A:$i,B:$i,C:$i]:
% 3.98/4.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.98/4.21       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.98/4.21           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.98/4.21             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.98/4.21         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.98/4.21           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.98/4.21             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.98/4.21  thf(zf_stmt_1, axiom,
% 3.98/4.21    (![B:$i,A:$i]:
% 3.98/4.21     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.98/4.21       ( zip_tseitin_0 @ B @ A ) ))).
% 3.98/4.21  thf('29', plain,
% 3.98/4.21      (![X41 : $i, X42 : $i]:
% 3.98/4.21         ((zip_tseitin_0 @ X41 @ X42) | ((X41) = (k1_xboole_0)))),
% 3.98/4.21      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.98/4.21  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.98/4.21  thf('30', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.98/4.21      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.98/4.21  thf('31', plain,
% 3.98/4.21      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 3.98/4.21      inference('sup+', [status(thm)], ['29', '30'])).
% 3.98/4.21  thf('32', plain,
% 3.98/4.21      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.98/4.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.98/4.21  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.98/4.21  thf(zf_stmt_3, axiom,
% 3.98/4.21    (![C:$i,B:$i,A:$i]:
% 3.98/4.21     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.98/4.21       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.98/4.21  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 3.98/4.21  thf(zf_stmt_5, axiom,
% 3.98/4.21    (![A:$i,B:$i,C:$i]:
% 3.98/4.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.98/4.21       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.98/4.21         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.98/4.21           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.98/4.21             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.98/4.21  thf('33', plain,
% 3.98/4.21      (![X46 : $i, X47 : $i, X48 : $i]:
% 3.98/4.21         (~ (zip_tseitin_0 @ X46 @ X47)
% 3.98/4.21          | (zip_tseitin_1 @ X48 @ X46 @ X47)
% 3.98/4.21          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46))))),
% 3.98/4.21      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.98/4.21  thf('34', plain,
% 3.98/4.21      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 3.98/4.21        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 3.98/4.21      inference('sup-', [status(thm)], ['32', '33'])).
% 3.98/4.21  thf('35', plain,
% 3.98/4.21      (((v1_xboole_0 @ sk_B_1) | (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A))),
% 3.98/4.21      inference('sup-', [status(thm)], ['31', '34'])).
% 3.98/4.21  thf('36', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 3.98/4.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.98/4.21  thf('37', plain,
% 3.98/4.21      (![X43 : $i, X44 : $i, X45 : $i]:
% 3.98/4.21         (~ (v1_funct_2 @ X45 @ X43 @ X44)
% 3.98/4.21          | ((X43) = (k1_relset_1 @ X43 @ X44 @ X45))
% 3.98/4.21          | ~ (zip_tseitin_1 @ X45 @ X44 @ X43))),
% 3.98/4.21      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.98/4.21  thf('38', plain,
% 3.98/4.21      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 3.98/4.21        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 3.98/4.21      inference('sup-', [status(thm)], ['36', '37'])).
% 3.98/4.21  thf('39', plain,
% 3.98/4.21      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.98/4.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.98/4.21  thf(redefinition_k1_relset_1, axiom,
% 3.98/4.21    (![A:$i,B:$i,C:$i]:
% 3.98/4.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.98/4.21       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.98/4.21  thf('40', plain,
% 3.98/4.21      (![X34 : $i, X35 : $i, X36 : $i]:
% 3.98/4.21         (((k1_relset_1 @ X35 @ X36 @ X34) = (k1_relat_1 @ X34))
% 3.98/4.21          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 3.98/4.21      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.98/4.21  thf('41', plain,
% 3.98/4.21      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 3.98/4.21      inference('sup-', [status(thm)], ['39', '40'])).
% 3.98/4.21  thf('42', plain,
% 3.98/4.21      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 3.98/4.21        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 3.98/4.21      inference('demod', [status(thm)], ['38', '41'])).
% 3.98/4.21  thf('43', plain,
% 3.98/4.21      (((v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 3.98/4.21      inference('sup-', [status(thm)], ['35', '42'])).
% 3.98/4.21  thf(l13_xboole_0, axiom,
% 3.98/4.21    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 3.98/4.21  thf('44', plain,
% 3.98/4.21      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 3.98/4.21      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.98/4.21  thf('45', plain,
% 3.98/4.21      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 3.98/4.21      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.98/4.21  thf('46', plain,
% 3.98/4.21      (![X0 : $i, X1 : $i]:
% 3.98/4.21         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 3.98/4.21      inference('sup+', [status(thm)], ['44', '45'])).
% 3.98/4.21  thf('47', plain,
% 3.98/4.21      (![X0 : $i]:
% 3.98/4.21         (((sk_A) = (k1_relat_1 @ sk_C_1))
% 3.98/4.21          | ~ (v1_xboole_0 @ X0)
% 3.98/4.21          | ((sk_B_1) = (X0)))),
% 3.98/4.21      inference('sup-', [status(thm)], ['43', '46'])).
% 3.98/4.21  thf('48', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B_1) != (k1_xboole_0)))),
% 3.98/4.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.98/4.21  thf('49', plain,
% 3.98/4.21      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 3.98/4.21      inference('split', [status(esa)], ['48'])).
% 3.98/4.21  thf(d10_xboole_0, axiom,
% 3.98/4.21    (![A:$i,B:$i]:
% 3.98/4.21     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.98/4.21  thf('50', plain,
% 3.98/4.21      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 3.98/4.21      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.98/4.21  thf('51', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 3.98/4.21      inference('simplify', [status(thm)], ['50'])).
% 3.98/4.21  thf(t3_subset, axiom,
% 3.98/4.21    (![A:$i,B:$i]:
% 3.98/4.21     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.98/4.21  thf('52', plain,
% 3.98/4.21      (![X14 : $i, X16 : $i]:
% 3.98/4.21         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 3.98/4.21      inference('cnf', [status(esa)], [t3_subset])).
% 3.98/4.21  thf('53', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 3.98/4.21      inference('sup-', [status(thm)], ['51', '52'])).
% 3.98/4.21  thf(t113_zfmisc_1, axiom,
% 3.98/4.21    (![A:$i,B:$i]:
% 3.98/4.21     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.98/4.21       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.98/4.21  thf('54', plain,
% 3.98/4.21      (![X12 : $i, X13 : $i]:
% 3.98/4.21         (((k2_zfmisc_1 @ X12 @ X13) = (k1_xboole_0))
% 3.98/4.21          | ((X13) != (k1_xboole_0)))),
% 3.98/4.21      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.98/4.21  thf('55', plain,
% 3.98/4.21      (![X12 : $i]: ((k2_zfmisc_1 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 3.98/4.21      inference('simplify', [status(thm)], ['54'])).
% 3.98/4.21  thf('56', plain,
% 3.98/4.21      (![X31 : $i, X32 : $i, X33 : $i]:
% 3.98/4.21         ((v5_relat_1 @ X31 @ X33)
% 3.98/4.21          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 3.98/4.21      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.98/4.21  thf('57', plain,
% 3.98/4.21      (![X1 : $i]:
% 3.98/4.21         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.98/4.21          | (v5_relat_1 @ X1 @ k1_xboole_0))),
% 3.98/4.21      inference('sup-', [status(thm)], ['55', '56'])).
% 3.98/4.21  thf('58', plain, ((v5_relat_1 @ k1_xboole_0 @ k1_xboole_0)),
% 3.98/4.21      inference('sup-', [status(thm)], ['53', '57'])).
% 3.98/4.21  thf('59', plain,
% 3.98/4.21      (![X19 : $i, X20 : $i]:
% 3.98/4.21         (~ (v5_relat_1 @ X19 @ X20)
% 3.98/4.21          | (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 3.98/4.21          | ~ (v1_relat_1 @ X19))),
% 3.98/4.21      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.98/4.21  thf('60', plain,
% 3.98/4.21      ((~ (v1_relat_1 @ k1_xboole_0)
% 3.98/4.21        | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ k1_xboole_0))),
% 3.98/4.21      inference('sup-', [status(thm)], ['58', '59'])).
% 3.98/4.21  thf('61', plain,
% 3.98/4.21      (![X12 : $i, X13 : $i]:
% 3.98/4.21         (((k2_zfmisc_1 @ X12 @ X13) = (k1_xboole_0))
% 3.98/4.21          | ((X12) != (k1_xboole_0)))),
% 3.98/4.21      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.98/4.21  thf('62', plain,
% 3.98/4.21      (![X13 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X13) = (k1_xboole_0))),
% 3.98/4.21      inference('simplify', [status(thm)], ['61'])).
% 3.98/4.21  thf('63', plain,
% 3.98/4.21      (![X23 : $i, X24 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X23 @ X24))),
% 3.98/4.21      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.98/4.21  thf('64', plain, ((v1_relat_1 @ k1_xboole_0)),
% 3.98/4.21      inference('sup+', [status(thm)], ['62', '63'])).
% 3.98/4.21  thf('65', plain, ((r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 3.98/4.21      inference('demod', [status(thm)], ['60', '64'])).
% 3.98/4.21  thf(d3_tarski, axiom,
% 3.98/4.21    (![A:$i,B:$i]:
% 3.98/4.21     ( ( r1_tarski @ A @ B ) <=>
% 3.98/4.21       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 3.98/4.21  thf('66', plain,
% 3.98/4.21      (![X4 : $i, X6 : $i]:
% 3.98/4.21         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 3.98/4.21      inference('cnf', [status(esa)], [d3_tarski])).
% 3.98/4.21  thf(d1_xboole_0, axiom,
% 3.98/4.21    (![A:$i]:
% 3.98/4.21     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 3.98/4.21  thf('67', plain,
% 3.98/4.21      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.98/4.21      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.98/4.21  thf('68', plain,
% 3.98/4.21      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 3.98/4.21      inference('sup-', [status(thm)], ['66', '67'])).
% 3.98/4.21  thf('69', plain,
% 3.98/4.21      (![X8 : $i, X10 : $i]:
% 3.98/4.21         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 3.98/4.21      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.98/4.21  thf('70', plain,
% 3.98/4.21      (![X0 : $i, X1 : $i]:
% 3.98/4.21         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 3.98/4.21      inference('sup-', [status(thm)], ['68', '69'])).
% 3.98/4.21  thf('71', plain,
% 3.98/4.21      ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 3.98/4.21        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 3.98/4.21      inference('sup-', [status(thm)], ['65', '70'])).
% 3.98/4.21  thf('72', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.98/4.21      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.98/4.21  thf('73', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.98/4.21      inference('demod', [status(thm)], ['71', '72'])).
% 3.98/4.21  thf('74', plain,
% 3.98/4.21      (![X29 : $i, X30 : $i]:
% 3.98/4.21         (~ (r1_tarski @ (k2_relat_1 @ X29) @ X30)
% 3.98/4.21          | ((k5_relat_1 @ X29 @ (k6_relat_1 @ X30)) = (X29))
% 3.98/4.21          | ~ (v1_relat_1 @ X29))),
% 3.98/4.21      inference('cnf', [status(esa)], [t79_relat_1])).
% 3.98/4.21  thf('75', plain,
% 3.98/4.21      (![X0 : $i]:
% 3.98/4.21         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 3.98/4.21          | ~ (v1_relat_1 @ k1_xboole_0)
% 3.98/4.21          | ((k5_relat_1 @ k1_xboole_0 @ (k6_relat_1 @ X0)) = (k1_xboole_0)))),
% 3.98/4.21      inference('sup-', [status(thm)], ['73', '74'])).
% 3.98/4.21  thf('76', plain, ((v1_relat_1 @ k1_xboole_0)),
% 3.98/4.21      inference('sup+', [status(thm)], ['62', '63'])).
% 3.98/4.21  thf('77', plain,
% 3.98/4.21      (![X0 : $i]:
% 3.98/4.21         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 3.98/4.21          | ((k5_relat_1 @ k1_xboole_0 @ (k6_relat_1 @ X0)) = (k1_xboole_0)))),
% 3.98/4.21      inference('demod', [status(thm)], ['75', '76'])).
% 3.98/4.21  thf('78', plain,
% 3.98/4.21      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 3.98/4.21      inference('sup-', [status(thm)], ['66', '67'])).
% 3.98/4.21  thf('79', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.98/4.21      inference('demod', [status(thm)], ['71', '72'])).
% 3.98/4.21  thf('80', plain,
% 3.98/4.21      (![X19 : $i, X20 : $i]:
% 3.98/4.21         (~ (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 3.98/4.21          | (v5_relat_1 @ X19 @ X20)
% 3.98/4.21          | ~ (v1_relat_1 @ X19))),
% 3.98/4.21      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.98/4.21  thf('81', plain,
% 3.98/4.21      (![X0 : $i]:
% 3.98/4.21         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 3.98/4.21          | ~ (v1_relat_1 @ k1_xboole_0)
% 3.98/4.21          | (v5_relat_1 @ k1_xboole_0 @ X0))),
% 3.98/4.21      inference('sup-', [status(thm)], ['79', '80'])).
% 3.98/4.21  thf('82', plain, ((v1_relat_1 @ k1_xboole_0)),
% 3.98/4.21      inference('sup+', [status(thm)], ['62', '63'])).
% 3.98/4.21  thf('83', plain,
% 3.98/4.21      (![X0 : $i]:
% 3.98/4.21         (~ (r1_tarski @ k1_xboole_0 @ X0) | (v5_relat_1 @ k1_xboole_0 @ X0))),
% 3.98/4.21      inference('demod', [status(thm)], ['81', '82'])).
% 3.98/4.21  thf('84', plain,
% 3.98/4.21      (![X0 : $i]:
% 3.98/4.21         (~ (v1_xboole_0 @ k1_xboole_0) | (v5_relat_1 @ k1_xboole_0 @ X0))),
% 3.98/4.21      inference('sup-', [status(thm)], ['78', '83'])).
% 3.98/4.21  thf('85', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.98/4.21      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.98/4.21  thf('86', plain, (![X0 : $i]: (v5_relat_1 @ k1_xboole_0 @ X0)),
% 3.98/4.21      inference('demod', [status(thm)], ['84', '85'])).
% 3.98/4.21  thf('87', plain,
% 3.98/4.21      (![X19 : $i, X20 : $i]:
% 3.98/4.21         (~ (v5_relat_1 @ X19 @ X20)
% 3.98/4.21          | (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 3.98/4.21          | ~ (v1_relat_1 @ X19))),
% 3.98/4.21      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.98/4.21  thf('88', plain,
% 3.98/4.21      (![X0 : $i]:
% 3.98/4.21         (~ (v1_relat_1 @ k1_xboole_0)
% 3.98/4.21          | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0))),
% 3.98/4.21      inference('sup-', [status(thm)], ['86', '87'])).
% 3.98/4.21  thf('89', plain, ((v1_relat_1 @ k1_xboole_0)),
% 3.98/4.21      inference('sup+', [status(thm)], ['62', '63'])).
% 3.98/4.21  thf('90', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.98/4.21      inference('demod', [status(thm)], ['71', '72'])).
% 3.98/4.21  thf('91', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 3.98/4.21      inference('demod', [status(thm)], ['88', '89', '90'])).
% 3.98/4.21  thf('92', plain,
% 3.98/4.21      (![X0 : $i]:
% 3.98/4.21         ((k5_relat_1 @ k1_xboole_0 @ (k6_relat_1 @ X0)) = (k1_xboole_0))),
% 3.98/4.21      inference('demod', [status(thm)], ['77', '91'])).
% 3.98/4.21  thf('93', plain,
% 3.98/4.21      (![X0 : $i, X1 : $i]:
% 3.98/4.21         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 3.98/4.21            = (k10_relat_1 @ X1 @ X0))
% 3.98/4.21          | ~ (v1_relat_1 @ X1))),
% 3.98/4.21      inference('demod', [status(thm)], ['22', '23'])).
% 3.98/4.21  thf('94', plain,
% 3.98/4.21      (![X0 : $i]:
% 3.98/4.21         (((k1_relat_1 @ k1_xboole_0) = (k10_relat_1 @ k1_xboole_0 @ X0))
% 3.98/4.21          | ~ (v1_relat_1 @ k1_xboole_0))),
% 3.98/4.21      inference('sup+', [status(thm)], ['92', '93'])).
% 3.98/4.21  thf('95', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.98/4.21      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.98/4.21  thf(fc10_relat_1, axiom,
% 3.98/4.21    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ))).
% 3.98/4.21  thf('96', plain,
% 3.98/4.21      (![X22 : $i]:
% 3.98/4.21         ((v1_xboole_0 @ (k1_relat_1 @ X22)) | ~ (v1_xboole_0 @ X22))),
% 3.98/4.21      inference('cnf', [status(esa)], [fc10_relat_1])).
% 3.98/4.21  thf('97', plain,
% 3.98/4.21      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 3.98/4.21      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.98/4.21  thf('98', plain,
% 3.98/4.21      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 3.98/4.21      inference('sup-', [status(thm)], ['96', '97'])).
% 3.98/4.21  thf('99', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.98/4.21      inference('sup-', [status(thm)], ['95', '98'])).
% 3.98/4.21  thf('100', plain, ((v1_relat_1 @ k1_xboole_0)),
% 3.98/4.21      inference('sup+', [status(thm)], ['62', '63'])).
% 3.98/4.21  thf('101', plain,
% 3.98/4.21      (![X0 : $i]: ((k1_xboole_0) = (k10_relat_1 @ k1_xboole_0 @ X0))),
% 3.98/4.21      inference('demod', [status(thm)], ['94', '99', '100'])).
% 3.98/4.21  thf('102', plain,
% 3.98/4.21      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 3.98/4.21      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.98/4.21  thf('103', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 3.98/4.21      inference('demod', [status(thm)], ['88', '89', '90'])).
% 3.98/4.21  thf('104', plain,
% 3.98/4.21      (![X14 : $i, X16 : $i]:
% 3.98/4.21         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 3.98/4.21      inference('cnf', [status(esa)], [t3_subset])).
% 3.98/4.21  thf('105', plain,
% 3.98/4.21      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 3.98/4.21      inference('sup-', [status(thm)], ['103', '104'])).
% 3.98/4.21  thf('106', plain,
% 3.98/4.21      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 3.98/4.21         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 3.98/4.21          | ((k8_relset_1 @ X38 @ X39 @ X37 @ X40) = (k10_relat_1 @ X37 @ X40)))),
% 3.98/4.21      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 3.98/4.21  thf('107', plain,
% 3.98/4.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.98/4.21         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 3.98/4.21           = (k10_relat_1 @ k1_xboole_0 @ X2))),
% 3.98/4.21      inference('sup-', [status(thm)], ['105', '106'])).
% 3.98/4.21  thf('108', plain,
% 3.98/4.21      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.98/4.21      inference('split', [status(esa)], ['48'])).
% 3.98/4.21  thf('109', plain,
% 3.98/4.21      (((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_B_1) != (sk_A))),
% 3.98/4.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.98/4.21  thf('110', plain,
% 3.98/4.21      ((((k8_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_1 @ sk_B_1) != (sk_A)))
% 3.98/4.21         <= ((((sk_A) = (k1_xboole_0))))),
% 3.98/4.21      inference('sup-', [status(thm)], ['108', '109'])).
% 3.98/4.21  thf('111', plain,
% 3.98/4.21      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.98/4.21      inference('split', [status(esa)], ['48'])).
% 3.98/4.21  thf('112', plain,
% 3.98/4.21      ((((k8_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_1 @ sk_B_1)
% 3.98/4.21          != (k1_xboole_0)))
% 3.98/4.21         <= ((((sk_A) = (k1_xboole_0))))),
% 3.98/4.21      inference('demod', [status(thm)], ['110', '111'])).
% 3.98/4.21  thf('113', plain,
% 3.98/4.21      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 3.98/4.21      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.98/4.21  thf('114', plain,
% 3.98/4.21      (![X13 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X13) = (k1_xboole_0))),
% 3.98/4.21      inference('simplify', [status(thm)], ['61'])).
% 3.98/4.21  thf('115', plain,
% 3.98/4.21      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.98/4.21      inference('split', [status(esa)], ['48'])).
% 3.98/4.21  thf('116', plain,
% 3.98/4.21      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.98/4.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.98/4.21  thf('117', plain,
% 3.98/4.21      (((m1_subset_1 @ sk_C_1 @ 
% 3.98/4.21         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 3.98/4.21         <= ((((sk_A) = (k1_xboole_0))))),
% 3.98/4.21      inference('sup+', [status(thm)], ['115', '116'])).
% 3.98/4.21  thf('118', plain,
% 3.98/4.21      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ k1_xboole_0)))
% 3.98/4.21         <= ((((sk_A) = (k1_xboole_0))))),
% 3.98/4.21      inference('sup+', [status(thm)], ['114', '117'])).
% 3.98/4.21  thf('119', plain,
% 3.98/4.21      (![X14 : $i, X15 : $i]:
% 3.98/4.21         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 3.98/4.21      inference('cnf', [status(esa)], [t3_subset])).
% 3.98/4.21  thf('120', plain,
% 3.98/4.21      (((r1_tarski @ sk_C_1 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 3.98/4.21      inference('sup-', [status(thm)], ['118', '119'])).
% 3.98/4.21  thf('121', plain,
% 3.98/4.21      (![X3 : $i, X4 : $i, X5 : $i]:
% 3.98/4.21         (~ (r2_hidden @ X3 @ X4)
% 3.98/4.21          | (r2_hidden @ X3 @ X5)
% 3.98/4.21          | ~ (r1_tarski @ X4 @ X5))),
% 3.98/4.21      inference('cnf', [status(esa)], [d3_tarski])).
% 3.98/4.21  thf('122', plain,
% 3.98/4.21      ((![X0 : $i]:
% 3.98/4.21          ((r2_hidden @ X0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_C_1)))
% 3.98/4.21         <= ((((sk_A) = (k1_xboole_0))))),
% 3.98/4.21      inference('sup-', [status(thm)], ['120', '121'])).
% 3.98/4.21  thf('123', plain,
% 3.98/4.21      ((((v1_xboole_0 @ sk_C_1) | (r2_hidden @ (sk_B @ sk_C_1) @ k1_xboole_0)))
% 3.98/4.21         <= ((((sk_A) = (k1_xboole_0))))),
% 3.98/4.21      inference('sup-', [status(thm)], ['113', '122'])).
% 3.98/4.21  thf('124', plain,
% 3.98/4.21      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.98/4.21      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.98/4.21  thf('125', plain,
% 3.98/4.21      ((((v1_xboole_0 @ sk_C_1) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 3.98/4.21         <= ((((sk_A) = (k1_xboole_0))))),
% 3.98/4.21      inference('sup-', [status(thm)], ['123', '124'])).
% 3.98/4.21  thf('126', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.98/4.21      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.98/4.21  thf('127', plain, (((v1_xboole_0 @ sk_C_1)) <= ((((sk_A) = (k1_xboole_0))))),
% 3.98/4.21      inference('demod', [status(thm)], ['125', '126'])).
% 3.98/4.21  thf('128', plain,
% 3.98/4.21      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 3.98/4.21      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.98/4.21  thf('129', plain,
% 3.98/4.21      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.98/4.21      inference('sup-', [status(thm)], ['127', '128'])).
% 3.98/4.21  thf('130', plain,
% 3.98/4.21      ((((k8_relset_1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0 @ sk_B_1)
% 3.98/4.21          != (k1_xboole_0)))
% 3.98/4.21         <= ((((sk_A) = (k1_xboole_0))))),
% 3.98/4.21      inference('demod', [status(thm)], ['112', '129'])).
% 3.98/4.21  thf('131', plain,
% 3.98/4.21      ((((k10_relat_1 @ k1_xboole_0 @ sk_B_1) != (k1_xboole_0)))
% 3.98/4.21         <= ((((sk_A) = (k1_xboole_0))))),
% 3.98/4.21      inference('sup-', [status(thm)], ['107', '130'])).
% 3.98/4.21  thf('132', plain,
% 3.98/4.21      ((![X0 : $i]:
% 3.98/4.21          (((k10_relat_1 @ X0 @ sk_B_1) != (k1_xboole_0))
% 3.98/4.21           | ~ (v1_xboole_0 @ X0)))
% 3.98/4.21         <= ((((sk_A) = (k1_xboole_0))))),
% 3.98/4.21      inference('sup-', [status(thm)], ['102', '131'])).
% 3.98/4.21  thf('133', plain,
% 3.98/4.21      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 3.98/4.21         <= ((((sk_A) = (k1_xboole_0))))),
% 3.98/4.21      inference('sup-', [status(thm)], ['101', '132'])).
% 3.98/4.22  thf('134', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.98/4.22      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.98/4.22  thf('135', plain,
% 3.98/4.22      ((((k1_xboole_0) != (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.98/4.22      inference('demod', [status(thm)], ['133', '134'])).
% 3.98/4.22  thf('136', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 3.98/4.22      inference('simplify', [status(thm)], ['135'])).
% 3.98/4.22  thf('137', plain,
% 3.98/4.22      (~ (((sk_B_1) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 3.98/4.22      inference('split', [status(esa)], ['48'])).
% 3.98/4.22  thf('138', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 3.98/4.22      inference('sat_resolution*', [status(thm)], ['136', '137'])).
% 3.98/4.22  thf('139', plain, (((sk_B_1) != (k1_xboole_0))),
% 3.98/4.22      inference('simpl_trail', [status(thm)], ['49', '138'])).
% 3.98/4.22  thf('140', plain,
% 3.98/4.22      (![X0 : $i]:
% 3.98/4.22         (((X0) != (k1_xboole_0))
% 3.98/4.22          | ~ (v1_xboole_0 @ X0)
% 3.98/4.22          | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 3.98/4.22      inference('sup-', [status(thm)], ['47', '139'])).
% 3.98/4.22  thf('141', plain,
% 3.98/4.22      ((((sk_A) = (k1_relat_1 @ sk_C_1)) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 3.98/4.22      inference('simplify', [status(thm)], ['140'])).
% 3.98/4.22  thf('142', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.98/4.22      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.98/4.22  thf('143', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 3.98/4.22      inference('simplify_reflect+', [status(thm)], ['141', '142'])).
% 3.98/4.22  thf('144', plain, (((sk_A) != (sk_A))),
% 3.98/4.22      inference('demod', [status(thm)], ['28', '143'])).
% 3.98/4.22  thf('145', plain, ($false), inference('simplify', [status(thm)], ['144'])).
% 3.98/4.22  
% 3.98/4.22  % SZS output end Refutation
% 3.98/4.22  
% 3.98/4.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
