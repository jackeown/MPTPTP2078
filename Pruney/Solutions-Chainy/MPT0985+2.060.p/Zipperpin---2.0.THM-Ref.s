%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EO85na0yad

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:35 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :  262 (2847 expanded)
%              Number of leaves         :   52 ( 904 expanded)
%              Depth                    :   29
%              Number of atoms          : 1681 (28937 expanded)
%              Number of equality atoms :  114 (1706 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t31_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( v2_funct_1 @ C )
            & ( ( k2_relset_1 @ A @ B @ C )
              = B ) )
         => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
            & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
            & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('4',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ X13 )
        = ( k4_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X14: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('19',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('22',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('23',plain,(
    ! [X40: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('24',plain,(
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('25',plain,(
    ! [X40: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X40 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('26',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ( v1_xboole_0 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k6_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('29',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('30',plain,(
    v1_xboole_0 @ ( k6_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('32',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X40: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X40 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('34',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('36',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','36'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('38',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v5_relat_1 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( v5_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v5_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','39'])).

thf('41',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('43',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v5_relat_1 @ X9 @ X10 )
      | ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','31'])).

thf('46',plain,(
    ! [X40: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X40 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('47',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['45','48'])).

thf('50',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t72_relat_1,axiom,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('51',plain,(
    ! [X12: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X12 ) )
      = ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('52',plain,(
    ! [X11: $i] :
      ( ( ( k2_relat_1 @ X11 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X0 ) )
      = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = ( k1_relat_1 @ ( k6_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['50','55'])).

thf('57',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','31'])).

thf('58',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('60',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('61',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v5_relat_1 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('62',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v5_relat_1 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v5_relat_1 @ X9 @ X10 )
      | ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('65',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['45','48'])).

thf('67',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('68',plain,(
    r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['65','66','67'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('69',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('70',plain,(
    m1_subset_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('72',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X24 ) ) )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('73',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('75',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    v1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('78',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['58','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['44','49','79'])).

thf('81',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('82',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('83',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['76','77'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['84','85'])).

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

thf('87',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X33
       != ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('90',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X32 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('91',plain,(
    ! [X31: $i] :
      ( zip_tseitin_0 @ X31 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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

thf('93',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['89','95'])).

thf('97',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('98',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('99',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('100',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('102',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['99','102'])).

thf('104',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ( X33
        = ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('106',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('109',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['106','109'])).

thf('111',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['103','110'])).

thf('112',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('113',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k2_relat_1 @ X15 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('114',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('116',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['114','115','116','117'])).

thf('119',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('120',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('121',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['118','123'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('125',plain,(
    ! [X42: $i] :
      ( ( v1_funct_2 @ X42 @ ( k1_relat_1 @ X42 ) @ ( k2_relat_1 @ X42 ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('126',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('128',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k1_relat_1 @ X15 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('129',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('131',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['129','130','131','132'])).

thf('134',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('135',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('136',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('138',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('140',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('141',plain,(
    ! [X14: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('142',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('143',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('144',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('146',plain,(
    v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['126','133','139','145'])).

thf('147',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['111','146'])).

thf('148',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('149',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('150',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['147','150'])).

thf('152',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['97','98','151'])).

thf('153',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['147','150'])).

thf('154',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('156',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,
    ( ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['153','156'])).

thf('158',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('159',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('160',plain,
    ( ( v1_xboole_0 @ sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['157','158','159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('162',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','31'])).

thf('164',plain,(
    ! [X12: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X12 ) )
      = ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('165',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['163','164'])).

thf('166',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','31'])).

thf('167',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['152','162','167'])).

thf('169',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['96','168'])).

thf('170',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('171',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['17','169','170'])).

thf('172',plain,(
    ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['10','171'])).

thf('173',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['129','130','131','132'])).

thf('174',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('175',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('176',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['174','175'])).

thf('177',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('182',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['165','166'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['181','182'])).

thf('184',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['183','184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('187',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['186','187'])).

thf('189',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('190',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('191',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,
    ( ~ ( v1_xboole_0 @ ( k4_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['188','191'])).

thf('193',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['185','192'])).

thf('194',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_B @ X0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['180','193'])).

thf('195',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('196',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['106','109'])).

thf('198',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['17','169','170'])).

thf('200',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['198','199'])).

thf('201',plain,
    ( sk_A
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['173','200'])).

thf('202',plain,(
    ! [X42: $i] :
      ( ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X42 ) @ ( k2_relat_1 @ X42 ) ) ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('203',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['201','202'])).

thf('204',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['118','123'])).

thf('205',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('206',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('207',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['203','204','205','206'])).

thf('208',plain,(
    $false ),
    inference(demod,[status(thm)],['172','207'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EO85na0yad
% 0.13/0.37  % Computer   : n007.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 10:13:21 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 1.43/1.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.43/1.62  % Solved by: fo/fo7.sh
% 1.43/1.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.43/1.62  % done 1901 iterations in 1.158s
% 1.43/1.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.43/1.62  % SZS output start Refutation
% 1.43/1.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.43/1.62  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.43/1.62  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.43/1.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.43/1.62  thf(sk_C_type, type, sk_C: $i).
% 1.43/1.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.43/1.62  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.43/1.62  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.43/1.62  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 1.43/1.62  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.43/1.62  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.43/1.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.43/1.62  thf(sk_A_type, type, sk_A: $i).
% 1.43/1.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.43/1.62  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.43/1.62  thf(sk_B_type, type, sk_B: $i).
% 1.43/1.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.43/1.62  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.43/1.62  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.43/1.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.43/1.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.43/1.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.43/1.62  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.43/1.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.43/1.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.43/1.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.43/1.62  thf(t31_funct_2, conjecture,
% 1.43/1.62    (![A:$i,B:$i,C:$i]:
% 1.43/1.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.43/1.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.43/1.62       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.43/1.62         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.43/1.62           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.43/1.62           ( m1_subset_1 @
% 1.43/1.62             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.43/1.62  thf(zf_stmt_0, negated_conjecture,
% 1.43/1.62    (~( ![A:$i,B:$i,C:$i]:
% 1.43/1.62        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.43/1.62            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.43/1.62          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.43/1.62            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.43/1.62              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.43/1.62              ( m1_subset_1 @
% 1.43/1.62                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 1.43/1.62    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 1.43/1.62  thf('0', plain,
% 1.43/1.62      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.43/1.62        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 1.43/1.62        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.43/1.62             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.43/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.62  thf('1', plain,
% 1.43/1.62      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.43/1.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 1.43/1.62         <= (~
% 1.43/1.62             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.43/1.62               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.43/1.62      inference('split', [status(esa)], ['0'])).
% 1.43/1.62  thf('2', plain,
% 1.43/1.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.43/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.62  thf(cc1_relset_1, axiom,
% 1.43/1.62    (![A:$i,B:$i,C:$i]:
% 1.43/1.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.43/1.62       ( v1_relat_1 @ C ) ))).
% 1.43/1.62  thf('3', plain,
% 1.43/1.62      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.43/1.62         ((v1_relat_1 @ X16)
% 1.43/1.62          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.43/1.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.43/1.62  thf('4', plain, ((v1_relat_1 @ sk_C)),
% 1.43/1.62      inference('sup-', [status(thm)], ['2', '3'])).
% 1.43/1.62  thf(d9_funct_1, axiom,
% 1.43/1.62    (![A:$i]:
% 1.43/1.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.43/1.62       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 1.43/1.62  thf('5', plain,
% 1.43/1.62      (![X13 : $i]:
% 1.43/1.62         (~ (v2_funct_1 @ X13)
% 1.43/1.62          | ((k2_funct_1 @ X13) = (k4_relat_1 @ X13))
% 1.43/1.62          | ~ (v1_funct_1 @ X13)
% 1.43/1.62          | ~ (v1_relat_1 @ X13))),
% 1.43/1.62      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.43/1.62  thf('6', plain,
% 1.43/1.62      ((~ (v1_funct_1 @ sk_C)
% 1.43/1.62        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 1.43/1.62        | ~ (v2_funct_1 @ sk_C))),
% 1.43/1.62      inference('sup-', [status(thm)], ['4', '5'])).
% 1.43/1.62  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 1.43/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.62  thf('8', plain, ((v2_funct_1 @ sk_C)),
% 1.43/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.62  thf('9', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.43/1.62      inference('demod', [status(thm)], ['6', '7', '8'])).
% 1.43/1.62  thf('10', plain,
% 1.43/1.62      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.43/1.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 1.43/1.62         <= (~
% 1.43/1.62             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.43/1.62               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.43/1.62      inference('demod', [status(thm)], ['1', '9'])).
% 1.43/1.62  thf('11', plain, ((v1_relat_1 @ sk_C)),
% 1.43/1.62      inference('sup-', [status(thm)], ['2', '3'])).
% 1.43/1.62  thf(dt_k2_funct_1, axiom,
% 1.43/1.62    (![A:$i]:
% 1.43/1.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.43/1.62       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.43/1.62         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.43/1.62  thf('12', plain,
% 1.43/1.62      (![X14 : $i]:
% 1.43/1.62         ((v1_funct_1 @ (k2_funct_1 @ X14))
% 1.43/1.62          | ~ (v1_funct_1 @ X14)
% 1.43/1.62          | ~ (v1_relat_1 @ X14))),
% 1.43/1.62      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.43/1.62  thf('13', plain,
% 1.43/1.62      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.43/1.62         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.43/1.62      inference('split', [status(esa)], ['0'])).
% 1.43/1.62  thf('14', plain,
% 1.43/1.62      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 1.43/1.62         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.43/1.62      inference('sup-', [status(thm)], ['12', '13'])).
% 1.43/1.62  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 1.43/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.62  thf('16', plain,
% 1.43/1.62      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.43/1.62      inference('demod', [status(thm)], ['14', '15'])).
% 1.43/1.62  thf('17', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.43/1.62      inference('sup-', [status(thm)], ['11', '16'])).
% 1.43/1.62  thf(t113_zfmisc_1, axiom,
% 1.43/1.62    (![A:$i,B:$i]:
% 1.43/1.62     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.43/1.62       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.43/1.62  thf('18', plain,
% 1.43/1.62      (![X2 : $i, X3 : $i]:
% 1.43/1.62         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 1.43/1.62      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.43/1.62  thf('19', plain,
% 1.43/1.62      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 1.43/1.62      inference('simplify', [status(thm)], ['18'])).
% 1.43/1.62  thf(l13_xboole_0, axiom,
% 1.43/1.62    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.43/1.62  thf('20', plain,
% 1.43/1.62      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.43/1.62      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.43/1.62  thf('21', plain,
% 1.43/1.62      (![X2 : $i, X3 : $i]:
% 1.43/1.62         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 1.43/1.62      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.43/1.62  thf('22', plain,
% 1.43/1.62      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 1.43/1.62      inference('simplify', [status(thm)], ['21'])).
% 1.43/1.62  thf(dt_k6_partfun1, axiom,
% 1.43/1.62    (![A:$i]:
% 1.43/1.62     ( ( m1_subset_1 @
% 1.43/1.62         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 1.43/1.62       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 1.43/1.62  thf('23', plain,
% 1.43/1.62      (![X40 : $i]:
% 1.43/1.62         (m1_subset_1 @ (k6_partfun1 @ X40) @ 
% 1.43/1.62          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X40)))),
% 1.43/1.62      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.43/1.62  thf(redefinition_k6_partfun1, axiom,
% 1.43/1.62    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.43/1.62  thf('24', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 1.43/1.62      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.43/1.62  thf('25', plain,
% 1.43/1.62      (![X40 : $i]:
% 1.43/1.62         (m1_subset_1 @ (k6_relat_1 @ X40) @ 
% 1.43/1.62          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X40)))),
% 1.43/1.62      inference('demod', [status(thm)], ['23', '24'])).
% 1.43/1.62  thf(cc1_subset_1, axiom,
% 1.43/1.62    (![A:$i]:
% 1.43/1.62     ( ( v1_xboole_0 @ A ) =>
% 1.43/1.62       ( ![B:$i]:
% 1.43/1.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 1.43/1.62  thf('26', plain,
% 1.43/1.62      (![X4 : $i, X5 : $i]:
% 1.43/1.62         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 1.43/1.62          | (v1_xboole_0 @ X4)
% 1.43/1.62          | ~ (v1_xboole_0 @ X5))),
% 1.43/1.62      inference('cnf', [status(esa)], [cc1_subset_1])).
% 1.43/1.62  thf('27', plain,
% 1.43/1.62      (![X0 : $i]:
% 1.43/1.62         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X0))
% 1.43/1.62          | (v1_xboole_0 @ (k6_relat_1 @ X0)))),
% 1.43/1.62      inference('sup-', [status(thm)], ['25', '26'])).
% 1.43/1.62  thf('28', plain,
% 1.43/1.62      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.43/1.62        | (v1_xboole_0 @ (k6_relat_1 @ k1_xboole_0)))),
% 1.43/1.62      inference('sup-', [status(thm)], ['22', '27'])).
% 1.43/1.62  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.43/1.62  thf('29', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.43/1.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.43/1.62  thf('30', plain, ((v1_xboole_0 @ (k6_relat_1 @ k1_xboole_0))),
% 1.43/1.62      inference('demod', [status(thm)], ['28', '29'])).
% 1.43/1.62  thf('31', plain,
% 1.43/1.62      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.43/1.62      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.43/1.62  thf('32', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.43/1.62      inference('sup-', [status(thm)], ['30', '31'])).
% 1.43/1.62  thf('33', plain,
% 1.43/1.62      (![X40 : $i]:
% 1.43/1.62         (m1_subset_1 @ (k6_relat_1 @ X40) @ 
% 1.43/1.62          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X40)))),
% 1.43/1.62      inference('demod', [status(thm)], ['23', '24'])).
% 1.43/1.62  thf('34', plain,
% 1.43/1.62      ((m1_subset_1 @ k1_xboole_0 @ 
% 1.43/1.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 1.43/1.62      inference('sup+', [status(thm)], ['32', '33'])).
% 1.43/1.62  thf('35', plain,
% 1.43/1.62      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 1.43/1.62      inference('simplify', [status(thm)], ['18'])).
% 1.43/1.62  thf('36', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 1.43/1.62      inference('demod', [status(thm)], ['34', '35'])).
% 1.43/1.62  thf('37', plain,
% 1.43/1.62      (![X0 : $i]:
% 1.43/1.62         ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.43/1.62          | ~ (v1_xboole_0 @ X0))),
% 1.43/1.62      inference('sup+', [status(thm)], ['20', '36'])).
% 1.43/1.62  thf(cc2_relset_1, axiom,
% 1.43/1.62    (![A:$i,B:$i,C:$i]:
% 1.43/1.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.43/1.62       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.43/1.62  thf('38', plain,
% 1.43/1.62      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.43/1.62         ((v5_relat_1 @ X19 @ X21)
% 1.43/1.62          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 1.43/1.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.43/1.62  thf('39', plain,
% 1.43/1.62      (![X0 : $i, X1 : $i]:
% 1.43/1.62         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 1.43/1.62          | (v5_relat_1 @ k1_xboole_0 @ X0))),
% 1.43/1.62      inference('sup-', [status(thm)], ['37', '38'])).
% 1.43/1.62  thf('40', plain,
% 1.43/1.62      (![X0 : $i]:
% 1.43/1.62         (~ (v1_xboole_0 @ k1_xboole_0) | (v5_relat_1 @ k1_xboole_0 @ X0))),
% 1.43/1.62      inference('sup-', [status(thm)], ['19', '39'])).
% 1.43/1.62  thf('41', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.43/1.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.43/1.62  thf('42', plain, (![X0 : $i]: (v5_relat_1 @ k1_xboole_0 @ X0)),
% 1.43/1.62      inference('demod', [status(thm)], ['40', '41'])).
% 1.43/1.62  thf(d19_relat_1, axiom,
% 1.43/1.62    (![A:$i,B:$i]:
% 1.43/1.62     ( ( v1_relat_1 @ B ) =>
% 1.43/1.62       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.43/1.62  thf('43', plain,
% 1.43/1.62      (![X9 : $i, X10 : $i]:
% 1.43/1.62         (~ (v5_relat_1 @ X9 @ X10)
% 1.43/1.62          | (r1_tarski @ (k2_relat_1 @ X9) @ X10)
% 1.43/1.62          | ~ (v1_relat_1 @ X9))),
% 1.43/1.62      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.43/1.62  thf('44', plain,
% 1.43/1.62      (![X0 : $i]:
% 1.43/1.62         (~ (v1_relat_1 @ k1_xboole_0)
% 1.43/1.62          | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0))),
% 1.43/1.62      inference('sup-', [status(thm)], ['42', '43'])).
% 1.43/1.62  thf('45', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.43/1.62      inference('sup-', [status(thm)], ['30', '31'])).
% 1.43/1.62  thf('46', plain,
% 1.43/1.62      (![X40 : $i]:
% 1.43/1.62         (m1_subset_1 @ (k6_relat_1 @ X40) @ 
% 1.43/1.62          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X40)))),
% 1.43/1.62      inference('demod', [status(thm)], ['23', '24'])).
% 1.43/1.62  thf('47', plain,
% 1.43/1.62      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.43/1.62         ((v1_relat_1 @ X16)
% 1.43/1.62          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.43/1.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.43/1.62  thf('48', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 1.43/1.62      inference('sup-', [status(thm)], ['46', '47'])).
% 1.43/1.62  thf('49', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.43/1.62      inference('sup+', [status(thm)], ['45', '48'])).
% 1.43/1.62  thf('50', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.43/1.62      inference('sup-', [status(thm)], ['30', '31'])).
% 1.43/1.62  thf(t72_relat_1, axiom,
% 1.43/1.62    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 1.43/1.62  thf('51', plain,
% 1.43/1.62      (![X12 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X12)) = (k6_relat_1 @ X12))),
% 1.43/1.62      inference('cnf', [status(esa)], [t72_relat_1])).
% 1.43/1.62  thf(t37_relat_1, axiom,
% 1.43/1.62    (![A:$i]:
% 1.43/1.62     ( ( v1_relat_1 @ A ) =>
% 1.43/1.62       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 1.43/1.62         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 1.43/1.62  thf('52', plain,
% 1.43/1.62      (![X11 : $i]:
% 1.43/1.62         (((k2_relat_1 @ X11) = (k1_relat_1 @ (k4_relat_1 @ X11)))
% 1.43/1.62          | ~ (v1_relat_1 @ X11))),
% 1.43/1.62      inference('cnf', [status(esa)], [t37_relat_1])).
% 1.43/1.62  thf('53', plain,
% 1.43/1.62      (![X0 : $i]:
% 1.43/1.62         (((k2_relat_1 @ (k6_relat_1 @ X0)) = (k1_relat_1 @ (k6_relat_1 @ X0)))
% 1.43/1.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.43/1.62      inference('sup+', [status(thm)], ['51', '52'])).
% 1.43/1.62  thf('54', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 1.43/1.62      inference('sup-', [status(thm)], ['46', '47'])).
% 1.43/1.62  thf('55', plain,
% 1.43/1.62      (![X0 : $i]:
% 1.43/1.62         ((k2_relat_1 @ (k6_relat_1 @ X0)) = (k1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.43/1.62      inference('demod', [status(thm)], ['53', '54'])).
% 1.43/1.62  thf('56', plain,
% 1.43/1.62      (((k2_relat_1 @ k1_xboole_0) = (k1_relat_1 @ (k6_relat_1 @ k1_xboole_0)))),
% 1.43/1.62      inference('sup+', [status(thm)], ['50', '55'])).
% 1.43/1.62  thf('57', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.43/1.62      inference('sup-', [status(thm)], ['30', '31'])).
% 1.43/1.62  thf('58', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 1.43/1.62      inference('demod', [status(thm)], ['56', '57'])).
% 1.43/1.62  thf('59', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 1.43/1.62      inference('demod', [status(thm)], ['34', '35'])).
% 1.43/1.62  thf('60', plain,
% 1.43/1.62      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 1.43/1.62      inference('simplify', [status(thm)], ['21'])).
% 1.43/1.62  thf('61', plain,
% 1.43/1.62      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.43/1.62         ((v5_relat_1 @ X19 @ X21)
% 1.43/1.62          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 1.43/1.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.43/1.62  thf('62', plain,
% 1.43/1.62      (![X1 : $i]:
% 1.43/1.62         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.43/1.62          | (v5_relat_1 @ X1 @ k1_xboole_0))),
% 1.43/1.62      inference('sup-', [status(thm)], ['60', '61'])).
% 1.43/1.62  thf('63', plain, ((v5_relat_1 @ k1_xboole_0 @ k1_xboole_0)),
% 1.43/1.62      inference('sup-', [status(thm)], ['59', '62'])).
% 1.43/1.62  thf('64', plain,
% 1.43/1.62      (![X9 : $i, X10 : $i]:
% 1.43/1.62         (~ (v5_relat_1 @ X9 @ X10)
% 1.43/1.62          | (r1_tarski @ (k2_relat_1 @ X9) @ X10)
% 1.43/1.62          | ~ (v1_relat_1 @ X9))),
% 1.43/1.62      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.43/1.62  thf('65', plain,
% 1.43/1.62      ((~ (v1_relat_1 @ k1_xboole_0)
% 1.43/1.62        | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ k1_xboole_0))),
% 1.43/1.62      inference('sup-', [status(thm)], ['63', '64'])).
% 1.43/1.62  thf('66', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.43/1.62      inference('sup+', [status(thm)], ['45', '48'])).
% 1.43/1.62  thf('67', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 1.43/1.62      inference('demod', [status(thm)], ['56', '57'])).
% 1.43/1.62  thf('68', plain, ((r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 1.43/1.62      inference('demod', [status(thm)], ['65', '66', '67'])).
% 1.43/1.62  thf(t3_subset, axiom,
% 1.43/1.62    (![A:$i,B:$i]:
% 1.43/1.62     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.43/1.62  thf('69', plain,
% 1.43/1.62      (![X6 : $i, X8 : $i]:
% 1.43/1.62         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 1.43/1.62      inference('cnf', [status(esa)], [t3_subset])).
% 1.43/1.62  thf('70', plain,
% 1.43/1.62      ((m1_subset_1 @ (k1_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 1.43/1.62      inference('sup-', [status(thm)], ['68', '69'])).
% 1.43/1.62  thf('71', plain,
% 1.43/1.62      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 1.43/1.62      inference('simplify', [status(thm)], ['18'])).
% 1.43/1.62  thf(cc3_relset_1, axiom,
% 1.43/1.62    (![A:$i,B:$i]:
% 1.43/1.62     ( ( v1_xboole_0 @ A ) =>
% 1.43/1.62       ( ![C:$i]:
% 1.43/1.62         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.43/1.62           ( v1_xboole_0 @ C ) ) ) ))).
% 1.43/1.62  thf('72', plain,
% 1.43/1.62      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.43/1.62         (~ (v1_xboole_0 @ X22)
% 1.43/1.62          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X24)))
% 1.43/1.62          | (v1_xboole_0 @ X23))),
% 1.43/1.62      inference('cnf', [status(esa)], [cc3_relset_1])).
% 1.43/1.62  thf('73', plain,
% 1.43/1.62      (![X1 : $i]:
% 1.43/1.62         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.43/1.62          | (v1_xboole_0 @ X1)
% 1.43/1.62          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.43/1.62      inference('sup-', [status(thm)], ['71', '72'])).
% 1.43/1.62  thf('74', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.43/1.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.43/1.62  thf('75', plain,
% 1.43/1.62      (![X1 : $i]:
% 1.43/1.62         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.43/1.62          | (v1_xboole_0 @ X1))),
% 1.43/1.62      inference('demod', [status(thm)], ['73', '74'])).
% 1.43/1.62  thf('76', plain, ((v1_xboole_0 @ (k1_relat_1 @ k1_xboole_0))),
% 1.43/1.62      inference('sup-', [status(thm)], ['70', '75'])).
% 1.43/1.62  thf('77', plain,
% 1.43/1.62      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.43/1.62      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.43/1.62  thf('78', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.43/1.62      inference('sup-', [status(thm)], ['76', '77'])).
% 1.43/1.62  thf('79', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.43/1.62      inference('demod', [status(thm)], ['58', '78'])).
% 1.43/1.62  thf('80', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.43/1.62      inference('demod', [status(thm)], ['44', '49', '79'])).
% 1.43/1.62  thf('81', plain,
% 1.43/1.62      (![X6 : $i, X8 : $i]:
% 1.43/1.62         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 1.43/1.62      inference('cnf', [status(esa)], [t3_subset])).
% 1.43/1.62  thf('82', plain,
% 1.43/1.62      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.43/1.62      inference('sup-', [status(thm)], ['80', '81'])).
% 1.43/1.62  thf(redefinition_k1_relset_1, axiom,
% 1.43/1.62    (![A:$i,B:$i,C:$i]:
% 1.43/1.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.43/1.62       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.43/1.62  thf('83', plain,
% 1.43/1.62      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.43/1.62         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 1.43/1.62          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 1.43/1.62      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.43/1.62  thf('84', plain,
% 1.43/1.62      (![X0 : $i, X1 : $i]:
% 1.43/1.62         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 1.43/1.62      inference('sup-', [status(thm)], ['82', '83'])).
% 1.43/1.62  thf('85', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.43/1.62      inference('sup-', [status(thm)], ['76', '77'])).
% 1.43/1.62  thf('86', plain,
% 1.43/1.62      (![X0 : $i, X1 : $i]:
% 1.43/1.62         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.43/1.62      inference('demod', [status(thm)], ['84', '85'])).
% 1.43/1.62  thf(d1_funct_2, axiom,
% 1.43/1.62    (![A:$i,B:$i,C:$i]:
% 1.43/1.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.43/1.62       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.43/1.62           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.43/1.62             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.43/1.62         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.43/1.62           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.43/1.62             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.43/1.62  thf(zf_stmt_1, axiom,
% 1.43/1.62    (![C:$i,B:$i,A:$i]:
% 1.43/1.62     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.43/1.62       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.43/1.62  thf('87', plain,
% 1.43/1.62      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.43/1.62         (((X33) != (k1_relset_1 @ X33 @ X34 @ X35))
% 1.43/1.62          | (v1_funct_2 @ X35 @ X33 @ X34)
% 1.43/1.62          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 1.43/1.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.43/1.62  thf('88', plain,
% 1.43/1.62      (![X0 : $i, X1 : $i]:
% 1.43/1.62         (((X1) != (k1_xboole_0))
% 1.43/1.62          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 1.43/1.62          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 1.43/1.62      inference('sup-', [status(thm)], ['86', '87'])).
% 1.43/1.62  thf('89', plain,
% 1.43/1.62      (![X0 : $i]:
% 1.43/1.62         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.43/1.62          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 1.43/1.62      inference('simplify', [status(thm)], ['88'])).
% 1.43/1.62  thf(zf_stmt_2, axiom,
% 1.43/1.62    (![B:$i,A:$i]:
% 1.43/1.62     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.43/1.62       ( zip_tseitin_0 @ B @ A ) ))).
% 1.43/1.62  thf('90', plain,
% 1.43/1.62      (![X31 : $i, X32 : $i]:
% 1.43/1.62         ((zip_tseitin_0 @ X31 @ X32) | ((X32) != (k1_xboole_0)))),
% 1.43/1.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.43/1.62  thf('91', plain, (![X31 : $i]: (zip_tseitin_0 @ X31 @ k1_xboole_0)),
% 1.43/1.62      inference('simplify', [status(thm)], ['90'])).
% 1.43/1.62  thf('92', plain,
% 1.43/1.62      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.43/1.62      inference('sup-', [status(thm)], ['80', '81'])).
% 1.43/1.62  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.43/1.62  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.43/1.62  thf(zf_stmt_5, axiom,
% 1.43/1.62    (![A:$i,B:$i,C:$i]:
% 1.43/1.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.43/1.62       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.43/1.62         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.43/1.62           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.43/1.62             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.43/1.62  thf('93', plain,
% 1.43/1.62      (![X36 : $i, X37 : $i, X38 : $i]:
% 1.43/1.62         (~ (zip_tseitin_0 @ X36 @ X37)
% 1.43/1.62          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 1.43/1.62          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 1.43/1.62      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.43/1.62  thf('94', plain,
% 1.43/1.62      (![X0 : $i, X1 : $i]:
% 1.43/1.62         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 1.43/1.62      inference('sup-', [status(thm)], ['92', '93'])).
% 1.43/1.62  thf('95', plain,
% 1.43/1.62      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.43/1.62      inference('sup-', [status(thm)], ['91', '94'])).
% 1.43/1.62  thf('96', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.43/1.62      inference('demod', [status(thm)], ['89', '95'])).
% 1.43/1.62  thf('97', plain,
% 1.43/1.62      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 1.43/1.62         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.43/1.62      inference('split', [status(esa)], ['0'])).
% 1.43/1.62  thf('98', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.43/1.62      inference('demod', [status(thm)], ['6', '7', '8'])).
% 1.43/1.62  thf('99', plain,
% 1.43/1.62      (![X31 : $i, X32 : $i]:
% 1.43/1.62         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 1.43/1.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.43/1.62  thf('100', plain,
% 1.43/1.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.43/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.62  thf('101', plain,
% 1.43/1.62      (![X36 : $i, X37 : $i, X38 : $i]:
% 1.43/1.62         (~ (zip_tseitin_0 @ X36 @ X37)
% 1.43/1.62          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 1.43/1.62          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 1.43/1.62      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.43/1.62  thf('102', plain,
% 1.43/1.62      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.43/1.62      inference('sup-', [status(thm)], ['100', '101'])).
% 1.43/1.62  thf('103', plain,
% 1.43/1.62      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 1.43/1.62      inference('sup-', [status(thm)], ['99', '102'])).
% 1.43/1.62  thf('104', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.43/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.62  thf('105', plain,
% 1.43/1.62      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.43/1.62         (~ (v1_funct_2 @ X35 @ X33 @ X34)
% 1.43/1.62          | ((X33) = (k1_relset_1 @ X33 @ X34 @ X35))
% 1.43/1.62          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 1.43/1.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.43/1.62  thf('106', plain,
% 1.43/1.62      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 1.43/1.62        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 1.43/1.62      inference('sup-', [status(thm)], ['104', '105'])).
% 1.43/1.62  thf('107', plain,
% 1.43/1.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.43/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.62  thf('108', plain,
% 1.43/1.62      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.43/1.62         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 1.43/1.62          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 1.43/1.62      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.43/1.62  thf('109', plain,
% 1.43/1.62      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 1.43/1.62      inference('sup-', [status(thm)], ['107', '108'])).
% 1.43/1.62  thf('110', plain,
% 1.43/1.62      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.43/1.62      inference('demod', [status(thm)], ['106', '109'])).
% 1.43/1.62  thf('111', plain,
% 1.43/1.62      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.43/1.62      inference('sup-', [status(thm)], ['103', '110'])).
% 1.43/1.62  thf('112', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.43/1.62      inference('demod', [status(thm)], ['6', '7', '8'])).
% 1.43/1.62  thf(t55_funct_1, axiom,
% 1.43/1.62    (![A:$i]:
% 1.43/1.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.43/1.62       ( ( v2_funct_1 @ A ) =>
% 1.43/1.62         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.43/1.62           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.43/1.62  thf('113', plain,
% 1.43/1.62      (![X15 : $i]:
% 1.43/1.62         (~ (v2_funct_1 @ X15)
% 1.43/1.62          | ((k2_relat_1 @ X15) = (k1_relat_1 @ (k2_funct_1 @ X15)))
% 1.43/1.62          | ~ (v1_funct_1 @ X15)
% 1.43/1.62          | ~ (v1_relat_1 @ X15))),
% 1.43/1.62      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.43/1.62  thf('114', plain,
% 1.43/1.62      ((((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))
% 1.43/1.62        | ~ (v1_relat_1 @ sk_C)
% 1.43/1.62        | ~ (v1_funct_1 @ sk_C)
% 1.43/1.62        | ~ (v2_funct_1 @ sk_C))),
% 1.43/1.62      inference('sup+', [status(thm)], ['112', '113'])).
% 1.43/1.62  thf('115', plain, ((v1_relat_1 @ sk_C)),
% 1.43/1.62      inference('sup-', [status(thm)], ['2', '3'])).
% 1.43/1.62  thf('116', plain, ((v1_funct_1 @ sk_C)),
% 1.43/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.62  thf('117', plain, ((v2_funct_1 @ sk_C)),
% 1.43/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.62  thf('118', plain,
% 1.43/1.62      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.43/1.62      inference('demod', [status(thm)], ['114', '115', '116', '117'])).
% 1.43/1.62  thf('119', plain,
% 1.43/1.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.43/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.62  thf(redefinition_k2_relset_1, axiom,
% 1.43/1.62    (![A:$i,B:$i,C:$i]:
% 1.43/1.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.43/1.62       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.43/1.62  thf('120', plain,
% 1.43/1.62      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.43/1.62         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 1.43/1.62          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 1.43/1.62      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.43/1.62  thf('121', plain,
% 1.43/1.62      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.43/1.62      inference('sup-', [status(thm)], ['119', '120'])).
% 1.43/1.62  thf('122', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.43/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.62  thf('123', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.43/1.62      inference('sup+', [status(thm)], ['121', '122'])).
% 1.43/1.62  thf('124', plain, (((sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.43/1.62      inference('demod', [status(thm)], ['118', '123'])).
% 1.43/1.62  thf(t3_funct_2, axiom,
% 1.43/1.62    (![A:$i]:
% 1.43/1.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.43/1.62       ( ( v1_funct_1 @ A ) & 
% 1.43/1.62         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.43/1.62         ( m1_subset_1 @
% 1.43/1.62           A @ 
% 1.43/1.62           ( k1_zfmisc_1 @
% 1.43/1.62             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.43/1.62  thf('125', plain,
% 1.43/1.62      (![X42 : $i]:
% 1.43/1.62         ((v1_funct_2 @ X42 @ (k1_relat_1 @ X42) @ (k2_relat_1 @ X42))
% 1.43/1.62          | ~ (v1_funct_1 @ X42)
% 1.43/1.62          | ~ (v1_relat_1 @ X42))),
% 1.43/1.62      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.43/1.62  thf('126', plain,
% 1.43/1.62      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ 
% 1.43/1.62         (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 1.43/1.62        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 1.43/1.62        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C)))),
% 1.43/1.62      inference('sup+', [status(thm)], ['124', '125'])).
% 1.43/1.62  thf('127', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.43/1.62      inference('demod', [status(thm)], ['6', '7', '8'])).
% 1.43/1.62  thf('128', plain,
% 1.43/1.62      (![X15 : $i]:
% 1.43/1.62         (~ (v2_funct_1 @ X15)
% 1.43/1.62          | ((k1_relat_1 @ X15) = (k2_relat_1 @ (k2_funct_1 @ X15)))
% 1.43/1.62          | ~ (v1_funct_1 @ X15)
% 1.43/1.62          | ~ (v1_relat_1 @ X15))),
% 1.43/1.62      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.43/1.62  thf('129', plain,
% 1.43/1.62      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 1.43/1.62        | ~ (v1_relat_1 @ sk_C)
% 1.43/1.62        | ~ (v1_funct_1 @ sk_C)
% 1.43/1.62        | ~ (v2_funct_1 @ sk_C))),
% 1.43/1.62      inference('sup+', [status(thm)], ['127', '128'])).
% 1.43/1.62  thf('130', plain, ((v1_relat_1 @ sk_C)),
% 1.43/1.62      inference('sup-', [status(thm)], ['2', '3'])).
% 1.43/1.62  thf('131', plain, ((v1_funct_1 @ sk_C)),
% 1.43/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.62  thf('132', plain, ((v2_funct_1 @ sk_C)),
% 1.43/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.62  thf('133', plain,
% 1.43/1.62      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.43/1.62      inference('demod', [status(thm)], ['129', '130', '131', '132'])).
% 1.43/1.62  thf('134', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.43/1.62      inference('demod', [status(thm)], ['6', '7', '8'])).
% 1.43/1.62  thf('135', plain,
% 1.43/1.62      (![X14 : $i]:
% 1.43/1.62         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 1.43/1.62          | ~ (v1_funct_1 @ X14)
% 1.43/1.62          | ~ (v1_relat_1 @ X14))),
% 1.43/1.62      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.43/1.62  thf('136', plain,
% 1.43/1.62      (((v1_relat_1 @ (k4_relat_1 @ sk_C))
% 1.43/1.62        | ~ (v1_relat_1 @ sk_C)
% 1.43/1.62        | ~ (v1_funct_1 @ sk_C))),
% 1.43/1.62      inference('sup+', [status(thm)], ['134', '135'])).
% 1.43/1.62  thf('137', plain, ((v1_relat_1 @ sk_C)),
% 1.43/1.62      inference('sup-', [status(thm)], ['2', '3'])).
% 1.43/1.62  thf('138', plain, ((v1_funct_1 @ sk_C)),
% 1.43/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.62  thf('139', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 1.43/1.62      inference('demod', [status(thm)], ['136', '137', '138'])).
% 1.43/1.62  thf('140', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.43/1.62      inference('demod', [status(thm)], ['6', '7', '8'])).
% 1.43/1.62  thf('141', plain,
% 1.43/1.62      (![X14 : $i]:
% 1.43/1.62         ((v1_funct_1 @ (k2_funct_1 @ X14))
% 1.43/1.62          | ~ (v1_funct_1 @ X14)
% 1.43/1.62          | ~ (v1_relat_1 @ X14))),
% 1.43/1.62      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.43/1.62  thf('142', plain,
% 1.43/1.62      (((v1_funct_1 @ (k4_relat_1 @ sk_C))
% 1.43/1.62        | ~ (v1_relat_1 @ sk_C)
% 1.43/1.62        | ~ (v1_funct_1 @ sk_C))),
% 1.43/1.62      inference('sup+', [status(thm)], ['140', '141'])).
% 1.43/1.62  thf('143', plain, ((v1_relat_1 @ sk_C)),
% 1.43/1.62      inference('sup-', [status(thm)], ['2', '3'])).
% 1.43/1.62  thf('144', plain, ((v1_funct_1 @ sk_C)),
% 1.43/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.62  thf('145', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 1.43/1.62      inference('demod', [status(thm)], ['142', '143', '144'])).
% 1.43/1.62  thf('146', plain,
% 1.43/1.62      ((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))),
% 1.43/1.62      inference('demod', [status(thm)], ['126', '133', '139', '145'])).
% 1.43/1.62  thf('147', plain,
% 1.43/1.62      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A)
% 1.43/1.62        | ((sk_B) = (k1_xboole_0)))),
% 1.43/1.62      inference('sup+', [status(thm)], ['111', '146'])).
% 1.43/1.62  thf('148', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.43/1.62      inference('demod', [status(thm)], ['6', '7', '8'])).
% 1.43/1.62  thf('149', plain,
% 1.43/1.62      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 1.43/1.62         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.43/1.62      inference('split', [status(esa)], ['0'])).
% 1.43/1.62  thf('150', plain,
% 1.43/1.62      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A))
% 1.43/1.62         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.43/1.62      inference('sup-', [status(thm)], ['148', '149'])).
% 1.43/1.62  thf('151', plain,
% 1.43/1.62      ((((sk_B) = (k1_xboole_0)))
% 1.43/1.62         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.43/1.62      inference('sup-', [status(thm)], ['147', '150'])).
% 1.43/1.62  thf('152', plain,
% 1.43/1.62      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ k1_xboole_0 @ sk_A))
% 1.43/1.62         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.43/1.62      inference('demod', [status(thm)], ['97', '98', '151'])).
% 1.43/1.62  thf('153', plain,
% 1.43/1.62      ((((sk_B) = (k1_xboole_0)))
% 1.43/1.62         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.43/1.62      inference('sup-', [status(thm)], ['147', '150'])).
% 1.43/1.62  thf('154', plain,
% 1.43/1.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.43/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.62  thf('155', plain,
% 1.43/1.62      (![X4 : $i, X5 : $i]:
% 1.43/1.62         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 1.43/1.62          | (v1_xboole_0 @ X4)
% 1.43/1.62          | ~ (v1_xboole_0 @ X5))),
% 1.43/1.62      inference('cnf', [status(esa)], [cc1_subset_1])).
% 1.43/1.62  thf('156', plain,
% 1.43/1.62      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 1.43/1.62      inference('sup-', [status(thm)], ['154', '155'])).
% 1.43/1.62  thf('157', plain,
% 1.43/1.62      (((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0))
% 1.43/1.62         | (v1_xboole_0 @ sk_C)))
% 1.43/1.62         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.43/1.62      inference('sup-', [status(thm)], ['153', '156'])).
% 1.43/1.62  thf('158', plain,
% 1.43/1.62      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 1.43/1.62      inference('simplify', [status(thm)], ['21'])).
% 1.43/1.62  thf('159', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.43/1.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.43/1.62  thf('160', plain,
% 1.43/1.62      (((v1_xboole_0 @ sk_C))
% 1.43/1.62         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.43/1.62      inference('demod', [status(thm)], ['157', '158', '159'])).
% 1.43/1.62  thf('161', plain,
% 1.43/1.62      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.43/1.62      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.43/1.62  thf('162', plain,
% 1.43/1.62      ((((sk_C) = (k1_xboole_0)))
% 1.43/1.62         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.43/1.62      inference('sup-', [status(thm)], ['160', '161'])).
% 1.43/1.62  thf('163', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.43/1.62      inference('sup-', [status(thm)], ['30', '31'])).
% 1.43/1.62  thf('164', plain,
% 1.43/1.62      (![X12 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X12)) = (k6_relat_1 @ X12))),
% 1.43/1.62      inference('cnf', [status(esa)], [t72_relat_1])).
% 1.43/1.62  thf('165', plain,
% 1.43/1.62      (((k4_relat_1 @ k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 1.43/1.62      inference('sup+', [status(thm)], ['163', '164'])).
% 1.43/1.62  thf('166', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.43/1.62      inference('sup-', [status(thm)], ['30', '31'])).
% 1.43/1.62  thf('167', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.43/1.62      inference('demod', [status(thm)], ['165', '166'])).
% 1.43/1.62  thf('168', plain,
% 1.43/1.62      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A))
% 1.43/1.62         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.43/1.62      inference('demod', [status(thm)], ['152', '162', '167'])).
% 1.43/1.62  thf('169', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 1.43/1.62      inference('sup-', [status(thm)], ['96', '168'])).
% 1.43/1.62  thf('170', plain,
% 1.43/1.62      (~
% 1.43/1.62       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.43/1.62         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 1.43/1.62       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 1.43/1.62       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.43/1.62      inference('split', [status(esa)], ['0'])).
% 1.43/1.62  thf('171', plain,
% 1.43/1.62      (~
% 1.43/1.62       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.43/1.62         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.43/1.62      inference('sat_resolution*', [status(thm)], ['17', '169', '170'])).
% 1.43/1.62  thf('172', plain,
% 1.43/1.62      (~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.43/1.62          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.43/1.62      inference('simpl_trail', [status(thm)], ['10', '171'])).
% 1.43/1.62  thf('173', plain,
% 1.43/1.62      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.43/1.62      inference('demod', [status(thm)], ['129', '130', '131', '132'])).
% 1.43/1.62  thf('174', plain,
% 1.43/1.62      (![X31 : $i, X32 : $i]:
% 1.43/1.62         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 1.43/1.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.43/1.62  thf('175', plain,
% 1.43/1.62      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 1.43/1.62      inference('simplify', [status(thm)], ['21'])).
% 1.43/1.62  thf('176', plain,
% 1.43/1.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.43/1.62         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 1.43/1.62      inference('sup+', [status(thm)], ['174', '175'])).
% 1.43/1.62  thf('177', plain,
% 1.43/1.62      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 1.43/1.62      inference('sup-', [status(thm)], ['154', '155'])).
% 1.43/1.62  thf('178', plain,
% 1.43/1.62      (![X0 : $i]:
% 1.43/1.62         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.43/1.62          | (zip_tseitin_0 @ sk_B @ X0)
% 1.43/1.62          | (v1_xboole_0 @ sk_C))),
% 1.43/1.62      inference('sup-', [status(thm)], ['176', '177'])).
% 1.43/1.62  thf('179', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.43/1.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.43/1.62  thf('180', plain,
% 1.43/1.62      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | (v1_xboole_0 @ sk_C))),
% 1.43/1.62      inference('demod', [status(thm)], ['178', '179'])).
% 1.43/1.62  thf('181', plain,
% 1.43/1.62      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.43/1.62      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.43/1.62  thf('182', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.43/1.62      inference('demod', [status(thm)], ['165', '166'])).
% 1.43/1.62  thf('183', plain,
% 1.43/1.62      (![X0 : $i]: (((k4_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.43/1.62      inference('sup+', [status(thm)], ['181', '182'])).
% 1.43/1.62  thf('184', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.43/1.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.43/1.62  thf('185', plain,
% 1.43/1.62      (![X0 : $i]: ((v1_xboole_0 @ (k4_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.43/1.62      inference('sup+', [status(thm)], ['183', '184'])).
% 1.43/1.62  thf('186', plain,
% 1.43/1.62      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.43/1.62      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.43/1.62  thf('187', plain,
% 1.43/1.62      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.43/1.62      inference('sup-', [status(thm)], ['80', '81'])).
% 1.43/1.62  thf('188', plain,
% 1.43/1.62      (![X0 : $i, X1 : $i]:
% 1.43/1.62         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 1.43/1.62      inference('sup+', [status(thm)], ['186', '187'])).
% 1.43/1.62  thf('189', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.43/1.62      inference('demod', [status(thm)], ['6', '7', '8'])).
% 1.43/1.62  thf('190', plain,
% 1.43/1.62      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.43/1.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 1.43/1.62         <= (~
% 1.43/1.62             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.43/1.62               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.43/1.62      inference('split', [status(esa)], ['0'])).
% 1.43/1.62  thf('191', plain,
% 1.43/1.62      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.43/1.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 1.43/1.62         <= (~
% 1.43/1.62             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.43/1.62               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.43/1.62      inference('sup-', [status(thm)], ['189', '190'])).
% 1.43/1.62  thf('192', plain,
% 1.43/1.62      ((~ (v1_xboole_0 @ (k4_relat_1 @ sk_C)))
% 1.43/1.62         <= (~
% 1.43/1.62             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.43/1.62               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.43/1.62      inference('sup-', [status(thm)], ['188', '191'])).
% 1.43/1.62  thf('193', plain,
% 1.43/1.62      ((~ (v1_xboole_0 @ sk_C))
% 1.43/1.62         <= (~
% 1.43/1.62             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.43/1.62               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.43/1.62      inference('sup-', [status(thm)], ['185', '192'])).
% 1.43/1.62  thf('194', plain,
% 1.43/1.62      ((![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0))
% 1.43/1.62         <= (~
% 1.43/1.62             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.43/1.62               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.43/1.62      inference('sup-', [status(thm)], ['180', '193'])).
% 1.43/1.62  thf('195', plain,
% 1.43/1.62      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.43/1.62      inference('sup-', [status(thm)], ['100', '101'])).
% 1.43/1.62  thf('196', plain,
% 1.43/1.62      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A))
% 1.43/1.62         <= (~
% 1.43/1.62             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.43/1.62               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.43/1.62      inference('sup-', [status(thm)], ['194', '195'])).
% 1.43/1.62  thf('197', plain,
% 1.43/1.62      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.43/1.62      inference('demod', [status(thm)], ['106', '109'])).
% 1.43/1.62  thf('198', plain,
% 1.43/1.62      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 1.43/1.62         <= (~
% 1.43/1.62             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.43/1.62               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.43/1.62      inference('sup-', [status(thm)], ['196', '197'])).
% 1.43/1.62  thf('199', plain,
% 1.43/1.62      (~
% 1.43/1.62       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.43/1.62         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.43/1.62      inference('sat_resolution*', [status(thm)], ['17', '169', '170'])).
% 1.43/1.62  thf('200', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 1.43/1.62      inference('simpl_trail', [status(thm)], ['198', '199'])).
% 1.43/1.62  thf('201', plain, (((sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.43/1.62      inference('demod', [status(thm)], ['173', '200'])).
% 1.43/1.62  thf('202', plain,
% 1.43/1.62      (![X42 : $i]:
% 1.43/1.62         ((m1_subset_1 @ X42 @ 
% 1.43/1.62           (k1_zfmisc_1 @ 
% 1.43/1.62            (k2_zfmisc_1 @ (k1_relat_1 @ X42) @ (k2_relat_1 @ X42))))
% 1.43/1.62          | ~ (v1_funct_1 @ X42)
% 1.43/1.62          | ~ (v1_relat_1 @ X42))),
% 1.43/1.62      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.43/1.62  thf('203', plain,
% 1.43/1.62      (((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.43/1.62         (k1_zfmisc_1 @ 
% 1.43/1.62          (k2_zfmisc_1 @ (k1_relat_1 @ (k4_relat_1 @ sk_C)) @ sk_A)))
% 1.43/1.62        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 1.43/1.62        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C)))),
% 1.43/1.62      inference('sup+', [status(thm)], ['201', '202'])).
% 1.43/1.62  thf('204', plain, (((sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.43/1.62      inference('demod', [status(thm)], ['118', '123'])).
% 1.43/1.62  thf('205', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 1.43/1.62      inference('demod', [status(thm)], ['136', '137', '138'])).
% 1.43/1.62  thf('206', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 1.43/1.62      inference('demod', [status(thm)], ['142', '143', '144'])).
% 1.43/1.62  thf('207', plain,
% 1.43/1.62      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.43/1.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.43/1.62      inference('demod', [status(thm)], ['203', '204', '205', '206'])).
% 1.43/1.62  thf('208', plain, ($false), inference('demod', [status(thm)], ['172', '207'])).
% 1.43/1.62  
% 1.43/1.62  % SZS output end Refutation
% 1.43/1.62  
% 1.43/1.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
