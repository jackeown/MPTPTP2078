%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.p48MkcBNfu

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:47 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  118 (2463 expanded)
%              Number of leaves         :   28 ( 740 expanded)
%              Depth                    :   19
%              Number of atoms          :  831 (23874 expanded)
%              Number of equality atoms :   59 ( 760 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('3',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X9 ) @ X10 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X11 )
      | ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_0 @ X17 @ X18 )
      | ( zip_tseitin_1 @ X19 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('14',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k1_relset_1 @ X7 @ X8 @ X6 )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X14
       != ( k1_relset_1 @ X14 @ X15 @ X16 ) )
      | ( v1_funct_2 @ X16 @ X14 @ X15 )
      | ~ ( zip_tseitin_1 @ X16 @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t3_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf(zf_stmt_5,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v1_funct_1 @ A )
          & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
          & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t3_funct_2])).

thf('21',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('22',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
   <= ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('24',plain,
    ( ~ ( v1_funct_1 @ sk_A )
   <= ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['21'])).

thf('25',plain,(
    v1_funct_1 @ sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('27',plain,
    ( ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['21'])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ sk_A )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('30',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['21'])).

thf('32',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['25','30','31'])).

thf('33',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['22','32'])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('36',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('38',plain,
    ( ~ ( zip_tseitin_0 @ k1_xboole_0 @ ( k1_relat_1 @ sk_A ) )
    | ( zip_tseitin_1 @ sk_A @ ( k2_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['34','35'])).

thf('40',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('41',plain,
    ( ~ ( zip_tseitin_0 @ k1_xboole_0 @ ( k1_relat_1 @ sk_A ) )
    | ( zip_tseitin_1 @ sk_A @ k1_xboole_0 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['34','35'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('43',plain,(
    ! [X5: $i] :
      ( ( ( k2_relat_1 @ X5 )
       != k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('44',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('46',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['46'])).

thf('49',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['46'])).

thf('50',plain,
    ( ~ ( zip_tseitin_0 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['41','47','48','49'])).

thf('51',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['34','35'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('53',plain,
    ( ~ ( zip_tseitin_1 @ sk_A @ k1_xboole_0 @ ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('55',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['34','35'])).

thf('56',plain,
    ( ~ ( zip_tseitin_1 @ sk_A @ k1_xboole_0 @ ( k1_relat_1 @ sk_A ) )
    | ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['46'])).

thf('58',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['46'])).

thf('59',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['46'])).

thf('60',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['46'])).

thf('61',plain,
    ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57','58','59','60'])).

thf('62',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['22','32'])).

thf('63',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['34','35'])).

thf('64',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['46'])).

thf('66',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['46'])).

thf('67',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['61','67'])).

thf('69',plain,(
    ~ ( zip_tseitin_0 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['50','68'])).

thf('70',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['34','35'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('72',plain,
    ( ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ k1_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('74',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['46'])).

thf('76',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['46'])).

thf('77',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( X17 != k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( v1_funct_2 @ X19 @ X18 @ X17 )
      | ( X19 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('79',plain,(
    ! [X18: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X18 @ k1_xboole_0 )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','79'])).

thf('81',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('82',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 )
      | ( X13 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X12: $i] :
      ( zip_tseitin_0 @ X12 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['83','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['86'])).

thf('88',plain,(
    $false ),
    inference(demod,[status(thm)],['69','82','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.p48MkcBNfu
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 18:07:06 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.40/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.58  % Solved by: fo/fo7.sh
% 0.40/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.58  % done 117 iterations in 0.089s
% 0.40/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.58  % SZS output start Refutation
% 0.40/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.40/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.58  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.40/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.58  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.40/0.58  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.40/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.40/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.58  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.40/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.58  thf(d1_funct_2, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.58       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.40/0.58           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.40/0.58             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.40/0.58         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.40/0.58           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.40/0.58             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.40/0.58  thf(zf_stmt_0, axiom,
% 0.40/0.58    (![B:$i,A:$i]:
% 0.40/0.58     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.40/0.58       ( zip_tseitin_0 @ B @ A ) ))).
% 0.40/0.58  thf('0', plain,
% 0.40/0.58      (![X12 : $i, X13 : $i]:
% 0.40/0.58         ((zip_tseitin_0 @ X12 @ X13) | ((X12) = (k1_xboole_0)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(dt_k2_subset_1, axiom,
% 0.40/0.58    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.40/0.58  thf('1', plain,
% 0.40/0.58      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.40/0.58  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.40/0.58  thf('2', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.40/0.58      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.40/0.58  thf('3', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.40/0.58      inference('demod', [status(thm)], ['1', '2'])).
% 0.40/0.58  thf(t3_subset, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.40/0.58  thf('4', plain,
% 0.40/0.58      (![X2 : $i, X3 : $i]:
% 0.40/0.58         ((r1_tarski @ X2 @ X3) | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.58  thf('5', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.40/0.58      inference('sup-', [status(thm)], ['3', '4'])).
% 0.40/0.58  thf('6', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.40/0.58      inference('sup-', [status(thm)], ['3', '4'])).
% 0.40/0.58  thf(t11_relset_1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( v1_relat_1 @ C ) =>
% 0.40/0.58       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.40/0.58           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.40/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.40/0.58  thf('7', plain,
% 0.40/0.58      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.40/0.58         (~ (r1_tarski @ (k1_relat_1 @ X9) @ X10)
% 0.40/0.58          | ~ (r1_tarski @ (k2_relat_1 @ X9) @ X11)
% 0.40/0.58          | (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.40/0.58          | ~ (v1_relat_1 @ X9))),
% 0.40/0.58      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.40/0.58  thf('8', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (~ (v1_relat_1 @ X0)
% 0.40/0.58          | (m1_subset_1 @ X0 @ 
% 0.40/0.58             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.40/0.58          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.40/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.40/0.58  thf('9', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((m1_subset_1 @ X0 @ 
% 0.40/0.58           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.40/0.58          | ~ (v1_relat_1 @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['5', '8'])).
% 0.40/0.58  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.40/0.58  thf(zf_stmt_2, axiom,
% 0.40/0.58    (![C:$i,B:$i,A:$i]:
% 0.40/0.58     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.40/0.58       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.40/0.58  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.40/0.58  thf(zf_stmt_4, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.58       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.40/0.58         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.40/0.58           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.40/0.58             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.40/0.58  thf('10', plain,
% 0.40/0.58      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.40/0.58         (~ (zip_tseitin_0 @ X17 @ X18)
% 0.40/0.58          | (zip_tseitin_1 @ X19 @ X17 @ X18)
% 0.40/0.58          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17))))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.40/0.58  thf('11', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (v1_relat_1 @ X0)
% 0.40/0.58          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.40/0.58          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['9', '10'])).
% 0.40/0.58  thf('12', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.40/0.58          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.40/0.58          | ~ (v1_relat_1 @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['0', '11'])).
% 0.40/0.58  thf('13', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((m1_subset_1 @ X0 @ 
% 0.40/0.58           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.40/0.58          | ~ (v1_relat_1 @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['5', '8'])).
% 0.40/0.58  thf(redefinition_k1_relset_1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.58       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.40/0.58  thf('14', plain,
% 0.40/0.58      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.40/0.58         (((k1_relset_1 @ X7 @ X8 @ X6) = (k1_relat_1 @ X6))
% 0.40/0.58          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.40/0.58      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.40/0.58  thf('15', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (v1_relat_1 @ X0)
% 0.40/0.58          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.40/0.58              = (k1_relat_1 @ X0)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['13', '14'])).
% 0.40/0.58  thf('16', plain,
% 0.40/0.58      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.40/0.58         (((X14) != (k1_relset_1 @ X14 @ X15 @ X16))
% 0.40/0.58          | (v1_funct_2 @ X16 @ X14 @ X15)
% 0.40/0.58          | ~ (zip_tseitin_1 @ X16 @ X15 @ X14))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.40/0.58  thf('17', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.40/0.58          | ~ (v1_relat_1 @ X0)
% 0.40/0.58          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.40/0.58          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['15', '16'])).
% 0.40/0.58  thf('18', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.40/0.58          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.40/0.58          | ~ (v1_relat_1 @ X0))),
% 0.40/0.58      inference('simplify', [status(thm)], ['17'])).
% 0.40/0.58  thf('19', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (v1_relat_1 @ X0)
% 0.40/0.58          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.40/0.58          | ~ (v1_relat_1 @ X0)
% 0.40/0.58          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['12', '18'])).
% 0.40/0.58  thf('20', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.40/0.58          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.40/0.58          | ~ (v1_relat_1 @ X0))),
% 0.40/0.58      inference('simplify', [status(thm)], ['19'])).
% 0.40/0.58  thf(t3_funct_2, conjecture,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.40/0.58       ( ( v1_funct_1 @ A ) & 
% 0.40/0.58         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.40/0.58         ( m1_subset_1 @
% 0.40/0.58           A @ 
% 0.40/0.58           ( k1_zfmisc_1 @
% 0.40/0.58             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.40/0.58  thf(zf_stmt_5, negated_conjecture,
% 0.40/0.58    (~( ![A:$i]:
% 0.40/0.58        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.40/0.58          ( ( v1_funct_1 @ A ) & 
% 0.40/0.58            ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.40/0.58            ( m1_subset_1 @
% 0.40/0.58              A @ 
% 0.40/0.58              ( k1_zfmisc_1 @
% 0.40/0.58                ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 0.40/0.58    inference('cnf.neg', [status(esa)], [t3_funct_2])).
% 0.40/0.58  thf('21', plain,
% 0.40/0.58      ((~ (v1_funct_1 @ sk_A)
% 0.40/0.58        | ~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.40/0.58        | ~ (m1_subset_1 @ sk_A @ 
% 0.40/0.58             (k1_zfmisc_1 @ 
% 0.40/0.58              (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.40/0.58  thf('22', plain,
% 0.40/0.58      ((~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 0.40/0.58         <= (~
% 0.40/0.58             ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 0.40/0.58      inference('split', [status(esa)], ['21'])).
% 0.40/0.58  thf('23', plain, ((v1_funct_1 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.40/0.58  thf('24', plain, ((~ (v1_funct_1 @ sk_A)) <= (~ ((v1_funct_1 @ sk_A)))),
% 0.40/0.58      inference('split', [status(esa)], ['21'])).
% 0.40/0.58  thf('25', plain, (((v1_funct_1 @ sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['23', '24'])).
% 0.40/0.58  thf('26', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((m1_subset_1 @ X0 @ 
% 0.40/0.58           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.40/0.58          | ~ (v1_relat_1 @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['5', '8'])).
% 0.40/0.58  thf('27', plain,
% 0.40/0.58      ((~ (m1_subset_1 @ sk_A @ 
% 0.40/0.58           (k1_zfmisc_1 @ 
% 0.40/0.58            (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))
% 0.40/0.58         <= (~
% 0.40/0.58             ((m1_subset_1 @ sk_A @ 
% 0.40/0.58               (k1_zfmisc_1 @ 
% 0.40/0.58                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.40/0.58      inference('split', [status(esa)], ['21'])).
% 0.40/0.58  thf('28', plain,
% 0.40/0.58      ((~ (v1_relat_1 @ sk_A))
% 0.40/0.58         <= (~
% 0.40/0.58             ((m1_subset_1 @ sk_A @ 
% 0.40/0.58               (k1_zfmisc_1 @ 
% 0.40/0.58                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['26', '27'])).
% 0.40/0.58  thf('29', plain, ((v1_relat_1 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.40/0.58  thf('30', plain,
% 0.40/0.58      (((m1_subset_1 @ sk_A @ 
% 0.40/0.58         (k1_zfmisc_1 @ 
% 0.40/0.58          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.40/0.58      inference('demod', [status(thm)], ['28', '29'])).
% 0.40/0.58  thf('31', plain,
% 0.40/0.58      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) | 
% 0.40/0.58       ~
% 0.40/0.58       ((m1_subset_1 @ sk_A @ 
% 0.40/0.58         (k1_zfmisc_1 @ 
% 0.40/0.58          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))) | 
% 0.40/0.58       ~ ((v1_funct_1 @ sk_A))),
% 0.40/0.58      inference('split', [status(esa)], ['21'])).
% 0.40/0.58  thf('32', plain,
% 0.40/0.58      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 0.40/0.58      inference('sat_resolution*', [status(thm)], ['25', '30', '31'])).
% 0.40/0.58  thf('33', plain,
% 0.40/0.58      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.40/0.58      inference('simpl_trail', [status(thm)], ['22', '32'])).
% 0.40/0.58  thf('34', plain,
% 0.40/0.58      ((~ (v1_relat_1 @ sk_A) | ((k2_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['20', '33'])).
% 0.40/0.58  thf('35', plain, ((v1_relat_1 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.40/0.58  thf('36', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.40/0.58      inference('demod', [status(thm)], ['34', '35'])).
% 0.40/0.58  thf('37', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (v1_relat_1 @ X0)
% 0.40/0.58          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.40/0.58          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['9', '10'])).
% 0.40/0.58  thf('38', plain,
% 0.40/0.58      ((~ (zip_tseitin_0 @ k1_xboole_0 @ (k1_relat_1 @ sk_A))
% 0.40/0.58        | (zip_tseitin_1 @ sk_A @ (k2_relat_1 @ sk_A) @ (k1_relat_1 @ sk_A))
% 0.40/0.58        | ~ (v1_relat_1 @ sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['36', '37'])).
% 0.40/0.58  thf('39', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.40/0.58      inference('demod', [status(thm)], ['34', '35'])).
% 0.40/0.58  thf('40', plain, ((v1_relat_1 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.40/0.58  thf('41', plain,
% 0.40/0.58      ((~ (zip_tseitin_0 @ k1_xboole_0 @ (k1_relat_1 @ sk_A))
% 0.40/0.58        | (zip_tseitin_1 @ sk_A @ k1_xboole_0 @ (k1_relat_1 @ sk_A)))),
% 0.40/0.58      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.40/0.58  thf('42', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.40/0.58      inference('demod', [status(thm)], ['34', '35'])).
% 0.40/0.58  thf(t64_relat_1, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( v1_relat_1 @ A ) =>
% 0.40/0.58       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.40/0.58           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.40/0.58         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.40/0.58  thf('43', plain,
% 0.40/0.58      (![X5 : $i]:
% 0.40/0.58         (((k2_relat_1 @ X5) != (k1_xboole_0))
% 0.40/0.58          | ((X5) = (k1_xboole_0))
% 0.40/0.58          | ~ (v1_relat_1 @ X5))),
% 0.40/0.58      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.40/0.58  thf('44', plain,
% 0.40/0.58      ((((k1_xboole_0) != (k1_xboole_0))
% 0.40/0.58        | ~ (v1_relat_1 @ sk_A)
% 0.40/0.58        | ((sk_A) = (k1_xboole_0)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['42', '43'])).
% 0.40/0.58  thf('45', plain, ((v1_relat_1 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.40/0.58  thf('46', plain,
% 0.40/0.58      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.40/0.58      inference('demod', [status(thm)], ['44', '45'])).
% 0.40/0.58  thf('47', plain, (((sk_A) = (k1_xboole_0))),
% 0.40/0.58      inference('simplify', [status(thm)], ['46'])).
% 0.40/0.58  thf('48', plain, (((sk_A) = (k1_xboole_0))),
% 0.40/0.58      inference('simplify', [status(thm)], ['46'])).
% 0.40/0.58  thf('49', plain, (((sk_A) = (k1_xboole_0))),
% 0.40/0.58      inference('simplify', [status(thm)], ['46'])).
% 0.40/0.58  thf('50', plain,
% 0.40/0.58      ((~ (zip_tseitin_0 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0))
% 0.40/0.58        | (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 0.40/0.58           (k1_relat_1 @ k1_xboole_0)))),
% 0.40/0.58      inference('demod', [status(thm)], ['41', '47', '48', '49'])).
% 0.40/0.58  thf('51', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.40/0.58      inference('demod', [status(thm)], ['34', '35'])).
% 0.40/0.58  thf('52', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.40/0.58          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.40/0.58          | ~ (v1_relat_1 @ X0))),
% 0.40/0.58      inference('simplify', [status(thm)], ['17'])).
% 0.40/0.58  thf('53', plain,
% 0.40/0.58      ((~ (zip_tseitin_1 @ sk_A @ k1_xboole_0 @ (k1_relat_1 @ sk_A))
% 0.40/0.58        | ~ (v1_relat_1 @ sk_A)
% 0.40/0.58        | (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['51', '52'])).
% 0.40/0.58  thf('54', plain, ((v1_relat_1 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.40/0.58  thf('55', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.40/0.58      inference('demod', [status(thm)], ['34', '35'])).
% 0.40/0.58  thf('56', plain,
% 0.40/0.58      ((~ (zip_tseitin_1 @ sk_A @ k1_xboole_0 @ (k1_relat_1 @ sk_A))
% 0.40/0.58        | (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ k1_xboole_0))),
% 0.40/0.58      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.40/0.58  thf('57', plain, (((sk_A) = (k1_xboole_0))),
% 0.40/0.58      inference('simplify', [status(thm)], ['46'])).
% 0.40/0.58  thf('58', plain, (((sk_A) = (k1_xboole_0))),
% 0.40/0.58      inference('simplify', [status(thm)], ['46'])).
% 0.40/0.58  thf('59', plain, (((sk_A) = (k1_xboole_0))),
% 0.40/0.58      inference('simplify', [status(thm)], ['46'])).
% 0.40/0.58  thf('60', plain, (((sk_A) = (k1_xboole_0))),
% 0.40/0.58      inference('simplify', [status(thm)], ['46'])).
% 0.40/0.58  thf('61', plain,
% 0.40/0.58      ((~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 0.40/0.58           (k1_relat_1 @ k1_xboole_0))
% 0.40/0.58        | (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0))),
% 0.40/0.58      inference('demod', [status(thm)], ['56', '57', '58', '59', '60'])).
% 0.40/0.58  thf('62', plain,
% 0.40/0.58      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.40/0.58      inference('simpl_trail', [status(thm)], ['22', '32'])).
% 0.40/0.58  thf('63', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.40/0.58      inference('demod', [status(thm)], ['34', '35'])).
% 0.40/0.58  thf('64', plain, (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ k1_xboole_0)),
% 0.40/0.58      inference('demod', [status(thm)], ['62', '63'])).
% 0.40/0.58  thf('65', plain, (((sk_A) = (k1_xboole_0))),
% 0.40/0.58      inference('simplify', [status(thm)], ['46'])).
% 0.40/0.58  thf('66', plain, (((sk_A) = (k1_xboole_0))),
% 0.40/0.58      inference('simplify', [status(thm)], ['46'])).
% 0.40/0.58  thf('67', plain,
% 0.40/0.58      (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 0.40/0.58      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.40/0.58  thf('68', plain,
% 0.40/0.58      (~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 0.40/0.58          (k1_relat_1 @ k1_xboole_0))),
% 0.40/0.58      inference('clc', [status(thm)], ['61', '67'])).
% 0.40/0.58  thf('69', plain,
% 0.40/0.58      (~ (zip_tseitin_0 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0))),
% 0.40/0.58      inference('clc', [status(thm)], ['50', '68'])).
% 0.40/0.58  thf('70', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.40/0.58      inference('demod', [status(thm)], ['34', '35'])).
% 0.40/0.58  thf('71', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((m1_subset_1 @ X0 @ 
% 0.40/0.58           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.40/0.58          | ~ (v1_relat_1 @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['5', '8'])).
% 0.40/0.58  thf('72', plain,
% 0.40/0.58      (((m1_subset_1 @ sk_A @ 
% 0.40/0.58         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ k1_xboole_0)))
% 0.40/0.58        | ~ (v1_relat_1 @ sk_A))),
% 0.40/0.58      inference('sup+', [status(thm)], ['70', '71'])).
% 0.40/0.58  thf('73', plain, ((v1_relat_1 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.40/0.58  thf('74', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_A @ 
% 0.40/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ k1_xboole_0)))),
% 0.40/0.58      inference('demod', [status(thm)], ['72', '73'])).
% 0.40/0.58  thf('75', plain, (((sk_A) = (k1_xboole_0))),
% 0.40/0.58      inference('simplify', [status(thm)], ['46'])).
% 0.40/0.58  thf('76', plain, (((sk_A) = (k1_xboole_0))),
% 0.40/0.58      inference('simplify', [status(thm)], ['46'])).
% 0.40/0.58  thf('77', plain,
% 0.40/0.58      ((m1_subset_1 @ k1_xboole_0 @ 
% 0.40/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)))),
% 0.40/0.58      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.40/0.58  thf('78', plain,
% 0.40/0.58      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.40/0.58         (((X17) != (k1_xboole_0))
% 0.40/0.58          | ((X18) = (k1_xboole_0))
% 0.40/0.58          | (v1_funct_2 @ X19 @ X18 @ X17)
% 0.40/0.58          | ((X19) != (k1_xboole_0))
% 0.40/0.58          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17))))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.40/0.58  thf('79', plain,
% 0.40/0.58      (![X18 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 0.40/0.58             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ k1_xboole_0)))
% 0.40/0.58          | (v1_funct_2 @ k1_xboole_0 @ X18 @ k1_xboole_0)
% 0.40/0.58          | ((X18) = (k1_xboole_0)))),
% 0.40/0.58      inference('simplify', [status(thm)], ['78'])).
% 0.40/0.58  thf('80', plain,
% 0.40/0.58      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.40/0.58        | (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['77', '79'])).
% 0.40/0.58  thf('81', plain,
% 0.40/0.58      (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 0.40/0.58      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.40/0.58  thf('82', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.58      inference('clc', [status(thm)], ['80', '81'])).
% 0.40/0.58  thf('83', plain,
% 0.40/0.58      (![X12 : $i, X13 : $i]:
% 0.40/0.58         ((zip_tseitin_0 @ X12 @ X13) | ((X12) = (k1_xboole_0)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('84', plain,
% 0.40/0.58      (![X12 : $i, X13 : $i]:
% 0.40/0.58         ((zip_tseitin_0 @ X12 @ X13) | ((X13) != (k1_xboole_0)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('85', plain, (![X12 : $i]: (zip_tseitin_0 @ X12 @ k1_xboole_0)),
% 0.40/0.58      inference('simplify', [status(thm)], ['84'])).
% 0.40/0.58  thf('86', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.58         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.40/0.58      inference('sup+', [status(thm)], ['83', '85'])).
% 0.40/0.58  thf('87', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.40/0.58      inference('eq_fact', [status(thm)], ['86'])).
% 0.40/0.58  thf('88', plain, ($false),
% 0.40/0.58      inference('demod', [status(thm)], ['69', '82', '87'])).
% 0.40/0.58  
% 0.40/0.58  % SZS output end Refutation
% 0.40/0.58  
% 0.40/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
