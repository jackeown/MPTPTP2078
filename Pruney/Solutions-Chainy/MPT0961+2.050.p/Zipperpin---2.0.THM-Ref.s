%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Wfn6HiVVI1

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:45 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 344 expanded)
%              Number of leaves         :   30 ( 104 expanded)
%              Depth                    :   15
%              Number of atoms          :  755 (3743 expanded)
%              Number of equality atoms :   60 ( 156 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t3_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v1_funct_1 @ A )
          & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
          & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t3_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
   <= ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_A )
   <= ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    v1_funct_1 @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X10 ) @ X11 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X10 ) @ X12 )
      | ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,
    ( ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ sk_A )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['4','14','15'])).

thf('17',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','16'])).

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

thf('18',plain,(
    ! [X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

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

thf('20',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( zip_tseitin_0 @ X19 @ X20 )
      | ( zip_tseitin_1 @ X21 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('24',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X16
       != ( k1_relset_1 @ X16 @ X17 @ X18 ) )
      | ( v1_funct_2 @ X18 @ X16 @ X17 )
      | ~ ( zip_tseitin_1 @ X18 @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','16'])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','34'])).

thf('36',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['32','33'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('37',plain,(
    ! [X6: $i] :
      ( ( ( k2_relat_1 @ X6 )
       != k1_xboole_0 )
      | ( X6 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('38',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['40'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('43',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('44',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('45',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('46',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k1_relat_1 @ ( k6_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('50',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('51',plain,
    ( ( k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X16
       != ( k1_relset_1 @ X16 @ X17 @ X18 ) )
      | ( v1_funct_2 @ X18 @ X16 @ X17 )
      | ~ ( zip_tseitin_1 @ X18 @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('53',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    | ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('55',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('56',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('57',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('58',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','58'])).

thf('60',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('61',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( zip_tseitin_0 @ X19 @ X20 )
      | ( zip_tseitin_1 @ X21 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 )
      | ( X15 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('64',plain,(
    ! [X14: $i] :
      ( zip_tseitin_0 @ X14 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['62','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','65'])).

thf('67',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','66'])).

thf('68',plain,(
    v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['35','41','42','43','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Wfn6HiVVI1
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:01:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.47/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.69  % Solved by: fo/fo7.sh
% 0.47/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.69  % done 137 iterations in 0.201s
% 0.47/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.69  % SZS output start Refutation
% 0.47/0.69  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.69  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.47/0.69  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.47/0.69  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.47/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.69  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.69  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.69  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.69  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.47/0.69  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.69  thf(t3_funct_2, conjecture,
% 0.47/0.69    (![A:$i]:
% 0.47/0.69     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.69       ( ( v1_funct_1 @ A ) & 
% 0.47/0.69         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.47/0.69         ( m1_subset_1 @
% 0.47/0.69           A @ 
% 0.47/0.69           ( k1_zfmisc_1 @
% 0.47/0.69             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.47/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.69    (~( ![A:$i]:
% 0.47/0.69        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.69          ( ( v1_funct_1 @ A ) & 
% 0.47/0.69            ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.47/0.69            ( m1_subset_1 @
% 0.47/0.69              A @ 
% 0.47/0.69              ( k1_zfmisc_1 @
% 0.47/0.69                ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 0.47/0.69    inference('cnf.neg', [status(esa)], [t3_funct_2])).
% 0.47/0.69  thf('0', plain,
% 0.47/0.69      ((~ (v1_funct_1 @ sk_A)
% 0.47/0.69        | ~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.47/0.69        | ~ (m1_subset_1 @ sk_A @ 
% 0.47/0.69             (k1_zfmisc_1 @ 
% 0.47/0.69              (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('1', plain,
% 0.47/0.69      ((~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 0.47/0.69         <= (~
% 0.47/0.69             ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 0.47/0.69      inference('split', [status(esa)], ['0'])).
% 0.47/0.69  thf('2', plain, ((v1_funct_1 @ sk_A)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('3', plain, ((~ (v1_funct_1 @ sk_A)) <= (~ ((v1_funct_1 @ sk_A)))),
% 0.47/0.69      inference('split', [status(esa)], ['0'])).
% 0.47/0.69  thf('4', plain, (((v1_funct_1 @ sk_A))),
% 0.47/0.69      inference('sup-', [status(thm)], ['2', '3'])).
% 0.47/0.69  thf(d10_xboole_0, axiom,
% 0.47/0.69    (![A:$i,B:$i]:
% 0.47/0.69     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.69  thf('5', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.47/0.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.69  thf('6', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.47/0.69      inference('simplify', [status(thm)], ['5'])).
% 0.47/0.69  thf('7', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.47/0.69      inference('simplify', [status(thm)], ['5'])).
% 0.47/0.69  thf(t11_relset_1, axiom,
% 0.47/0.69    (![A:$i,B:$i,C:$i]:
% 0.47/0.69     ( ( v1_relat_1 @ C ) =>
% 0.47/0.69       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.47/0.69           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.47/0.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.47/0.69  thf('8', plain,
% 0.47/0.69      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.47/0.69         (~ (r1_tarski @ (k1_relat_1 @ X10) @ X11)
% 0.47/0.69          | ~ (r1_tarski @ (k2_relat_1 @ X10) @ X12)
% 0.47/0.69          | (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.47/0.69          | ~ (v1_relat_1 @ X10))),
% 0.47/0.69      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.47/0.69  thf('9', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]:
% 0.47/0.69         (~ (v1_relat_1 @ X0)
% 0.47/0.69          | (m1_subset_1 @ X0 @ 
% 0.47/0.69             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.47/0.69          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.47/0.69      inference('sup-', [status(thm)], ['7', '8'])).
% 0.47/0.69  thf('10', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         ((m1_subset_1 @ X0 @ 
% 0.47/0.69           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.47/0.69          | ~ (v1_relat_1 @ X0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['6', '9'])).
% 0.47/0.69  thf('11', plain,
% 0.47/0.69      ((~ (m1_subset_1 @ sk_A @ 
% 0.47/0.69           (k1_zfmisc_1 @ 
% 0.47/0.69            (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))
% 0.47/0.69         <= (~
% 0.47/0.69             ((m1_subset_1 @ sk_A @ 
% 0.47/0.69               (k1_zfmisc_1 @ 
% 0.47/0.69                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.47/0.69      inference('split', [status(esa)], ['0'])).
% 0.47/0.69  thf('12', plain,
% 0.47/0.69      ((~ (v1_relat_1 @ sk_A))
% 0.47/0.69         <= (~
% 0.47/0.69             ((m1_subset_1 @ sk_A @ 
% 0.47/0.69               (k1_zfmisc_1 @ 
% 0.47/0.69                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.47/0.69      inference('sup-', [status(thm)], ['10', '11'])).
% 0.47/0.69  thf('13', plain, ((v1_relat_1 @ sk_A)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('14', plain,
% 0.47/0.69      (((m1_subset_1 @ sk_A @ 
% 0.47/0.69         (k1_zfmisc_1 @ 
% 0.47/0.69          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.47/0.69      inference('demod', [status(thm)], ['12', '13'])).
% 0.47/0.69  thf('15', plain,
% 0.47/0.69      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) | 
% 0.47/0.69       ~
% 0.47/0.69       ((m1_subset_1 @ sk_A @ 
% 0.47/0.69         (k1_zfmisc_1 @ 
% 0.47/0.69          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))) | 
% 0.47/0.69       ~ ((v1_funct_1 @ sk_A))),
% 0.47/0.69      inference('split', [status(esa)], ['0'])).
% 0.47/0.69  thf('16', plain,
% 0.47/0.69      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 0.47/0.69      inference('sat_resolution*', [status(thm)], ['4', '14', '15'])).
% 0.47/0.69  thf('17', plain,
% 0.47/0.69      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.47/0.69      inference('simpl_trail', [status(thm)], ['1', '16'])).
% 0.47/0.69  thf(d1_funct_2, axiom,
% 0.47/0.69    (![A:$i,B:$i,C:$i]:
% 0.47/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.69       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.47/0.69           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.47/0.69             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.47/0.69         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.69           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.47/0.69             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.47/0.69  thf(zf_stmt_1, axiom,
% 0.47/0.69    (![B:$i,A:$i]:
% 0.47/0.69     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.69       ( zip_tseitin_0 @ B @ A ) ))).
% 0.47/0.69  thf('18', plain,
% 0.47/0.69      (![X14 : $i, X15 : $i]:
% 0.47/0.69         ((zip_tseitin_0 @ X14 @ X15) | ((X14) = (k1_xboole_0)))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.47/0.69  thf('19', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         ((m1_subset_1 @ X0 @ 
% 0.47/0.69           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.47/0.69          | ~ (v1_relat_1 @ X0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['6', '9'])).
% 0.47/0.69  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.47/0.69  thf(zf_stmt_3, axiom,
% 0.47/0.69    (![C:$i,B:$i,A:$i]:
% 0.47/0.69     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.47/0.69       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.47/0.69  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.47/0.69  thf(zf_stmt_5, axiom,
% 0.47/0.69    (![A:$i,B:$i,C:$i]:
% 0.47/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.69       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.47/0.69         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.47/0.69           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.47/0.69             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.47/0.69  thf('20', plain,
% 0.47/0.69      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.47/0.69         (~ (zip_tseitin_0 @ X19 @ X20)
% 0.47/0.69          | (zip_tseitin_1 @ X21 @ X19 @ X20)
% 0.47/0.69          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19))))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.47/0.69  thf('21', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (~ (v1_relat_1 @ X0)
% 0.47/0.69          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.47/0.69          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['19', '20'])).
% 0.47/0.69  thf('22', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.47/0.69          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.47/0.69          | ~ (v1_relat_1 @ X0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['18', '21'])).
% 0.47/0.69  thf('23', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         ((m1_subset_1 @ X0 @ 
% 0.47/0.69           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.47/0.69          | ~ (v1_relat_1 @ X0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['6', '9'])).
% 0.47/0.69  thf(redefinition_k1_relset_1, axiom,
% 0.47/0.69    (![A:$i,B:$i,C:$i]:
% 0.47/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.69       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.47/0.69  thf('24', plain,
% 0.47/0.69      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.47/0.69         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 0.47/0.69          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.47/0.69      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.47/0.69  thf('25', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (~ (v1_relat_1 @ X0)
% 0.47/0.69          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.47/0.69              = (k1_relat_1 @ X0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['23', '24'])).
% 0.47/0.69  thf('26', plain,
% 0.47/0.69      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.47/0.69         (((X16) != (k1_relset_1 @ X16 @ X17 @ X18))
% 0.47/0.69          | (v1_funct_2 @ X18 @ X16 @ X17)
% 0.47/0.69          | ~ (zip_tseitin_1 @ X18 @ X17 @ X16))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.47/0.69  thf('27', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.47/0.69          | ~ (v1_relat_1 @ X0)
% 0.47/0.69          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.47/0.69          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['25', '26'])).
% 0.47/0.69  thf('28', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.47/0.69          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.47/0.69          | ~ (v1_relat_1 @ X0))),
% 0.47/0.69      inference('simplify', [status(thm)], ['27'])).
% 0.47/0.69  thf('29', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (~ (v1_relat_1 @ X0)
% 0.47/0.69          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.47/0.69          | ~ (v1_relat_1 @ X0)
% 0.47/0.69          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['22', '28'])).
% 0.47/0.69  thf('30', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.47/0.69          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.47/0.69          | ~ (v1_relat_1 @ X0))),
% 0.47/0.69      inference('simplify', [status(thm)], ['29'])).
% 0.47/0.69  thf('31', plain,
% 0.47/0.69      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.47/0.69      inference('simpl_trail', [status(thm)], ['1', '16'])).
% 0.47/0.69  thf('32', plain,
% 0.47/0.69      ((~ (v1_relat_1 @ sk_A) | ((k2_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['30', '31'])).
% 0.47/0.69  thf('33', plain, ((v1_relat_1 @ sk_A)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('34', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.47/0.69      inference('demod', [status(thm)], ['32', '33'])).
% 0.47/0.69  thf('35', plain, (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ k1_xboole_0)),
% 0.47/0.69      inference('demod', [status(thm)], ['17', '34'])).
% 0.47/0.69  thf('36', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.47/0.69      inference('demod', [status(thm)], ['32', '33'])).
% 0.47/0.69  thf(t64_relat_1, axiom,
% 0.47/0.69    (![A:$i]:
% 0.47/0.69     ( ( v1_relat_1 @ A ) =>
% 0.47/0.69       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.47/0.69           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.69         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.47/0.69  thf('37', plain,
% 0.47/0.69      (![X6 : $i]:
% 0.47/0.69         (((k2_relat_1 @ X6) != (k1_xboole_0))
% 0.47/0.69          | ((X6) = (k1_xboole_0))
% 0.47/0.69          | ~ (v1_relat_1 @ X6))),
% 0.47/0.69      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.47/0.69  thf('38', plain,
% 0.47/0.69      ((((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.69        | ~ (v1_relat_1 @ sk_A)
% 0.47/0.69        | ((sk_A) = (k1_xboole_0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['36', '37'])).
% 0.47/0.69  thf('39', plain, ((v1_relat_1 @ sk_A)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('40', plain,
% 0.47/0.69      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.47/0.69      inference('demod', [status(thm)], ['38', '39'])).
% 0.47/0.69  thf('41', plain, (((sk_A) = (k1_xboole_0))),
% 0.47/0.69      inference('simplify', [status(thm)], ['40'])).
% 0.47/0.69  thf('42', plain, (((sk_A) = (k1_xboole_0))),
% 0.47/0.69      inference('simplify', [status(thm)], ['40'])).
% 0.47/0.69  thf(t60_relat_1, axiom,
% 0.47/0.69    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.47/0.69     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.47/0.69  thf('43', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.69      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.47/0.69  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.47/0.69  thf('44', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.69      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.47/0.69  thf(t29_relset_1, axiom,
% 0.47/0.69    (![A:$i]:
% 0.47/0.69     ( m1_subset_1 @
% 0.47/0.69       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.47/0.69  thf('45', plain,
% 0.47/0.69      (![X13 : $i]:
% 0.47/0.69         (m1_subset_1 @ (k6_relat_1 @ X13) @ 
% 0.47/0.69          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X13)))),
% 0.47/0.69      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.47/0.69  thf('46', plain,
% 0.47/0.69      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.47/0.69         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 0.47/0.69          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.47/0.69      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.47/0.69  thf('47', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         ((k1_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0))
% 0.47/0.69           = (k1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['45', '46'])).
% 0.47/0.69  thf('48', plain,
% 0.47/0.69      (((k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.47/0.69         = (k1_relat_1 @ (k6_relat_1 @ k1_xboole_0)))),
% 0.47/0.69      inference('sup+', [status(thm)], ['44', '47'])).
% 0.47/0.69  thf('49', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.69      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.47/0.69  thf('50', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.69      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.47/0.69  thf('51', plain,
% 0.47/0.69      (((k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.69      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.47/0.69  thf('52', plain,
% 0.47/0.69      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.47/0.69         (((X16) != (k1_relset_1 @ X16 @ X17 @ X18))
% 0.47/0.69          | (v1_funct_2 @ X18 @ X16 @ X17)
% 0.47/0.69          | ~ (zip_tseitin_1 @ X18 @ X17 @ X16))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.47/0.69  thf('53', plain,
% 0.47/0.69      ((((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.69        | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.47/0.69        | (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['51', '52'])).
% 0.47/0.69  thf('54', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.69      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.47/0.69  thf('55', plain,
% 0.47/0.69      (![X13 : $i]:
% 0.47/0.69         (m1_subset_1 @ (k6_relat_1 @ X13) @ 
% 0.47/0.69          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X13)))),
% 0.47/0.69      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.47/0.69  thf('56', plain,
% 0.47/0.69      ((m1_subset_1 @ k1_xboole_0 @ 
% 0.47/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.47/0.69      inference('sup+', [status(thm)], ['54', '55'])).
% 0.47/0.69  thf(t113_zfmisc_1, axiom,
% 0.47/0.69    (![A:$i,B:$i]:
% 0.47/0.69     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.47/0.69       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.47/0.69  thf('57', plain,
% 0.47/0.69      (![X4 : $i, X5 : $i]:
% 0.47/0.69         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 0.47/0.69      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.47/0.69  thf('58', plain,
% 0.47/0.69      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.47/0.69      inference('simplify', [status(thm)], ['57'])).
% 0.47/0.69  thf('59', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.47/0.69      inference('demod', [status(thm)], ['56', '58'])).
% 0.47/0.69  thf('60', plain,
% 0.47/0.69      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.47/0.69      inference('simplify', [status(thm)], ['57'])).
% 0.47/0.69  thf('61', plain,
% 0.47/0.69      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.47/0.69         (~ (zip_tseitin_0 @ X19 @ X20)
% 0.47/0.69          | (zip_tseitin_1 @ X21 @ X19 @ X20)
% 0.47/0.69          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19))))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.47/0.69  thf('62', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]:
% 0.47/0.69         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.47/0.69          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0)
% 0.47/0.69          | ~ (zip_tseitin_0 @ X0 @ k1_xboole_0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['60', '61'])).
% 0.47/0.69  thf('63', plain,
% 0.47/0.69      (![X14 : $i, X15 : $i]:
% 0.47/0.69         ((zip_tseitin_0 @ X14 @ X15) | ((X15) != (k1_xboole_0)))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.47/0.69  thf('64', plain, (![X14 : $i]: (zip_tseitin_0 @ X14 @ k1_xboole_0)),
% 0.47/0.69      inference('simplify', [status(thm)], ['63'])).
% 0.47/0.69  thf('65', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]:
% 0.47/0.69         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.47/0.69          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0))),
% 0.47/0.69      inference('demod', [status(thm)], ['62', '64'])).
% 0.47/0.69  thf('66', plain,
% 0.47/0.69      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.47/0.69      inference('sup-', [status(thm)], ['59', '65'])).
% 0.47/0.69  thf('67', plain,
% 0.47/0.69      ((((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.69        | (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.47/0.69      inference('demod', [status(thm)], ['53', '66'])).
% 0.47/0.69  thf('68', plain, ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.47/0.69      inference('simplify', [status(thm)], ['67'])).
% 0.47/0.69  thf('69', plain, ($false),
% 0.47/0.69      inference('demod', [status(thm)], ['35', '41', '42', '43', '68'])).
% 0.47/0.69  
% 0.47/0.69  % SZS output end Refutation
% 0.47/0.69  
% 0.47/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
