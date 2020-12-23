%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tzotGwBDZr

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:02 EST 2020

% Result     : Theorem 9.72s
% Output     : Refutation 9.72s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 278 expanded)
%              Number of leaves         :   46 ( 101 expanded)
%              Depth                    :   15
%              Number of atoms          : 1524 (5874 expanded)
%              Number of equality atoms :   67 (  89 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('0',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 )
      | ( X4 = X5 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_zfmisc_1 @ X7 @ X8 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('6',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('13',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( r2_relset_1 @ X25 @ X26 @ X24 @ X27 )
      | ( X24 != X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('14',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_relset_1 @ X25 @ X26 @ X27 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['6','15'])).

thf('17',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_relset_1 @ X3 @ X2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','20'])).

thf(t87_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( v3_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ ( k6_partfun1 @ A ) )
           => ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( v3_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ A )
              & ( v3_funct_2 @ C @ A @ A )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ ( k6_partfun1 @ A ) )
             => ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_funct_2])).

thf('22',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k2_funct_2 @ A @ B )
        = ( k2_funct_1 @ B ) ) ) )).

thf('24',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k2_funct_2 @ X43 @ X42 )
        = ( k2_funct_1 @ X42 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X43 ) ) )
      | ~ ( v3_funct_2 @ X42 @ X43 @ X43 )
      | ~ ( v1_funct_2 @ X42 @ X43 @ X43 )
      | ~ ( v1_funct_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('25',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B )
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','29'])).

thf('31',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('33',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X20 ) ) )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('34',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['31','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) )
        & ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A )
        & ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A )
        & ( m1_subset_1 @ ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ) )).

thf('37',plain,(
    ! [X40: $i,X41: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X40 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X40 ) ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X40 ) ) )
      | ~ ( v3_funct_2 @ X41 @ X40 @ X40 )
      | ~ ( v1_funct_2 @ X41 @ X40 @ X40 )
      | ~ ( v1_funct_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('38',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39','40','41'])).

thf('43',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X20 ) ) )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( k2_funct_2 @ sk_A @ sk_B ) )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['35','46'])).

thf('48',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C_1 ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('49',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('50',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C_1 ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('53',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( X24 = X27 )
      | ~ ( r2_relset_1 @ X25 @ X26 @ X24 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C_1 )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C_1 )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','61'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('63',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('64',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C_1 )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ C )
                = B )
              & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
              & ( v2_funct_1 @ C ) )
           => ( ( A = k1_xboole_0 )
              | ( B = k1_xboole_0 )
              | ( D
                = ( k2_funct_1 @ C ) ) ) ) ) ) )).

thf('66',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X51 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ( X49
        = ( k2_funct_1 @ X52 ) )
      | ~ ( r2_relset_1 @ X51 @ X51 @ ( k1_partfun1 @ X51 @ X50 @ X50 @ X51 @ X52 @ X49 ) @ ( k6_partfun1 @ X51 ) )
      | ( X50 = k1_xboole_0 )
      | ( X51 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X52 )
      | ( ( k2_relset_1 @ X51 @ X50 @ X52 )
       != X50 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X50 ) ) )
      | ~ ( v1_funct_2 @ X52 @ X51 @ X50 )
      | ~ ( v1_funct_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t36_funct_2])).

thf('67',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('68',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X51 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ( X49
        = ( k2_funct_1 @ X52 ) )
      | ~ ( r2_relset_1 @ X51 @ X51 @ ( k1_partfun1 @ X51 @ X50 @ X50 @ X51 @ X52 @ X49 ) @ ( k6_relat_1 @ X51 ) )
      | ( X50 = k1_xboole_0 )
      | ( X51 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X52 )
      | ( ( k2_relset_1 @ X51 @ X50 @ X52 )
       != X50 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X50 ) ) )
      | ~ ( v1_funct_2 @ X52 @ X51 @ X50 )
      | ~ ( v1_funct_1 @ X52 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C_1 ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_C_1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C_1 ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_C_1
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( sk_C_1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C_1 ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C_1
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','73'])).

thf('75',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('76',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_relset_1 @ X25 @ X26 @ X27 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('77',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('82',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('83',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) ) ) ) )).

thf('85',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_1 @ X29 )
      | ~ ( v3_funct_2 @ X29 @ X30 @ X31 )
      | ( v2_funct_2 @ X29 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('86',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['86','87','88'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('90',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v2_funct_2 @ X33 @ X32 )
      | ( ( k2_relat_1 @ X33 )
        = X32 )
      | ~ ( v5_relat_1 @ X33 @ X32 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('91',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('93',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('94',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('96',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v5_relat_1 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('97',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['91','94','97'])).

thf('99',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['83','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_1 @ X29 )
      | ~ ( v3_funct_2 @ X29 @ X30 @ X31 )
      | ( v2_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('102',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,
    ( ( sk_A != sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C_1
      = ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['74','77','78','79','80','99','105'])).

thf('107',plain,
    ( ( sk_C_1
      = ( k2_funct_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','29'])).

thf('109',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_relset_1 @ X25 @ X26 @ X27 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('112',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['109','112'])).

thf('114',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('115',plain,(
    $false ),
    inference(demod,[status(thm)],['47','113','114'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tzotGwBDZr
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:35:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 9.72/9.90  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 9.72/9.90  % Solved by: fo/fo7.sh
% 9.72/9.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.72/9.90  % done 11058 iterations in 9.446s
% 9.72/9.90  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 9.72/9.90  % SZS output start Refutation
% 9.72/9.90  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 9.72/9.90  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 9.72/9.90  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 9.72/9.90  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 9.72/9.90  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 9.72/9.90  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 9.72/9.90  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 9.72/9.90  thf(sk_B_type, type, sk_B: $i).
% 9.72/9.90  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 9.72/9.90  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 9.72/9.90  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 9.72/9.90  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 9.72/9.90  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 9.72/9.90  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 9.72/9.90  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 9.72/9.90  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 9.72/9.90  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 9.72/9.90  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 9.72/9.90  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 9.72/9.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 9.72/9.90  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 9.72/9.90  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 9.72/9.90  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 9.72/9.90  thf(sk_C_1_type, type, sk_C_1: $i).
% 9.72/9.90  thf(sk_A_type, type, sk_A: $i).
% 9.72/9.90  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 9.72/9.90  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 9.72/9.90  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 9.72/9.90  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 9.72/9.90      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 9.72/9.90  thf(t8_boole, axiom,
% 9.72/9.90    (![A:$i,B:$i]:
% 9.72/9.90     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 9.72/9.90  thf('1', plain,
% 9.72/9.90      (![X4 : $i, X5 : $i]:
% 9.72/9.90         (~ (v1_xboole_0 @ X4) | ~ (v1_xboole_0 @ X5) | ((X4) = (X5)))),
% 9.72/9.90      inference('cnf', [status(esa)], [t8_boole])).
% 9.72/9.90  thf('2', plain,
% 9.72/9.90      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 9.72/9.90      inference('sup-', [status(thm)], ['0', '1'])).
% 9.72/9.90  thf('3', plain,
% 9.72/9.90      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 9.72/9.90      inference('sup-', [status(thm)], ['0', '1'])).
% 9.72/9.90  thf('4', plain,
% 9.72/9.90      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 9.72/9.90      inference('sup-', [status(thm)], ['0', '1'])).
% 9.72/9.90  thf(t113_zfmisc_1, axiom,
% 9.72/9.90    (![A:$i,B:$i]:
% 9.72/9.90     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 9.72/9.90       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 9.72/9.90  thf('5', plain,
% 9.72/9.90      (![X7 : $i, X8 : $i]:
% 9.72/9.90         (((k2_zfmisc_1 @ X7 @ X8) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 9.72/9.90      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 9.72/9.90  thf('6', plain,
% 9.72/9.90      (![X7 : $i]: ((k2_zfmisc_1 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 9.72/9.90      inference('simplify', [status(thm)], ['5'])).
% 9.72/9.90  thf(d3_tarski, axiom,
% 9.72/9.90    (![A:$i,B:$i]:
% 9.72/9.90     ( ( r1_tarski @ A @ B ) <=>
% 9.72/9.90       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 9.72/9.90  thf('7', plain,
% 9.72/9.90      (![X1 : $i, X3 : $i]:
% 9.72/9.90         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 9.72/9.90      inference('cnf', [status(esa)], [d3_tarski])).
% 9.72/9.90  thf('8', plain,
% 9.72/9.90      (![X1 : $i, X3 : $i]:
% 9.72/9.90         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 9.72/9.90      inference('cnf', [status(esa)], [d3_tarski])).
% 9.72/9.90  thf('9', plain,
% 9.72/9.90      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 9.72/9.90      inference('sup-', [status(thm)], ['7', '8'])).
% 9.72/9.90  thf('10', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 9.72/9.90      inference('simplify', [status(thm)], ['9'])).
% 9.72/9.90  thf(t3_subset, axiom,
% 9.72/9.90    (![A:$i,B:$i]:
% 9.72/9.90     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 9.72/9.90  thf('11', plain,
% 9.72/9.90      (![X9 : $i, X11 : $i]:
% 9.72/9.90         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 9.72/9.90      inference('cnf', [status(esa)], [t3_subset])).
% 9.72/9.90  thf('12', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 9.72/9.90      inference('sup-', [status(thm)], ['10', '11'])).
% 9.72/9.90  thf(redefinition_r2_relset_1, axiom,
% 9.72/9.90    (![A:$i,B:$i,C:$i,D:$i]:
% 9.72/9.90     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 9.72/9.90         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 9.72/9.90       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 9.72/9.90  thf('13', plain,
% 9.72/9.90      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 9.72/9.90         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 9.72/9.90          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 9.72/9.90          | (r2_relset_1 @ X25 @ X26 @ X24 @ X27)
% 9.72/9.90          | ((X24) != (X27)))),
% 9.72/9.90      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 9.72/9.90  thf('14', plain,
% 9.72/9.90      (![X25 : $i, X26 : $i, X27 : $i]:
% 9.72/9.90         ((r2_relset_1 @ X25 @ X26 @ X27 @ X27)
% 9.72/9.90          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 9.72/9.90      inference('simplify', [status(thm)], ['13'])).
% 9.72/9.90  thf('15', plain,
% 9.72/9.90      (![X0 : $i, X1 : $i]:
% 9.72/9.90         (r2_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 9.72/9.90          (k2_zfmisc_1 @ X1 @ X0))),
% 9.72/9.90      inference('sup-', [status(thm)], ['12', '14'])).
% 9.72/9.90  thf('16', plain,
% 9.72/9.90      (![X0 : $i]:
% 9.72/9.90         (r2_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 @ 
% 9.72/9.90          (k2_zfmisc_1 @ X0 @ k1_xboole_0))),
% 9.72/9.90      inference('sup+', [status(thm)], ['6', '15'])).
% 9.72/9.90  thf('17', plain,
% 9.72/9.90      (![X7 : $i]: ((k2_zfmisc_1 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 9.72/9.90      inference('simplify', [status(thm)], ['5'])).
% 9.72/9.90  thf('18', plain,
% 9.72/9.90      (![X0 : $i]: (r2_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 9.72/9.90      inference('demod', [status(thm)], ['16', '17'])).
% 9.72/9.90  thf('19', plain,
% 9.72/9.90      (![X0 : $i, X1 : $i]:
% 9.72/9.90         ((r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)
% 9.72/9.90          | ~ (v1_xboole_0 @ X0))),
% 9.72/9.90      inference('sup+', [status(thm)], ['4', '18'])).
% 9.72/9.90  thf('20', plain,
% 9.72/9.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.72/9.90         ((r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0)
% 9.72/9.90          | ~ (v1_xboole_0 @ X0)
% 9.72/9.90          | ~ (v1_xboole_0 @ X1))),
% 9.72/9.90      inference('sup+', [status(thm)], ['3', '19'])).
% 9.72/9.90  thf('21', plain,
% 9.72/9.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 9.72/9.90         ((r2_relset_1 @ X3 @ X2 @ X1 @ X0)
% 9.72/9.90          | ~ (v1_xboole_0 @ X0)
% 9.72/9.90          | ~ (v1_xboole_0 @ X2)
% 9.72/9.90          | ~ (v1_xboole_0 @ X1))),
% 9.72/9.90      inference('sup+', [status(thm)], ['2', '20'])).
% 9.72/9.90  thf(t87_funct_2, conjecture,
% 9.72/9.90    (![A:$i,B:$i]:
% 9.72/9.90     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 9.72/9.90         ( v3_funct_2 @ B @ A @ A ) & 
% 9.72/9.90         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 9.72/9.90       ( ![C:$i]:
% 9.72/9.90         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 9.72/9.90             ( v3_funct_2 @ C @ A @ A ) & 
% 9.72/9.90             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 9.72/9.90           ( ( r2_relset_1 @
% 9.72/9.90               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 9.72/9.90               ( k6_partfun1 @ A ) ) =>
% 9.72/9.90             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 9.72/9.90  thf(zf_stmt_0, negated_conjecture,
% 9.72/9.90    (~( ![A:$i,B:$i]:
% 9.72/9.90        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 9.72/9.90            ( v3_funct_2 @ B @ A @ A ) & 
% 9.72/9.90            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 9.72/9.90          ( ![C:$i]:
% 9.72/9.90            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 9.72/9.90                ( v3_funct_2 @ C @ A @ A ) & 
% 9.72/9.90                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 9.72/9.90              ( ( r2_relset_1 @
% 9.72/9.90                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 9.72/9.90                  ( k6_partfun1 @ A ) ) =>
% 9.72/9.90                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 9.72/9.90    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 9.72/9.90  thf('22', plain,
% 9.72/9.90      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 9.72/9.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.72/9.90  thf('23', plain,
% 9.72/9.90      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.72/9.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.72/9.90  thf(redefinition_k2_funct_2, axiom,
% 9.72/9.90    (![A:$i,B:$i]:
% 9.72/9.90     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 9.72/9.90         ( v3_funct_2 @ B @ A @ A ) & 
% 9.72/9.90         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 9.72/9.90       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 9.72/9.90  thf('24', plain,
% 9.72/9.90      (![X42 : $i, X43 : $i]:
% 9.72/9.90         (((k2_funct_2 @ X43 @ X42) = (k2_funct_1 @ X42))
% 9.72/9.90          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X43)))
% 9.72/9.90          | ~ (v3_funct_2 @ X42 @ X43 @ X43)
% 9.72/9.90          | ~ (v1_funct_2 @ X42 @ X43 @ X43)
% 9.72/9.90          | ~ (v1_funct_1 @ X42))),
% 9.72/9.90      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 9.72/9.90  thf('25', plain,
% 9.72/9.90      ((~ (v1_funct_1 @ sk_B)
% 9.72/9.90        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 9.72/9.90        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 9.72/9.90        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 9.72/9.90      inference('sup-', [status(thm)], ['23', '24'])).
% 9.72/9.90  thf('26', plain, ((v1_funct_1 @ sk_B)),
% 9.72/9.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.72/9.90  thf('27', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 9.72/9.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.72/9.90  thf('28', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 9.72/9.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.72/9.90  thf('29', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 9.72/9.90      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 9.72/9.90  thf('30', plain,
% 9.72/9.90      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ (k2_funct_1 @ sk_B))),
% 9.72/9.90      inference('demod', [status(thm)], ['22', '29'])).
% 9.72/9.90  thf('31', plain,
% 9.72/9.90      ((~ (v1_xboole_0 @ sk_C_1)
% 9.72/9.90        | ~ (v1_xboole_0 @ sk_A)
% 9.72/9.90        | ~ (v1_xboole_0 @ (k2_funct_1 @ sk_B)))),
% 9.72/9.90      inference('sup-', [status(thm)], ['21', '30'])).
% 9.72/9.90  thf('32', plain,
% 9.72/9.90      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.72/9.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.72/9.90  thf(cc3_relset_1, axiom,
% 9.72/9.90    (![A:$i,B:$i]:
% 9.72/9.90     ( ( v1_xboole_0 @ A ) =>
% 9.72/9.90       ( ![C:$i]:
% 9.72/9.90         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.72/9.90           ( v1_xboole_0 @ C ) ) ) ))).
% 9.72/9.90  thf('33', plain,
% 9.72/9.90      (![X18 : $i, X19 : $i, X20 : $i]:
% 9.72/9.90         (~ (v1_xboole_0 @ X18)
% 9.72/9.90          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X20)))
% 9.72/9.90          | (v1_xboole_0 @ X19))),
% 9.72/9.90      inference('cnf', [status(esa)], [cc3_relset_1])).
% 9.72/9.90  thf('34', plain, (((v1_xboole_0 @ sk_C_1) | ~ (v1_xboole_0 @ sk_A))),
% 9.72/9.90      inference('sup-', [status(thm)], ['32', '33'])).
% 9.72/9.90  thf('35', plain,
% 9.72/9.90      ((~ (v1_xboole_0 @ (k2_funct_1 @ sk_B)) | ~ (v1_xboole_0 @ sk_A))),
% 9.72/9.90      inference('clc', [status(thm)], ['31', '34'])).
% 9.72/9.90  thf('36', plain,
% 9.72/9.90      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.72/9.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.72/9.90  thf(dt_k2_funct_2, axiom,
% 9.72/9.90    (![A:$i,B:$i]:
% 9.72/9.90     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 9.72/9.90         ( v3_funct_2 @ B @ A @ A ) & 
% 9.72/9.90         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 9.72/9.90       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 9.72/9.90         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 9.72/9.90         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 9.72/9.90         ( m1_subset_1 @
% 9.72/9.90           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 9.72/9.90  thf('37', plain,
% 9.72/9.90      (![X40 : $i, X41 : $i]:
% 9.72/9.90         ((m1_subset_1 @ (k2_funct_2 @ X40 @ X41) @ 
% 9.72/9.90           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X40)))
% 9.72/9.90          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X40)))
% 9.72/9.90          | ~ (v3_funct_2 @ X41 @ X40 @ X40)
% 9.72/9.90          | ~ (v1_funct_2 @ X41 @ X40 @ X40)
% 9.72/9.90          | ~ (v1_funct_1 @ X41))),
% 9.72/9.90      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 9.72/9.90  thf('38', plain,
% 9.72/9.90      ((~ (v1_funct_1 @ sk_B)
% 9.72/9.90        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 9.72/9.90        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 9.72/9.90        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 9.72/9.90           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 9.72/9.90      inference('sup-', [status(thm)], ['36', '37'])).
% 9.72/9.90  thf('39', plain, ((v1_funct_1 @ sk_B)),
% 9.72/9.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.72/9.90  thf('40', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 9.72/9.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.72/9.90  thf('41', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 9.72/9.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.72/9.90  thf('42', plain,
% 9.72/9.90      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 9.72/9.90        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.72/9.90      inference('demod', [status(thm)], ['38', '39', '40', '41'])).
% 9.72/9.90  thf('43', plain,
% 9.72/9.90      (![X18 : $i, X19 : $i, X20 : $i]:
% 9.72/9.90         (~ (v1_xboole_0 @ X18)
% 9.72/9.90          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X20)))
% 9.72/9.90          | (v1_xboole_0 @ X19))),
% 9.72/9.90      inference('cnf', [status(esa)], [cc3_relset_1])).
% 9.72/9.90  thf('44', plain,
% 9.72/9.90      (((v1_xboole_0 @ (k2_funct_2 @ sk_A @ sk_B)) | ~ (v1_xboole_0 @ sk_A))),
% 9.72/9.90      inference('sup-', [status(thm)], ['42', '43'])).
% 9.72/9.90  thf('45', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 9.72/9.90      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 9.72/9.90  thf('46', plain,
% 9.72/9.90      (((v1_xboole_0 @ (k2_funct_1 @ sk_B)) | ~ (v1_xboole_0 @ sk_A))),
% 9.72/9.90      inference('demod', [status(thm)], ['44', '45'])).
% 9.72/9.90  thf('47', plain, (~ (v1_xboole_0 @ sk_A)),
% 9.72/9.90      inference('clc', [status(thm)], ['35', '46'])).
% 9.72/9.90  thf('48', plain,
% 9.72/9.90      ((r2_relset_1 @ sk_A @ sk_A @ 
% 9.72/9.90        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C_1) @ 
% 9.72/9.90        (k6_partfun1 @ sk_A))),
% 9.72/9.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.72/9.90  thf(redefinition_k6_partfun1, axiom,
% 9.72/9.90    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 9.72/9.91  thf('49', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 9.72/9.91      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 9.72/9.91  thf('50', plain,
% 9.72/9.91      ((r2_relset_1 @ sk_A @ sk_A @ 
% 9.72/9.91        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C_1) @ 
% 9.72/9.91        (k6_relat_1 @ sk_A))),
% 9.72/9.91      inference('demod', [status(thm)], ['48', '49'])).
% 9.72/9.91  thf('51', plain,
% 9.72/9.91      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.72/9.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.72/9.91  thf('52', plain,
% 9.72/9.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.72/9.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.72/9.91  thf(dt_k1_partfun1, axiom,
% 9.72/9.91    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 9.72/9.91     ( ( ( v1_funct_1 @ E ) & 
% 9.72/9.91         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 9.72/9.91         ( v1_funct_1 @ F ) & 
% 9.72/9.91         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 9.72/9.91       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 9.72/9.91         ( m1_subset_1 @
% 9.72/9.91           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 9.72/9.91           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 9.72/9.91  thf('53', plain,
% 9.72/9.91      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 9.72/9.91         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 9.72/9.91          | ~ (v1_funct_1 @ X34)
% 9.72/9.91          | ~ (v1_funct_1 @ X37)
% 9.72/9.91          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 9.72/9.91          | (m1_subset_1 @ (k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37) @ 
% 9.72/9.91             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X39))))),
% 9.72/9.91      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 9.72/9.91  thf('54', plain,
% 9.72/9.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.72/9.91         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 9.72/9.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 9.72/9.91          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 9.72/9.91          | ~ (v1_funct_1 @ X1)
% 9.72/9.91          | ~ (v1_funct_1 @ sk_B))),
% 9.72/9.91      inference('sup-', [status(thm)], ['52', '53'])).
% 9.72/9.91  thf('55', plain, ((v1_funct_1 @ sk_B)),
% 9.72/9.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.72/9.91  thf('56', plain,
% 9.72/9.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.72/9.91         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 9.72/9.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 9.72/9.91          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 9.72/9.91          | ~ (v1_funct_1 @ X1))),
% 9.72/9.91      inference('demod', [status(thm)], ['54', '55'])).
% 9.72/9.91  thf('57', plain,
% 9.72/9.91      ((~ (v1_funct_1 @ sk_C_1)
% 9.72/9.91        | (m1_subset_1 @ 
% 9.72/9.91           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C_1) @ 
% 9.72/9.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 9.72/9.91      inference('sup-', [status(thm)], ['51', '56'])).
% 9.72/9.91  thf('58', plain, ((v1_funct_1 @ sk_C_1)),
% 9.72/9.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.72/9.91  thf('59', plain,
% 9.72/9.91      ((m1_subset_1 @ 
% 9.72/9.91        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C_1) @ 
% 9.72/9.91        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.72/9.91      inference('demod', [status(thm)], ['57', '58'])).
% 9.72/9.91  thf('60', plain,
% 9.72/9.91      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 9.72/9.91         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 9.72/9.91          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 9.72/9.91          | ((X24) = (X27))
% 9.72/9.91          | ~ (r2_relset_1 @ X25 @ X26 @ X24 @ X27))),
% 9.72/9.91      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 9.72/9.91  thf('61', plain,
% 9.72/9.91      (![X0 : $i]:
% 9.72/9.91         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 9.72/9.91             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C_1) @ X0)
% 9.72/9.91          | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C_1) = (X0))
% 9.72/9.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 9.72/9.91      inference('sup-', [status(thm)], ['59', '60'])).
% 9.72/9.91  thf('62', plain,
% 9.72/9.91      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 9.72/9.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 9.72/9.91        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C_1)
% 9.72/9.91            = (k6_relat_1 @ sk_A)))),
% 9.72/9.91      inference('sup-', [status(thm)], ['50', '61'])).
% 9.72/9.91  thf(t29_relset_1, axiom,
% 9.72/9.91    (![A:$i]:
% 9.72/9.91     ( m1_subset_1 @
% 9.72/9.91       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 9.72/9.91  thf('63', plain,
% 9.72/9.91      (![X28 : $i]:
% 9.72/9.91         (m1_subset_1 @ (k6_relat_1 @ X28) @ 
% 9.72/9.91          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 9.72/9.91      inference('cnf', [status(esa)], [t29_relset_1])).
% 9.72/9.91  thf('64', plain,
% 9.72/9.91      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C_1)
% 9.72/9.91         = (k6_relat_1 @ sk_A))),
% 9.72/9.91      inference('demod', [status(thm)], ['62', '63'])).
% 9.72/9.91  thf('65', plain,
% 9.72/9.91      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.72/9.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.72/9.91  thf(t36_funct_2, axiom,
% 9.72/9.91    (![A:$i,B:$i,C:$i]:
% 9.72/9.91     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 9.72/9.91         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 9.72/9.91       ( ![D:$i]:
% 9.72/9.91         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 9.72/9.91             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 9.72/9.91           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 9.72/9.91               ( r2_relset_1 @
% 9.72/9.91                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 9.72/9.91                 ( k6_partfun1 @ A ) ) & 
% 9.72/9.91               ( v2_funct_1 @ C ) ) =>
% 9.72/9.91             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 9.72/9.91               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 9.72/9.91  thf('66', plain,
% 9.72/9.91      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 9.72/9.91         (~ (v1_funct_1 @ X49)
% 9.72/9.91          | ~ (v1_funct_2 @ X49 @ X50 @ X51)
% 9.72/9.91          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 9.72/9.91          | ((X49) = (k2_funct_1 @ X52))
% 9.72/9.91          | ~ (r2_relset_1 @ X51 @ X51 @ 
% 9.72/9.91               (k1_partfun1 @ X51 @ X50 @ X50 @ X51 @ X52 @ X49) @ 
% 9.72/9.91               (k6_partfun1 @ X51))
% 9.72/9.91          | ((X50) = (k1_xboole_0))
% 9.72/9.91          | ((X51) = (k1_xboole_0))
% 9.72/9.91          | ~ (v2_funct_1 @ X52)
% 9.72/9.91          | ((k2_relset_1 @ X51 @ X50 @ X52) != (X50))
% 9.72/9.91          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X50)))
% 9.72/9.91          | ~ (v1_funct_2 @ X52 @ X51 @ X50)
% 9.72/9.91          | ~ (v1_funct_1 @ X52))),
% 9.72/9.91      inference('cnf', [status(esa)], [t36_funct_2])).
% 9.72/9.91  thf('67', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 9.72/9.91      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 9.72/9.91  thf('68', plain,
% 9.72/9.91      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 9.72/9.91         (~ (v1_funct_1 @ X49)
% 9.72/9.91          | ~ (v1_funct_2 @ X49 @ X50 @ X51)
% 9.72/9.91          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 9.72/9.91          | ((X49) = (k2_funct_1 @ X52))
% 9.72/9.91          | ~ (r2_relset_1 @ X51 @ X51 @ 
% 9.72/9.91               (k1_partfun1 @ X51 @ X50 @ X50 @ X51 @ X52 @ X49) @ 
% 9.72/9.91               (k6_relat_1 @ X51))
% 9.72/9.91          | ((X50) = (k1_xboole_0))
% 9.72/9.91          | ((X51) = (k1_xboole_0))
% 9.72/9.91          | ~ (v2_funct_1 @ X52)
% 9.72/9.91          | ((k2_relset_1 @ X51 @ X50 @ X52) != (X50))
% 9.72/9.91          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X50)))
% 9.72/9.91          | ~ (v1_funct_2 @ X52 @ X51 @ X50)
% 9.72/9.91          | ~ (v1_funct_1 @ X52))),
% 9.72/9.91      inference('demod', [status(thm)], ['66', '67'])).
% 9.72/9.91  thf('69', plain,
% 9.72/9.91      (![X0 : $i]:
% 9.72/9.91         (~ (v1_funct_1 @ X0)
% 9.72/9.91          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 9.72/9.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 9.72/9.91          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 9.72/9.91          | ~ (v2_funct_1 @ X0)
% 9.72/9.91          | ((sk_A) = (k1_xboole_0))
% 9.72/9.91          | ((sk_A) = (k1_xboole_0))
% 9.72/9.91          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 9.72/9.91               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C_1) @ 
% 9.72/9.91               (k6_relat_1 @ sk_A))
% 9.72/9.91          | ((sk_C_1) = (k2_funct_1 @ X0))
% 9.72/9.91          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_A)
% 9.72/9.91          | ~ (v1_funct_1 @ sk_C_1))),
% 9.72/9.91      inference('sup-', [status(thm)], ['65', '68'])).
% 9.72/9.91  thf('70', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_A)),
% 9.72/9.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.72/9.91  thf('71', plain, ((v1_funct_1 @ sk_C_1)),
% 9.72/9.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.72/9.91  thf('72', plain,
% 9.72/9.91      (![X0 : $i]:
% 9.72/9.91         (~ (v1_funct_1 @ X0)
% 9.72/9.91          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 9.72/9.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 9.72/9.91          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 9.72/9.91          | ~ (v2_funct_1 @ X0)
% 9.72/9.91          | ((sk_A) = (k1_xboole_0))
% 9.72/9.91          | ((sk_A) = (k1_xboole_0))
% 9.72/9.91          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 9.72/9.91               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C_1) @ 
% 9.72/9.91               (k6_relat_1 @ sk_A))
% 9.72/9.91          | ((sk_C_1) = (k2_funct_1 @ X0)))),
% 9.72/9.91      inference('demod', [status(thm)], ['69', '70', '71'])).
% 9.72/9.91  thf('73', plain,
% 9.72/9.91      (![X0 : $i]:
% 9.72/9.91         (((sk_C_1) = (k2_funct_1 @ X0))
% 9.72/9.91          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 9.72/9.91               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C_1) @ 
% 9.72/9.91               (k6_relat_1 @ sk_A))
% 9.72/9.91          | ((sk_A) = (k1_xboole_0))
% 9.72/9.91          | ~ (v2_funct_1 @ X0)
% 9.72/9.91          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 9.72/9.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 9.72/9.91          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 9.72/9.91          | ~ (v1_funct_1 @ X0))),
% 9.72/9.91      inference('simplify', [status(thm)], ['72'])).
% 9.72/9.91  thf('74', plain,
% 9.72/9.91      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 9.72/9.91           (k6_relat_1 @ sk_A))
% 9.72/9.91        | ~ (v1_funct_1 @ sk_B)
% 9.72/9.91        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 9.72/9.91        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 9.72/9.91        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 9.72/9.91        | ~ (v2_funct_1 @ sk_B)
% 9.72/9.91        | ((sk_A) = (k1_xboole_0))
% 9.72/9.91        | ((sk_C_1) = (k2_funct_1 @ sk_B)))),
% 9.72/9.91      inference('sup-', [status(thm)], ['64', '73'])).
% 9.72/9.91  thf('75', plain,
% 9.72/9.91      (![X28 : $i]:
% 9.72/9.91         (m1_subset_1 @ (k6_relat_1 @ X28) @ 
% 9.72/9.91          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 9.72/9.91      inference('cnf', [status(esa)], [t29_relset_1])).
% 9.72/9.91  thf('76', plain,
% 9.72/9.91      (![X25 : $i, X26 : $i, X27 : $i]:
% 9.72/9.91         ((r2_relset_1 @ X25 @ X26 @ X27 @ X27)
% 9.72/9.91          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 9.72/9.91      inference('simplify', [status(thm)], ['13'])).
% 9.72/9.91  thf('77', plain,
% 9.72/9.91      (![X0 : $i]:
% 9.72/9.91         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 9.72/9.91      inference('sup-', [status(thm)], ['75', '76'])).
% 9.72/9.91  thf('78', plain, ((v1_funct_1 @ sk_B)),
% 9.72/9.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.72/9.91  thf('79', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 9.72/9.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.72/9.91  thf('80', plain,
% 9.72/9.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.72/9.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.72/9.91  thf('81', plain,
% 9.72/9.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.72/9.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.72/9.91  thf(redefinition_k2_relset_1, axiom,
% 9.72/9.91    (![A:$i,B:$i,C:$i]:
% 9.72/9.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.72/9.91       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 9.72/9.91  thf('82', plain,
% 9.72/9.91      (![X21 : $i, X22 : $i, X23 : $i]:
% 9.72/9.91         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 9.72/9.91          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 9.72/9.91      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 9.72/9.91  thf('83', plain,
% 9.72/9.91      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 9.72/9.91      inference('sup-', [status(thm)], ['81', '82'])).
% 9.72/9.91  thf('84', plain,
% 9.72/9.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.72/9.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.72/9.91  thf(cc2_funct_2, axiom,
% 9.72/9.91    (![A:$i,B:$i,C:$i]:
% 9.72/9.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.72/9.91       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 9.72/9.91         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 9.72/9.91  thf('85', plain,
% 9.72/9.91      (![X29 : $i, X30 : $i, X31 : $i]:
% 9.72/9.91         (~ (v1_funct_1 @ X29)
% 9.72/9.91          | ~ (v3_funct_2 @ X29 @ X30 @ X31)
% 9.72/9.91          | (v2_funct_2 @ X29 @ X31)
% 9.72/9.91          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 9.72/9.91      inference('cnf', [status(esa)], [cc2_funct_2])).
% 9.72/9.91  thf('86', plain,
% 9.72/9.91      (((v2_funct_2 @ sk_B @ sk_A)
% 9.72/9.91        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 9.72/9.91        | ~ (v1_funct_1 @ sk_B))),
% 9.72/9.91      inference('sup-', [status(thm)], ['84', '85'])).
% 9.72/9.91  thf('87', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 9.72/9.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.72/9.91  thf('88', plain, ((v1_funct_1 @ sk_B)),
% 9.72/9.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.72/9.91  thf('89', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 9.72/9.91      inference('demod', [status(thm)], ['86', '87', '88'])).
% 9.72/9.91  thf(d3_funct_2, axiom,
% 9.72/9.91    (![A:$i,B:$i]:
% 9.72/9.91     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 9.72/9.91       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 9.72/9.91  thf('90', plain,
% 9.72/9.91      (![X32 : $i, X33 : $i]:
% 9.72/9.91         (~ (v2_funct_2 @ X33 @ X32)
% 9.72/9.91          | ((k2_relat_1 @ X33) = (X32))
% 9.72/9.91          | ~ (v5_relat_1 @ X33 @ X32)
% 9.72/9.91          | ~ (v1_relat_1 @ X33))),
% 9.72/9.91      inference('cnf', [status(esa)], [d3_funct_2])).
% 9.72/9.91  thf('91', plain,
% 9.72/9.91      ((~ (v1_relat_1 @ sk_B)
% 9.72/9.91        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 9.72/9.91        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 9.72/9.91      inference('sup-', [status(thm)], ['89', '90'])).
% 9.72/9.91  thf('92', plain,
% 9.72/9.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.72/9.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.72/9.91  thf(cc1_relset_1, axiom,
% 9.72/9.91    (![A:$i,B:$i,C:$i]:
% 9.72/9.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.72/9.91       ( v1_relat_1 @ C ) ))).
% 9.72/9.91  thf('93', plain,
% 9.72/9.91      (![X12 : $i, X13 : $i, X14 : $i]:
% 9.72/9.91         ((v1_relat_1 @ X12)
% 9.72/9.91          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 9.72/9.91      inference('cnf', [status(esa)], [cc1_relset_1])).
% 9.72/9.91  thf('94', plain, ((v1_relat_1 @ sk_B)),
% 9.72/9.91      inference('sup-', [status(thm)], ['92', '93'])).
% 9.72/9.91  thf('95', plain,
% 9.72/9.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.72/9.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.72/9.91  thf(cc2_relset_1, axiom,
% 9.72/9.91    (![A:$i,B:$i,C:$i]:
% 9.72/9.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.72/9.91       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 9.72/9.91  thf('96', plain,
% 9.72/9.91      (![X15 : $i, X16 : $i, X17 : $i]:
% 9.72/9.91         ((v5_relat_1 @ X15 @ X17)
% 9.72/9.91          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 9.72/9.91      inference('cnf', [status(esa)], [cc2_relset_1])).
% 9.72/9.91  thf('97', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 9.72/9.91      inference('sup-', [status(thm)], ['95', '96'])).
% 9.72/9.91  thf('98', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 9.72/9.91      inference('demod', [status(thm)], ['91', '94', '97'])).
% 9.72/9.91  thf('99', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 9.72/9.91      inference('demod', [status(thm)], ['83', '98'])).
% 9.72/9.91  thf('100', plain,
% 9.72/9.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.72/9.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.72/9.91  thf('101', plain,
% 9.72/9.91      (![X29 : $i, X30 : $i, X31 : $i]:
% 9.72/9.91         (~ (v1_funct_1 @ X29)
% 9.72/9.91          | ~ (v3_funct_2 @ X29 @ X30 @ X31)
% 9.72/9.91          | (v2_funct_1 @ X29)
% 9.72/9.91          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 9.72/9.91      inference('cnf', [status(esa)], [cc2_funct_2])).
% 9.72/9.91  thf('102', plain,
% 9.72/9.91      (((v2_funct_1 @ sk_B)
% 9.72/9.91        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 9.72/9.91        | ~ (v1_funct_1 @ sk_B))),
% 9.72/9.91      inference('sup-', [status(thm)], ['100', '101'])).
% 9.72/9.91  thf('103', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 9.72/9.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.72/9.91  thf('104', plain, ((v1_funct_1 @ sk_B)),
% 9.72/9.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.72/9.91  thf('105', plain, ((v2_funct_1 @ sk_B)),
% 9.72/9.91      inference('demod', [status(thm)], ['102', '103', '104'])).
% 9.72/9.91  thf('106', plain,
% 9.72/9.91      ((((sk_A) != (sk_A))
% 9.72/9.91        | ((sk_A) = (k1_xboole_0))
% 9.72/9.91        | ((sk_C_1) = (k2_funct_1 @ sk_B)))),
% 9.72/9.91      inference('demod', [status(thm)],
% 9.72/9.91                ['74', '77', '78', '79', '80', '99', '105'])).
% 9.72/9.91  thf('107', plain,
% 9.72/9.91      ((((sk_C_1) = (k2_funct_1 @ sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 9.72/9.91      inference('simplify', [status(thm)], ['106'])).
% 9.72/9.91  thf('108', plain,
% 9.72/9.91      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ (k2_funct_1 @ sk_B))),
% 9.72/9.91      inference('demod', [status(thm)], ['22', '29'])).
% 9.72/9.91  thf('109', plain,
% 9.72/9.91      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_C_1)
% 9.72/9.91        | ((sk_A) = (k1_xboole_0)))),
% 9.72/9.91      inference('sup-', [status(thm)], ['107', '108'])).
% 9.72/9.91  thf('110', plain,
% 9.72/9.91      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.72/9.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.72/9.91  thf('111', plain,
% 9.72/9.91      (![X25 : $i, X26 : $i, X27 : $i]:
% 9.72/9.91         ((r2_relset_1 @ X25 @ X26 @ X27 @ X27)
% 9.72/9.91          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 9.72/9.91      inference('simplify', [status(thm)], ['13'])).
% 9.72/9.91  thf('112', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_C_1)),
% 9.72/9.91      inference('sup-', [status(thm)], ['110', '111'])).
% 9.72/9.91  thf('113', plain, (((sk_A) = (k1_xboole_0))),
% 9.72/9.91      inference('demod', [status(thm)], ['109', '112'])).
% 9.72/9.91  thf('114', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 9.72/9.91      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 9.72/9.91  thf('115', plain, ($false),
% 9.72/9.91      inference('demod', [status(thm)], ['47', '113', '114'])).
% 9.72/9.91  
% 9.72/9.91  % SZS output end Refutation
% 9.72/9.91  
% 9.72/9.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
