%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5ryCmuDctc

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:03 EST 2020

% Result     : Theorem 4.25s
% Output     : Refutation 4.25s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 240 expanded)
%              Number of leaves         :   42 (  89 expanded)
%              Depth                    :   14
%              Number of atoms          : 1176 (5046 expanded)
%              Number of equality atoms :   56 (  74 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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
    ! [X35: $i,X36: $i] :
      ( ( ( k2_funct_2 @ X36 @ X35 )
        = ( k2_funct_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) )
      | ~ ( v3_funct_2 @ X35 @ X36 @ X36 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X36 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
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

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('33',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X18 ) ) )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

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
    ! [X33: $i,X34: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X33 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) )
      | ~ ( v3_funct_2 @ X34 @ X33 @ X33 )
      | ~ ( v1_funct_2 @ X34 @ X33 @ X33 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
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
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X18 ) ) )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

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

thf('49',plain,(
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

thf('50',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( X41
        = ( k2_funct_1 @ X44 ) )
      | ~ ( r2_relset_1 @ X43 @ X43 @ ( k1_partfun1 @ X43 @ X42 @ X42 @ X43 @ X44 @ X41 ) @ ( k6_partfun1 @ X43 ) )
      | ( X42 = k1_xboole_0 )
      | ( X43 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X44 )
      | ( ( k2_relset_1 @ X43 @ X42 @ X44 )
       != X42 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X43 @ X42 )
      | ~ ( v1_funct_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t36_funct_2])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C_1 ) @ ( k6_partfun1 @ sk_A ) )
      | ( sk_C_1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C_1 ) @ ( k6_partfun1 @ sk_A ) )
      | ( sk_C_1
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( sk_C_1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C_1 ) @ ( k6_partfun1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C_1
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('61',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('62',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
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

thf('64',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_1 @ X28 )
      | ~ ( v3_funct_2 @ X28 @ X29 @ X30 )
      | ( v2_funct_2 @ X28 @ X30 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('65',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['65','66','67'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('69',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v2_funct_2 @ X32 @ X31 )
      | ( ( k2_relat_1 @ X32 )
        = X31 )
      | ~ ( v5_relat_1 @ X32 @ X31 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('70',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('72',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('73',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('75',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v5_relat_1 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('76',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['70','73','76'])).

thf('78',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['62','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_1 @ X28 )
      | ~ ( v3_funct_2 @ X28 @ X29 @ X30 )
      | ( v2_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('81',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,
    ( ( sk_A != sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C_1
      = ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','57','58','59','78','84'])).

thf('86',plain,
    ( ( sk_C_1
      = ( k2_funct_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','29'])).

thf('88',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_relset_1 @ X25 @ X26 @ X27 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('91',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['88','91'])).

thf('93',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('94',plain,(
    $false ),
    inference(demod,[status(thm)],['47','92','93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5ryCmuDctc
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:11:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.25/4.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.25/4.45  % Solved by: fo/fo7.sh
% 4.25/4.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.25/4.45  % done 8968 iterations in 3.990s
% 4.25/4.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.25/4.45  % SZS output start Refutation
% 4.25/4.45  thf(sk_B_type, type, sk_B: $i).
% 4.25/4.45  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 4.25/4.45  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 4.25/4.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.25/4.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.25/4.45  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 4.25/4.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.25/4.45  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 4.25/4.45  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.25/4.45  thf(sk_A_type, type, sk_A: $i).
% 4.25/4.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.25/4.45  thf(sk_C_1_type, type, sk_C_1: $i).
% 4.25/4.45  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 4.25/4.45  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 4.25/4.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.25/4.45  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 4.25/4.45  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 4.25/4.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.25/4.45  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 4.25/4.45  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 4.25/4.45  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 4.25/4.45  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.25/4.45  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.25/4.45  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.25/4.45  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.25/4.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.25/4.45  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 4.25/4.45  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.25/4.45      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.25/4.45  thf(t8_boole, axiom,
% 4.25/4.45    (![A:$i,B:$i]:
% 4.25/4.45     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 4.25/4.45  thf('1', plain,
% 4.25/4.45      (![X4 : $i, X5 : $i]:
% 4.25/4.45         (~ (v1_xboole_0 @ X4) | ~ (v1_xboole_0 @ X5) | ((X4) = (X5)))),
% 4.25/4.45      inference('cnf', [status(esa)], [t8_boole])).
% 4.25/4.45  thf('2', plain,
% 4.25/4.45      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 4.25/4.45      inference('sup-', [status(thm)], ['0', '1'])).
% 4.25/4.45  thf('3', plain,
% 4.25/4.45      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 4.25/4.45      inference('sup-', [status(thm)], ['0', '1'])).
% 4.25/4.45  thf('4', plain,
% 4.25/4.45      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 4.25/4.45      inference('sup-', [status(thm)], ['0', '1'])).
% 4.25/4.45  thf(t113_zfmisc_1, axiom,
% 4.25/4.45    (![A:$i,B:$i]:
% 4.25/4.45     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 4.25/4.45       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 4.25/4.45  thf('5', plain,
% 4.25/4.45      (![X7 : $i, X8 : $i]:
% 4.25/4.45         (((k2_zfmisc_1 @ X7 @ X8) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 4.25/4.45      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 4.25/4.45  thf('6', plain,
% 4.25/4.45      (![X7 : $i]: ((k2_zfmisc_1 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 4.25/4.45      inference('simplify', [status(thm)], ['5'])).
% 4.25/4.45  thf(d3_tarski, axiom,
% 4.25/4.45    (![A:$i,B:$i]:
% 4.25/4.45     ( ( r1_tarski @ A @ B ) <=>
% 4.25/4.45       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 4.25/4.45  thf('7', plain,
% 4.25/4.45      (![X1 : $i, X3 : $i]:
% 4.25/4.45         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 4.25/4.45      inference('cnf', [status(esa)], [d3_tarski])).
% 4.25/4.45  thf('8', plain,
% 4.25/4.45      (![X1 : $i, X3 : $i]:
% 4.25/4.45         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 4.25/4.45      inference('cnf', [status(esa)], [d3_tarski])).
% 4.25/4.45  thf('9', plain,
% 4.25/4.45      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 4.25/4.45      inference('sup-', [status(thm)], ['7', '8'])).
% 4.25/4.45  thf('10', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 4.25/4.45      inference('simplify', [status(thm)], ['9'])).
% 4.25/4.45  thf(t3_subset, axiom,
% 4.25/4.45    (![A:$i,B:$i]:
% 4.25/4.45     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.25/4.45  thf('11', plain,
% 4.25/4.45      (![X9 : $i, X11 : $i]:
% 4.25/4.45         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 4.25/4.45      inference('cnf', [status(esa)], [t3_subset])).
% 4.25/4.45  thf('12', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 4.25/4.45      inference('sup-', [status(thm)], ['10', '11'])).
% 4.25/4.45  thf(redefinition_r2_relset_1, axiom,
% 4.25/4.45    (![A:$i,B:$i,C:$i,D:$i]:
% 4.25/4.45     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.25/4.45         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.25/4.45       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 4.25/4.45  thf('13', plain,
% 4.25/4.45      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 4.25/4.45         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 4.25/4.45          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 4.25/4.45          | (r2_relset_1 @ X25 @ X26 @ X24 @ X27)
% 4.25/4.45          | ((X24) != (X27)))),
% 4.25/4.45      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 4.25/4.45  thf('14', plain,
% 4.25/4.45      (![X25 : $i, X26 : $i, X27 : $i]:
% 4.25/4.45         ((r2_relset_1 @ X25 @ X26 @ X27 @ X27)
% 4.25/4.45          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 4.25/4.45      inference('simplify', [status(thm)], ['13'])).
% 4.25/4.45  thf('15', plain,
% 4.25/4.45      (![X0 : $i, X1 : $i]:
% 4.25/4.45         (r2_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 4.25/4.45          (k2_zfmisc_1 @ X1 @ X0))),
% 4.25/4.45      inference('sup-', [status(thm)], ['12', '14'])).
% 4.25/4.45  thf('16', plain,
% 4.25/4.45      (![X0 : $i]:
% 4.25/4.45         (r2_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 @ 
% 4.25/4.45          (k2_zfmisc_1 @ X0 @ k1_xboole_0))),
% 4.25/4.45      inference('sup+', [status(thm)], ['6', '15'])).
% 4.25/4.45  thf('17', plain,
% 4.25/4.45      (![X7 : $i]: ((k2_zfmisc_1 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 4.25/4.45      inference('simplify', [status(thm)], ['5'])).
% 4.25/4.45  thf('18', plain,
% 4.25/4.45      (![X0 : $i]: (r2_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 4.25/4.45      inference('demod', [status(thm)], ['16', '17'])).
% 4.25/4.45  thf('19', plain,
% 4.25/4.45      (![X0 : $i, X1 : $i]:
% 4.25/4.45         ((r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)
% 4.25/4.45          | ~ (v1_xboole_0 @ X0))),
% 4.25/4.45      inference('sup+', [status(thm)], ['4', '18'])).
% 4.25/4.45  thf('20', plain,
% 4.25/4.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.25/4.45         ((r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0)
% 4.25/4.45          | ~ (v1_xboole_0 @ X0)
% 4.25/4.45          | ~ (v1_xboole_0 @ X1))),
% 4.25/4.45      inference('sup+', [status(thm)], ['3', '19'])).
% 4.25/4.45  thf('21', plain,
% 4.25/4.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.25/4.45         ((r2_relset_1 @ X3 @ X2 @ X1 @ X0)
% 4.25/4.45          | ~ (v1_xboole_0 @ X0)
% 4.25/4.45          | ~ (v1_xboole_0 @ X2)
% 4.25/4.45          | ~ (v1_xboole_0 @ X1))),
% 4.25/4.45      inference('sup+', [status(thm)], ['2', '20'])).
% 4.25/4.45  thf(t87_funct_2, conjecture,
% 4.25/4.45    (![A:$i,B:$i]:
% 4.25/4.45     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 4.25/4.45         ( v3_funct_2 @ B @ A @ A ) & 
% 4.25/4.45         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 4.25/4.45       ( ![C:$i]:
% 4.25/4.45         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 4.25/4.45             ( v3_funct_2 @ C @ A @ A ) & 
% 4.25/4.45             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 4.25/4.45           ( ( r2_relset_1 @
% 4.25/4.45               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 4.25/4.45               ( k6_partfun1 @ A ) ) =>
% 4.25/4.45             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 4.25/4.45  thf(zf_stmt_0, negated_conjecture,
% 4.25/4.45    (~( ![A:$i,B:$i]:
% 4.25/4.45        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 4.25/4.45            ( v3_funct_2 @ B @ A @ A ) & 
% 4.25/4.45            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 4.25/4.45          ( ![C:$i]:
% 4.25/4.45            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 4.25/4.45                ( v3_funct_2 @ C @ A @ A ) & 
% 4.25/4.45                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 4.25/4.45              ( ( r2_relset_1 @
% 4.25/4.45                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 4.25/4.45                  ( k6_partfun1 @ A ) ) =>
% 4.25/4.45                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 4.25/4.45    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 4.25/4.45  thf('22', plain,
% 4.25/4.45      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 4.25/4.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.45  thf('23', plain,
% 4.25/4.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.25/4.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.45  thf(redefinition_k2_funct_2, axiom,
% 4.25/4.45    (![A:$i,B:$i]:
% 4.25/4.45     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 4.25/4.45         ( v3_funct_2 @ B @ A @ A ) & 
% 4.25/4.45         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 4.25/4.45       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 4.25/4.45  thf('24', plain,
% 4.25/4.45      (![X35 : $i, X36 : $i]:
% 4.25/4.45         (((k2_funct_2 @ X36 @ X35) = (k2_funct_1 @ X35))
% 4.25/4.45          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))
% 4.25/4.45          | ~ (v3_funct_2 @ X35 @ X36 @ X36)
% 4.25/4.45          | ~ (v1_funct_2 @ X35 @ X36 @ X36)
% 4.25/4.45          | ~ (v1_funct_1 @ X35))),
% 4.25/4.45      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 4.25/4.45  thf('25', plain,
% 4.25/4.45      ((~ (v1_funct_1 @ sk_B)
% 4.25/4.45        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 4.25/4.45        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 4.25/4.45        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 4.25/4.45      inference('sup-', [status(thm)], ['23', '24'])).
% 4.25/4.45  thf('26', plain, ((v1_funct_1 @ sk_B)),
% 4.25/4.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.45  thf('27', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 4.25/4.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.45  thf('28', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 4.25/4.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.45  thf('29', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 4.25/4.45      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 4.25/4.45  thf('30', plain,
% 4.25/4.45      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ (k2_funct_1 @ sk_B))),
% 4.25/4.45      inference('demod', [status(thm)], ['22', '29'])).
% 4.25/4.45  thf('31', plain,
% 4.25/4.45      ((~ (v1_xboole_0 @ sk_C_1)
% 4.25/4.45        | ~ (v1_xboole_0 @ sk_A)
% 4.25/4.45        | ~ (v1_xboole_0 @ (k2_funct_1 @ sk_B)))),
% 4.25/4.45      inference('sup-', [status(thm)], ['21', '30'])).
% 4.25/4.45  thf('32', plain,
% 4.25/4.45      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.25/4.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.45  thf(cc4_relset_1, axiom,
% 4.25/4.45    (![A:$i,B:$i]:
% 4.25/4.45     ( ( v1_xboole_0 @ A ) =>
% 4.25/4.45       ( ![C:$i]:
% 4.25/4.45         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 4.25/4.45           ( v1_xboole_0 @ C ) ) ) ))).
% 4.25/4.45  thf('33', plain,
% 4.25/4.45      (![X18 : $i, X19 : $i, X20 : $i]:
% 4.25/4.45         (~ (v1_xboole_0 @ X18)
% 4.25/4.45          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X18)))
% 4.25/4.45          | (v1_xboole_0 @ X19))),
% 4.25/4.45      inference('cnf', [status(esa)], [cc4_relset_1])).
% 4.25/4.45  thf('34', plain, (((v1_xboole_0 @ sk_C_1) | ~ (v1_xboole_0 @ sk_A))),
% 4.25/4.45      inference('sup-', [status(thm)], ['32', '33'])).
% 4.25/4.45  thf('35', plain,
% 4.25/4.45      ((~ (v1_xboole_0 @ (k2_funct_1 @ sk_B)) | ~ (v1_xboole_0 @ sk_A))),
% 4.25/4.45      inference('clc', [status(thm)], ['31', '34'])).
% 4.25/4.45  thf('36', plain,
% 4.25/4.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.25/4.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.45  thf(dt_k2_funct_2, axiom,
% 4.25/4.45    (![A:$i,B:$i]:
% 4.25/4.45     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 4.25/4.45         ( v3_funct_2 @ B @ A @ A ) & 
% 4.25/4.45         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 4.25/4.45       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 4.25/4.45         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 4.25/4.45         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 4.25/4.45         ( m1_subset_1 @
% 4.25/4.45           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 4.25/4.45  thf('37', plain,
% 4.25/4.45      (![X33 : $i, X34 : $i]:
% 4.25/4.45         ((m1_subset_1 @ (k2_funct_2 @ X33 @ X34) @ 
% 4.25/4.45           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))
% 4.25/4.45          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))
% 4.25/4.45          | ~ (v3_funct_2 @ X34 @ X33 @ X33)
% 4.25/4.45          | ~ (v1_funct_2 @ X34 @ X33 @ X33)
% 4.25/4.45          | ~ (v1_funct_1 @ X34))),
% 4.25/4.45      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 4.25/4.45  thf('38', plain,
% 4.25/4.45      ((~ (v1_funct_1 @ sk_B)
% 4.25/4.45        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 4.25/4.45        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 4.25/4.45        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 4.25/4.45           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 4.25/4.45      inference('sup-', [status(thm)], ['36', '37'])).
% 4.25/4.45  thf('39', plain, ((v1_funct_1 @ sk_B)),
% 4.25/4.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.45  thf('40', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 4.25/4.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.45  thf('41', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 4.25/4.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.45  thf('42', plain,
% 4.25/4.45      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 4.25/4.45        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.25/4.45      inference('demod', [status(thm)], ['38', '39', '40', '41'])).
% 4.25/4.45  thf('43', plain,
% 4.25/4.45      (![X18 : $i, X19 : $i, X20 : $i]:
% 4.25/4.45         (~ (v1_xboole_0 @ X18)
% 4.25/4.45          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X18)))
% 4.25/4.45          | (v1_xboole_0 @ X19))),
% 4.25/4.45      inference('cnf', [status(esa)], [cc4_relset_1])).
% 4.25/4.45  thf('44', plain,
% 4.25/4.45      (((v1_xboole_0 @ (k2_funct_2 @ sk_A @ sk_B)) | ~ (v1_xboole_0 @ sk_A))),
% 4.25/4.45      inference('sup-', [status(thm)], ['42', '43'])).
% 4.25/4.45  thf('45', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 4.25/4.45      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 4.25/4.45  thf('46', plain,
% 4.25/4.45      (((v1_xboole_0 @ (k2_funct_1 @ sk_B)) | ~ (v1_xboole_0 @ sk_A))),
% 4.25/4.45      inference('demod', [status(thm)], ['44', '45'])).
% 4.25/4.45  thf('47', plain, (~ (v1_xboole_0 @ sk_A)),
% 4.25/4.45      inference('clc', [status(thm)], ['35', '46'])).
% 4.25/4.45  thf('48', plain,
% 4.25/4.45      ((r2_relset_1 @ sk_A @ sk_A @ 
% 4.25/4.45        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C_1) @ 
% 4.25/4.45        (k6_partfun1 @ sk_A))),
% 4.25/4.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.45  thf('49', plain,
% 4.25/4.45      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.25/4.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.45  thf(t36_funct_2, axiom,
% 4.25/4.45    (![A:$i,B:$i,C:$i]:
% 4.25/4.45     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.25/4.45         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.25/4.45       ( ![D:$i]:
% 4.25/4.45         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.25/4.45             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.25/4.45           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 4.25/4.45               ( r2_relset_1 @
% 4.25/4.45                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 4.25/4.45                 ( k6_partfun1 @ A ) ) & 
% 4.25/4.45               ( v2_funct_1 @ C ) ) =>
% 4.25/4.45             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 4.25/4.45               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 4.25/4.45  thf('50', plain,
% 4.25/4.45      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 4.25/4.45         (~ (v1_funct_1 @ X41)
% 4.25/4.45          | ~ (v1_funct_2 @ X41 @ X42 @ X43)
% 4.25/4.45          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 4.25/4.45          | ((X41) = (k2_funct_1 @ X44))
% 4.25/4.45          | ~ (r2_relset_1 @ X43 @ X43 @ 
% 4.25/4.45               (k1_partfun1 @ X43 @ X42 @ X42 @ X43 @ X44 @ X41) @ 
% 4.25/4.45               (k6_partfun1 @ X43))
% 4.25/4.45          | ((X42) = (k1_xboole_0))
% 4.25/4.45          | ((X43) = (k1_xboole_0))
% 4.25/4.45          | ~ (v2_funct_1 @ X44)
% 4.25/4.45          | ((k2_relset_1 @ X43 @ X42 @ X44) != (X42))
% 4.25/4.45          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42)))
% 4.25/4.45          | ~ (v1_funct_2 @ X44 @ X43 @ X42)
% 4.25/4.45          | ~ (v1_funct_1 @ X44))),
% 4.25/4.45      inference('cnf', [status(esa)], [t36_funct_2])).
% 4.25/4.45  thf('51', plain,
% 4.25/4.45      (![X0 : $i]:
% 4.25/4.45         (~ (v1_funct_1 @ X0)
% 4.25/4.45          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 4.25/4.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 4.25/4.45          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 4.25/4.45          | ~ (v2_funct_1 @ X0)
% 4.25/4.45          | ((sk_A) = (k1_xboole_0))
% 4.25/4.45          | ((sk_A) = (k1_xboole_0))
% 4.25/4.45          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 4.25/4.45               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C_1) @ 
% 4.25/4.45               (k6_partfun1 @ sk_A))
% 4.25/4.45          | ((sk_C_1) = (k2_funct_1 @ X0))
% 4.25/4.45          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_A)
% 4.25/4.45          | ~ (v1_funct_1 @ sk_C_1))),
% 4.25/4.45      inference('sup-', [status(thm)], ['49', '50'])).
% 4.25/4.45  thf('52', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_A)),
% 4.25/4.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.45  thf('53', plain, ((v1_funct_1 @ sk_C_1)),
% 4.25/4.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.45  thf('54', plain,
% 4.25/4.45      (![X0 : $i]:
% 4.25/4.45         (~ (v1_funct_1 @ X0)
% 4.25/4.45          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 4.25/4.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 4.25/4.45          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 4.25/4.45          | ~ (v2_funct_1 @ X0)
% 4.25/4.45          | ((sk_A) = (k1_xboole_0))
% 4.25/4.45          | ((sk_A) = (k1_xboole_0))
% 4.25/4.45          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 4.25/4.45               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C_1) @ 
% 4.25/4.45               (k6_partfun1 @ sk_A))
% 4.25/4.45          | ((sk_C_1) = (k2_funct_1 @ X0)))),
% 4.25/4.45      inference('demod', [status(thm)], ['51', '52', '53'])).
% 4.25/4.45  thf('55', plain,
% 4.25/4.45      (![X0 : $i]:
% 4.25/4.45         (((sk_C_1) = (k2_funct_1 @ X0))
% 4.25/4.45          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 4.25/4.45               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C_1) @ 
% 4.25/4.45               (k6_partfun1 @ sk_A))
% 4.25/4.45          | ((sk_A) = (k1_xboole_0))
% 4.25/4.45          | ~ (v2_funct_1 @ X0)
% 4.25/4.45          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 4.25/4.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 4.25/4.45          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 4.25/4.45          | ~ (v1_funct_1 @ X0))),
% 4.25/4.45      inference('simplify', [status(thm)], ['54'])).
% 4.25/4.45  thf('56', plain,
% 4.25/4.45      ((~ (v1_funct_1 @ sk_B)
% 4.25/4.45        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 4.25/4.45        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 4.25/4.45        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 4.25/4.45        | ~ (v2_funct_1 @ sk_B)
% 4.25/4.45        | ((sk_A) = (k1_xboole_0))
% 4.25/4.45        | ((sk_C_1) = (k2_funct_1 @ sk_B)))),
% 4.25/4.45      inference('sup-', [status(thm)], ['48', '55'])).
% 4.25/4.45  thf('57', plain, ((v1_funct_1 @ sk_B)),
% 4.25/4.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.45  thf('58', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 4.25/4.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.45  thf('59', plain,
% 4.25/4.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.25/4.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.45  thf('60', plain,
% 4.25/4.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.25/4.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.45  thf(redefinition_k2_relset_1, axiom,
% 4.25/4.45    (![A:$i,B:$i,C:$i]:
% 4.25/4.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.25/4.45       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 4.25/4.45  thf('61', plain,
% 4.25/4.45      (![X21 : $i, X22 : $i, X23 : $i]:
% 4.25/4.45         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 4.25/4.45          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 4.25/4.45      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.25/4.45  thf('62', plain,
% 4.25/4.45      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 4.25/4.45      inference('sup-', [status(thm)], ['60', '61'])).
% 4.25/4.45  thf('63', plain,
% 4.25/4.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.25/4.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.45  thf(cc2_funct_2, axiom,
% 4.25/4.45    (![A:$i,B:$i,C:$i]:
% 4.25/4.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.25/4.45       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 4.25/4.45         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 4.25/4.45  thf('64', plain,
% 4.25/4.45      (![X28 : $i, X29 : $i, X30 : $i]:
% 4.25/4.45         (~ (v1_funct_1 @ X28)
% 4.25/4.45          | ~ (v3_funct_2 @ X28 @ X29 @ X30)
% 4.25/4.45          | (v2_funct_2 @ X28 @ X30)
% 4.25/4.45          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 4.25/4.45      inference('cnf', [status(esa)], [cc2_funct_2])).
% 4.25/4.45  thf('65', plain,
% 4.25/4.45      (((v2_funct_2 @ sk_B @ sk_A)
% 4.25/4.45        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 4.25/4.45        | ~ (v1_funct_1 @ sk_B))),
% 4.25/4.45      inference('sup-', [status(thm)], ['63', '64'])).
% 4.25/4.45  thf('66', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 4.25/4.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.45  thf('67', plain, ((v1_funct_1 @ sk_B)),
% 4.25/4.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.45  thf('68', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 4.25/4.45      inference('demod', [status(thm)], ['65', '66', '67'])).
% 4.25/4.45  thf(d3_funct_2, axiom,
% 4.25/4.45    (![A:$i,B:$i]:
% 4.25/4.45     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 4.25/4.45       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 4.25/4.45  thf('69', plain,
% 4.25/4.45      (![X31 : $i, X32 : $i]:
% 4.25/4.45         (~ (v2_funct_2 @ X32 @ X31)
% 4.25/4.45          | ((k2_relat_1 @ X32) = (X31))
% 4.25/4.45          | ~ (v5_relat_1 @ X32 @ X31)
% 4.25/4.45          | ~ (v1_relat_1 @ X32))),
% 4.25/4.45      inference('cnf', [status(esa)], [d3_funct_2])).
% 4.25/4.45  thf('70', plain,
% 4.25/4.45      ((~ (v1_relat_1 @ sk_B)
% 4.25/4.45        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 4.25/4.45        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 4.25/4.45      inference('sup-', [status(thm)], ['68', '69'])).
% 4.25/4.45  thf('71', plain,
% 4.25/4.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.25/4.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.45  thf(cc1_relset_1, axiom,
% 4.25/4.45    (![A:$i,B:$i,C:$i]:
% 4.25/4.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.25/4.45       ( v1_relat_1 @ C ) ))).
% 4.25/4.45  thf('72', plain,
% 4.25/4.45      (![X12 : $i, X13 : $i, X14 : $i]:
% 4.25/4.45         ((v1_relat_1 @ X12)
% 4.25/4.45          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 4.25/4.45      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.25/4.45  thf('73', plain, ((v1_relat_1 @ sk_B)),
% 4.25/4.45      inference('sup-', [status(thm)], ['71', '72'])).
% 4.25/4.45  thf('74', plain,
% 4.25/4.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.25/4.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.45  thf(cc2_relset_1, axiom,
% 4.25/4.45    (![A:$i,B:$i,C:$i]:
% 4.25/4.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.25/4.45       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 4.25/4.45  thf('75', plain,
% 4.25/4.45      (![X15 : $i, X16 : $i, X17 : $i]:
% 4.25/4.45         ((v5_relat_1 @ X15 @ X17)
% 4.25/4.45          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 4.25/4.45      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.25/4.45  thf('76', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 4.25/4.45      inference('sup-', [status(thm)], ['74', '75'])).
% 4.25/4.45  thf('77', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 4.25/4.45      inference('demod', [status(thm)], ['70', '73', '76'])).
% 4.25/4.45  thf('78', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 4.25/4.45      inference('demod', [status(thm)], ['62', '77'])).
% 4.25/4.45  thf('79', plain,
% 4.25/4.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.25/4.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.45  thf('80', plain,
% 4.25/4.45      (![X28 : $i, X29 : $i, X30 : $i]:
% 4.25/4.45         (~ (v1_funct_1 @ X28)
% 4.25/4.45          | ~ (v3_funct_2 @ X28 @ X29 @ X30)
% 4.25/4.45          | (v2_funct_1 @ X28)
% 4.25/4.45          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 4.25/4.45      inference('cnf', [status(esa)], [cc2_funct_2])).
% 4.25/4.45  thf('81', plain,
% 4.25/4.45      (((v2_funct_1 @ sk_B)
% 4.25/4.45        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 4.25/4.45        | ~ (v1_funct_1 @ sk_B))),
% 4.25/4.45      inference('sup-', [status(thm)], ['79', '80'])).
% 4.25/4.45  thf('82', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 4.25/4.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.45  thf('83', plain, ((v1_funct_1 @ sk_B)),
% 4.25/4.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.45  thf('84', plain, ((v2_funct_1 @ sk_B)),
% 4.25/4.45      inference('demod', [status(thm)], ['81', '82', '83'])).
% 4.25/4.45  thf('85', plain,
% 4.25/4.45      ((((sk_A) != (sk_A))
% 4.25/4.45        | ((sk_A) = (k1_xboole_0))
% 4.25/4.45        | ((sk_C_1) = (k2_funct_1 @ sk_B)))),
% 4.25/4.45      inference('demod', [status(thm)], ['56', '57', '58', '59', '78', '84'])).
% 4.25/4.45  thf('86', plain,
% 4.25/4.45      ((((sk_C_1) = (k2_funct_1 @ sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 4.25/4.45      inference('simplify', [status(thm)], ['85'])).
% 4.25/4.45  thf('87', plain,
% 4.25/4.45      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ (k2_funct_1 @ sk_B))),
% 4.25/4.45      inference('demod', [status(thm)], ['22', '29'])).
% 4.25/4.45  thf('88', plain,
% 4.25/4.45      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_C_1)
% 4.25/4.45        | ((sk_A) = (k1_xboole_0)))),
% 4.25/4.45      inference('sup-', [status(thm)], ['86', '87'])).
% 4.25/4.45  thf('89', plain,
% 4.25/4.45      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.25/4.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.45  thf('90', plain,
% 4.25/4.45      (![X25 : $i, X26 : $i, X27 : $i]:
% 4.25/4.45         ((r2_relset_1 @ X25 @ X26 @ X27 @ X27)
% 4.25/4.45          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 4.25/4.45      inference('simplify', [status(thm)], ['13'])).
% 4.25/4.45  thf('91', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_C_1)),
% 4.25/4.45      inference('sup-', [status(thm)], ['89', '90'])).
% 4.25/4.45  thf('92', plain, (((sk_A) = (k1_xboole_0))),
% 4.25/4.45      inference('demod', [status(thm)], ['88', '91'])).
% 4.25/4.45  thf('93', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.25/4.45      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.25/4.45  thf('94', plain, ($false),
% 4.25/4.45      inference('demod', [status(thm)], ['47', '92', '93'])).
% 4.25/4.45  
% 4.25/4.45  % SZS output end Refutation
% 4.25/4.45  
% 4.25/4.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
