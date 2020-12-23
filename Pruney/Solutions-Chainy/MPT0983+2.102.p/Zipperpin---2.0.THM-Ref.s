%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YWQCqEM0wj

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:17 EST 2020

% Result     : Theorem 2.34s
% Output     : Refutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 322 expanded)
%              Number of leaves         :   44 ( 111 expanded)
%              Depth                    :   14
%              Number of atoms          : 1391 (5062 expanded)
%              Number of equality atoms :   47 (  79 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t29_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
           => ( ( v2_funct_1 @ C )
              & ( v2_funct_2 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
             => ( ( v2_funct_1 @ C )
                & ( v2_funct_2 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_funct_2])).

thf('0',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('4',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ ( k6_partfun1 @ B ) )
           => ( ( k2_relset_1 @ A @ B @ C )
              = B ) ) ) ) )).

thf('6',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( r2_relset_1 @ X44 @ X44 @ ( k1_partfun1 @ X44 @ X45 @ X45 @ X44 @ X43 @ X46 ) @ ( k6_partfun1 @ X44 ) )
      | ( ( k2_relset_1 @ X45 @ X44 @ X46 )
        = X44 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X46 @ X45 @ X44 )
      | ~ ( v1_funct_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('7',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('8',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( r2_relset_1 @ X44 @ X44 @ ( k1_partfun1 @ X44 @ X45 @ X45 @ X44 @ X43 @ X46 ) @ ( k6_relat_1 @ X44 ) )
      | ( ( k2_relset_1 @ X45 @ X44 @ X46 )
        = X44 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X46 @ X45 @ X44 )
      | ~ ( v1_funct_1 @ X46 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['4','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('15',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X28 @ X26 )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('16',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['13','16','17','18','19'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['21'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('23',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ X18 )
      | ( v5_relat_1 @ X17 @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('25',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k2_relat_1 @ X35 )
       != X34 )
      | ( v2_funct_2 @ X35 @ X34 )
      | ~ ( v5_relat_1 @ X35 @ X34 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('26',plain,(
    ! [X35: $i] :
      ( ~ ( v1_relat_1 @ X35 )
      | ~ ( v5_relat_1 @ X35 @ ( k2_relat_1 @ X35 ) )
      | ( v2_funct_2 @ X35 @ ( k2_relat_1 @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['20','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('31',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('32',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','37'])).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('39',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_xboole_0 @ X9 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('40',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_xboole_0 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ( X7 = X8 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = X2 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_xboole_0 @ X9 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('43',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('44',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_xboole_0 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ( X7 = X8 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('48',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('49',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('50',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( r2_relset_1 @ X30 @ X31 @ X29 @ X32 )
      | ( X29 != X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('51',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( r2_relset_1 @ X30 @ X31 @ X32 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['46','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['41','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( r2_relset_1 @ X2 @ X1 @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('57',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('58',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('59',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('60',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X25 ) ) )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( k1_xboole_0
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf('65',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_xboole_0 @ X9 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('66',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('67',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf('71',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('72',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['57','72'])).

thf('74',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('75',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( X29 = X32 )
      | ~ ( r2_relset_1 @ X30 @ X31 @ X29 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      | ( k1_xboole_0 = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k1_xboole_0 = sk_C_1 )
    | ~ ( r2_relset_1 @ sk_A @ sk_B @ k1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['56','77'])).

thf('79',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_A )
    | ( k1_xboole_0 = sk_C_1 ) ),
    inference('sup-',[status(thm)],['55','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X25 ) ) )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('82',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k1_xboole_0 = sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['79','82'])).

thf('84',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('85',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('87',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['85','90'])).

thf('92',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( X29 = X32 )
      | ~ ( r2_relset_1 @ X30 @ X31 @ X29 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','95'])).

thf('97',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('98',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
           => ( ( ( C = k1_xboole_0 )
                & ( B != k1_xboole_0 ) )
              | ( v2_funct_1 @ D ) ) ) ) ) )).

thf('100',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X50 @ X48 @ X48 @ X49 @ X51 @ X47 ) )
      | ( v2_funct_1 @ X51 )
      | ( X49 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X48 ) ) )
      | ~ ( v1_funct_2 @ X51 @ X50 @ X48 )
      | ~ ( v1_funct_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['98','104'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('106',plain,(
    ! [X19: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('107',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( v2_funct_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['105','106','107','108','109'])).

thf('111',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','37'])).

thf('112',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('114',plain,(
    k1_xboole_0 = sk_C_1 ),
    inference(demod,[status(thm)],['83','112','113'])).

thf('115',plain,
    ( k1_xboole_0
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf('116',plain,(
    ! [X19: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('117',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    $false ),
    inference(demod,[status(thm)],['38','114','117'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YWQCqEM0wj
% 0.14/0.37  % Computer   : n004.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 14:15:39 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 2.34/2.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.34/2.56  % Solved by: fo/fo7.sh
% 2.34/2.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.34/2.56  % done 2955 iterations in 2.089s
% 2.34/2.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.34/2.56  % SZS output start Refutation
% 2.34/2.56  thf(sk_A_type, type, sk_A: $i).
% 2.34/2.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.34/2.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.34/2.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.34/2.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.34/2.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.34/2.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.34/2.56  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.34/2.56  thf(sk_D_type, type, sk_D: $i).
% 2.34/2.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.34/2.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.34/2.56  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.34/2.56  thf(sk_B_type, type, sk_B: $i).
% 2.34/2.56  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.34/2.56  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.34/2.56  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.34/2.56  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.34/2.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.34/2.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.34/2.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.34/2.56  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 2.34/2.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.34/2.56  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.34/2.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.34/2.56  thf(t29_funct_2, conjecture,
% 2.34/2.56    (![A:$i,B:$i,C:$i]:
% 2.34/2.56     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.34/2.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.34/2.56       ( ![D:$i]:
% 2.34/2.56         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.34/2.56             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.34/2.56           ( ( r2_relset_1 @
% 2.34/2.56               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.34/2.56               ( k6_partfun1 @ A ) ) =>
% 2.34/2.56             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 2.34/2.56  thf(zf_stmt_0, negated_conjecture,
% 2.34/2.56    (~( ![A:$i,B:$i,C:$i]:
% 2.34/2.56        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.34/2.56            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.34/2.56          ( ![D:$i]:
% 2.34/2.56            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.34/2.56                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.34/2.56              ( ( r2_relset_1 @
% 2.34/2.56                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.34/2.56                  ( k6_partfun1 @ A ) ) =>
% 2.34/2.56                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 2.34/2.56    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 2.34/2.56  thf('0', plain, ((~ (v2_funct_1 @ sk_C_1) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 2.34/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.56  thf('1', plain, ((~ (v2_funct_1 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 2.34/2.56      inference('split', [status(esa)], ['0'])).
% 2.34/2.56  thf('2', plain,
% 2.34/2.56      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.34/2.56        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ 
% 2.34/2.56        (k6_partfun1 @ sk_A))),
% 2.34/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.56  thf(redefinition_k6_partfun1, axiom,
% 2.34/2.56    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.34/2.56  thf('3', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 2.34/2.56      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.34/2.56  thf('4', plain,
% 2.34/2.56      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.34/2.56        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ 
% 2.34/2.56        (k6_relat_1 @ sk_A))),
% 2.34/2.56      inference('demod', [status(thm)], ['2', '3'])).
% 2.34/2.56  thf('5', plain,
% 2.34/2.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.34/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.56  thf(t24_funct_2, axiom,
% 2.34/2.56    (![A:$i,B:$i,C:$i]:
% 2.34/2.56     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.34/2.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.34/2.56       ( ![D:$i]:
% 2.34/2.56         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.34/2.56             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.34/2.56           ( ( r2_relset_1 @
% 2.34/2.56               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 2.34/2.56               ( k6_partfun1 @ B ) ) =>
% 2.34/2.56             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 2.34/2.56  thf('6', plain,
% 2.34/2.56      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 2.34/2.56         (~ (v1_funct_1 @ X43)
% 2.34/2.56          | ~ (v1_funct_2 @ X43 @ X44 @ X45)
% 2.34/2.56          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 2.34/2.56          | ~ (r2_relset_1 @ X44 @ X44 @ 
% 2.34/2.56               (k1_partfun1 @ X44 @ X45 @ X45 @ X44 @ X43 @ X46) @ 
% 2.34/2.56               (k6_partfun1 @ X44))
% 2.34/2.56          | ((k2_relset_1 @ X45 @ X44 @ X46) = (X44))
% 2.34/2.56          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 2.34/2.56          | ~ (v1_funct_2 @ X46 @ X45 @ X44)
% 2.34/2.56          | ~ (v1_funct_1 @ X46))),
% 2.34/2.56      inference('cnf', [status(esa)], [t24_funct_2])).
% 2.34/2.56  thf('7', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 2.34/2.56      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.34/2.56  thf('8', plain,
% 2.34/2.56      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 2.34/2.56         (~ (v1_funct_1 @ X43)
% 2.34/2.56          | ~ (v1_funct_2 @ X43 @ X44 @ X45)
% 2.34/2.56          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 2.34/2.56          | ~ (r2_relset_1 @ X44 @ X44 @ 
% 2.34/2.56               (k1_partfun1 @ X44 @ X45 @ X45 @ X44 @ X43 @ X46) @ 
% 2.34/2.56               (k6_relat_1 @ X44))
% 2.34/2.56          | ((k2_relset_1 @ X45 @ X44 @ X46) = (X44))
% 2.34/2.56          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 2.34/2.56          | ~ (v1_funct_2 @ X46 @ X45 @ X44)
% 2.34/2.56          | ~ (v1_funct_1 @ X46))),
% 2.34/2.56      inference('demod', [status(thm)], ['6', '7'])).
% 2.34/2.56  thf('9', plain,
% 2.34/2.56      (![X0 : $i]:
% 2.34/2.56         (~ (v1_funct_1 @ X0)
% 2.34/2.56          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.34/2.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.34/2.56          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.34/2.56          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.34/2.56               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 2.34/2.56               (k6_relat_1 @ sk_A))
% 2.34/2.56          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)
% 2.34/2.56          | ~ (v1_funct_1 @ sk_C_1))),
% 2.34/2.56      inference('sup-', [status(thm)], ['5', '8'])).
% 2.34/2.56  thf('10', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 2.34/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.56  thf('11', plain, ((v1_funct_1 @ sk_C_1)),
% 2.34/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.56  thf('12', plain,
% 2.34/2.56      (![X0 : $i]:
% 2.34/2.56         (~ (v1_funct_1 @ X0)
% 2.34/2.56          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.34/2.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.34/2.56          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.34/2.56          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.34/2.56               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 2.34/2.56               (k6_relat_1 @ sk_A)))),
% 2.34/2.56      inference('demod', [status(thm)], ['9', '10', '11'])).
% 2.34/2.56  thf('13', plain,
% 2.34/2.56      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 2.34/2.56        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.34/2.56        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.34/2.56        | ~ (v1_funct_1 @ sk_D))),
% 2.34/2.56      inference('sup-', [status(thm)], ['4', '12'])).
% 2.34/2.56  thf('14', plain,
% 2.34/2.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.34/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.56  thf(redefinition_k2_relset_1, axiom,
% 2.34/2.56    (![A:$i,B:$i,C:$i]:
% 2.34/2.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.34/2.56       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.34/2.56  thf('15', plain,
% 2.34/2.56      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.34/2.56         (((k2_relset_1 @ X27 @ X28 @ X26) = (k2_relat_1 @ X26))
% 2.34/2.56          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 2.34/2.56      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.34/2.56  thf('16', plain,
% 2.34/2.56      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.34/2.56      inference('sup-', [status(thm)], ['14', '15'])).
% 2.34/2.56  thf('17', plain,
% 2.34/2.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.34/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.56  thf('18', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.34/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.56  thf('19', plain, ((v1_funct_1 @ sk_D)),
% 2.34/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.56  thf('20', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.34/2.56      inference('demod', [status(thm)], ['13', '16', '17', '18', '19'])).
% 2.34/2.56  thf(d10_xboole_0, axiom,
% 2.34/2.56    (![A:$i,B:$i]:
% 2.34/2.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.34/2.56  thf('21', plain,
% 2.34/2.56      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 2.34/2.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.34/2.56  thf('22', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 2.34/2.56      inference('simplify', [status(thm)], ['21'])).
% 2.34/2.56  thf(d19_relat_1, axiom,
% 2.34/2.56    (![A:$i,B:$i]:
% 2.34/2.56     ( ( v1_relat_1 @ B ) =>
% 2.34/2.56       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 2.34/2.56  thf('23', plain,
% 2.34/2.56      (![X17 : $i, X18 : $i]:
% 2.34/2.56         (~ (r1_tarski @ (k2_relat_1 @ X17) @ X18)
% 2.34/2.56          | (v5_relat_1 @ X17 @ X18)
% 2.34/2.56          | ~ (v1_relat_1 @ X17))),
% 2.34/2.56      inference('cnf', [status(esa)], [d19_relat_1])).
% 2.34/2.56  thf('24', plain,
% 2.34/2.56      (![X0 : $i]:
% 2.34/2.56         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 2.34/2.56      inference('sup-', [status(thm)], ['22', '23'])).
% 2.34/2.56  thf(d3_funct_2, axiom,
% 2.34/2.56    (![A:$i,B:$i]:
% 2.34/2.56     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 2.34/2.56       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 2.34/2.56  thf('25', plain,
% 2.34/2.56      (![X34 : $i, X35 : $i]:
% 2.34/2.56         (((k2_relat_1 @ X35) != (X34))
% 2.34/2.56          | (v2_funct_2 @ X35 @ X34)
% 2.34/2.56          | ~ (v5_relat_1 @ X35 @ X34)
% 2.34/2.56          | ~ (v1_relat_1 @ X35))),
% 2.34/2.56      inference('cnf', [status(esa)], [d3_funct_2])).
% 2.34/2.56  thf('26', plain,
% 2.34/2.56      (![X35 : $i]:
% 2.34/2.56         (~ (v1_relat_1 @ X35)
% 2.34/2.56          | ~ (v5_relat_1 @ X35 @ (k2_relat_1 @ X35))
% 2.34/2.56          | (v2_funct_2 @ X35 @ (k2_relat_1 @ X35)))),
% 2.34/2.56      inference('simplify', [status(thm)], ['25'])).
% 2.34/2.56  thf('27', plain,
% 2.34/2.56      (![X0 : $i]:
% 2.34/2.56         (~ (v1_relat_1 @ X0)
% 2.34/2.56          | (v2_funct_2 @ X0 @ (k2_relat_1 @ X0))
% 2.34/2.56          | ~ (v1_relat_1 @ X0))),
% 2.34/2.56      inference('sup-', [status(thm)], ['24', '26'])).
% 2.34/2.56  thf('28', plain,
% 2.34/2.56      (![X0 : $i]:
% 2.34/2.56         ((v2_funct_2 @ X0 @ (k2_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 2.34/2.56      inference('simplify', [status(thm)], ['27'])).
% 2.34/2.56  thf('29', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 2.34/2.56      inference('sup+', [status(thm)], ['20', '28'])).
% 2.34/2.56  thf('30', plain,
% 2.34/2.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.34/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.56  thf(cc1_relset_1, axiom,
% 2.34/2.56    (![A:$i,B:$i,C:$i]:
% 2.34/2.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.34/2.56       ( v1_relat_1 @ C ) ))).
% 2.34/2.56  thf('31', plain,
% 2.34/2.56      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.34/2.56         ((v1_relat_1 @ X20)
% 2.34/2.56          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 2.34/2.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.34/2.56  thf('32', plain, ((v1_relat_1 @ sk_D)),
% 2.34/2.56      inference('sup-', [status(thm)], ['30', '31'])).
% 2.34/2.56  thf('33', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 2.34/2.56      inference('demod', [status(thm)], ['29', '32'])).
% 2.34/2.56  thf('34', plain,
% 2.34/2.56      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 2.34/2.56      inference('split', [status(esa)], ['0'])).
% 2.34/2.56  thf('35', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 2.34/2.56      inference('sup-', [status(thm)], ['33', '34'])).
% 2.34/2.56  thf('36', plain,
% 2.34/2.56      (~ ((v2_funct_1 @ sk_C_1)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 2.34/2.56      inference('split', [status(esa)], ['0'])).
% 2.34/2.56  thf('37', plain, (~ ((v2_funct_1 @ sk_C_1))),
% 2.34/2.56      inference('sat_resolution*', [status(thm)], ['35', '36'])).
% 2.34/2.56  thf('38', plain, (~ (v2_funct_1 @ sk_C_1)),
% 2.34/2.56      inference('simpl_trail', [status(thm)], ['1', '37'])).
% 2.34/2.56  thf(fc4_zfmisc_1, axiom,
% 2.34/2.56    (![A:$i,B:$i]:
% 2.34/2.56     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 2.34/2.56  thf('39', plain,
% 2.34/2.56      (![X9 : $i, X10 : $i]:
% 2.34/2.56         (~ (v1_xboole_0 @ X9) | (v1_xboole_0 @ (k2_zfmisc_1 @ X9 @ X10)))),
% 2.34/2.56      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 2.34/2.56  thf(t8_boole, axiom,
% 2.34/2.56    (![A:$i,B:$i]:
% 2.34/2.56     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 2.34/2.56  thf('40', plain,
% 2.34/2.56      (![X7 : $i, X8 : $i]:
% 2.34/2.56         (~ (v1_xboole_0 @ X7) | ~ (v1_xboole_0 @ X8) | ((X7) = (X8)))),
% 2.34/2.56      inference('cnf', [status(esa)], [t8_boole])).
% 2.34/2.56  thf('41', plain,
% 2.34/2.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.34/2.56         (~ (v1_xboole_0 @ X1)
% 2.34/2.56          | ((k2_zfmisc_1 @ X1 @ X0) = (X2))
% 2.34/2.56          | ~ (v1_xboole_0 @ X2))),
% 2.34/2.56      inference('sup-', [status(thm)], ['39', '40'])).
% 2.34/2.56  thf('42', plain,
% 2.34/2.56      (![X9 : $i, X10 : $i]:
% 2.34/2.56         (~ (v1_xboole_0 @ X9) | (v1_xboole_0 @ (k2_zfmisc_1 @ X9 @ X10)))),
% 2.34/2.56      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 2.34/2.56  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.34/2.56  thf('43', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.34/2.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.34/2.56  thf('44', plain,
% 2.34/2.56      (![X7 : $i, X8 : $i]:
% 2.34/2.56         (~ (v1_xboole_0 @ X7) | ~ (v1_xboole_0 @ X8) | ((X7) = (X8)))),
% 2.34/2.56      inference('cnf', [status(esa)], [t8_boole])).
% 2.34/2.56  thf('45', plain,
% 2.34/2.56      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 2.34/2.56      inference('sup-', [status(thm)], ['43', '44'])).
% 2.34/2.56  thf('46', plain,
% 2.34/2.56      (![X0 : $i, X1 : $i]:
% 2.34/2.56         (~ (v1_xboole_0 @ X1) | ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0)))),
% 2.34/2.56      inference('sup-', [status(thm)], ['42', '45'])).
% 2.34/2.56  thf('47', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 2.34/2.56      inference('simplify', [status(thm)], ['21'])).
% 2.34/2.56  thf(t3_subset, axiom,
% 2.34/2.56    (![A:$i,B:$i]:
% 2.34/2.56     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.34/2.57  thf('48', plain,
% 2.34/2.57      (![X11 : $i, X13 : $i]:
% 2.34/2.57         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 2.34/2.57      inference('cnf', [status(esa)], [t3_subset])).
% 2.34/2.57  thf('49', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.34/2.57      inference('sup-', [status(thm)], ['47', '48'])).
% 2.34/2.57  thf(redefinition_r2_relset_1, axiom,
% 2.34/2.57    (![A:$i,B:$i,C:$i,D:$i]:
% 2.34/2.57     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.34/2.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.34/2.57       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.34/2.57  thf('50', plain,
% 2.34/2.57      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 2.34/2.57         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 2.34/2.57          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 2.34/2.57          | (r2_relset_1 @ X30 @ X31 @ X29 @ X32)
% 2.34/2.57          | ((X29) != (X32)))),
% 2.34/2.57      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.34/2.57  thf('51', plain,
% 2.34/2.57      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.34/2.57         ((r2_relset_1 @ X30 @ X31 @ X32 @ X32)
% 2.34/2.57          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 2.34/2.57      inference('simplify', [status(thm)], ['50'])).
% 2.34/2.57  thf('52', plain,
% 2.34/2.57      (![X0 : $i, X1 : $i]:
% 2.34/2.57         (r2_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 2.34/2.57          (k2_zfmisc_1 @ X1 @ X0))),
% 2.34/2.57      inference('sup-', [status(thm)], ['49', '51'])).
% 2.34/2.57  thf('53', plain,
% 2.34/2.57      (![X0 : $i, X1 : $i]:
% 2.34/2.57         ((r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 2.34/2.57          | ~ (v1_xboole_0 @ X1))),
% 2.34/2.57      inference('sup+', [status(thm)], ['46', '52'])).
% 2.34/2.57  thf('54', plain,
% 2.34/2.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.34/2.57         ((r2_relset_1 @ X2 @ X1 @ k1_xboole_0 @ X0)
% 2.34/2.57          | ~ (v1_xboole_0 @ X0)
% 2.34/2.57          | ~ (v1_xboole_0 @ X2)
% 2.34/2.57          | ~ (v1_xboole_0 @ X2))),
% 2.34/2.57      inference('sup+', [status(thm)], ['41', '53'])).
% 2.34/2.57  thf('55', plain,
% 2.34/2.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.34/2.57         (~ (v1_xboole_0 @ X2)
% 2.34/2.57          | ~ (v1_xboole_0 @ X0)
% 2.34/2.57          | (r2_relset_1 @ X2 @ X1 @ k1_xboole_0 @ X0))),
% 2.34/2.57      inference('simplify', [status(thm)], ['54'])).
% 2.34/2.57  thf('56', plain,
% 2.34/2.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.34/2.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.57  thf(d3_tarski, axiom,
% 2.34/2.57    (![A:$i,B:$i]:
% 2.34/2.57     ( ( r1_tarski @ A @ B ) <=>
% 2.34/2.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.34/2.57  thf('57', plain,
% 2.34/2.57      (![X1 : $i, X3 : $i]:
% 2.34/2.57         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 2.34/2.57      inference('cnf', [status(esa)], [d3_tarski])).
% 2.34/2.57  thf('58', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.34/2.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.34/2.57  thf(t29_relset_1, axiom,
% 2.34/2.57    (![A:$i]:
% 2.34/2.57     ( m1_subset_1 @
% 2.34/2.57       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 2.34/2.57  thf('59', plain,
% 2.34/2.57      (![X33 : $i]:
% 2.34/2.57         (m1_subset_1 @ (k6_relat_1 @ X33) @ 
% 2.34/2.57          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 2.34/2.57      inference('cnf', [status(esa)], [t29_relset_1])).
% 2.34/2.57  thf(cc3_relset_1, axiom,
% 2.34/2.57    (![A:$i,B:$i]:
% 2.34/2.57     ( ( v1_xboole_0 @ A ) =>
% 2.34/2.57       ( ![C:$i]:
% 2.34/2.57         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.34/2.57           ( v1_xboole_0 @ C ) ) ) ))).
% 2.34/2.57  thf('60', plain,
% 2.34/2.57      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.34/2.57         (~ (v1_xboole_0 @ X23)
% 2.34/2.57          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X25)))
% 2.34/2.57          | (v1_xboole_0 @ X24))),
% 2.34/2.57      inference('cnf', [status(esa)], [cc3_relset_1])).
% 2.34/2.57  thf('61', plain,
% 2.34/2.57      (![X0 : $i]: ((v1_xboole_0 @ (k6_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 2.34/2.57      inference('sup-', [status(thm)], ['59', '60'])).
% 2.34/2.57  thf('62', plain,
% 2.34/2.57      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 2.34/2.57      inference('sup-', [status(thm)], ['43', '44'])).
% 2.34/2.57  thf('63', plain,
% 2.34/2.57      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (k6_relat_1 @ X0)))),
% 2.34/2.57      inference('sup-', [status(thm)], ['61', '62'])).
% 2.34/2.57  thf('64', plain, (((k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 2.34/2.57      inference('sup-', [status(thm)], ['58', '63'])).
% 2.34/2.57  thf('65', plain,
% 2.34/2.57      (![X9 : $i, X10 : $i]:
% 2.34/2.57         (~ (v1_xboole_0 @ X9) | (v1_xboole_0 @ (k2_zfmisc_1 @ X9 @ X10)))),
% 2.34/2.57      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 2.34/2.57  thf('66', plain,
% 2.34/2.57      (![X33 : $i]:
% 2.34/2.57         (m1_subset_1 @ (k6_relat_1 @ X33) @ 
% 2.34/2.57          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 2.34/2.57      inference('cnf', [status(esa)], [t29_relset_1])).
% 2.34/2.57  thf(t5_subset, axiom,
% 2.34/2.57    (![A:$i,B:$i,C:$i]:
% 2.34/2.57     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 2.34/2.57          ( v1_xboole_0 @ C ) ) ))).
% 2.34/2.57  thf('67', plain,
% 2.34/2.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.34/2.57         (~ (r2_hidden @ X14 @ X15)
% 2.34/2.57          | ~ (v1_xboole_0 @ X16)
% 2.34/2.57          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 2.34/2.57      inference('cnf', [status(esa)], [t5_subset])).
% 2.34/2.57  thf('68', plain,
% 2.34/2.57      (![X0 : $i, X1 : $i]:
% 2.34/2.57         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X0))
% 2.34/2.57          | ~ (r2_hidden @ X1 @ (k6_relat_1 @ X0)))),
% 2.34/2.57      inference('sup-', [status(thm)], ['66', '67'])).
% 2.34/2.57  thf('69', plain,
% 2.34/2.57      (![X0 : $i, X1 : $i]:
% 2.34/2.57         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ (k6_relat_1 @ X0)))),
% 2.34/2.57      inference('sup-', [status(thm)], ['65', '68'])).
% 2.34/2.57  thf('70', plain,
% 2.34/2.57      (![X0 : $i]:
% 2.34/2.57         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 2.34/2.57      inference('sup-', [status(thm)], ['64', '69'])).
% 2.34/2.57  thf('71', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.34/2.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.34/2.57  thf('72', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 2.34/2.57      inference('demod', [status(thm)], ['70', '71'])).
% 2.34/2.57  thf('73', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 2.34/2.57      inference('sup-', [status(thm)], ['57', '72'])).
% 2.34/2.57  thf('74', plain,
% 2.34/2.57      (![X11 : $i, X13 : $i]:
% 2.34/2.57         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 2.34/2.57      inference('cnf', [status(esa)], [t3_subset])).
% 2.34/2.57  thf('75', plain,
% 2.34/2.57      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 2.34/2.57      inference('sup-', [status(thm)], ['73', '74'])).
% 2.34/2.57  thf('76', plain,
% 2.34/2.57      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 2.34/2.57         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 2.34/2.57          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 2.34/2.57          | ((X29) = (X32))
% 2.34/2.57          | ~ (r2_relset_1 @ X30 @ X31 @ X29 @ X32))),
% 2.34/2.57      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.34/2.57  thf('77', plain,
% 2.34/2.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.34/2.57         (~ (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 2.34/2.57          | ((k1_xboole_0) = (X2))
% 2.34/2.57          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 2.34/2.57      inference('sup-', [status(thm)], ['75', '76'])).
% 2.34/2.57  thf('78', plain,
% 2.34/2.57      ((((k1_xboole_0) = (sk_C_1))
% 2.34/2.57        | ~ (r2_relset_1 @ sk_A @ sk_B @ k1_xboole_0 @ sk_C_1))),
% 2.34/2.57      inference('sup-', [status(thm)], ['56', '77'])).
% 2.34/2.57  thf('79', plain,
% 2.34/2.57      ((~ (v1_xboole_0 @ sk_C_1)
% 2.34/2.57        | ~ (v1_xboole_0 @ sk_A)
% 2.34/2.57        | ((k1_xboole_0) = (sk_C_1)))),
% 2.34/2.57      inference('sup-', [status(thm)], ['55', '78'])).
% 2.34/2.57  thf('80', plain,
% 2.34/2.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.34/2.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.57  thf('81', plain,
% 2.34/2.57      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.34/2.57         (~ (v1_xboole_0 @ X23)
% 2.34/2.57          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X25)))
% 2.34/2.57          | (v1_xboole_0 @ X24))),
% 2.34/2.57      inference('cnf', [status(esa)], [cc3_relset_1])).
% 2.34/2.57  thf('82', plain, (((v1_xboole_0 @ sk_C_1) | ~ (v1_xboole_0 @ sk_A))),
% 2.34/2.57      inference('sup-', [status(thm)], ['80', '81'])).
% 2.34/2.57  thf('83', plain, ((((k1_xboole_0) = (sk_C_1)) | ~ (v1_xboole_0 @ sk_A))),
% 2.34/2.57      inference('clc', [status(thm)], ['79', '82'])).
% 2.34/2.57  thf('84', plain,
% 2.34/2.57      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.34/2.57        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ 
% 2.34/2.57        (k6_relat_1 @ sk_A))),
% 2.34/2.57      inference('demod', [status(thm)], ['2', '3'])).
% 2.34/2.57  thf('85', plain,
% 2.34/2.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.34/2.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.57  thf('86', plain,
% 2.34/2.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.34/2.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.57  thf(dt_k1_partfun1, axiom,
% 2.34/2.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.34/2.57     ( ( ( v1_funct_1 @ E ) & 
% 2.34/2.57         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.34/2.57         ( v1_funct_1 @ F ) & 
% 2.34/2.57         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.34/2.57       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.34/2.57         ( m1_subset_1 @
% 2.34/2.57           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.34/2.57           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.34/2.57  thf('87', plain,
% 2.34/2.57      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 2.34/2.57         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 2.34/2.57          | ~ (v1_funct_1 @ X36)
% 2.34/2.57          | ~ (v1_funct_1 @ X39)
% 2.34/2.57          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 2.34/2.57          | (m1_subset_1 @ (k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39) @ 
% 2.34/2.57             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X41))))),
% 2.34/2.57      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.34/2.57  thf('88', plain,
% 2.34/2.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.34/2.57         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 2.34/2.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.34/2.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.34/2.57          | ~ (v1_funct_1 @ X1)
% 2.34/2.57          | ~ (v1_funct_1 @ sk_C_1))),
% 2.34/2.57      inference('sup-', [status(thm)], ['86', '87'])).
% 2.34/2.57  thf('89', plain, ((v1_funct_1 @ sk_C_1)),
% 2.34/2.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.57  thf('90', plain,
% 2.34/2.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.34/2.57         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 2.34/2.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.34/2.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.34/2.57          | ~ (v1_funct_1 @ X1))),
% 2.34/2.57      inference('demod', [status(thm)], ['88', '89'])).
% 2.34/2.57  thf('91', plain,
% 2.34/2.57      ((~ (v1_funct_1 @ sk_D)
% 2.34/2.57        | (m1_subset_1 @ 
% 2.34/2.57           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ 
% 2.34/2.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.34/2.57      inference('sup-', [status(thm)], ['85', '90'])).
% 2.34/2.57  thf('92', plain, ((v1_funct_1 @ sk_D)),
% 2.34/2.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.57  thf('93', plain,
% 2.34/2.57      ((m1_subset_1 @ 
% 2.34/2.57        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ 
% 2.34/2.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.34/2.57      inference('demod', [status(thm)], ['91', '92'])).
% 2.34/2.57  thf('94', plain,
% 2.34/2.57      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 2.34/2.57         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 2.34/2.57          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 2.34/2.57          | ((X29) = (X32))
% 2.34/2.57          | ~ (r2_relset_1 @ X30 @ X31 @ X29 @ X32))),
% 2.34/2.57      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.34/2.57  thf('95', plain,
% 2.34/2.57      (![X0 : $i]:
% 2.34/2.57         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.34/2.57             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ X0)
% 2.34/2.57          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D) = (X0))
% 2.34/2.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.34/2.57      inference('sup-', [status(thm)], ['93', '94'])).
% 2.34/2.57  thf('96', plain,
% 2.34/2.57      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 2.34/2.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.34/2.57        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D)
% 2.34/2.57            = (k6_relat_1 @ sk_A)))),
% 2.34/2.57      inference('sup-', [status(thm)], ['84', '95'])).
% 2.34/2.57  thf('97', plain,
% 2.34/2.57      (![X33 : $i]:
% 2.34/2.57         (m1_subset_1 @ (k6_relat_1 @ X33) @ 
% 2.34/2.57          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 2.34/2.57      inference('cnf', [status(esa)], [t29_relset_1])).
% 2.34/2.57  thf('98', plain,
% 2.34/2.57      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D)
% 2.34/2.57         = (k6_relat_1 @ sk_A))),
% 2.34/2.57      inference('demod', [status(thm)], ['96', '97'])).
% 2.34/2.57  thf('99', plain,
% 2.34/2.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.34/2.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.57  thf(t26_funct_2, axiom,
% 2.34/2.57    (![A:$i,B:$i,C:$i,D:$i]:
% 2.34/2.57     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.34/2.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.34/2.57       ( ![E:$i]:
% 2.34/2.57         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.34/2.57             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.34/2.57           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 2.34/2.57             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 2.34/2.57               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 2.34/2.57  thf('100', plain,
% 2.34/2.57      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 2.34/2.57         (~ (v1_funct_1 @ X47)
% 2.34/2.57          | ~ (v1_funct_2 @ X47 @ X48 @ X49)
% 2.34/2.57          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 2.34/2.57          | ~ (v2_funct_1 @ (k1_partfun1 @ X50 @ X48 @ X48 @ X49 @ X51 @ X47))
% 2.34/2.57          | (v2_funct_1 @ X51)
% 2.34/2.57          | ((X49) = (k1_xboole_0))
% 2.34/2.57          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X48)))
% 2.34/2.57          | ~ (v1_funct_2 @ X51 @ X50 @ X48)
% 2.34/2.57          | ~ (v1_funct_1 @ X51))),
% 2.34/2.57      inference('cnf', [status(esa)], [t26_funct_2])).
% 2.34/2.57  thf('101', plain,
% 2.34/2.57      (![X0 : $i, X1 : $i]:
% 2.34/2.57         (~ (v1_funct_1 @ X0)
% 2.34/2.57          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.34/2.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.34/2.57          | ((sk_A) = (k1_xboole_0))
% 2.34/2.57          | (v2_funct_1 @ X0)
% 2.34/2.57          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 2.34/2.57          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.34/2.57          | ~ (v1_funct_1 @ sk_D))),
% 2.34/2.57      inference('sup-', [status(thm)], ['99', '100'])).
% 2.34/2.57  thf('102', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.34/2.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.57  thf('103', plain, ((v1_funct_1 @ sk_D)),
% 2.34/2.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.57  thf('104', plain,
% 2.34/2.57      (![X0 : $i, X1 : $i]:
% 2.34/2.57         (~ (v1_funct_1 @ X0)
% 2.34/2.57          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.34/2.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.34/2.57          | ((sk_A) = (k1_xboole_0))
% 2.34/2.57          | (v2_funct_1 @ X0)
% 2.34/2.57          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 2.34/2.57      inference('demod', [status(thm)], ['101', '102', '103'])).
% 2.34/2.57  thf('105', plain,
% 2.34/2.57      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 2.34/2.57        | (v2_funct_1 @ sk_C_1)
% 2.34/2.57        | ((sk_A) = (k1_xboole_0))
% 2.34/2.57        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 2.34/2.57        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)
% 2.34/2.57        | ~ (v1_funct_1 @ sk_C_1))),
% 2.34/2.57      inference('sup-', [status(thm)], ['98', '104'])).
% 2.34/2.57  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 2.34/2.57  thf('106', plain, (![X19 : $i]: (v2_funct_1 @ (k6_relat_1 @ X19))),
% 2.34/2.57      inference('cnf', [status(esa)], [t52_funct_1])).
% 2.34/2.57  thf('107', plain,
% 2.34/2.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.34/2.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.57  thf('108', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 2.34/2.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.57  thf('109', plain, ((v1_funct_1 @ sk_C_1)),
% 2.34/2.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.57  thf('110', plain, (((v2_funct_1 @ sk_C_1) | ((sk_A) = (k1_xboole_0)))),
% 2.34/2.57      inference('demod', [status(thm)], ['105', '106', '107', '108', '109'])).
% 2.34/2.57  thf('111', plain, (~ (v2_funct_1 @ sk_C_1)),
% 2.34/2.57      inference('simpl_trail', [status(thm)], ['1', '37'])).
% 2.34/2.57  thf('112', plain, (((sk_A) = (k1_xboole_0))),
% 2.34/2.57      inference('clc', [status(thm)], ['110', '111'])).
% 2.34/2.57  thf('113', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.34/2.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.34/2.57  thf('114', plain, (((k1_xboole_0) = (sk_C_1))),
% 2.34/2.57      inference('demod', [status(thm)], ['83', '112', '113'])).
% 2.34/2.57  thf('115', plain, (((k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 2.34/2.57      inference('sup-', [status(thm)], ['58', '63'])).
% 2.34/2.57  thf('116', plain, (![X19 : $i]: (v2_funct_1 @ (k6_relat_1 @ X19))),
% 2.34/2.57      inference('cnf', [status(esa)], [t52_funct_1])).
% 2.34/2.57  thf('117', plain, ((v2_funct_1 @ k1_xboole_0)),
% 2.34/2.57      inference('sup+', [status(thm)], ['115', '116'])).
% 2.34/2.57  thf('118', plain, ($false),
% 2.34/2.57      inference('demod', [status(thm)], ['38', '114', '117'])).
% 2.34/2.57  
% 2.34/2.57  % SZS output end Refutation
% 2.34/2.57  
% 2.34/2.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
