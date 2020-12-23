%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Vy3k2qJxoD

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:08 EST 2020

% Result     : Theorem 9.64s
% Output     : Refutation 9.64s
% Verified   : 
% Statistics : Number of formulae       :  176 (1106 expanded)
%              Number of leaves         :   46 ( 346 expanded)
%              Depth                    :   14
%              Number of atoms          : 1269 (25817 expanded)
%              Number of equality atoms :   96 ( 486 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('4',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

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

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( v4_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['4','10'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v4_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('15',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('17',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('18',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('19',plain,(
    ! [X37: $i] :
      ( ( k6_partfun1 @ X37 )
      = ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('20',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['18','19'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('21',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('22',plain,(
    ! [X37: $i] :
      ( ( k6_partfun1 @ X37 )
      = ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('23',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['13','17','24'])).

thf('26',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('28',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( r2_relset_1 @ X27 @ X28 @ X26 @ X29 )
      | ( X26 != X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('29',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( r2_relset_1 @ X27 @ X28 @ X29 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('33',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['18','19'])).

thf(t67_funct_1,axiom,(
    ! [A: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('34',plain,(
    ! [X19: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X19 ) )
      = ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_1])).

thf('35',plain,(
    ! [X37: $i] :
      ( ( k6_partfun1 @ X37 )
      = ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('36',plain,(
    ! [X37: $i] :
      ( ( k6_partfun1 @ X37 )
      = ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('37',plain,(
    ! [X19: $i] :
      ( ( k2_funct_1 @ ( k6_partfun1 @ X19 ) )
      = ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = ( k6_partfun1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','37'])).

thf('39',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['18','19'])).

thf('40',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','40'])).

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

thf('42',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
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

thf('44',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k2_funct_2 @ X36 @ X35 )
        = ( k2_funct_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) )
      | ~ ( v3_funct_2 @ X35 @ X36 @ X36 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X36 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('45',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B )
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['45','46','47','48'])).

thf('50',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','49'])).

thf('51',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['41','50'])).

thf('52',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['31','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('55',plain,(
    r1_tarski @ sk_B @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('57',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_B )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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

thf('60',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( X42
        = ( k2_funct_1 @ X45 ) )
      | ~ ( r2_relset_1 @ X44 @ X44 @ ( k1_partfun1 @ X44 @ X43 @ X43 @ X44 @ X45 @ X42 ) @ ( k6_partfun1 @ X44 ) )
      | ( X43 = k1_xboole_0 )
      | ( X44 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X45 )
      | ( ( k2_relset_1 @ X44 @ X43 @ X45 )
       != X43 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X45 @ X44 @ X43 )
      | ~ ( v1_funct_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t36_funct_2])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','65'])).

thf('67',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('71',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('72',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
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

thf('74',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_1 @ X30 )
      | ~ ( v3_funct_2 @ X30 @ X31 @ X32 )
      | ( v2_funct_2 @ X30 @ X32 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('75',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['75','76','77'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('79',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v2_funct_2 @ X34 @ X33 )
      | ( ( k2_relat_1 @ X34 )
        = X33 )
      | ~ ( v5_relat_1 @ X34 @ X33 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('80',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('82',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('83',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('85',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v5_relat_1 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('88',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['80','85','88'])).

thf('90',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['72','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_1 @ X30 )
      | ~ ( v3_funct_2 @ X30 @ X31 @ X32 )
      | ( v2_funct_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('93',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,
    ( ( sk_A != sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['66','67','68','69','90','96'])).

thf('98',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','49'])).

thf('100',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( r2_relset_1 @ X27 @ X28 @ X29 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('103',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['100','103'])).

thf('105',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['100','103'])).

thf('106',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('107',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['13','17','24'])).

thf('108',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['100','103'])).

thf('109',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['100','103'])).

thf('110',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('111',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['57','104','105','106','107','108','109','110'])).

thf('112',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('113',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['52','111','112'])).

thf('114',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('116',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('118',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['100','103'])).

thf('120',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['100','103'])).

thf('121',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('122',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['13','17','24'])).

thf('123',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['100','103'])).

thf('124',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['100','103'])).

thf('125',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('126',plain,(
    k1_xboole_0 = sk_C ),
    inference(demod,[status(thm)],['118','119','120','121','122','123','124','125'])).

thf('127',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('128',plain,(
    $false ),
    inference(demod,[status(thm)],['113','126','127'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Vy3k2qJxoD
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:34:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 9.64/9.83  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 9.64/9.83  % Solved by: fo/fo7.sh
% 9.64/9.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.64/9.83  % done 10830 iterations in 9.365s
% 9.64/9.83  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 9.64/9.83  % SZS output start Refutation
% 9.64/9.83  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 9.64/9.83  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 9.64/9.83  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 9.64/9.83  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 9.64/9.83  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 9.64/9.83  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 9.64/9.83  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 9.64/9.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 9.64/9.83  thf(sk_B_type, type, sk_B: $i).
% 9.64/9.83  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 9.64/9.83  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 9.64/9.83  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 9.64/9.83  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 9.64/9.83  thf(sk_A_type, type, sk_A: $i).
% 9.64/9.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 9.64/9.83  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 9.64/9.83  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 9.64/9.83  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 9.64/9.83  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 9.64/9.83  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 9.64/9.83  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 9.64/9.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 9.64/9.83  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 9.64/9.83  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 9.64/9.83  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 9.64/9.83  thf(sk_C_type, type, sk_C: $i).
% 9.64/9.83  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 9.64/9.83  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 9.64/9.83      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 9.64/9.83  thf(t8_boole, axiom,
% 9.64/9.83    (![A:$i,B:$i]:
% 9.64/9.83     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 9.64/9.83  thf('1', plain,
% 9.64/9.83      (![X3 : $i, X4 : $i]:
% 9.64/9.83         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 9.64/9.83      inference('cnf', [status(esa)], [t8_boole])).
% 9.64/9.83  thf('2', plain,
% 9.64/9.83      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 9.64/9.83      inference('sup-', [status(thm)], ['0', '1'])).
% 9.64/9.83  thf(t113_zfmisc_1, axiom,
% 9.64/9.83    (![A:$i,B:$i]:
% 9.64/9.83     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 9.64/9.83       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 9.64/9.83  thf('3', plain,
% 9.64/9.83      (![X6 : $i, X7 : $i]:
% 9.64/9.83         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 9.64/9.83      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 9.64/9.83  thf('4', plain,
% 9.64/9.83      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 9.64/9.83      inference('simplify', [status(thm)], ['3'])).
% 9.64/9.83  thf(d10_xboole_0, axiom,
% 9.64/9.83    (![A:$i,B:$i]:
% 9.64/9.83     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 9.64/9.83  thf('5', plain,
% 9.64/9.83      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 9.64/9.83      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.64/9.83  thf('6', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 9.64/9.83      inference('simplify', [status(thm)], ['5'])).
% 9.64/9.83  thf(t3_subset, axiom,
% 9.64/9.83    (![A:$i,B:$i]:
% 9.64/9.83     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 9.64/9.83  thf('7', plain,
% 9.64/9.83      (![X8 : $i, X10 : $i]:
% 9.64/9.83         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 9.64/9.83      inference('cnf', [status(esa)], [t3_subset])).
% 9.64/9.83  thf('8', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 9.64/9.83      inference('sup-', [status(thm)], ['6', '7'])).
% 9.64/9.83  thf(cc2_relset_1, axiom,
% 9.64/9.83    (![A:$i,B:$i,C:$i]:
% 9.64/9.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.64/9.83       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 9.64/9.83  thf('9', plain,
% 9.64/9.83      (![X20 : $i, X21 : $i, X22 : $i]:
% 9.64/9.83         ((v4_relat_1 @ X20 @ X21)
% 9.64/9.83          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 9.64/9.83      inference('cnf', [status(esa)], [cc2_relset_1])).
% 9.64/9.83  thf('10', plain,
% 9.64/9.83      (![X0 : $i, X1 : $i]: (v4_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X1)),
% 9.64/9.83      inference('sup-', [status(thm)], ['8', '9'])).
% 9.64/9.83  thf('11', plain, (![X0 : $i]: (v4_relat_1 @ k1_xboole_0 @ X0)),
% 9.64/9.83      inference('sup+', [status(thm)], ['4', '10'])).
% 9.64/9.83  thf(d18_relat_1, axiom,
% 9.64/9.83    (![A:$i,B:$i]:
% 9.64/9.83     ( ( v1_relat_1 @ B ) =>
% 9.64/9.83       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 9.64/9.83  thf('12', plain,
% 9.64/9.83      (![X13 : $i, X14 : $i]:
% 9.64/9.83         (~ (v4_relat_1 @ X13 @ X14)
% 9.64/9.83          | (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 9.64/9.83          | ~ (v1_relat_1 @ X13))),
% 9.64/9.83      inference('cnf', [status(esa)], [d18_relat_1])).
% 9.64/9.83  thf('13', plain,
% 9.64/9.83      (![X0 : $i]:
% 9.64/9.83         (~ (v1_relat_1 @ k1_xboole_0)
% 9.64/9.83          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 9.64/9.83      inference('sup-', [status(thm)], ['11', '12'])).
% 9.64/9.83  thf('14', plain,
% 9.64/9.83      (![X6 : $i, X7 : $i]:
% 9.64/9.83         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 9.64/9.83      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 9.64/9.83  thf('15', plain,
% 9.64/9.83      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 9.64/9.83      inference('simplify', [status(thm)], ['14'])).
% 9.64/9.83  thf(fc6_relat_1, axiom,
% 9.64/9.83    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 9.64/9.83  thf('16', plain,
% 9.64/9.83      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X15 @ X16))),
% 9.64/9.83      inference('cnf', [status(esa)], [fc6_relat_1])).
% 9.64/9.83  thf('17', plain, ((v1_relat_1 @ k1_xboole_0)),
% 9.64/9.83      inference('sup+', [status(thm)], ['15', '16'])).
% 9.64/9.83  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 9.64/9.83  thf('18', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 9.64/9.83      inference('cnf', [status(esa)], [t81_relat_1])).
% 9.64/9.83  thf(redefinition_k6_partfun1, axiom,
% 9.64/9.83    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 9.64/9.83  thf('19', plain, (![X37 : $i]: ((k6_partfun1 @ X37) = (k6_relat_1 @ X37))),
% 9.64/9.83      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 9.64/9.83  thf('20', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 9.64/9.83      inference('demod', [status(thm)], ['18', '19'])).
% 9.64/9.83  thf(t71_relat_1, axiom,
% 9.64/9.83    (![A:$i]:
% 9.64/9.83     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 9.64/9.83       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 9.64/9.83  thf('21', plain, (![X17 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X17)) = (X17))),
% 9.64/9.83      inference('cnf', [status(esa)], [t71_relat_1])).
% 9.64/9.83  thf('22', plain, (![X37 : $i]: ((k6_partfun1 @ X37) = (k6_relat_1 @ X37))),
% 9.64/9.83      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 9.64/9.83  thf('23', plain, (![X17 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X17)) = (X17))),
% 9.64/9.83      inference('demod', [status(thm)], ['21', '22'])).
% 9.64/9.83  thf('24', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 9.64/9.83      inference('sup+', [status(thm)], ['20', '23'])).
% 9.64/9.83  thf('25', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 9.64/9.83      inference('demod', [status(thm)], ['13', '17', '24'])).
% 9.64/9.83  thf('26', plain,
% 9.64/9.83      (![X8 : $i, X10 : $i]:
% 9.64/9.83         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 9.64/9.83      inference('cnf', [status(esa)], [t3_subset])).
% 9.64/9.83  thf('27', plain,
% 9.64/9.83      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 9.64/9.83      inference('sup-', [status(thm)], ['25', '26'])).
% 9.64/9.83  thf(redefinition_r2_relset_1, axiom,
% 9.64/9.83    (![A:$i,B:$i,C:$i,D:$i]:
% 9.64/9.83     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 9.64/9.83         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 9.64/9.83       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 9.64/9.83  thf('28', plain,
% 9.64/9.83      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 9.64/9.83         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 9.64/9.83          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 9.64/9.83          | (r2_relset_1 @ X27 @ X28 @ X26 @ X29)
% 9.64/9.83          | ((X26) != (X29)))),
% 9.64/9.83      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 9.64/9.83  thf('29', plain,
% 9.64/9.83      (![X27 : $i, X28 : $i, X29 : $i]:
% 9.64/9.83         ((r2_relset_1 @ X27 @ X28 @ X29 @ X29)
% 9.64/9.83          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 9.64/9.83      inference('simplify', [status(thm)], ['28'])).
% 9.64/9.83  thf('30', plain,
% 9.64/9.83      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 9.64/9.83      inference('sup-', [status(thm)], ['27', '29'])).
% 9.64/9.83  thf('31', plain,
% 9.64/9.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.64/9.83         ((r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 9.64/9.83      inference('sup+', [status(thm)], ['2', '30'])).
% 9.64/9.83  thf('32', plain,
% 9.64/9.83      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 9.64/9.83      inference('sup-', [status(thm)], ['0', '1'])).
% 9.64/9.83  thf('33', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 9.64/9.83      inference('demod', [status(thm)], ['18', '19'])).
% 9.64/9.83  thf(t67_funct_1, axiom,
% 9.64/9.83    (![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 9.64/9.83  thf('34', plain,
% 9.64/9.83      (![X19 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X19)) = (k6_relat_1 @ X19))),
% 9.64/9.83      inference('cnf', [status(esa)], [t67_funct_1])).
% 9.64/9.83  thf('35', plain, (![X37 : $i]: ((k6_partfun1 @ X37) = (k6_relat_1 @ X37))),
% 9.64/9.83      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 9.64/9.83  thf('36', plain, (![X37 : $i]: ((k6_partfun1 @ X37) = (k6_relat_1 @ X37))),
% 9.64/9.83      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 9.64/9.83  thf('37', plain,
% 9.64/9.83      (![X19 : $i]: ((k2_funct_1 @ (k6_partfun1 @ X19)) = (k6_partfun1 @ X19))),
% 9.64/9.83      inference('demod', [status(thm)], ['34', '35', '36'])).
% 9.64/9.83  thf('38', plain,
% 9.64/9.83      (((k2_funct_1 @ k1_xboole_0) = (k6_partfun1 @ k1_xboole_0))),
% 9.64/9.83      inference('sup+', [status(thm)], ['33', '37'])).
% 9.64/9.83  thf('39', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 9.64/9.83      inference('demod', [status(thm)], ['18', '19'])).
% 9.64/9.83  thf('40', plain, (((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))),
% 9.64/9.83      inference('sup+', [status(thm)], ['38', '39'])).
% 9.64/9.83  thf('41', plain,
% 9.64/9.83      (![X0 : $i]: (((k2_funct_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 9.64/9.83      inference('sup+', [status(thm)], ['32', '40'])).
% 9.64/9.83  thf(t87_funct_2, conjecture,
% 9.64/9.83    (![A:$i,B:$i]:
% 9.64/9.83     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 9.64/9.83         ( v3_funct_2 @ B @ A @ A ) & 
% 9.64/9.83         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 9.64/9.83       ( ![C:$i]:
% 9.64/9.83         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 9.64/9.83             ( v3_funct_2 @ C @ A @ A ) & 
% 9.64/9.83             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 9.64/9.83           ( ( r2_relset_1 @
% 9.64/9.83               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 9.64/9.83               ( k6_partfun1 @ A ) ) =>
% 9.64/9.83             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 9.64/9.83  thf(zf_stmt_0, negated_conjecture,
% 9.64/9.83    (~( ![A:$i,B:$i]:
% 9.64/9.83        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 9.64/9.83            ( v3_funct_2 @ B @ A @ A ) & 
% 9.64/9.83            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 9.64/9.83          ( ![C:$i]:
% 9.64/9.83            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 9.64/9.83                ( v3_funct_2 @ C @ A @ A ) & 
% 9.64/9.83                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 9.64/9.83              ( ( r2_relset_1 @
% 9.64/9.83                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 9.64/9.83                  ( k6_partfun1 @ A ) ) =>
% 9.64/9.83                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 9.64/9.83    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 9.64/9.83  thf('42', plain,
% 9.64/9.83      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B))),
% 9.64/9.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.83  thf('43', plain,
% 9.64/9.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.64/9.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.83  thf(redefinition_k2_funct_2, axiom,
% 9.64/9.83    (![A:$i,B:$i]:
% 9.64/9.83     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 9.64/9.83         ( v3_funct_2 @ B @ A @ A ) & 
% 9.64/9.83         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 9.64/9.83       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 9.64/9.83  thf('44', plain,
% 9.64/9.83      (![X35 : $i, X36 : $i]:
% 9.64/9.83         (((k2_funct_2 @ X36 @ X35) = (k2_funct_1 @ X35))
% 9.64/9.83          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))
% 9.64/9.83          | ~ (v3_funct_2 @ X35 @ X36 @ X36)
% 9.64/9.83          | ~ (v1_funct_2 @ X35 @ X36 @ X36)
% 9.64/9.83          | ~ (v1_funct_1 @ X35))),
% 9.64/9.83      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 9.64/9.83  thf('45', plain,
% 9.64/9.83      ((~ (v1_funct_1 @ sk_B)
% 9.64/9.83        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 9.64/9.83        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 9.64/9.83        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 9.64/9.83      inference('sup-', [status(thm)], ['43', '44'])).
% 9.64/9.83  thf('46', plain, ((v1_funct_1 @ sk_B)),
% 9.64/9.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.83  thf('47', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 9.64/9.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.83  thf('48', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 9.64/9.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.83  thf('49', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 9.64/9.83      inference('demod', [status(thm)], ['45', '46', '47', '48'])).
% 9.64/9.83  thf('50', plain,
% 9.64/9.83      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 9.64/9.83      inference('demod', [status(thm)], ['42', '49'])).
% 9.64/9.83  thf('51', plain,
% 9.64/9.83      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ k1_xboole_0)
% 9.64/9.83        | ~ (v1_xboole_0 @ sk_B))),
% 9.64/9.83      inference('sup-', [status(thm)], ['41', '50'])).
% 9.64/9.83  thf('52', plain, ((~ (v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_B))),
% 9.64/9.83      inference('sup-', [status(thm)], ['31', '51'])).
% 9.64/9.83  thf('53', plain,
% 9.64/9.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.64/9.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.83  thf('54', plain,
% 9.64/9.83      (![X8 : $i, X9 : $i]:
% 9.64/9.83         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 9.64/9.83      inference('cnf', [status(esa)], [t3_subset])).
% 9.64/9.83  thf('55', plain, ((r1_tarski @ sk_B @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 9.64/9.83      inference('sup-', [status(thm)], ['53', '54'])).
% 9.64/9.83  thf('56', plain,
% 9.64/9.83      (![X0 : $i, X2 : $i]:
% 9.64/9.83         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 9.64/9.83      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.64/9.83  thf('57', plain,
% 9.64/9.83      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_B)
% 9.64/9.83        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (sk_B)))),
% 9.64/9.83      inference('sup-', [status(thm)], ['55', '56'])).
% 9.64/9.83  thf('58', plain,
% 9.64/9.83      ((r2_relset_1 @ sk_A @ sk_A @ 
% 9.64/9.83        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 9.64/9.83        (k6_partfun1 @ sk_A))),
% 9.64/9.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.83  thf('59', plain,
% 9.64/9.83      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.64/9.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.83  thf(t36_funct_2, axiom,
% 9.64/9.83    (![A:$i,B:$i,C:$i]:
% 9.64/9.83     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 9.64/9.83         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 9.64/9.83       ( ![D:$i]:
% 9.64/9.83         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 9.64/9.83             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 9.64/9.83           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 9.64/9.83               ( r2_relset_1 @
% 9.64/9.83                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 9.64/9.83                 ( k6_partfun1 @ A ) ) & 
% 9.64/9.83               ( v2_funct_1 @ C ) ) =>
% 9.64/9.83             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 9.64/9.83               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 9.64/9.83  thf('60', plain,
% 9.64/9.83      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 9.64/9.83         (~ (v1_funct_1 @ X42)
% 9.64/9.83          | ~ (v1_funct_2 @ X42 @ X43 @ X44)
% 9.64/9.83          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 9.64/9.83          | ((X42) = (k2_funct_1 @ X45))
% 9.64/9.83          | ~ (r2_relset_1 @ X44 @ X44 @ 
% 9.64/9.83               (k1_partfun1 @ X44 @ X43 @ X43 @ X44 @ X45 @ X42) @ 
% 9.64/9.83               (k6_partfun1 @ X44))
% 9.64/9.83          | ((X43) = (k1_xboole_0))
% 9.64/9.83          | ((X44) = (k1_xboole_0))
% 9.64/9.83          | ~ (v2_funct_1 @ X45)
% 9.64/9.83          | ((k2_relset_1 @ X44 @ X43 @ X45) != (X43))
% 9.64/9.83          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43)))
% 9.64/9.83          | ~ (v1_funct_2 @ X45 @ X44 @ X43)
% 9.64/9.83          | ~ (v1_funct_1 @ X45))),
% 9.64/9.83      inference('cnf', [status(esa)], [t36_funct_2])).
% 9.64/9.83  thf('61', plain,
% 9.64/9.83      (![X0 : $i]:
% 9.64/9.83         (~ (v1_funct_1 @ X0)
% 9.64/9.83          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 9.64/9.83          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 9.64/9.83          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 9.64/9.83          | ~ (v2_funct_1 @ X0)
% 9.64/9.83          | ((sk_A) = (k1_xboole_0))
% 9.64/9.83          | ((sk_A) = (k1_xboole_0))
% 9.64/9.83          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 9.64/9.83               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 9.64/9.83               (k6_partfun1 @ sk_A))
% 9.64/9.83          | ((sk_C) = (k2_funct_1 @ X0))
% 9.64/9.83          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 9.64/9.83          | ~ (v1_funct_1 @ sk_C))),
% 9.64/9.83      inference('sup-', [status(thm)], ['59', '60'])).
% 9.64/9.83  thf('62', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 9.64/9.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.83  thf('63', plain, ((v1_funct_1 @ sk_C)),
% 9.64/9.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.83  thf('64', plain,
% 9.64/9.83      (![X0 : $i]:
% 9.64/9.83         (~ (v1_funct_1 @ X0)
% 9.64/9.83          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 9.64/9.83          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 9.64/9.83          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 9.64/9.83          | ~ (v2_funct_1 @ X0)
% 9.64/9.83          | ((sk_A) = (k1_xboole_0))
% 9.64/9.83          | ((sk_A) = (k1_xboole_0))
% 9.64/9.83          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 9.64/9.83               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 9.64/9.83               (k6_partfun1 @ sk_A))
% 9.64/9.83          | ((sk_C) = (k2_funct_1 @ X0)))),
% 9.64/9.83      inference('demod', [status(thm)], ['61', '62', '63'])).
% 9.64/9.83  thf('65', plain,
% 9.64/9.83      (![X0 : $i]:
% 9.64/9.83         (((sk_C) = (k2_funct_1 @ X0))
% 9.64/9.83          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 9.64/9.83               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 9.64/9.83               (k6_partfun1 @ sk_A))
% 9.64/9.83          | ((sk_A) = (k1_xboole_0))
% 9.64/9.83          | ~ (v2_funct_1 @ X0)
% 9.64/9.83          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 9.64/9.83          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 9.64/9.83          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 9.64/9.83          | ~ (v1_funct_1 @ X0))),
% 9.64/9.83      inference('simplify', [status(thm)], ['64'])).
% 9.64/9.83  thf('66', plain,
% 9.64/9.83      ((~ (v1_funct_1 @ sk_B)
% 9.64/9.83        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 9.64/9.83        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 9.64/9.83        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 9.64/9.83        | ~ (v2_funct_1 @ sk_B)
% 9.64/9.83        | ((sk_A) = (k1_xboole_0))
% 9.64/9.83        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 9.64/9.83      inference('sup-', [status(thm)], ['58', '65'])).
% 9.64/9.83  thf('67', plain, ((v1_funct_1 @ sk_B)),
% 9.64/9.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.83  thf('68', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 9.64/9.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.83  thf('69', plain,
% 9.64/9.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.64/9.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.83  thf('70', plain,
% 9.64/9.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.64/9.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.83  thf(redefinition_k2_relset_1, axiom,
% 9.64/9.83    (![A:$i,B:$i,C:$i]:
% 9.64/9.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.64/9.83       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 9.64/9.83  thf('71', plain,
% 9.64/9.83      (![X23 : $i, X24 : $i, X25 : $i]:
% 9.64/9.83         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 9.64/9.83          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 9.64/9.83      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 9.64/9.83  thf('72', plain,
% 9.64/9.83      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 9.64/9.83      inference('sup-', [status(thm)], ['70', '71'])).
% 9.64/9.83  thf('73', plain,
% 9.64/9.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.64/9.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.83  thf(cc2_funct_2, axiom,
% 9.64/9.83    (![A:$i,B:$i,C:$i]:
% 9.64/9.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.64/9.83       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 9.64/9.83         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 9.64/9.83  thf('74', plain,
% 9.64/9.83      (![X30 : $i, X31 : $i, X32 : $i]:
% 9.64/9.83         (~ (v1_funct_1 @ X30)
% 9.64/9.83          | ~ (v3_funct_2 @ X30 @ X31 @ X32)
% 9.64/9.83          | (v2_funct_2 @ X30 @ X32)
% 9.64/9.83          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 9.64/9.83      inference('cnf', [status(esa)], [cc2_funct_2])).
% 9.64/9.83  thf('75', plain,
% 9.64/9.83      (((v2_funct_2 @ sk_B @ sk_A)
% 9.64/9.83        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 9.64/9.83        | ~ (v1_funct_1 @ sk_B))),
% 9.64/9.83      inference('sup-', [status(thm)], ['73', '74'])).
% 9.64/9.83  thf('76', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 9.64/9.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.83  thf('77', plain, ((v1_funct_1 @ sk_B)),
% 9.64/9.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.83  thf('78', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 9.64/9.83      inference('demod', [status(thm)], ['75', '76', '77'])).
% 9.64/9.83  thf(d3_funct_2, axiom,
% 9.64/9.83    (![A:$i,B:$i]:
% 9.64/9.83     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 9.64/9.83       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 9.64/9.83  thf('79', plain,
% 9.64/9.83      (![X33 : $i, X34 : $i]:
% 9.64/9.83         (~ (v2_funct_2 @ X34 @ X33)
% 9.64/9.83          | ((k2_relat_1 @ X34) = (X33))
% 9.64/9.83          | ~ (v5_relat_1 @ X34 @ X33)
% 9.64/9.83          | ~ (v1_relat_1 @ X34))),
% 9.64/9.83      inference('cnf', [status(esa)], [d3_funct_2])).
% 9.64/9.83  thf('80', plain,
% 9.64/9.83      ((~ (v1_relat_1 @ sk_B)
% 9.64/9.83        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 9.64/9.83        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 9.64/9.83      inference('sup-', [status(thm)], ['78', '79'])).
% 9.64/9.83  thf('81', plain,
% 9.64/9.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.64/9.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.83  thf(cc2_relat_1, axiom,
% 9.64/9.83    (![A:$i]:
% 9.64/9.83     ( ( v1_relat_1 @ A ) =>
% 9.64/9.83       ( ![B:$i]:
% 9.64/9.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 9.64/9.83  thf('82', plain,
% 9.64/9.83      (![X11 : $i, X12 : $i]:
% 9.64/9.83         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 9.64/9.83          | (v1_relat_1 @ X11)
% 9.64/9.83          | ~ (v1_relat_1 @ X12))),
% 9.64/9.83      inference('cnf', [status(esa)], [cc2_relat_1])).
% 9.64/9.83  thf('83', plain,
% 9.64/9.83      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 9.64/9.83      inference('sup-', [status(thm)], ['81', '82'])).
% 9.64/9.83  thf('84', plain,
% 9.64/9.83      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X15 @ X16))),
% 9.64/9.83      inference('cnf', [status(esa)], [fc6_relat_1])).
% 9.64/9.83  thf('85', plain, ((v1_relat_1 @ sk_B)),
% 9.64/9.83      inference('demod', [status(thm)], ['83', '84'])).
% 9.64/9.83  thf('86', plain,
% 9.64/9.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.64/9.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.83  thf('87', plain,
% 9.64/9.83      (![X20 : $i, X21 : $i, X22 : $i]:
% 9.64/9.83         ((v5_relat_1 @ X20 @ X22)
% 9.64/9.83          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 9.64/9.83      inference('cnf', [status(esa)], [cc2_relset_1])).
% 9.64/9.83  thf('88', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 9.64/9.83      inference('sup-', [status(thm)], ['86', '87'])).
% 9.64/9.83  thf('89', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 9.64/9.83      inference('demod', [status(thm)], ['80', '85', '88'])).
% 9.64/9.83  thf('90', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 9.64/9.83      inference('demod', [status(thm)], ['72', '89'])).
% 9.64/9.83  thf('91', plain,
% 9.64/9.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.64/9.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.83  thf('92', plain,
% 9.64/9.83      (![X30 : $i, X31 : $i, X32 : $i]:
% 9.64/9.83         (~ (v1_funct_1 @ X30)
% 9.64/9.83          | ~ (v3_funct_2 @ X30 @ X31 @ X32)
% 9.64/9.83          | (v2_funct_1 @ X30)
% 9.64/9.83          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 9.64/9.83      inference('cnf', [status(esa)], [cc2_funct_2])).
% 9.64/9.83  thf('93', plain,
% 9.64/9.83      (((v2_funct_1 @ sk_B)
% 9.64/9.83        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 9.64/9.83        | ~ (v1_funct_1 @ sk_B))),
% 9.64/9.83      inference('sup-', [status(thm)], ['91', '92'])).
% 9.64/9.83  thf('94', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 9.64/9.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.83  thf('95', plain, ((v1_funct_1 @ sk_B)),
% 9.64/9.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.83  thf('96', plain, ((v2_funct_1 @ sk_B)),
% 9.64/9.83      inference('demod', [status(thm)], ['93', '94', '95'])).
% 9.64/9.83  thf('97', plain,
% 9.64/9.83      ((((sk_A) != (sk_A))
% 9.64/9.83        | ((sk_A) = (k1_xboole_0))
% 9.64/9.83        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 9.64/9.83      inference('demod', [status(thm)], ['66', '67', '68', '69', '90', '96'])).
% 9.64/9.83  thf('98', plain,
% 9.64/9.83      ((((sk_C) = (k2_funct_1 @ sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 9.64/9.83      inference('simplify', [status(thm)], ['97'])).
% 9.64/9.83  thf('99', plain,
% 9.64/9.83      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 9.64/9.83      inference('demod', [status(thm)], ['42', '49'])).
% 9.64/9.83  thf('100', plain,
% 9.64/9.83      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 9.64/9.83      inference('sup-', [status(thm)], ['98', '99'])).
% 9.64/9.83  thf('101', plain,
% 9.64/9.83      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.64/9.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.83  thf('102', plain,
% 9.64/9.83      (![X27 : $i, X28 : $i, X29 : $i]:
% 9.64/9.83         ((r2_relset_1 @ X27 @ X28 @ X29 @ X29)
% 9.64/9.83          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 9.64/9.83      inference('simplify', [status(thm)], ['28'])).
% 9.64/9.83  thf('103', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 9.64/9.83      inference('sup-', [status(thm)], ['101', '102'])).
% 9.64/9.83  thf('104', plain, (((sk_A) = (k1_xboole_0))),
% 9.64/9.83      inference('demod', [status(thm)], ['100', '103'])).
% 9.64/9.83  thf('105', plain, (((sk_A) = (k1_xboole_0))),
% 9.64/9.83      inference('demod', [status(thm)], ['100', '103'])).
% 9.64/9.83  thf('106', plain,
% 9.64/9.83      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 9.64/9.83      inference('simplify', [status(thm)], ['14'])).
% 9.64/9.83  thf('107', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 9.64/9.83      inference('demod', [status(thm)], ['13', '17', '24'])).
% 9.64/9.83  thf('108', plain, (((sk_A) = (k1_xboole_0))),
% 9.64/9.83      inference('demod', [status(thm)], ['100', '103'])).
% 9.64/9.83  thf('109', plain, (((sk_A) = (k1_xboole_0))),
% 9.64/9.83      inference('demod', [status(thm)], ['100', '103'])).
% 9.64/9.83  thf('110', plain,
% 9.64/9.83      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 9.64/9.83      inference('simplify', [status(thm)], ['14'])).
% 9.64/9.83  thf('111', plain, (((k1_xboole_0) = (sk_B))),
% 9.64/9.83      inference('demod', [status(thm)],
% 9.64/9.83                ['57', '104', '105', '106', '107', '108', '109', '110'])).
% 9.64/9.83  thf('112', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 9.64/9.83      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 9.64/9.83  thf('113', plain, (~ (v1_xboole_0 @ sk_C)),
% 9.64/9.83      inference('demod', [status(thm)], ['52', '111', '112'])).
% 9.64/9.83  thf('114', plain,
% 9.64/9.83      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.64/9.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.83  thf('115', plain,
% 9.64/9.83      (![X8 : $i, X9 : $i]:
% 9.64/9.83         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 9.64/9.83      inference('cnf', [status(esa)], [t3_subset])).
% 9.64/9.83  thf('116', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 9.64/9.83      inference('sup-', [status(thm)], ['114', '115'])).
% 9.64/9.83  thf('117', plain,
% 9.64/9.83      (![X0 : $i, X2 : $i]:
% 9.64/9.83         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 9.64/9.83      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.64/9.83  thf('118', plain,
% 9.64/9.83      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_C)
% 9.64/9.83        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (sk_C)))),
% 9.64/9.83      inference('sup-', [status(thm)], ['116', '117'])).
% 9.64/9.83  thf('119', plain, (((sk_A) = (k1_xboole_0))),
% 9.64/9.83      inference('demod', [status(thm)], ['100', '103'])).
% 9.64/9.83  thf('120', plain, (((sk_A) = (k1_xboole_0))),
% 9.64/9.83      inference('demod', [status(thm)], ['100', '103'])).
% 9.64/9.83  thf('121', plain,
% 9.64/9.83      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 9.64/9.83      inference('simplify', [status(thm)], ['14'])).
% 9.64/9.83  thf('122', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 9.64/9.83      inference('demod', [status(thm)], ['13', '17', '24'])).
% 9.64/9.83  thf('123', plain, (((sk_A) = (k1_xboole_0))),
% 9.64/9.83      inference('demod', [status(thm)], ['100', '103'])).
% 9.64/9.83  thf('124', plain, (((sk_A) = (k1_xboole_0))),
% 9.64/9.83      inference('demod', [status(thm)], ['100', '103'])).
% 9.64/9.83  thf('125', plain,
% 9.64/9.83      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 9.64/9.83      inference('simplify', [status(thm)], ['14'])).
% 9.64/9.83  thf('126', plain, (((k1_xboole_0) = (sk_C))),
% 9.64/9.83      inference('demod', [status(thm)],
% 9.64/9.83                ['118', '119', '120', '121', '122', '123', '124', '125'])).
% 9.64/9.83  thf('127', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 9.64/9.83      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 9.64/9.83  thf('128', plain, ($false),
% 9.64/9.83      inference('demod', [status(thm)], ['113', '126', '127'])).
% 9.64/9.83  
% 9.64/9.83  % SZS output end Refutation
% 9.64/9.83  
% 9.64/9.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
