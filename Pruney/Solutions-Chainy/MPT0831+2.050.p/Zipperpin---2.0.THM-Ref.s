%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MLYv6CJDu9

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:27 EST 2020

% Result     : Theorem 0.73s
% Output     : Refutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 325 expanded)
%              Number of leaves         :   31 ( 110 expanded)
%              Depth                    :   20
%              Number of atoms          :  662 (3074 expanded)
%              Number of equality atoms :   74 ( 189 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_relset_1_type,type,(
    k5_relset_1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t34_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ( r1_tarski @ B @ C )
       => ( r2_relset_1 @ B @ A @ ( k5_relset_1 @ B @ A @ D @ C ) @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
       => ( ( r1_tarski @ B @ C )
         => ( r2_relset_1 @ B @ A @ ( k5_relset_1 @ B @ A @ D @ C ) @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_relset_1])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_B_1 @ sk_A @ ( k5_relset_1 @ sk_B_1 @ sk_A @ sk_D @ sk_C ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k5_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k5_relset_1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( ( k5_relset_1 @ X36 @ X37 @ X35 @ X38 )
        = ( k7_relat_1 @ X35 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k5_relset_1 @ sk_B_1 @ sk_A @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r2_relset_1 @ sk_B_1 @ sk_A @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t195_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = A )
            & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = B ) ) ) )).

thf('5',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X26 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) )
        = X26 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ( r1_tarski @ ( k1_relat_1 @ X29 ) @ ( k1_relat_1 @ X28 ) )
      | ~ ( r1_tarski @ X29 @ X28 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X19: $i,X20: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X19: $i,X20: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('17',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','15','16'])).

thf('18',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B_1 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['5','17'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('19',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X30 ) @ X31 )
      | ( ( k7_relat_1 @ X30 @ X31 )
        = X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('20',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k7_relat_1 @ sk_D @ sk_B_1 )
      = sk_D ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('22',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k7_relat_1 @ sk_D @ sk_B_1 )
      = sk_D ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k7_relat_1 @ sk_D @ sk_B_1 )
      = sk_D ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('24',plain,(
    r1_tarski @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t102_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = ( k7_relat_1 @ C @ A ) ) ) ) )).

thf('25',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X21 @ X22 )
      | ~ ( v1_relat_1 @ X23 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X23 @ X21 ) @ X22 )
        = ( k7_relat_1 @ X23 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t102_relat_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ sk_B_1 ) @ sk_C )
        = ( k7_relat_1 @ X0 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k7_relat_1 @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ sk_B_1 ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('29',plain,
    ( ( ( k7_relat_1 @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ sk_B_1 ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k7_relat_1 @ sk_D @ sk_C )
      = sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','29'])).

thf('31',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k7_relat_1 @ sk_D @ sk_C )
      = sk_D ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ~ ( r2_relset_1 @ sk_B_1 @ sk_A @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('33',plain,
    ( ~ ( r2_relset_1 @ sk_B_1 @ sk_A @ sk_D @ sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('35',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( r2_relset_1 @ X40 @ X41 @ X39 @ X42 )
      | ( X39 != X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('36',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( r2_relset_1 @ X40 @ X41 @ X42 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    r2_relset_1 @ sk_B_1 @ sk_A @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','37'])).

thf('39',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('40',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('41',plain,
    ( ( k3_xboole_0 @ sk_D @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) )
    = sk_D ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k3_xboole_0 @ sk_D @ ( k2_zfmisc_1 @ sk_B_1 @ k1_xboole_0 ) )
      = sk_D )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('43',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('44',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('45',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('46',plain,
    ( ( k1_xboole_0 = sk_D )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','44','45'])).

thf('47',plain,
    ( ( k3_xboole_0 @ sk_D @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) )
    = sk_D ),
    inference('sup-',[status(thm)],['39','40'])).

thf('48',plain,
    ( ( ( k3_xboole_0 @ sk_D @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A ) )
      = sk_D )
    | ( k1_xboole_0 = sk_D ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('50',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('52',plain,
    ( ( k1_xboole_0 = sk_D )
    | ( k1_xboole_0 = sk_D ) ),
    inference(demod,[status(thm)],['48','50','51'])).

thf('53',plain,(
    k1_xboole_0 = sk_D ),
    inference(simplify,[status(thm)],['52'])).

thf(t111_relat_1,axiom,(
    ! [A: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('54',plain,(
    ! [X25: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X25 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t111_relat_1])).

thf('55',plain,(
    k1_xboole_0 = sk_D ),
    inference(simplify,[status(thm)],['52'])).

thf(t25_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('56',plain,(
    ! [X47: $i,X48: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t25_relset_1])).

thf('57',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( r2_relset_1 @ X40 @ X41 @ X42 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['4','53','54','55','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MLYv6CJDu9
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:01:40 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.73/0.96  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.73/0.96  % Solved by: fo/fo7.sh
% 0.73/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.73/0.96  % done 780 iterations in 0.508s
% 0.73/0.96  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.73/0.96  % SZS output start Refutation
% 0.73/0.96  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.73/0.96  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.73/0.96  thf(sk_C_type, type, sk_C: $i).
% 0.73/0.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.73/0.96  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.73/0.96  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.73/0.96  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.73/0.96  thf(sk_D_type, type, sk_D: $i).
% 0.73/0.96  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.73/0.96  thf(k5_relset_1_type, type, k5_relset_1: $i > $i > $i > $i > $i).
% 0.73/0.96  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.73/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.73/0.96  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.73/0.96  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.73/0.96  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.73/0.96  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.73/0.96  thf(t34_relset_1, conjecture,
% 0.73/0.96    (![A:$i,B:$i,C:$i,D:$i]:
% 0.73/0.96     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.73/0.96       ( ( r1_tarski @ B @ C ) =>
% 0.73/0.96         ( r2_relset_1 @ B @ A @ ( k5_relset_1 @ B @ A @ D @ C ) @ D ) ) ))).
% 0.73/0.96  thf(zf_stmt_0, negated_conjecture,
% 0.73/0.96    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.73/0.96        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.73/0.96          ( ( r1_tarski @ B @ C ) =>
% 0.73/0.96            ( r2_relset_1 @ B @ A @ ( k5_relset_1 @ B @ A @ D @ C ) @ D ) ) ) )),
% 0.73/0.96    inference('cnf.neg', [status(esa)], [t34_relset_1])).
% 0.73/0.96  thf('0', plain,
% 0.73/0.96      (~ (r2_relset_1 @ sk_B_1 @ sk_A @ 
% 0.73/0.96          (k5_relset_1 @ sk_B_1 @ sk_A @ sk_D @ sk_C) @ sk_D)),
% 0.73/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.96  thf('1', plain,
% 0.73/0.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.73/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.96  thf(redefinition_k5_relset_1, axiom,
% 0.73/0.96    (![A:$i,B:$i,C:$i,D:$i]:
% 0.73/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.73/0.96       ( ( k5_relset_1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.73/0.96  thf('2', plain,
% 0.73/0.96      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.73/0.96         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.73/0.96          | ((k5_relset_1 @ X36 @ X37 @ X35 @ X38) = (k7_relat_1 @ X35 @ X38)))),
% 0.73/0.96      inference('cnf', [status(esa)], [redefinition_k5_relset_1])).
% 0.73/0.96  thf('3', plain,
% 0.73/0.96      (![X0 : $i]:
% 0.73/0.96         ((k5_relset_1 @ sk_B_1 @ sk_A @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.73/0.96      inference('sup-', [status(thm)], ['1', '2'])).
% 0.73/0.96  thf('4', plain,
% 0.73/0.96      (~ (r2_relset_1 @ sk_B_1 @ sk_A @ (k7_relat_1 @ sk_D @ sk_C) @ sk_D)),
% 0.73/0.96      inference('demod', [status(thm)], ['0', '3'])).
% 0.73/0.96  thf(t195_relat_1, axiom,
% 0.73/0.96    (![A:$i,B:$i]:
% 0.73/0.96     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.73/0.96          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 0.73/0.96               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 0.73/0.96  thf('5', plain,
% 0.73/0.96      (![X26 : $i, X27 : $i]:
% 0.73/0.96         (((X26) = (k1_xboole_0))
% 0.73/0.96          | ((k1_relat_1 @ (k2_zfmisc_1 @ X26 @ X27)) = (X26))
% 0.73/0.96          | ((X27) = (k1_xboole_0)))),
% 0.73/0.96      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.73/0.96  thf('6', plain,
% 0.73/0.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.73/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.96  thf(t3_subset, axiom,
% 0.73/0.96    (![A:$i,B:$i]:
% 0.73/0.96     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.73/0.96  thf('7', plain,
% 0.73/0.96      (![X14 : $i, X15 : $i]:
% 0.73/0.96         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.73/0.96      inference('cnf', [status(esa)], [t3_subset])).
% 0.73/0.96  thf('8', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))),
% 0.73/0.96      inference('sup-', [status(thm)], ['6', '7'])).
% 0.73/0.96  thf(t25_relat_1, axiom,
% 0.73/0.96    (![A:$i]:
% 0.73/0.96     ( ( v1_relat_1 @ A ) =>
% 0.73/0.96       ( ![B:$i]:
% 0.73/0.96         ( ( v1_relat_1 @ B ) =>
% 0.73/0.96           ( ( r1_tarski @ A @ B ) =>
% 0.73/0.96             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.73/0.96               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.73/0.96  thf('9', plain,
% 0.73/0.96      (![X28 : $i, X29 : $i]:
% 0.73/0.96         (~ (v1_relat_1 @ X28)
% 0.73/0.96          | (r1_tarski @ (k1_relat_1 @ X29) @ (k1_relat_1 @ X28))
% 0.73/0.96          | ~ (r1_tarski @ X29 @ X28)
% 0.73/0.96          | ~ (v1_relat_1 @ X29))),
% 0.73/0.96      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.73/0.96  thf('10', plain,
% 0.73/0.96      ((~ (v1_relat_1 @ sk_D)
% 0.73/0.96        | (r1_tarski @ (k1_relat_1 @ sk_D) @ 
% 0.73/0.96           (k1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 0.73/0.96        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.73/0.96      inference('sup-', [status(thm)], ['8', '9'])).
% 0.73/0.96  thf('11', plain,
% 0.73/0.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.73/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.96  thf(cc2_relat_1, axiom,
% 0.73/0.96    (![A:$i]:
% 0.73/0.96     ( ( v1_relat_1 @ A ) =>
% 0.73/0.96       ( ![B:$i]:
% 0.73/0.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.73/0.96  thf('12', plain,
% 0.73/0.96      (![X17 : $i, X18 : $i]:
% 0.73/0.96         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.73/0.96          | (v1_relat_1 @ X17)
% 0.73/0.96          | ~ (v1_relat_1 @ X18))),
% 0.73/0.96      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.73/0.96  thf('13', plain,
% 0.73/0.96      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.73/0.96      inference('sup-', [status(thm)], ['11', '12'])).
% 0.73/0.96  thf(fc6_relat_1, axiom,
% 0.73/0.96    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.73/0.96  thf('14', plain,
% 0.73/0.96      (![X19 : $i, X20 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X19 @ X20))),
% 0.73/0.96      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.73/0.96  thf('15', plain, ((v1_relat_1 @ sk_D)),
% 0.73/0.96      inference('demod', [status(thm)], ['13', '14'])).
% 0.73/0.96  thf('16', plain,
% 0.73/0.96      (![X19 : $i, X20 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X19 @ X20))),
% 0.73/0.96      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.73/0.96  thf('17', plain,
% 0.73/0.96      ((r1_tarski @ (k1_relat_1 @ sk_D) @ 
% 0.73/0.96        (k1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.73/0.96      inference('demod', [status(thm)], ['10', '15', '16'])).
% 0.73/0.96  thf('18', plain,
% 0.73/0.96      (((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B_1)
% 0.73/0.96        | ((sk_A) = (k1_xboole_0))
% 0.73/0.96        | ((sk_B_1) = (k1_xboole_0)))),
% 0.73/0.96      inference('sup+', [status(thm)], ['5', '17'])).
% 0.73/0.96  thf(t97_relat_1, axiom,
% 0.73/0.96    (![A:$i,B:$i]:
% 0.73/0.96     ( ( v1_relat_1 @ B ) =>
% 0.73/0.96       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.73/0.96         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.73/0.96  thf('19', plain,
% 0.73/0.96      (![X30 : $i, X31 : $i]:
% 0.73/0.96         (~ (r1_tarski @ (k1_relat_1 @ X30) @ X31)
% 0.73/0.96          | ((k7_relat_1 @ X30 @ X31) = (X30))
% 0.73/0.96          | ~ (v1_relat_1 @ X30))),
% 0.73/0.96      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.73/0.96  thf('20', plain,
% 0.73/0.96      ((((sk_B_1) = (k1_xboole_0))
% 0.73/0.96        | ((sk_A) = (k1_xboole_0))
% 0.73/0.96        | ~ (v1_relat_1 @ sk_D)
% 0.73/0.96        | ((k7_relat_1 @ sk_D @ sk_B_1) = (sk_D)))),
% 0.73/0.96      inference('sup-', [status(thm)], ['18', '19'])).
% 0.73/0.96  thf('21', plain, ((v1_relat_1 @ sk_D)),
% 0.73/0.96      inference('demod', [status(thm)], ['13', '14'])).
% 0.73/0.96  thf('22', plain,
% 0.73/0.96      ((((sk_B_1) = (k1_xboole_0))
% 0.73/0.96        | ((sk_A) = (k1_xboole_0))
% 0.73/0.96        | ((k7_relat_1 @ sk_D @ sk_B_1) = (sk_D)))),
% 0.73/0.96      inference('demod', [status(thm)], ['20', '21'])).
% 0.73/0.96  thf('23', plain,
% 0.73/0.96      ((((sk_B_1) = (k1_xboole_0))
% 0.73/0.96        | ((sk_A) = (k1_xboole_0))
% 0.73/0.96        | ((k7_relat_1 @ sk_D @ sk_B_1) = (sk_D)))),
% 0.73/0.96      inference('demod', [status(thm)], ['20', '21'])).
% 0.73/0.96  thf('24', plain, ((r1_tarski @ sk_B_1 @ sk_C)),
% 0.73/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.96  thf(t102_relat_1, axiom,
% 0.73/0.96    (![A:$i,B:$i,C:$i]:
% 0.73/0.96     ( ( v1_relat_1 @ C ) =>
% 0.73/0.96       ( ( r1_tarski @ A @ B ) =>
% 0.73/0.96         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k7_relat_1 @ C @ A ) ) ) ))).
% 0.73/0.96  thf('25', plain,
% 0.73/0.96      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.73/0.96         (~ (r1_tarski @ X21 @ X22)
% 0.73/0.96          | ~ (v1_relat_1 @ X23)
% 0.73/0.96          | ((k7_relat_1 @ (k7_relat_1 @ X23 @ X21) @ X22)
% 0.73/0.96              = (k7_relat_1 @ X23 @ X21)))),
% 0.73/0.96      inference('cnf', [status(esa)], [t102_relat_1])).
% 0.73/0.96  thf('26', plain,
% 0.73/0.96      (![X0 : $i]:
% 0.73/0.96         (((k7_relat_1 @ (k7_relat_1 @ X0 @ sk_B_1) @ sk_C)
% 0.73/0.96            = (k7_relat_1 @ X0 @ sk_B_1))
% 0.73/0.96          | ~ (v1_relat_1 @ X0))),
% 0.73/0.96      inference('sup-', [status(thm)], ['24', '25'])).
% 0.73/0.96  thf('27', plain,
% 0.73/0.96      ((((k7_relat_1 @ sk_D @ sk_C) = (k7_relat_1 @ sk_D @ sk_B_1))
% 0.73/0.96        | ((sk_A) = (k1_xboole_0))
% 0.73/0.96        | ((sk_B_1) = (k1_xboole_0))
% 0.73/0.96        | ~ (v1_relat_1 @ sk_D))),
% 0.73/0.96      inference('sup+', [status(thm)], ['23', '26'])).
% 0.73/0.96  thf('28', plain, ((v1_relat_1 @ sk_D)),
% 0.73/0.96      inference('demod', [status(thm)], ['13', '14'])).
% 0.73/0.96  thf('29', plain,
% 0.73/0.96      ((((k7_relat_1 @ sk_D @ sk_C) = (k7_relat_1 @ sk_D @ sk_B_1))
% 0.73/0.96        | ((sk_A) = (k1_xboole_0))
% 0.73/0.96        | ((sk_B_1) = (k1_xboole_0)))),
% 0.73/0.96      inference('demod', [status(thm)], ['27', '28'])).
% 0.73/0.96  thf('30', plain,
% 0.73/0.96      ((((k7_relat_1 @ sk_D @ sk_C) = (sk_D))
% 0.73/0.96        | ((sk_A) = (k1_xboole_0))
% 0.73/0.96        | ((sk_B_1) = (k1_xboole_0))
% 0.73/0.96        | ((sk_B_1) = (k1_xboole_0))
% 0.73/0.96        | ((sk_A) = (k1_xboole_0)))),
% 0.73/0.96      inference('sup+', [status(thm)], ['22', '29'])).
% 0.73/0.96  thf('31', plain,
% 0.73/0.96      ((((sk_B_1) = (k1_xboole_0))
% 0.73/0.96        | ((sk_A) = (k1_xboole_0))
% 0.73/0.96        | ((k7_relat_1 @ sk_D @ sk_C) = (sk_D)))),
% 0.73/0.96      inference('simplify', [status(thm)], ['30'])).
% 0.73/0.96  thf('32', plain,
% 0.73/0.96      (~ (r2_relset_1 @ sk_B_1 @ sk_A @ (k7_relat_1 @ sk_D @ sk_C) @ sk_D)),
% 0.73/0.96      inference('demod', [status(thm)], ['0', '3'])).
% 0.73/0.96  thf('33', plain,
% 0.73/0.96      ((~ (r2_relset_1 @ sk_B_1 @ sk_A @ sk_D @ sk_D)
% 0.73/0.96        | ((sk_A) = (k1_xboole_0))
% 0.73/0.96        | ((sk_B_1) = (k1_xboole_0)))),
% 0.73/0.96      inference('sup-', [status(thm)], ['31', '32'])).
% 0.73/0.96  thf('34', plain,
% 0.73/0.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.73/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.96  thf(redefinition_r2_relset_1, axiom,
% 0.73/0.96    (![A:$i,B:$i,C:$i,D:$i]:
% 0.73/0.96     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.73/0.96         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.73/0.96       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.73/0.96  thf('35', plain,
% 0.73/0.96      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.73/0.96         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.73/0.96          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.73/0.96          | (r2_relset_1 @ X40 @ X41 @ X39 @ X42)
% 0.73/0.96          | ((X39) != (X42)))),
% 0.73/0.96      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.73/0.96  thf('36', plain,
% 0.73/0.96      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.73/0.96         ((r2_relset_1 @ X40 @ X41 @ X42 @ X42)
% 0.73/0.96          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 0.73/0.96      inference('simplify', [status(thm)], ['35'])).
% 0.73/0.96  thf('37', plain, ((r2_relset_1 @ sk_B_1 @ sk_A @ sk_D @ sk_D)),
% 0.73/0.96      inference('sup-', [status(thm)], ['34', '36'])).
% 0.73/0.96  thf('38', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.73/0.96      inference('demod', [status(thm)], ['33', '37'])).
% 0.73/0.96  thf('39', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))),
% 0.73/0.96      inference('sup-', [status(thm)], ['6', '7'])).
% 0.73/0.96  thf(t28_xboole_1, axiom,
% 0.73/0.96    (![A:$i,B:$i]:
% 0.73/0.96     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.73/0.96  thf('40', plain,
% 0.73/0.96      (![X3 : $i, X4 : $i]:
% 0.73/0.96         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 0.73/0.96      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.73/0.96  thf('41', plain,
% 0.73/0.96      (((k3_xboole_0 @ sk_D @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)) = (sk_D))),
% 0.73/0.96      inference('sup-', [status(thm)], ['39', '40'])).
% 0.73/0.96  thf('42', plain,
% 0.73/0.96      ((((k3_xboole_0 @ sk_D @ (k2_zfmisc_1 @ sk_B_1 @ k1_xboole_0)) = (sk_D))
% 0.73/0.96        | ((sk_B_1) = (k1_xboole_0)))),
% 0.73/0.96      inference('sup+', [status(thm)], ['38', '41'])).
% 0.73/0.96  thf(t113_zfmisc_1, axiom,
% 0.73/0.96    (![A:$i,B:$i]:
% 0.73/0.96     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.73/0.96       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.73/0.96  thf('43', plain,
% 0.73/0.96      (![X8 : $i, X9 : $i]:
% 0.73/0.96         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 0.73/0.96      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.73/0.96  thf('44', plain,
% 0.73/0.96      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.73/0.96      inference('simplify', [status(thm)], ['43'])).
% 0.73/0.96  thf(t2_boole, axiom,
% 0.73/0.96    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.73/0.96  thf('45', plain,
% 0.73/0.96      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.73/0.96      inference('cnf', [status(esa)], [t2_boole])).
% 0.73/0.96  thf('46', plain, ((((k1_xboole_0) = (sk_D)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.73/0.96      inference('demod', [status(thm)], ['42', '44', '45'])).
% 0.73/0.96  thf('47', plain,
% 0.73/0.96      (((k3_xboole_0 @ sk_D @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)) = (sk_D))),
% 0.73/0.96      inference('sup-', [status(thm)], ['39', '40'])).
% 0.73/0.96  thf('48', plain,
% 0.73/0.96      ((((k3_xboole_0 @ sk_D @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_A)) = (sk_D))
% 0.73/0.96        | ((k1_xboole_0) = (sk_D)))),
% 0.73/0.96      inference('sup+', [status(thm)], ['46', '47'])).
% 0.73/0.96  thf('49', plain,
% 0.73/0.96      (![X8 : $i, X9 : $i]:
% 0.73/0.96         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 0.73/0.96      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.73/0.96  thf('50', plain,
% 0.73/0.96      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 0.73/0.96      inference('simplify', [status(thm)], ['49'])).
% 0.73/0.96  thf('51', plain,
% 0.73/0.96      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.73/0.96      inference('cnf', [status(esa)], [t2_boole])).
% 0.73/0.96  thf('52', plain, ((((k1_xboole_0) = (sk_D)) | ((k1_xboole_0) = (sk_D)))),
% 0.73/0.96      inference('demod', [status(thm)], ['48', '50', '51'])).
% 0.73/0.96  thf('53', plain, (((k1_xboole_0) = (sk_D))),
% 0.73/0.96      inference('simplify', [status(thm)], ['52'])).
% 0.73/0.96  thf(t111_relat_1, axiom,
% 0.73/0.96    (![A:$i]: ( ( k7_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.73/0.96  thf('54', plain,
% 0.73/0.96      (![X25 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X25) = (k1_xboole_0))),
% 0.73/0.96      inference('cnf', [status(esa)], [t111_relat_1])).
% 0.73/0.96  thf('55', plain, (((k1_xboole_0) = (sk_D))),
% 0.73/0.96      inference('simplify', [status(thm)], ['52'])).
% 0.73/0.96  thf(t25_relset_1, axiom,
% 0.73/0.96    (![A:$i,B:$i]:
% 0.73/0.96     ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.73/0.96  thf('56', plain,
% 0.73/0.96      (![X47 : $i, X48 : $i]:
% 0.73/0.96         (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))),
% 0.73/0.96      inference('cnf', [status(esa)], [t25_relset_1])).
% 0.73/0.96  thf('57', plain,
% 0.73/0.96      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.73/0.96         ((r2_relset_1 @ X40 @ X41 @ X42 @ X42)
% 0.73/0.96          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 0.73/0.96      inference('simplify', [status(thm)], ['35'])).
% 0.73/0.96  thf('58', plain,
% 0.73/0.96      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.73/0.96      inference('sup-', [status(thm)], ['56', '57'])).
% 0.73/0.96  thf('59', plain, ($false),
% 0.73/0.96      inference('demod', [status(thm)], ['4', '53', '54', '55', '58'])).
% 0.73/0.96  
% 0.73/0.96  % SZS output end Refutation
% 0.73/0.96  
% 0.73/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
