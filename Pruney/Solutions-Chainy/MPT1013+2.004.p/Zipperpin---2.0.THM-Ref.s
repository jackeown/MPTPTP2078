%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KbevxVYGVH

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:43 EST 2020

% Result     : Theorem 2.33s
% Output     : Refutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :  141 (1838 expanded)
%              Number of leaves         :   34 ( 545 expanded)
%              Depth                    :   19
%              Number of atoms          : 1004 (29632 expanded)
%              Number of equality atoms :   99 (2352 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(t62_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
          = k1_xboole_0 )
        & ( ( k5_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ) )).

thf('0',plain,(
    ! [X29: $i] :
      ( ( ( k5_relat_1 @ X29 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t62_relat_1])).

thf(t73_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
         => ( ( ( ( k2_relset_1 @ A @ A @ B )
                = A )
              & ( ( k2_relset_1 @ A @ A @ C )
                = A ) )
           => ( ( k2_relset_1 @ A @ A @ ( k4_relset_1 @ A @ A @ A @ A @ C @ B ) )
              = A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
           => ( ( ( ( k2_relset_1 @ A @ A @ B )
                  = A )
                & ( ( k2_relset_1 @ A @ A @ C )
                  = A ) )
             => ( ( k2_relset_1 @ A @ A @ ( k4_relset_1 @ A @ A @ A @ A @ C @ B ) )
                = A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t73_funct_2])).

thf('1',plain,(
    ( k2_relset_1 @ sk_A @ sk_A @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('4',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( ( k4_relset_1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46 )
        = ( k5_relat_1 @ X43 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ( k2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['1','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( m1_subset_1 @ ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) )).

thf('10',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relset_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,
    ( ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('14',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('15',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( ( k2_relset_1 @ X41 @ X42 @ X40 )
        = ( k2_relat_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('16',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_B ) )
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['7','16'])).

thf(t195_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = A )
            & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = B ) ) ) )).

thf('18',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X24 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) )
        = X24 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['19'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('21',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ( v4_relat_1 @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['18','22'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('24',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ B ) )
         => ( v4_relat_1 @ C @ A ) ) ) )).

thf('27',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v4_relat_1 @ X13 @ X15 )
      | ~ ( v4_relat_1 @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc5_relat_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
      | ~ ( v4_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ X0 )
      | ( v4_relat_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ X0 )
      | ( v4_relat_1 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( v4_relat_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,
    ( ( v4_relat_1 @ sk_B @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X26
        = ( k7_relat_1 @ X26 @ X27 ) )
      | ~ ( v4_relat_1 @ X26 @ X27 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('34',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_B
      = ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('36',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v1_relat_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('37',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B
      = ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','37'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('39',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) )
        = ( k9_relat_1 @ X20 @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('40',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = ( k9_relat_1 @ sk_B @ sk_A ) )
    | ( sk_A = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['35','36'])).

thf('42',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = ( k9_relat_1 @ sk_B @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( ( k2_relset_1 @ X41 @ X42 @ X40 )
        = ( k2_relat_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('45',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_A
      = ( k9_relat_1 @ sk_B @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','47'])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('49',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X23 @ X22 ) )
        = ( k9_relat_1 @ X22 @ ( k2_relat_1 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('50',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['7','16'])).

thf('51',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_C ) )
     != sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( ( k2_relset_1 @ X41 @ X42 @ X40 )
        = ( k2_relat_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('54',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_C )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v1_relat_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('59',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['35','36'])).

thf('61',plain,(
    ( k9_relat_1 @ sk_B @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['51','56','59','60'])).

thf('62',plain,
    ( ( sk_A != sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','61'])).

thf('63',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['17','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('66',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('67',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('69',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['62'])).

thf('71',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['62'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('72',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('73',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['72'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('74',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('75',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('76',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['62'])).

thf('78',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['62'])).

thf('79',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('80',plain,(
    k1_xboole_0 = sk_C ),
    inference(demod,[status(thm)],['69','70','71','73','76','77','78','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('83',plain,(
    r1_tarski @ sk_B @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('85',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_B )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['62'])).

thf('87',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['62'])).

thf('88',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('89',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('90',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['62'])).

thf('91',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['62'])).

thf('92',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('93',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['85','86','87','88','89','90','91','92'])).

thf('94',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['64','80','93'])).

thf('95',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','94'])).

thf('96',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['45','46'])).

thf('97',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['62'])).

thf('98',plain,
    ( ( k2_relat_1 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['85','86','87','88','89','90','91','92'])).

thf('100',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('102',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('103',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['95','100','103'])).

thf('105',plain,(
    $false ),
    inference(simplify,[status(thm)],['104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KbevxVYGVH
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:47:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.33/2.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.33/2.58  % Solved by: fo/fo7.sh
% 2.33/2.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.33/2.58  % done 1788 iterations in 2.125s
% 2.33/2.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.33/2.58  % SZS output start Refutation
% 2.33/2.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.33/2.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.33/2.58  thf(sk_A_type, type, sk_A: $i).
% 2.33/2.58  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.33/2.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.33/2.58  thf(sk_C_type, type, sk_C: $i).
% 2.33/2.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.33/2.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.33/2.58  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.33/2.58  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 2.33/2.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.33/2.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.33/2.58  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.33/2.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.33/2.58  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.33/2.58  thf(sk_B_type, type, sk_B: $i).
% 2.33/2.58  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 2.33/2.58  thf(t62_relat_1, axiom,
% 2.33/2.58    (![A:$i]:
% 2.33/2.58     ( ( v1_relat_1 @ A ) =>
% 2.33/2.58       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 2.33/2.58         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 2.33/2.58  thf('0', plain,
% 2.33/2.58      (![X29 : $i]:
% 2.33/2.58         (((k5_relat_1 @ X29 @ k1_xboole_0) = (k1_xboole_0))
% 2.33/2.58          | ~ (v1_relat_1 @ X29))),
% 2.33/2.58      inference('cnf', [status(esa)], [t62_relat_1])).
% 2.33/2.58  thf(t73_funct_2, conjecture,
% 2.33/2.58    (![A:$i,B:$i]:
% 2.33/2.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 2.33/2.58       ( ![C:$i]:
% 2.33/2.58         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 2.33/2.58           ( ( ( ( k2_relset_1 @ A @ A @ B ) = ( A ) ) & 
% 2.33/2.58               ( ( k2_relset_1 @ A @ A @ C ) = ( A ) ) ) =>
% 2.33/2.58             ( ( k2_relset_1 @ A @ A @ ( k4_relset_1 @ A @ A @ A @ A @ C @ B ) ) =
% 2.33/2.58               ( A ) ) ) ) ) ))).
% 2.33/2.58  thf(zf_stmt_0, negated_conjecture,
% 2.33/2.58    (~( ![A:$i,B:$i]:
% 2.33/2.58        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 2.33/2.58          ( ![C:$i]:
% 2.33/2.58            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 2.33/2.58              ( ( ( ( k2_relset_1 @ A @ A @ B ) = ( A ) ) & 
% 2.33/2.58                  ( ( k2_relset_1 @ A @ A @ C ) = ( A ) ) ) =>
% 2.33/2.58                ( ( k2_relset_1 @
% 2.33/2.58                    A @ A @ ( k4_relset_1 @ A @ A @ A @ A @ C @ B ) ) =
% 2.33/2.58                  ( A ) ) ) ) ) ) )),
% 2.33/2.58    inference('cnf.neg', [status(esa)], [t73_funct_2])).
% 2.33/2.58  thf('1', plain,
% 2.33/2.58      (((k2_relset_1 @ sk_A @ sk_A @ 
% 2.33/2.58         (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_A))),
% 2.33/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.58  thf('2', plain,
% 2.33/2.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.33/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.58  thf('3', plain,
% 2.33/2.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.33/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.58  thf(redefinition_k4_relset_1, axiom,
% 2.33/2.58    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.33/2.58     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.33/2.58         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.33/2.58       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.33/2.58  thf('4', plain,
% 2.33/2.58      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 2.33/2.58         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 2.33/2.58          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 2.33/2.58          | ((k4_relset_1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46)
% 2.33/2.58              = (k5_relat_1 @ X43 @ X46)))),
% 2.33/2.58      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 2.33/2.58  thf('5', plain,
% 2.33/2.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.33/2.58         (((k4_relset_1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0)
% 2.33/2.58            = (k5_relat_1 @ sk_C @ X0))
% 2.33/2.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 2.33/2.58      inference('sup-', [status(thm)], ['3', '4'])).
% 2.33/2.58  thf('6', plain,
% 2.33/2.58      (((k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 2.33/2.58         = (k5_relat_1 @ sk_C @ sk_B))),
% 2.33/2.58      inference('sup-', [status(thm)], ['2', '5'])).
% 2.33/2.58  thf('7', plain,
% 2.33/2.58      (((k2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_B)) != (sk_A))),
% 2.33/2.58      inference('demod', [status(thm)], ['1', '6'])).
% 2.33/2.58  thf('8', plain,
% 2.33/2.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.33/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.58  thf('9', plain,
% 2.33/2.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.33/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.58  thf(dt_k4_relset_1, axiom,
% 2.33/2.58    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.33/2.58     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.33/2.58         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.33/2.58       ( m1_subset_1 @
% 2.33/2.58         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.33/2.58         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 2.33/2.58  thf('10', plain,
% 2.33/2.58      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 2.33/2.58         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 2.33/2.58          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 2.33/2.58          | (m1_subset_1 @ (k4_relset_1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37) @ 
% 2.33/2.58             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X39))))),
% 2.33/2.58      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 2.33/2.58  thf('11', plain,
% 2.33/2.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.33/2.58         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1) @ 
% 2.33/2.58           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.33/2.58          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 2.33/2.58      inference('sup-', [status(thm)], ['9', '10'])).
% 2.33/2.58  thf('12', plain,
% 2.33/2.58      ((m1_subset_1 @ 
% 2.33/2.58        (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ 
% 2.33/2.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.33/2.58      inference('sup-', [status(thm)], ['8', '11'])).
% 2.33/2.58  thf('13', plain,
% 2.33/2.58      (((k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 2.33/2.58         = (k5_relat_1 @ sk_C @ sk_B))),
% 2.33/2.58      inference('sup-', [status(thm)], ['2', '5'])).
% 2.33/2.58  thf('14', plain,
% 2.33/2.58      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_B) @ 
% 2.33/2.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.33/2.58      inference('demod', [status(thm)], ['12', '13'])).
% 2.33/2.58  thf(redefinition_k2_relset_1, axiom,
% 2.33/2.58    (![A:$i,B:$i,C:$i]:
% 2.33/2.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.33/2.58       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.33/2.58  thf('15', plain,
% 2.33/2.58      (![X40 : $i, X41 : $i, X42 : $i]:
% 2.33/2.58         (((k2_relset_1 @ X41 @ X42 @ X40) = (k2_relat_1 @ X40))
% 2.33/2.58          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 2.33/2.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.33/2.58  thf('16', plain,
% 2.33/2.58      (((k2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_B))
% 2.33/2.58         = (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))),
% 2.33/2.58      inference('sup-', [status(thm)], ['14', '15'])).
% 2.33/2.58  thf('17', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)) != (sk_A))),
% 2.33/2.58      inference('demod', [status(thm)], ['7', '16'])).
% 2.33/2.58  thf(t195_relat_1, axiom,
% 2.33/2.58    (![A:$i,B:$i]:
% 2.33/2.58     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 2.33/2.58          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 2.33/2.58               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 2.33/2.58  thf('18', plain,
% 2.33/2.58      (![X24 : $i, X25 : $i]:
% 2.33/2.58         (((X24) = (k1_xboole_0))
% 2.33/2.58          | ((k1_relat_1 @ (k2_zfmisc_1 @ X24 @ X25)) = (X24))
% 2.33/2.58          | ((X25) = (k1_xboole_0)))),
% 2.33/2.58      inference('cnf', [status(esa)], [t195_relat_1])).
% 2.33/2.58  thf(d10_xboole_0, axiom,
% 2.33/2.58    (![A:$i,B:$i]:
% 2.33/2.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.33/2.58  thf('19', plain,
% 2.33/2.58      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 2.33/2.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.33/2.58  thf('20', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.33/2.58      inference('simplify', [status(thm)], ['19'])).
% 2.33/2.58  thf(d18_relat_1, axiom,
% 2.33/2.58    (![A:$i,B:$i]:
% 2.33/2.58     ( ( v1_relat_1 @ B ) =>
% 2.33/2.58       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 2.33/2.58  thf('21', plain,
% 2.33/2.58      (![X16 : $i, X17 : $i]:
% 2.33/2.58         (~ (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 2.33/2.58          | (v4_relat_1 @ X16 @ X17)
% 2.33/2.58          | ~ (v1_relat_1 @ X16))),
% 2.33/2.58      inference('cnf', [status(esa)], [d18_relat_1])).
% 2.33/2.58  thf('22', plain,
% 2.33/2.58      (![X0 : $i]:
% 2.33/2.58         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 2.33/2.58      inference('sup-', [status(thm)], ['20', '21'])).
% 2.33/2.58  thf('23', plain,
% 2.33/2.58      (![X0 : $i, X1 : $i]:
% 2.33/2.58         ((v4_relat_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X0)
% 2.33/2.58          | ((X1) = (k1_xboole_0))
% 2.33/2.58          | ((X0) = (k1_xboole_0))
% 2.33/2.58          | ~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)))),
% 2.33/2.58      inference('sup+', [status(thm)], ['18', '22'])).
% 2.33/2.58  thf(fc6_relat_1, axiom,
% 2.33/2.58    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.33/2.58  thf('24', plain,
% 2.33/2.58      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 2.33/2.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.33/2.58  thf('25', plain,
% 2.33/2.58      (![X0 : $i, X1 : $i]:
% 2.33/2.58         ((v4_relat_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X0)
% 2.33/2.58          | ((X1) = (k1_xboole_0))
% 2.33/2.58          | ((X0) = (k1_xboole_0)))),
% 2.33/2.58      inference('demod', [status(thm)], ['23', '24'])).
% 2.33/2.58  thf('26', plain,
% 2.33/2.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.33/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.58  thf(cc5_relat_1, axiom,
% 2.33/2.58    (![A:$i,B:$i]:
% 2.33/2.58     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 2.33/2.58       ( ![C:$i]:
% 2.33/2.58         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ B ) ) => ( v4_relat_1 @ C @ A ) ) ) ))).
% 2.33/2.58  thf('27', plain,
% 2.33/2.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.33/2.58         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 2.33/2.58          | (v4_relat_1 @ X13 @ X15)
% 2.33/2.58          | ~ (v4_relat_1 @ X14 @ X15)
% 2.33/2.58          | ~ (v1_relat_1 @ X14))),
% 2.33/2.58      inference('cnf', [status(esa)], [cc5_relat_1])).
% 2.33/2.58  thf('28', plain,
% 2.33/2.58      (![X0 : $i]:
% 2.33/2.58         (~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 2.33/2.58          | ~ (v4_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ X0)
% 2.33/2.58          | (v4_relat_1 @ sk_B @ X0))),
% 2.33/2.58      inference('sup-', [status(thm)], ['26', '27'])).
% 2.33/2.58  thf('29', plain,
% 2.33/2.58      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 2.33/2.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.33/2.58  thf('30', plain,
% 2.33/2.58      (![X0 : $i]:
% 2.33/2.58         (~ (v4_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ X0)
% 2.33/2.58          | (v4_relat_1 @ sk_B @ X0))),
% 2.33/2.58      inference('demod', [status(thm)], ['28', '29'])).
% 2.33/2.58  thf('31', plain,
% 2.33/2.58      ((((sk_A) = (k1_xboole_0))
% 2.33/2.58        | ((sk_A) = (k1_xboole_0))
% 2.33/2.58        | (v4_relat_1 @ sk_B @ sk_A))),
% 2.33/2.58      inference('sup-', [status(thm)], ['25', '30'])).
% 2.33/2.58  thf('32', plain, (((v4_relat_1 @ sk_B @ sk_A) | ((sk_A) = (k1_xboole_0)))),
% 2.33/2.58      inference('simplify', [status(thm)], ['31'])).
% 2.33/2.58  thf(t209_relat_1, axiom,
% 2.33/2.58    (![A:$i,B:$i]:
% 2.33/2.58     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 2.33/2.58       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 2.33/2.58  thf('33', plain,
% 2.33/2.58      (![X26 : $i, X27 : $i]:
% 2.33/2.58         (((X26) = (k7_relat_1 @ X26 @ X27))
% 2.33/2.58          | ~ (v4_relat_1 @ X26 @ X27)
% 2.33/2.58          | ~ (v1_relat_1 @ X26))),
% 2.33/2.58      inference('cnf', [status(esa)], [t209_relat_1])).
% 2.33/2.58  thf('34', plain,
% 2.33/2.58      ((((sk_A) = (k1_xboole_0))
% 2.33/2.58        | ~ (v1_relat_1 @ sk_B)
% 2.33/2.58        | ((sk_B) = (k7_relat_1 @ sk_B @ sk_A)))),
% 2.33/2.58      inference('sup-', [status(thm)], ['32', '33'])).
% 2.33/2.58  thf('35', plain,
% 2.33/2.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.33/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.58  thf(cc1_relset_1, axiom,
% 2.33/2.58    (![A:$i,B:$i,C:$i]:
% 2.33/2.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.33/2.58       ( v1_relat_1 @ C ) ))).
% 2.33/2.58  thf('36', plain,
% 2.33/2.58      (![X31 : $i, X32 : $i, X33 : $i]:
% 2.33/2.58         ((v1_relat_1 @ X31)
% 2.33/2.58          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 2.33/2.58      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.33/2.58  thf('37', plain, ((v1_relat_1 @ sk_B)),
% 2.33/2.58      inference('sup-', [status(thm)], ['35', '36'])).
% 2.33/2.58  thf('38', plain,
% 2.33/2.58      ((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k7_relat_1 @ sk_B @ sk_A)))),
% 2.33/2.58      inference('demod', [status(thm)], ['34', '37'])).
% 2.33/2.58  thf(t148_relat_1, axiom,
% 2.33/2.58    (![A:$i,B:$i]:
% 2.33/2.58     ( ( v1_relat_1 @ B ) =>
% 2.33/2.58       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 2.33/2.58  thf('39', plain,
% 2.33/2.58      (![X20 : $i, X21 : $i]:
% 2.33/2.58         (((k2_relat_1 @ (k7_relat_1 @ X20 @ X21)) = (k9_relat_1 @ X20 @ X21))
% 2.33/2.58          | ~ (v1_relat_1 @ X20))),
% 2.33/2.58      inference('cnf', [status(esa)], [t148_relat_1])).
% 2.33/2.58  thf('40', plain,
% 2.33/2.58      ((((k2_relat_1 @ sk_B) = (k9_relat_1 @ sk_B @ sk_A))
% 2.33/2.58        | ((sk_A) = (k1_xboole_0))
% 2.33/2.58        | ~ (v1_relat_1 @ sk_B))),
% 2.33/2.58      inference('sup+', [status(thm)], ['38', '39'])).
% 2.33/2.58  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 2.33/2.58      inference('sup-', [status(thm)], ['35', '36'])).
% 2.33/2.58  thf('42', plain,
% 2.33/2.58      ((((k2_relat_1 @ sk_B) = (k9_relat_1 @ sk_B @ sk_A))
% 2.33/2.58        | ((sk_A) = (k1_xboole_0)))),
% 2.33/2.58      inference('demod', [status(thm)], ['40', '41'])).
% 2.33/2.58  thf('43', plain,
% 2.33/2.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.33/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.58  thf('44', plain,
% 2.33/2.58      (![X40 : $i, X41 : $i, X42 : $i]:
% 2.33/2.58         (((k2_relset_1 @ X41 @ X42 @ X40) = (k2_relat_1 @ X40))
% 2.33/2.58          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 2.33/2.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.33/2.58  thf('45', plain,
% 2.33/2.58      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 2.33/2.58      inference('sup-', [status(thm)], ['43', '44'])).
% 2.33/2.58  thf('46', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 2.33/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.58  thf('47', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 2.33/2.58      inference('sup+', [status(thm)], ['45', '46'])).
% 2.33/2.58  thf('48', plain,
% 2.33/2.58      ((((sk_A) = (k9_relat_1 @ sk_B @ sk_A)) | ((sk_A) = (k1_xboole_0)))),
% 2.33/2.58      inference('demod', [status(thm)], ['42', '47'])).
% 2.33/2.58  thf(t160_relat_1, axiom,
% 2.33/2.58    (![A:$i]:
% 2.33/2.58     ( ( v1_relat_1 @ A ) =>
% 2.33/2.58       ( ![B:$i]:
% 2.33/2.58         ( ( v1_relat_1 @ B ) =>
% 2.33/2.58           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 2.33/2.58             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 2.33/2.58  thf('49', plain,
% 2.33/2.58      (![X22 : $i, X23 : $i]:
% 2.33/2.58         (~ (v1_relat_1 @ X22)
% 2.33/2.58          | ((k2_relat_1 @ (k5_relat_1 @ X23 @ X22))
% 2.33/2.58              = (k9_relat_1 @ X22 @ (k2_relat_1 @ X23)))
% 2.33/2.58          | ~ (v1_relat_1 @ X23))),
% 2.33/2.58      inference('cnf', [status(esa)], [t160_relat_1])).
% 2.33/2.58  thf('50', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)) != (sk_A))),
% 2.33/2.58      inference('demod', [status(thm)], ['7', '16'])).
% 2.33/2.58  thf('51', plain,
% 2.33/2.58      ((((k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_C)) != (sk_A))
% 2.33/2.58        | ~ (v1_relat_1 @ sk_C)
% 2.33/2.58        | ~ (v1_relat_1 @ sk_B))),
% 2.33/2.58      inference('sup-', [status(thm)], ['49', '50'])).
% 2.33/2.58  thf('52', plain,
% 2.33/2.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.33/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.58  thf('53', plain,
% 2.33/2.58      (![X40 : $i, X41 : $i, X42 : $i]:
% 2.33/2.58         (((k2_relset_1 @ X41 @ X42 @ X40) = (k2_relat_1 @ X40))
% 2.33/2.58          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 2.33/2.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.33/2.58  thf('54', plain,
% 2.33/2.58      (((k2_relset_1 @ sk_A @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 2.33/2.58      inference('sup-', [status(thm)], ['52', '53'])).
% 2.33/2.58  thf('55', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_C) = (sk_A))),
% 2.33/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.58  thf('56', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 2.33/2.58      inference('sup+', [status(thm)], ['54', '55'])).
% 2.33/2.58  thf('57', plain,
% 2.33/2.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.33/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.58  thf('58', plain,
% 2.33/2.58      (![X31 : $i, X32 : $i, X33 : $i]:
% 2.33/2.58         ((v1_relat_1 @ X31)
% 2.33/2.58          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 2.33/2.58      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.33/2.58  thf('59', plain, ((v1_relat_1 @ sk_C)),
% 2.33/2.58      inference('sup-', [status(thm)], ['57', '58'])).
% 2.33/2.58  thf('60', plain, ((v1_relat_1 @ sk_B)),
% 2.33/2.58      inference('sup-', [status(thm)], ['35', '36'])).
% 2.33/2.58  thf('61', plain, (((k9_relat_1 @ sk_B @ sk_A) != (sk_A))),
% 2.33/2.58      inference('demod', [status(thm)], ['51', '56', '59', '60'])).
% 2.33/2.58  thf('62', plain, ((((sk_A) != (sk_A)) | ((sk_A) = (k1_xboole_0)))),
% 2.33/2.58      inference('sup-', [status(thm)], ['48', '61'])).
% 2.33/2.58  thf('63', plain, (((sk_A) = (k1_xboole_0))),
% 2.33/2.58      inference('simplify', [status(thm)], ['62'])).
% 2.33/2.58  thf('64', plain,
% 2.33/2.58      (((k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)) != (k1_xboole_0))),
% 2.33/2.58      inference('demod', [status(thm)], ['17', '63'])).
% 2.33/2.58  thf('65', plain,
% 2.33/2.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.33/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.58  thf(t3_subset, axiom,
% 2.33/2.58    (![A:$i,B:$i]:
% 2.33/2.58     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.33/2.58  thf('66', plain,
% 2.33/2.58      (![X7 : $i, X8 : $i]:
% 2.33/2.58         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 2.33/2.58      inference('cnf', [status(esa)], [t3_subset])).
% 2.33/2.58  thf('67', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 2.33/2.58      inference('sup-', [status(thm)], ['65', '66'])).
% 2.33/2.58  thf('68', plain,
% 2.33/2.58      (![X0 : $i, X2 : $i]:
% 2.33/2.58         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.33/2.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.33/2.58  thf('69', plain,
% 2.33/2.58      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_C)
% 2.33/2.58        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (sk_C)))),
% 2.33/2.58      inference('sup-', [status(thm)], ['67', '68'])).
% 2.33/2.58  thf('70', plain, (((sk_A) = (k1_xboole_0))),
% 2.33/2.58      inference('simplify', [status(thm)], ['62'])).
% 2.33/2.58  thf('71', plain, (((sk_A) = (k1_xboole_0))),
% 2.33/2.58      inference('simplify', [status(thm)], ['62'])).
% 2.33/2.58  thf(t113_zfmisc_1, axiom,
% 2.33/2.58    (![A:$i,B:$i]:
% 2.33/2.58     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.33/2.58       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.33/2.58  thf('72', plain,
% 2.33/2.58      (![X4 : $i, X5 : $i]:
% 2.33/2.58         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 2.33/2.58      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.33/2.58  thf('73', plain,
% 2.33/2.58      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 2.33/2.58      inference('simplify', [status(thm)], ['72'])).
% 2.33/2.58  thf(t4_subset_1, axiom,
% 2.33/2.58    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 2.33/2.58  thf('74', plain,
% 2.33/2.58      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 2.33/2.58      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.33/2.58  thf('75', plain,
% 2.33/2.58      (![X7 : $i, X8 : $i]:
% 2.33/2.58         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 2.33/2.58      inference('cnf', [status(esa)], [t3_subset])).
% 2.33/2.58  thf('76', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 2.33/2.58      inference('sup-', [status(thm)], ['74', '75'])).
% 2.33/2.58  thf('77', plain, (((sk_A) = (k1_xboole_0))),
% 2.33/2.58      inference('simplify', [status(thm)], ['62'])).
% 2.33/2.58  thf('78', plain, (((sk_A) = (k1_xboole_0))),
% 2.33/2.58      inference('simplify', [status(thm)], ['62'])).
% 2.33/2.58  thf('79', plain,
% 2.33/2.58      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 2.33/2.58      inference('simplify', [status(thm)], ['72'])).
% 2.33/2.58  thf('80', plain, (((k1_xboole_0) = (sk_C))),
% 2.33/2.58      inference('demod', [status(thm)],
% 2.33/2.58                ['69', '70', '71', '73', '76', '77', '78', '79'])).
% 2.33/2.58  thf('81', plain,
% 2.33/2.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.33/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.58  thf('82', plain,
% 2.33/2.58      (![X7 : $i, X8 : $i]:
% 2.33/2.58         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 2.33/2.58      inference('cnf', [status(esa)], [t3_subset])).
% 2.33/2.58  thf('83', plain, ((r1_tarski @ sk_B @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 2.33/2.58      inference('sup-', [status(thm)], ['81', '82'])).
% 2.33/2.58  thf('84', plain,
% 2.33/2.58      (![X0 : $i, X2 : $i]:
% 2.33/2.58         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.33/2.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.33/2.58  thf('85', plain,
% 2.33/2.58      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_B)
% 2.33/2.58        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (sk_B)))),
% 2.33/2.58      inference('sup-', [status(thm)], ['83', '84'])).
% 2.33/2.58  thf('86', plain, (((sk_A) = (k1_xboole_0))),
% 2.33/2.58      inference('simplify', [status(thm)], ['62'])).
% 2.33/2.58  thf('87', plain, (((sk_A) = (k1_xboole_0))),
% 2.33/2.58      inference('simplify', [status(thm)], ['62'])).
% 2.33/2.58  thf('88', plain,
% 2.33/2.58      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 2.33/2.58      inference('simplify', [status(thm)], ['72'])).
% 2.33/2.58  thf('89', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 2.33/2.58      inference('sup-', [status(thm)], ['74', '75'])).
% 2.33/2.58  thf('90', plain, (((sk_A) = (k1_xboole_0))),
% 2.33/2.58      inference('simplify', [status(thm)], ['62'])).
% 2.33/2.58  thf('91', plain, (((sk_A) = (k1_xboole_0))),
% 2.33/2.58      inference('simplify', [status(thm)], ['62'])).
% 2.33/2.58  thf('92', plain,
% 2.33/2.58      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 2.33/2.58      inference('simplify', [status(thm)], ['72'])).
% 2.33/2.58  thf('93', plain, (((k1_xboole_0) = (sk_B))),
% 2.33/2.58      inference('demod', [status(thm)],
% 2.33/2.58                ['85', '86', '87', '88', '89', '90', '91', '92'])).
% 2.33/2.58  thf('94', plain,
% 2.33/2.58      (((k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 2.33/2.58         != (k1_xboole_0))),
% 2.33/2.58      inference('demod', [status(thm)], ['64', '80', '93'])).
% 2.33/2.58  thf('95', plain,
% 2.33/2.58      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 2.33/2.58        | ~ (v1_relat_1 @ k1_xboole_0))),
% 2.33/2.58      inference('sup-', [status(thm)], ['0', '94'])).
% 2.33/2.58  thf('96', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 2.33/2.58      inference('sup+', [status(thm)], ['45', '46'])).
% 2.33/2.58  thf('97', plain, (((sk_A) = (k1_xboole_0))),
% 2.33/2.58      inference('simplify', [status(thm)], ['62'])).
% 2.33/2.58  thf('98', plain, (((k2_relat_1 @ sk_B) = (k1_xboole_0))),
% 2.33/2.58      inference('demod', [status(thm)], ['96', '97'])).
% 2.33/2.58  thf('99', plain, (((k1_xboole_0) = (sk_B))),
% 2.33/2.58      inference('demod', [status(thm)],
% 2.33/2.58                ['85', '86', '87', '88', '89', '90', '91', '92'])).
% 2.33/2.58  thf('100', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.33/2.58      inference('demod', [status(thm)], ['98', '99'])).
% 2.33/2.58  thf('101', plain,
% 2.33/2.58      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 2.33/2.58      inference('simplify', [status(thm)], ['72'])).
% 2.33/2.58  thf('102', plain,
% 2.33/2.58      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 2.33/2.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.33/2.58  thf('103', plain, ((v1_relat_1 @ k1_xboole_0)),
% 2.33/2.58      inference('sup+', [status(thm)], ['101', '102'])).
% 2.33/2.58  thf('104', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 2.33/2.58      inference('demod', [status(thm)], ['95', '100', '103'])).
% 2.33/2.58  thf('105', plain, ($false), inference('simplify', [status(thm)], ['104'])).
% 2.33/2.58  
% 2.33/2.58  % SZS output end Refutation
% 2.33/2.58  
% 2.33/2.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
