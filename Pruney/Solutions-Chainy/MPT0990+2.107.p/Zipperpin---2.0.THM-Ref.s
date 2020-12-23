%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dX3fhBABa8

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:12 EST 2020

% Result     : Theorem 0.96s
% Output     : Refutation 0.96s
% Verified   : 
% Statistics : Number of formulae       :  255 ( 977 expanded)
%              Number of leaves         :   56 ( 308 expanded)
%              Depth                    :   23
%              Number of atoms          : 2275 (20699 expanded)
%              Number of equality atoms :  142 (1352 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(t36_funct_2,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
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
                  = ( k2_funct_1 @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( v4_relat_1 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15
        = ( k7_relat_1 @ X15 @ X16 ) )
      | ~ ( v4_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('9',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['4','9'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) )
        = ( k9_relat_1 @ X10 @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X12: $i] :
      ( ( ( k10_relat_1 @ X12 @ ( k2_relat_1 @ X12 ) )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_D @ sk_B ) @ ( k9_relat_1 @ sk_D @ sk_B ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['7','8'])).

thf('16',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['7','8'])).

thf('17',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['4','9'])).

thf('18',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['4','9'])).

thf('19',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) )
        = ( k9_relat_1 @ X10 @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('20',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k9_relat_1 @ sk_D @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['7','8'])).

thf('22',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k9_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['4','9'])).

thf('24',plain,
    ( ( k10_relat_1 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['14','15','16','17','22','23'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('25',plain,(
    ! [X20: $i] :
      ( ( ( k5_relat_1 @ X20 @ ( k6_relat_1 @ ( k2_relat_1 @ X20 ) ) )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('26',plain,(
    ! [X66: $i] :
      ( ( k6_partfun1 @ X66 )
      = ( k6_relat_1 @ X66 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('27',plain,(
    ! [X20: $i] :
      ( ( ( k5_relat_1 @ X20 @ ( k6_partfun1 @ ( k2_relat_1 @ X20 ) ) )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X20: $i] :
      ( ( ( k5_relat_1 @ X20 @ ( k6_partfun1 @ ( k2_relat_1 @ X20 ) ) )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('29',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) )
        = ( k10_relat_1 @ X14 @ ( k1_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('31',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['30'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('32',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ( v4_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) @ ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('36',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('37',plain,(
    ! [X66: $i] :
      ( ( k6_partfun1 @ X66 )
      = ( k6_relat_1 @ X66 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('38',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X22 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('39',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('40',plain,(
    ! [X66: $i] :
      ( ( k6_partfun1 @ X66 )
      = ( k6_relat_1 @ X66 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('41',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['35','38','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15
        = ( k7_relat_1 @ X15 @ X16 ) )
      | ~ ( v4_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k7_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k7_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( sk_D
      = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['24','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['7','8'])).

thf('51',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('52',plain,(
    ! [X38: $i] :
      ( ~ ( v2_funct_1 @ X38 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X38 ) )
        = X38 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('53',plain,(
    ! [X38: $i] :
      ( ~ ( v2_funct_1 @ X38 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X38 ) )
        = X38 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('54',plain,(
    ! [X26: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( v2_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('55',plain,(
    ! [X21: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('56',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('57',plain,(
    ! [X35: $i] :
      ( ~ ( v2_funct_1 @ X35 )
      | ( ( k1_relat_1 @ X35 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('58',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('59',plain,(
    ! [X35: $i] :
      ( ~ ( v2_funct_1 @ X35 )
      | ( ( k2_relat_1 @ X35 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15
        = ( k7_relat_1 @ X15 @ X16 ) )
      | ~ ( v4_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k7_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k7_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k7_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['51','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['7','8'])).

thf('79',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) )
      = sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('84',plain,(
    ! [X60: $i,X61: $i,X62: $i,X63: $i,X64: $i,X65: $i] :
      ( ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X61 @ X62 ) ) )
      | ~ ( v1_funct_1 @ X60 )
      | ~ ( v1_funct_1 @ X63 )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X64 @ X65 ) ) )
      | ( ( k1_partfun1 @ X61 @ X62 @ X64 @ X65 @ X60 @ X63 )
        = ( k5_relat_1 @ X60 @ X63 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['82','87'])).

thf('89',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['81','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('94',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X54 ) ) )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X57 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X53 @ X54 @ X56 @ X57 @ X52 @ X55 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X57 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['92','97'])).

thf('99',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('101',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('102',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ( X48 = X51 )
      | ~ ( r2_relset_1 @ X49 @ X50 @ X48 @ X51 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['91','103'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('105',plain,(
    ! [X59: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X59 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X59 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('106',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['104','105'])).

thf(t64_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) )
              & ( ( k5_relat_1 @ B @ A )
                = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('107',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v1_relat_1 @ X36 )
      | ~ ( v1_funct_1 @ X36 )
      | ( X36
        = ( k2_funct_1 @ X37 ) )
      | ( ( k5_relat_1 @ X36 @ X37 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X37 ) ) )
      | ( ( k2_relat_1 @ X36 )
       != ( k1_relat_1 @ X37 ) )
      | ~ ( v2_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('108',plain,(
    ! [X66: $i] :
      ( ( k6_partfun1 @ X66 )
      = ( k6_relat_1 @ X66 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('109',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v1_relat_1 @ X36 )
      | ~ ( v1_funct_1 @ X36 )
      | ( X36
        = ( k2_funct_1 @ X37 ) )
      | ( ( k5_relat_1 @ X36 @ X37 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X37 ) ) )
      | ( ( k2_relat_1 @ X36 )
       != ( k1_relat_1 @ X37 ) )
      | ~ ( v2_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['106','109'])).

thf('111',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('113',plain,(
    ! [X67: $i,X68: $i,X69: $i,X70: $i] :
      ( ~ ( v1_funct_1 @ X67 )
      | ~ ( v1_funct_2 @ X67 @ X68 @ X69 )
      | ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X68 @ X69 ) ) )
      | ~ ( r2_relset_1 @ X68 @ X68 @ ( k1_partfun1 @ X68 @ X69 @ X69 @ X68 @ X67 @ X70 ) @ ( k6_partfun1 @ X68 ) )
      | ( ( k2_relset_1 @ X69 @ X68 @ X70 )
        = X68 )
      | ~ ( m1_subset_1 @ X70 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X69 @ X68 ) ) )
      | ~ ( v1_funct_2 @ X70 @ X69 @ X68 )
      | ~ ( v1_funct_1 @ X70 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['111','117'])).

thf('119',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('120',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( ( k2_relset_1 @ X46 @ X47 @ X45 )
        = ( k2_relat_1 @ X45 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('121',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['118','121','122','123','124'])).

thf('126',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['7','8'])).

thf('127',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( ( k2_relset_1 @ X46 @ X47 @ X45 )
        = ( k2_relat_1 @ X45 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('130',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('136',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('138',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['110','125','126','127','132','133','138'])).

thf('140',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['104','105'])).

thf(t48_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) ) )
           => ( ( v2_funct_1 @ B )
              & ( v2_funct_1 @ A ) ) ) ) ) )).

thf('142',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ~ ( v1_funct_1 @ X33 )
      | ( v2_funct_1 @ X34 )
      | ( ( k2_relat_1 @ X33 )
       != ( k1_relat_1 @ X34 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X33 @ X34 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('143',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('144',plain,(
    ! [X25: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('145',plain,(
    ! [X66: $i] :
      ( ( k6_partfun1 @ X66 )
      = ( k6_relat_1 @ X66 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('146',plain,(
    ! [X25: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X25 ) ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['7','8'])).

thf('148',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['130','131'])).

thf('150',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['136','137'])).

thf('152',plain,
    ( ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['143','146','147','148','149','150','151'])).

thf('153',plain,
    ( ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(clc,[status(thm)],['140','152'])).

thf('154',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf('155',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('156',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['7','8'])).

thf('158',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['130','131'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('160',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ X27 @ ( k2_relat_1 @ X28 ) )
      | ( ( k9_relat_1 @ X28 @ ( k10_relat_1 @ X28 @ X27 ) )
        = X27 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('161',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['136','137'])).

thf('163',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['161','162','163'])).

thf('165',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['158','164'])).

thf('166',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('167',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) )
        = ( k10_relat_1 @ X14 @ ( k1_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('168',plain,
    ( ( ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) )
      = ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('170',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['136','137'])).

thf('171',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['7','8'])).

thf('172',plain,
    ( sk_A
    = ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['168','169','170','171'])).

thf('173',plain,
    ( ( k9_relat_1 @ sk_C @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['165','172'])).

thf('174',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( v4_relat_1 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('176',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15
        = ( k7_relat_1 @ X15 @ X16 ) )
      | ~ ( v4_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('178',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['136','137'])).

thf('180',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) )
        = ( k9_relat_1 @ X10 @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('182',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['180','181'])).

thf('183',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['136','137'])).

thf('184',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['182','183'])).

thf('185',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['130','131'])).

thf('186',plain,
    ( sk_B
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['184','185'])).

thf('187',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['173','186'])).

thf('188',plain,
    ( ( sk_B != sk_B )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['153','187'])).

thf('189',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['188'])).

thf('190',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['80','189'])).

thf('191',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    ~ ( v2_funct_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['190','191'])).

thf('193',plain,
    ( ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['143','146','147','148','149','150','151'])).

thf('194',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['173','186'])).

thf('195',plain,
    ( ( sk_B != sk_B )
    | ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['193','194'])).

thf('196',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['195'])).

thf('197',plain,(
    $false ),
    inference(demod,[status(thm)],['192','196'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dX3fhBABa8
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:26:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.96/1.15  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.96/1.15  % Solved by: fo/fo7.sh
% 0.96/1.15  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.96/1.15  % done 1109 iterations in 0.685s
% 0.96/1.15  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.96/1.15  % SZS output start Refutation
% 0.96/1.15  thf(sk_D_type, type, sk_D: $i).
% 0.96/1.15  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.96/1.15  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.96/1.15  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.96/1.15  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.96/1.15  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.96/1.15  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.96/1.15  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.96/1.15  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.96/1.15  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.96/1.15  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.96/1.15  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.96/1.15  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.96/1.15  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.96/1.15  thf(sk_B_type, type, sk_B: $i).
% 0.96/1.15  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.96/1.15  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.96/1.15  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.96/1.15  thf(sk_C_type, type, sk_C: $i).
% 0.96/1.15  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.96/1.15  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.96/1.15  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.96/1.15  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.96/1.15  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.96/1.15  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.96/1.15  thf(sk_A_type, type, sk_A: $i).
% 0.96/1.15  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.96/1.15  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.96/1.15  thf(t36_funct_2, conjecture,
% 0.96/1.15    (![A:$i,B:$i,C:$i]:
% 0.96/1.15     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.96/1.15         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.96/1.15       ( ![D:$i]:
% 0.96/1.15         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.96/1.15             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.96/1.15           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.96/1.15               ( r2_relset_1 @
% 0.96/1.15                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.96/1.15                 ( k6_partfun1 @ A ) ) & 
% 0.96/1.15               ( v2_funct_1 @ C ) ) =>
% 0.96/1.15             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.96/1.15               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.96/1.15  thf(zf_stmt_0, negated_conjecture,
% 0.96/1.15    (~( ![A:$i,B:$i,C:$i]:
% 0.96/1.15        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.96/1.15            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.96/1.15          ( ![D:$i]:
% 0.96/1.15            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.96/1.15                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.96/1.15              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.96/1.15                  ( r2_relset_1 @
% 0.96/1.15                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.96/1.15                    ( k6_partfun1 @ A ) ) & 
% 0.96/1.15                  ( v2_funct_1 @ C ) ) =>
% 0.96/1.15                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.96/1.15                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.96/1.15    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.96/1.15  thf('0', plain,
% 0.96/1.15      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf(cc2_relset_1, axiom,
% 0.96/1.15    (![A:$i,B:$i,C:$i]:
% 0.96/1.15     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.96/1.15       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.96/1.15  thf('1', plain,
% 0.96/1.15      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.96/1.15         ((v4_relat_1 @ X42 @ X43)
% 0.96/1.15          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44))))),
% 0.96/1.15      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.96/1.15  thf('2', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 0.96/1.15      inference('sup-', [status(thm)], ['0', '1'])).
% 0.96/1.15  thf(t209_relat_1, axiom,
% 0.96/1.15    (![A:$i,B:$i]:
% 0.96/1.15     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.96/1.15       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.96/1.15  thf('3', plain,
% 0.96/1.15      (![X15 : $i, X16 : $i]:
% 0.96/1.15         (((X15) = (k7_relat_1 @ X15 @ X16))
% 0.96/1.15          | ~ (v4_relat_1 @ X15 @ X16)
% 0.96/1.15          | ~ (v1_relat_1 @ X15))),
% 0.96/1.15      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.96/1.15  thf('4', plain,
% 0.96/1.15      ((~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ sk_B)))),
% 0.96/1.15      inference('sup-', [status(thm)], ['2', '3'])).
% 0.96/1.15  thf('5', plain,
% 0.96/1.15      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf(cc2_relat_1, axiom,
% 0.96/1.15    (![A:$i]:
% 0.96/1.15     ( ( v1_relat_1 @ A ) =>
% 0.96/1.15       ( ![B:$i]:
% 0.96/1.15         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.96/1.15  thf('6', plain,
% 0.96/1.15      (![X3 : $i, X4 : $i]:
% 0.96/1.15         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.96/1.15          | (v1_relat_1 @ X3)
% 0.96/1.15          | ~ (v1_relat_1 @ X4))),
% 0.96/1.15      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.96/1.15  thf('7', plain,
% 0.96/1.15      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.96/1.15      inference('sup-', [status(thm)], ['5', '6'])).
% 0.96/1.15  thf(fc6_relat_1, axiom,
% 0.96/1.15    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.96/1.15  thf('8', plain,
% 0.96/1.15      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.96/1.15      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.96/1.15  thf('9', plain, ((v1_relat_1 @ sk_D)),
% 0.96/1.15      inference('demod', [status(thm)], ['7', '8'])).
% 0.96/1.15  thf('10', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 0.96/1.15      inference('demod', [status(thm)], ['4', '9'])).
% 0.96/1.15  thf(t148_relat_1, axiom,
% 0.96/1.15    (![A:$i,B:$i]:
% 0.96/1.15     ( ( v1_relat_1 @ B ) =>
% 0.96/1.15       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.96/1.15  thf('11', plain,
% 0.96/1.15      (![X10 : $i, X11 : $i]:
% 0.96/1.15         (((k2_relat_1 @ (k7_relat_1 @ X10 @ X11)) = (k9_relat_1 @ X10 @ X11))
% 0.96/1.15          | ~ (v1_relat_1 @ X10))),
% 0.96/1.15      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.96/1.15  thf(t169_relat_1, axiom,
% 0.96/1.15    (![A:$i]:
% 0.96/1.15     ( ( v1_relat_1 @ A ) =>
% 0.96/1.15       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.96/1.15  thf('12', plain,
% 0.96/1.15      (![X12 : $i]:
% 0.96/1.15         (((k10_relat_1 @ X12 @ (k2_relat_1 @ X12)) = (k1_relat_1 @ X12))
% 0.96/1.15          | ~ (v1_relat_1 @ X12))),
% 0.96/1.15      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.96/1.15  thf('13', plain,
% 0.96/1.15      (![X0 : $i, X1 : $i]:
% 0.96/1.15         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.96/1.15            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.96/1.15          | ~ (v1_relat_1 @ X1)
% 0.96/1.15          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.96/1.15      inference('sup+', [status(thm)], ['11', '12'])).
% 0.96/1.15  thf('14', plain,
% 0.96/1.15      ((~ (v1_relat_1 @ sk_D)
% 0.96/1.15        | ~ (v1_relat_1 @ sk_D)
% 0.96/1.15        | ((k10_relat_1 @ (k7_relat_1 @ sk_D @ sk_B) @ 
% 0.96/1.15            (k9_relat_1 @ sk_D @ sk_B))
% 0.96/1.15            = (k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_B))))),
% 0.96/1.15      inference('sup-', [status(thm)], ['10', '13'])).
% 0.96/1.15  thf('15', plain, ((v1_relat_1 @ sk_D)),
% 0.96/1.15      inference('demod', [status(thm)], ['7', '8'])).
% 0.96/1.15  thf('16', plain, ((v1_relat_1 @ sk_D)),
% 0.96/1.15      inference('demod', [status(thm)], ['7', '8'])).
% 0.96/1.15  thf('17', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 0.96/1.15      inference('demod', [status(thm)], ['4', '9'])).
% 0.96/1.15  thf('18', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 0.96/1.15      inference('demod', [status(thm)], ['4', '9'])).
% 0.96/1.15  thf('19', plain,
% 0.96/1.15      (![X10 : $i, X11 : $i]:
% 0.96/1.15         (((k2_relat_1 @ (k7_relat_1 @ X10 @ X11)) = (k9_relat_1 @ X10 @ X11))
% 0.96/1.15          | ~ (v1_relat_1 @ X10))),
% 0.96/1.15      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.96/1.15  thf('20', plain,
% 0.96/1.15      ((((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ sk_B))
% 0.96/1.15        | ~ (v1_relat_1 @ sk_D))),
% 0.96/1.15      inference('sup+', [status(thm)], ['18', '19'])).
% 0.96/1.15  thf('21', plain, ((v1_relat_1 @ sk_D)),
% 0.96/1.15      inference('demod', [status(thm)], ['7', '8'])).
% 0.96/1.15  thf('22', plain, (((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ sk_B))),
% 0.96/1.15      inference('demod', [status(thm)], ['20', '21'])).
% 0.96/1.15  thf('23', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 0.96/1.15      inference('demod', [status(thm)], ['4', '9'])).
% 0.96/1.15  thf('24', plain,
% 0.96/1.15      (((k10_relat_1 @ sk_D @ (k2_relat_1 @ sk_D)) = (k1_relat_1 @ sk_D))),
% 0.96/1.15      inference('demod', [status(thm)], ['14', '15', '16', '17', '22', '23'])).
% 0.96/1.15  thf(t80_relat_1, axiom,
% 0.96/1.15    (![A:$i]:
% 0.96/1.15     ( ( v1_relat_1 @ A ) =>
% 0.96/1.15       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.96/1.15  thf('25', plain,
% 0.96/1.15      (![X20 : $i]:
% 0.96/1.15         (((k5_relat_1 @ X20 @ (k6_relat_1 @ (k2_relat_1 @ X20))) = (X20))
% 0.96/1.15          | ~ (v1_relat_1 @ X20))),
% 0.96/1.15      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.96/1.15  thf(redefinition_k6_partfun1, axiom,
% 0.96/1.15    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.96/1.15  thf('26', plain, (![X66 : $i]: ((k6_partfun1 @ X66) = (k6_relat_1 @ X66))),
% 0.96/1.15      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.96/1.15  thf('27', plain,
% 0.96/1.15      (![X20 : $i]:
% 0.96/1.15         (((k5_relat_1 @ X20 @ (k6_partfun1 @ (k2_relat_1 @ X20))) = (X20))
% 0.96/1.15          | ~ (v1_relat_1 @ X20))),
% 0.96/1.15      inference('demod', [status(thm)], ['25', '26'])).
% 0.96/1.15  thf('28', plain,
% 0.96/1.15      (![X20 : $i]:
% 0.96/1.15         (((k5_relat_1 @ X20 @ (k6_partfun1 @ (k2_relat_1 @ X20))) = (X20))
% 0.96/1.15          | ~ (v1_relat_1 @ X20))),
% 0.96/1.15      inference('demod', [status(thm)], ['25', '26'])).
% 0.96/1.15  thf(t182_relat_1, axiom,
% 0.96/1.15    (![A:$i]:
% 0.96/1.15     ( ( v1_relat_1 @ A ) =>
% 0.96/1.15       ( ![B:$i]:
% 0.96/1.15         ( ( v1_relat_1 @ B ) =>
% 0.96/1.15           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.96/1.15             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.96/1.15  thf('29', plain,
% 0.96/1.15      (![X13 : $i, X14 : $i]:
% 0.96/1.15         (~ (v1_relat_1 @ X13)
% 0.96/1.15          | ((k1_relat_1 @ (k5_relat_1 @ X14 @ X13))
% 0.96/1.15              = (k10_relat_1 @ X14 @ (k1_relat_1 @ X13)))
% 0.96/1.15          | ~ (v1_relat_1 @ X14))),
% 0.96/1.15      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.96/1.15  thf(d10_xboole_0, axiom,
% 0.96/1.15    (![A:$i,B:$i]:
% 0.96/1.15     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.96/1.15  thf('30', plain,
% 0.96/1.15      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.96/1.15      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.96/1.15  thf('31', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.96/1.15      inference('simplify', [status(thm)], ['30'])).
% 0.96/1.15  thf(d18_relat_1, axiom,
% 0.96/1.15    (![A:$i,B:$i]:
% 0.96/1.15     ( ( v1_relat_1 @ B ) =>
% 0.96/1.15       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.96/1.15  thf('32', plain,
% 0.96/1.15      (![X5 : $i, X6 : $i]:
% 0.96/1.15         (~ (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 0.96/1.15          | (v4_relat_1 @ X5 @ X6)
% 0.96/1.15          | ~ (v1_relat_1 @ X5))),
% 0.96/1.15      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.96/1.15  thf('33', plain,
% 0.96/1.15      (![X0 : $i]:
% 0.96/1.15         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.96/1.15      inference('sup-', [status(thm)], ['31', '32'])).
% 0.96/1.15  thf('34', plain,
% 0.96/1.15      (![X0 : $i, X1 : $i]:
% 0.96/1.15         ((v4_relat_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 0.96/1.15           (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.96/1.15          | ~ (v1_relat_1 @ X1)
% 0.96/1.15          | ~ (v1_relat_1 @ X0)
% 0.96/1.15          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.96/1.15      inference('sup+', [status(thm)], ['29', '33'])).
% 0.96/1.15  thf('35', plain,
% 0.96/1.15      (![X0 : $i]:
% 0.96/1.15         (~ (v1_relat_1 @ X0)
% 0.96/1.15          | ~ (v1_relat_1 @ X0)
% 0.96/1.15          | ~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 0.96/1.15          | ~ (v1_relat_1 @ X0)
% 0.96/1.15          | (v4_relat_1 @ 
% 0.96/1.15             (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) @ 
% 0.96/1.15             (k10_relat_1 @ X0 @ 
% 0.96/1.15              (k1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0))))))),
% 0.96/1.15      inference('sup-', [status(thm)], ['28', '34'])).
% 0.96/1.15  thf(fc3_funct_1, axiom,
% 0.96/1.15    (![A:$i]:
% 0.96/1.15     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.96/1.15       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.96/1.15  thf('36', plain, (![X22 : $i]: (v1_relat_1 @ (k6_relat_1 @ X22))),
% 0.96/1.15      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.96/1.15  thf('37', plain, (![X66 : $i]: ((k6_partfun1 @ X66) = (k6_relat_1 @ X66))),
% 0.96/1.15      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.96/1.15  thf('38', plain, (![X22 : $i]: (v1_relat_1 @ (k6_partfun1 @ X22))),
% 0.96/1.15      inference('demod', [status(thm)], ['36', '37'])).
% 0.96/1.15  thf(t71_relat_1, axiom,
% 0.96/1.15    (![A:$i]:
% 0.96/1.15     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.96/1.15       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.96/1.15  thf('39', plain, (![X17 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X17)) = (X17))),
% 0.96/1.15      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.96/1.15  thf('40', plain, (![X66 : $i]: ((k6_partfun1 @ X66) = (k6_relat_1 @ X66))),
% 0.96/1.15      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.96/1.15  thf('41', plain, (![X17 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X17)) = (X17))),
% 0.96/1.15      inference('demod', [status(thm)], ['39', '40'])).
% 0.96/1.15  thf('42', plain,
% 0.96/1.15      (![X0 : $i]:
% 0.96/1.15         (~ (v1_relat_1 @ X0)
% 0.96/1.15          | ~ (v1_relat_1 @ X0)
% 0.96/1.15          | ~ (v1_relat_1 @ X0)
% 0.96/1.15          | (v4_relat_1 @ 
% 0.96/1.15             (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) @ 
% 0.96/1.15             (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 0.96/1.15      inference('demod', [status(thm)], ['35', '38', '41'])).
% 0.96/1.15  thf('43', plain,
% 0.96/1.15      (![X0 : $i]:
% 0.96/1.15         ((v4_relat_1 @ 
% 0.96/1.15           (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) @ 
% 0.96/1.15           (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.96/1.15          | ~ (v1_relat_1 @ X0))),
% 0.96/1.15      inference('simplify', [status(thm)], ['42'])).
% 0.96/1.15  thf('44', plain,
% 0.96/1.15      (![X0 : $i]:
% 0.96/1.15         ((v4_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.96/1.15          | ~ (v1_relat_1 @ X0)
% 0.96/1.15          | ~ (v1_relat_1 @ X0))),
% 0.96/1.15      inference('sup+', [status(thm)], ['27', '43'])).
% 0.96/1.15  thf('45', plain,
% 0.96/1.15      (![X0 : $i]:
% 0.96/1.15         (~ (v1_relat_1 @ X0)
% 0.96/1.15          | (v4_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 0.96/1.15      inference('simplify', [status(thm)], ['44'])).
% 0.96/1.15  thf('46', plain,
% 0.96/1.15      (![X15 : $i, X16 : $i]:
% 0.96/1.15         (((X15) = (k7_relat_1 @ X15 @ X16))
% 0.96/1.15          | ~ (v4_relat_1 @ X15 @ X16)
% 0.96/1.15          | ~ (v1_relat_1 @ X15))),
% 0.96/1.15      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.96/1.15  thf('47', plain,
% 0.96/1.15      (![X0 : $i]:
% 0.96/1.15         (~ (v1_relat_1 @ X0)
% 0.96/1.15          | ~ (v1_relat_1 @ X0)
% 0.96/1.15          | ((X0) = (k7_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))))),
% 0.96/1.15      inference('sup-', [status(thm)], ['45', '46'])).
% 0.96/1.15  thf('48', plain,
% 0.96/1.15      (![X0 : $i]:
% 0.96/1.15         (((X0) = (k7_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))
% 0.96/1.15          | ~ (v1_relat_1 @ X0))),
% 0.96/1.15      inference('simplify', [status(thm)], ['47'])).
% 0.96/1.15  thf('49', plain,
% 0.96/1.15      ((((sk_D) = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))
% 0.96/1.15        | ~ (v1_relat_1 @ sk_D))),
% 0.96/1.15      inference('sup+', [status(thm)], ['24', '48'])).
% 0.96/1.15  thf('50', plain, ((v1_relat_1 @ sk_D)),
% 0.96/1.15      inference('demod', [status(thm)], ['7', '8'])).
% 0.96/1.15  thf('51', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))),
% 0.96/1.15      inference('demod', [status(thm)], ['49', '50'])).
% 0.96/1.15  thf(t65_funct_1, axiom,
% 0.96/1.15    (![A:$i]:
% 0.96/1.15     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.96/1.15       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.96/1.15  thf('52', plain,
% 0.96/1.15      (![X38 : $i]:
% 0.96/1.15         (~ (v2_funct_1 @ X38)
% 0.96/1.15          | ((k2_funct_1 @ (k2_funct_1 @ X38)) = (X38))
% 0.96/1.15          | ~ (v1_funct_1 @ X38)
% 0.96/1.15          | ~ (v1_relat_1 @ X38))),
% 0.96/1.15      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.96/1.15  thf('53', plain,
% 0.96/1.15      (![X38 : $i]:
% 0.96/1.15         (~ (v2_funct_1 @ X38)
% 0.96/1.15          | ((k2_funct_1 @ (k2_funct_1 @ X38)) = (X38))
% 0.96/1.15          | ~ (v1_funct_1 @ X38)
% 0.96/1.15          | ~ (v1_relat_1 @ X38))),
% 0.96/1.15      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.96/1.15  thf(fc6_funct_1, axiom,
% 0.96/1.15    (![A:$i]:
% 0.96/1.15     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.96/1.15       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.96/1.15         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.96/1.15         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.96/1.15  thf('54', plain,
% 0.96/1.15      (![X26 : $i]:
% 0.96/1.15         ((v2_funct_1 @ (k2_funct_1 @ X26))
% 0.96/1.15          | ~ (v2_funct_1 @ X26)
% 0.96/1.15          | ~ (v1_funct_1 @ X26)
% 0.96/1.15          | ~ (v1_relat_1 @ X26))),
% 0.96/1.15      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.96/1.15  thf(dt_k2_funct_1, axiom,
% 0.96/1.15    (![A:$i]:
% 0.96/1.15     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.96/1.15       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.96/1.15         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.96/1.15  thf('55', plain,
% 0.96/1.15      (![X21 : $i]:
% 0.96/1.15         ((v1_funct_1 @ (k2_funct_1 @ X21))
% 0.96/1.15          | ~ (v1_funct_1 @ X21)
% 0.96/1.15          | ~ (v1_relat_1 @ X21))),
% 0.96/1.15      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.96/1.15  thf('56', plain,
% 0.96/1.15      (![X21 : $i]:
% 0.96/1.15         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 0.96/1.15          | ~ (v1_funct_1 @ X21)
% 0.96/1.15          | ~ (v1_relat_1 @ X21))),
% 0.96/1.15      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.96/1.15  thf(t55_funct_1, axiom,
% 0.96/1.15    (![A:$i]:
% 0.96/1.15     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.96/1.15       ( ( v2_funct_1 @ A ) =>
% 0.96/1.15         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.96/1.15           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.96/1.15  thf('57', plain,
% 0.96/1.15      (![X35 : $i]:
% 0.96/1.15         (~ (v2_funct_1 @ X35)
% 0.96/1.15          | ((k1_relat_1 @ X35) = (k2_relat_1 @ (k2_funct_1 @ X35)))
% 0.96/1.15          | ~ (v1_funct_1 @ X35)
% 0.96/1.15          | ~ (v1_relat_1 @ X35))),
% 0.96/1.15      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.96/1.15  thf('58', plain,
% 0.96/1.15      (![X21 : $i]:
% 0.96/1.15         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 0.96/1.15          | ~ (v1_funct_1 @ X21)
% 0.96/1.15          | ~ (v1_relat_1 @ X21))),
% 0.96/1.15      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.96/1.15  thf('59', plain,
% 0.96/1.15      (![X35 : $i]:
% 0.96/1.15         (~ (v2_funct_1 @ X35)
% 0.96/1.15          | ((k2_relat_1 @ X35) = (k1_relat_1 @ (k2_funct_1 @ X35)))
% 0.96/1.15          | ~ (v1_funct_1 @ X35)
% 0.96/1.15          | ~ (v1_relat_1 @ X35))),
% 0.96/1.15      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.96/1.15  thf('60', plain,
% 0.96/1.15      (![X0 : $i]:
% 0.96/1.15         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.96/1.15      inference('sup-', [status(thm)], ['31', '32'])).
% 0.96/1.15  thf('61', plain,
% 0.96/1.15      (![X0 : $i]:
% 0.96/1.15         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.96/1.15          | ~ (v1_relat_1 @ X0)
% 0.96/1.15          | ~ (v1_funct_1 @ X0)
% 0.96/1.15          | ~ (v2_funct_1 @ X0)
% 0.96/1.15          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.96/1.15      inference('sup+', [status(thm)], ['59', '60'])).
% 0.96/1.15  thf('62', plain,
% 0.96/1.15      (![X0 : $i]:
% 0.96/1.15         (~ (v1_relat_1 @ X0)
% 0.96/1.15          | ~ (v1_funct_1 @ X0)
% 0.96/1.15          | ~ (v2_funct_1 @ X0)
% 0.96/1.15          | ~ (v1_funct_1 @ X0)
% 0.96/1.15          | ~ (v1_relat_1 @ X0)
% 0.96/1.15          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.96/1.15      inference('sup-', [status(thm)], ['58', '61'])).
% 0.96/1.15  thf('63', plain,
% 0.96/1.15      (![X0 : $i]:
% 0.96/1.15         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.96/1.15          | ~ (v2_funct_1 @ X0)
% 0.96/1.15          | ~ (v1_funct_1 @ X0)
% 0.96/1.15          | ~ (v1_relat_1 @ X0))),
% 0.96/1.15      inference('simplify', [status(thm)], ['62'])).
% 0.96/1.15  thf('64', plain,
% 0.96/1.15      (![X0 : $i]:
% 0.96/1.15         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.96/1.15          | ~ (v1_relat_1 @ X0)
% 0.96/1.15          | ~ (v1_funct_1 @ X0)
% 0.96/1.15          | ~ (v2_funct_1 @ X0)
% 0.96/1.15          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.96/1.15          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.96/1.15          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.96/1.15      inference('sup+', [status(thm)], ['57', '63'])).
% 0.96/1.15  thf('65', plain,
% 0.96/1.15      (![X0 : $i]:
% 0.96/1.15         (~ (v1_relat_1 @ X0)
% 0.96/1.15          | ~ (v1_funct_1 @ X0)
% 0.96/1.15          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.96/1.15          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.96/1.15          | ~ (v2_funct_1 @ X0)
% 0.96/1.15          | ~ (v1_funct_1 @ X0)
% 0.96/1.15          | ~ (v1_relat_1 @ X0)
% 0.96/1.15          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.96/1.15      inference('sup-', [status(thm)], ['56', '64'])).
% 0.96/1.15  thf('66', plain,
% 0.96/1.15      (![X0 : $i]:
% 0.96/1.15         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.96/1.15          | ~ (v2_funct_1 @ X0)
% 0.96/1.15          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.96/1.15          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.96/1.15          | ~ (v1_funct_1 @ X0)
% 0.96/1.15          | ~ (v1_relat_1 @ X0))),
% 0.96/1.15      inference('simplify', [status(thm)], ['65'])).
% 0.96/1.15  thf('67', plain,
% 0.96/1.15      (![X0 : $i]:
% 0.96/1.15         (~ (v1_relat_1 @ X0)
% 0.96/1.15          | ~ (v1_funct_1 @ X0)
% 0.96/1.15          | ~ (v1_relat_1 @ X0)
% 0.96/1.15          | ~ (v1_funct_1 @ X0)
% 0.96/1.15          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.96/1.15          | ~ (v2_funct_1 @ X0)
% 0.96/1.15          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.96/1.15      inference('sup-', [status(thm)], ['55', '66'])).
% 0.96/1.15  thf('68', plain,
% 0.96/1.15      (![X0 : $i]:
% 0.96/1.15         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.96/1.15          | ~ (v2_funct_1 @ X0)
% 0.96/1.15          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.96/1.15          | ~ (v1_funct_1 @ X0)
% 0.96/1.15          | ~ (v1_relat_1 @ X0))),
% 0.96/1.15      inference('simplify', [status(thm)], ['67'])).
% 0.96/1.15  thf('69', plain,
% 0.96/1.15      (![X0 : $i]:
% 0.96/1.15         (~ (v1_relat_1 @ X0)
% 0.96/1.15          | ~ (v1_funct_1 @ X0)
% 0.96/1.15          | ~ (v2_funct_1 @ X0)
% 0.96/1.15          | ~ (v1_relat_1 @ X0)
% 0.96/1.15          | ~ (v1_funct_1 @ X0)
% 0.96/1.15          | ~ (v2_funct_1 @ X0)
% 0.96/1.15          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.96/1.15      inference('sup-', [status(thm)], ['54', '68'])).
% 0.96/1.15  thf('70', plain,
% 0.96/1.15      (![X0 : $i]:
% 0.96/1.15         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.96/1.15          | ~ (v2_funct_1 @ X0)
% 0.96/1.15          | ~ (v1_funct_1 @ X0)
% 0.96/1.15          | ~ (v1_relat_1 @ X0))),
% 0.96/1.15      inference('simplify', [status(thm)], ['69'])).
% 0.96/1.15  thf('71', plain,
% 0.96/1.15      (![X15 : $i, X16 : $i]:
% 0.96/1.15         (((X15) = (k7_relat_1 @ X15 @ X16))
% 0.96/1.15          | ~ (v4_relat_1 @ X15 @ X16)
% 0.96/1.15          | ~ (v1_relat_1 @ X15))),
% 0.96/1.15      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.96/1.15  thf('72', plain,
% 0.96/1.15      (![X0 : $i]:
% 0.96/1.15         (~ (v1_relat_1 @ X0)
% 0.96/1.15          | ~ (v1_funct_1 @ X0)
% 0.96/1.15          | ~ (v2_funct_1 @ X0)
% 0.96/1.15          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.96/1.15          | ((k2_funct_1 @ (k2_funct_1 @ X0))
% 0.96/1.15              = (k7_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.96/1.15                 (k1_relat_1 @ X0))))),
% 0.96/1.15      inference('sup-', [status(thm)], ['70', '71'])).
% 0.96/1.15  thf('73', plain,
% 0.96/1.15      (![X0 : $i]:
% 0.96/1.15         (~ (v1_relat_1 @ X0)
% 0.96/1.15          | ~ (v1_relat_1 @ X0)
% 0.96/1.15          | ~ (v1_funct_1 @ X0)
% 0.96/1.15          | ~ (v2_funct_1 @ X0)
% 0.96/1.15          | ((k2_funct_1 @ (k2_funct_1 @ X0))
% 0.96/1.15              = (k7_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.96/1.15                 (k1_relat_1 @ X0)))
% 0.96/1.15          | ~ (v2_funct_1 @ X0)
% 0.96/1.15          | ~ (v1_funct_1 @ X0)
% 0.96/1.15          | ~ (v1_relat_1 @ X0))),
% 0.96/1.15      inference('sup-', [status(thm)], ['53', '72'])).
% 0.96/1.15  thf('74', plain,
% 0.96/1.15      (![X0 : $i]:
% 0.96/1.15         (((k2_funct_1 @ (k2_funct_1 @ X0))
% 0.96/1.15            = (k7_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.96/1.15               (k1_relat_1 @ X0)))
% 0.96/1.15          | ~ (v2_funct_1 @ X0)
% 0.96/1.15          | ~ (v1_funct_1 @ X0)
% 0.96/1.15          | ~ (v1_relat_1 @ X0))),
% 0.96/1.15      inference('simplify', [status(thm)], ['73'])).
% 0.96/1.15  thf('75', plain,
% 0.96/1.15      (![X0 : $i]:
% 0.96/1.15         (((k2_funct_1 @ (k2_funct_1 @ X0))
% 0.96/1.15            = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.96/1.15          | ~ (v1_relat_1 @ X0)
% 0.96/1.15          | ~ (v1_funct_1 @ X0)
% 0.96/1.15          | ~ (v2_funct_1 @ X0)
% 0.96/1.15          | ~ (v1_relat_1 @ X0)
% 0.96/1.15          | ~ (v1_funct_1 @ X0)
% 0.96/1.15          | ~ (v2_funct_1 @ X0))),
% 0.96/1.15      inference('sup+', [status(thm)], ['52', '74'])).
% 0.96/1.15  thf('76', plain,
% 0.96/1.15      (![X0 : $i]:
% 0.96/1.15         (~ (v2_funct_1 @ X0)
% 0.96/1.15          | ~ (v1_funct_1 @ X0)
% 0.96/1.15          | ~ (v1_relat_1 @ X0)
% 0.96/1.15          | ((k2_funct_1 @ (k2_funct_1 @ X0))
% 0.96/1.15              = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.96/1.15      inference('simplify', [status(thm)], ['75'])).
% 0.96/1.15  thf('77', plain,
% 0.96/1.15      ((((k2_funct_1 @ (k2_funct_1 @ sk_D)) = (sk_D))
% 0.96/1.15        | ~ (v1_relat_1 @ sk_D)
% 0.96/1.15        | ~ (v1_funct_1 @ sk_D)
% 0.96/1.15        | ~ (v2_funct_1 @ sk_D))),
% 0.96/1.15      inference('sup+', [status(thm)], ['51', '76'])).
% 0.96/1.15  thf('78', plain, ((v1_relat_1 @ sk_D)),
% 0.96/1.15      inference('demod', [status(thm)], ['7', '8'])).
% 0.96/1.15  thf('79', plain, ((v1_funct_1 @ sk_D)),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('80', plain,
% 0.96/1.15      ((((k2_funct_1 @ (k2_funct_1 @ sk_D)) = (sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 0.96/1.15      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.96/1.15  thf('81', plain,
% 0.96/1.15      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.96/1.15        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.96/1.15        (k6_partfun1 @ sk_A))),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('82', plain,
% 0.96/1.15      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('83', plain,
% 0.96/1.15      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf(redefinition_k1_partfun1, axiom,
% 0.96/1.15    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.96/1.15     ( ( ( v1_funct_1 @ E ) & 
% 0.96/1.15         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.96/1.15         ( v1_funct_1 @ F ) & 
% 0.96/1.15         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.96/1.15       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.96/1.15  thf('84', plain,
% 0.96/1.15      (![X60 : $i, X61 : $i, X62 : $i, X63 : $i, X64 : $i, X65 : $i]:
% 0.96/1.15         (~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X61 @ X62)))
% 0.96/1.15          | ~ (v1_funct_1 @ X60)
% 0.96/1.15          | ~ (v1_funct_1 @ X63)
% 0.96/1.15          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X64 @ X65)))
% 0.96/1.15          | ((k1_partfun1 @ X61 @ X62 @ X64 @ X65 @ X60 @ X63)
% 0.96/1.15              = (k5_relat_1 @ X60 @ X63)))),
% 0.96/1.15      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.96/1.15  thf('85', plain,
% 0.96/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.96/1.15         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.96/1.15            = (k5_relat_1 @ sk_C @ X0))
% 0.96/1.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.96/1.15          | ~ (v1_funct_1 @ X0)
% 0.96/1.15          | ~ (v1_funct_1 @ sk_C))),
% 0.96/1.15      inference('sup-', [status(thm)], ['83', '84'])).
% 0.96/1.15  thf('86', plain, ((v1_funct_1 @ sk_C)),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('87', plain,
% 0.96/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.96/1.15         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.96/1.15            = (k5_relat_1 @ sk_C @ X0))
% 0.96/1.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.96/1.15          | ~ (v1_funct_1 @ X0))),
% 0.96/1.15      inference('demod', [status(thm)], ['85', '86'])).
% 0.96/1.15  thf('88', plain,
% 0.96/1.15      ((~ (v1_funct_1 @ sk_D)
% 0.96/1.15        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.96/1.15            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.96/1.15      inference('sup-', [status(thm)], ['82', '87'])).
% 0.96/1.15  thf('89', plain, ((v1_funct_1 @ sk_D)),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('90', plain,
% 0.96/1.15      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.96/1.15         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.96/1.15      inference('demod', [status(thm)], ['88', '89'])).
% 0.96/1.15  thf('91', plain,
% 0.96/1.15      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.96/1.15        (k6_partfun1 @ sk_A))),
% 0.96/1.15      inference('demod', [status(thm)], ['81', '90'])).
% 0.96/1.15  thf('92', plain,
% 0.96/1.15      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('93', plain,
% 0.96/1.15      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf(dt_k1_partfun1, axiom,
% 0.96/1.15    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.96/1.15     ( ( ( v1_funct_1 @ E ) & 
% 0.96/1.15         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.96/1.15         ( v1_funct_1 @ F ) & 
% 0.96/1.15         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.96/1.15       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.96/1.15         ( m1_subset_1 @
% 0.96/1.15           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.96/1.15           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.96/1.15  thf('94', plain,
% 0.96/1.15      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 0.96/1.15         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X54)))
% 0.96/1.15          | ~ (v1_funct_1 @ X52)
% 0.96/1.15          | ~ (v1_funct_1 @ X55)
% 0.96/1.15          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X57)))
% 0.96/1.15          | (m1_subset_1 @ (k1_partfun1 @ X53 @ X54 @ X56 @ X57 @ X52 @ X55) @ 
% 0.96/1.15             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X57))))),
% 0.96/1.15      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.96/1.15  thf('95', plain,
% 0.96/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.96/1.15         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.96/1.15           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.96/1.15          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.96/1.15          | ~ (v1_funct_1 @ X1)
% 0.96/1.15          | ~ (v1_funct_1 @ sk_C))),
% 0.96/1.15      inference('sup-', [status(thm)], ['93', '94'])).
% 0.96/1.15  thf('96', plain, ((v1_funct_1 @ sk_C)),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('97', plain,
% 0.96/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.96/1.15         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.96/1.15           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.96/1.15          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.96/1.15          | ~ (v1_funct_1 @ X1))),
% 0.96/1.15      inference('demod', [status(thm)], ['95', '96'])).
% 0.96/1.15  thf('98', plain,
% 0.96/1.15      ((~ (v1_funct_1 @ sk_D)
% 0.96/1.15        | (m1_subset_1 @ 
% 0.96/1.15           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.96/1.15           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.96/1.15      inference('sup-', [status(thm)], ['92', '97'])).
% 0.96/1.15  thf('99', plain, ((v1_funct_1 @ sk_D)),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('100', plain,
% 0.96/1.15      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.96/1.15         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.96/1.15      inference('demod', [status(thm)], ['88', '89'])).
% 0.96/1.15  thf('101', plain,
% 0.96/1.15      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.96/1.15        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.96/1.15      inference('demod', [status(thm)], ['98', '99', '100'])).
% 0.96/1.15  thf(redefinition_r2_relset_1, axiom,
% 0.96/1.15    (![A:$i,B:$i,C:$i,D:$i]:
% 0.96/1.15     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.96/1.15         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.96/1.15       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.96/1.15  thf('102', plain,
% 0.96/1.15      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 0.96/1.15         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 0.96/1.15          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 0.96/1.15          | ((X48) = (X51))
% 0.96/1.15          | ~ (r2_relset_1 @ X49 @ X50 @ X48 @ X51))),
% 0.96/1.15      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.96/1.15  thf('103', plain,
% 0.96/1.15      (![X0 : $i]:
% 0.96/1.15         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 0.96/1.15          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 0.96/1.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.96/1.15      inference('sup-', [status(thm)], ['101', '102'])).
% 0.96/1.15  thf('104', plain,
% 0.96/1.15      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.96/1.15           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.96/1.15        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 0.96/1.15      inference('sup-', [status(thm)], ['91', '103'])).
% 0.96/1.15  thf(dt_k6_partfun1, axiom,
% 0.96/1.15    (![A:$i]:
% 0.96/1.15     ( ( m1_subset_1 @
% 0.96/1.15         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.96/1.15       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.96/1.15  thf('105', plain,
% 0.96/1.15      (![X59 : $i]:
% 0.96/1.15         (m1_subset_1 @ (k6_partfun1 @ X59) @ 
% 0.96/1.15          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X59)))),
% 0.96/1.15      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.96/1.15  thf('106', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.96/1.15      inference('demod', [status(thm)], ['104', '105'])).
% 0.96/1.15  thf(t64_funct_1, axiom,
% 0.96/1.15    (![A:$i]:
% 0.96/1.15     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.96/1.15       ( ![B:$i]:
% 0.96/1.15         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.96/1.15           ( ( ( v2_funct_1 @ A ) & 
% 0.96/1.15               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.96/1.15               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.96/1.15             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.96/1.15  thf('107', plain,
% 0.96/1.15      (![X36 : $i, X37 : $i]:
% 0.96/1.15         (~ (v1_relat_1 @ X36)
% 0.96/1.15          | ~ (v1_funct_1 @ X36)
% 0.96/1.15          | ((X36) = (k2_funct_1 @ X37))
% 0.96/1.15          | ((k5_relat_1 @ X36 @ X37) != (k6_relat_1 @ (k2_relat_1 @ X37)))
% 0.96/1.15          | ((k2_relat_1 @ X36) != (k1_relat_1 @ X37))
% 0.96/1.15          | ~ (v2_funct_1 @ X37)
% 0.96/1.15          | ~ (v1_funct_1 @ X37)
% 0.96/1.15          | ~ (v1_relat_1 @ X37))),
% 0.96/1.15      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.96/1.15  thf('108', plain, (![X66 : $i]: ((k6_partfun1 @ X66) = (k6_relat_1 @ X66))),
% 0.96/1.15      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.96/1.15  thf('109', plain,
% 0.96/1.15      (![X36 : $i, X37 : $i]:
% 0.96/1.15         (~ (v1_relat_1 @ X36)
% 0.96/1.15          | ~ (v1_funct_1 @ X36)
% 0.96/1.15          | ((X36) = (k2_funct_1 @ X37))
% 0.96/1.15          | ((k5_relat_1 @ X36 @ X37) != (k6_partfun1 @ (k2_relat_1 @ X37)))
% 0.96/1.15          | ((k2_relat_1 @ X36) != (k1_relat_1 @ X37))
% 0.96/1.15          | ~ (v2_funct_1 @ X37)
% 0.96/1.15          | ~ (v1_funct_1 @ X37)
% 0.96/1.15          | ~ (v1_relat_1 @ X37))),
% 0.96/1.15      inference('demod', [status(thm)], ['107', '108'])).
% 0.96/1.15  thf('110', plain,
% 0.96/1.15      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 0.96/1.15        | ~ (v1_relat_1 @ sk_D)
% 0.96/1.15        | ~ (v1_funct_1 @ sk_D)
% 0.96/1.15        | ~ (v2_funct_1 @ sk_D)
% 0.96/1.15        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.96/1.15        | ((sk_C) = (k2_funct_1 @ sk_D))
% 0.96/1.15        | ~ (v1_funct_1 @ sk_C)
% 0.96/1.15        | ~ (v1_relat_1 @ sk_C))),
% 0.96/1.15      inference('sup-', [status(thm)], ['106', '109'])).
% 0.96/1.15  thf('111', plain,
% 0.96/1.15      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.96/1.15        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.96/1.15        (k6_partfun1 @ sk_A))),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('112', plain,
% 0.96/1.15      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf(t24_funct_2, axiom,
% 0.96/1.15    (![A:$i,B:$i,C:$i]:
% 0.96/1.15     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.96/1.15         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.96/1.15       ( ![D:$i]:
% 0.96/1.15         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.96/1.15             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.96/1.15           ( ( r2_relset_1 @
% 0.96/1.15               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.96/1.15               ( k6_partfun1 @ B ) ) =>
% 0.96/1.15             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.96/1.15  thf('113', plain,
% 0.96/1.15      (![X67 : $i, X68 : $i, X69 : $i, X70 : $i]:
% 0.96/1.15         (~ (v1_funct_1 @ X67)
% 0.96/1.15          | ~ (v1_funct_2 @ X67 @ X68 @ X69)
% 0.96/1.15          | ~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X68 @ X69)))
% 0.96/1.15          | ~ (r2_relset_1 @ X68 @ X68 @ 
% 0.96/1.15               (k1_partfun1 @ X68 @ X69 @ X69 @ X68 @ X67 @ X70) @ 
% 0.96/1.15               (k6_partfun1 @ X68))
% 0.96/1.15          | ((k2_relset_1 @ X69 @ X68 @ X70) = (X68))
% 0.96/1.15          | ~ (m1_subset_1 @ X70 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X69 @ X68)))
% 0.96/1.15          | ~ (v1_funct_2 @ X70 @ X69 @ X68)
% 0.96/1.15          | ~ (v1_funct_1 @ X70))),
% 0.96/1.15      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.96/1.15  thf('114', plain,
% 0.96/1.15      (![X0 : $i]:
% 0.96/1.15         (~ (v1_funct_1 @ X0)
% 0.96/1.15          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.96/1.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.96/1.15          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.96/1.15          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.96/1.15               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.96/1.15               (k6_partfun1 @ sk_A))
% 0.96/1.15          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.96/1.15          | ~ (v1_funct_1 @ sk_C))),
% 0.96/1.15      inference('sup-', [status(thm)], ['112', '113'])).
% 0.96/1.15  thf('115', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('116', plain, ((v1_funct_1 @ sk_C)),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('117', plain,
% 0.96/1.15      (![X0 : $i]:
% 0.96/1.15         (~ (v1_funct_1 @ X0)
% 0.96/1.15          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.96/1.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.96/1.15          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.96/1.15          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.96/1.15               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.96/1.15               (k6_partfun1 @ sk_A)))),
% 0.96/1.15      inference('demod', [status(thm)], ['114', '115', '116'])).
% 0.96/1.15  thf('118', plain,
% 0.96/1.15      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.96/1.15        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.96/1.15        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.96/1.15        | ~ (v1_funct_1 @ sk_D))),
% 0.96/1.15      inference('sup-', [status(thm)], ['111', '117'])).
% 0.96/1.15  thf('119', plain,
% 0.96/1.15      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf(redefinition_k2_relset_1, axiom,
% 0.96/1.15    (![A:$i,B:$i,C:$i]:
% 0.96/1.15     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.96/1.15       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.96/1.15  thf('120', plain,
% 0.96/1.15      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.96/1.15         (((k2_relset_1 @ X46 @ X47 @ X45) = (k2_relat_1 @ X45))
% 0.96/1.15          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47))))),
% 0.96/1.15      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.96/1.15  thf('121', plain,
% 0.96/1.15      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.96/1.15      inference('sup-', [status(thm)], ['119', '120'])).
% 0.96/1.15  thf('122', plain,
% 0.96/1.15      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('123', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('124', plain, ((v1_funct_1 @ sk_D)),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('125', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.96/1.15      inference('demod', [status(thm)], ['118', '121', '122', '123', '124'])).
% 0.96/1.15  thf('126', plain, ((v1_relat_1 @ sk_D)),
% 0.96/1.15      inference('demod', [status(thm)], ['7', '8'])).
% 0.96/1.15  thf('127', plain, ((v1_funct_1 @ sk_D)),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('128', plain,
% 0.96/1.15      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('129', plain,
% 0.96/1.15      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.96/1.15         (((k2_relset_1 @ X46 @ X47 @ X45) = (k2_relat_1 @ X45))
% 0.96/1.15          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47))))),
% 0.96/1.15      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.96/1.15  thf('130', plain,
% 0.96/1.15      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.96/1.15      inference('sup-', [status(thm)], ['128', '129'])).
% 0.96/1.15  thf('131', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('132', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.96/1.15      inference('sup+', [status(thm)], ['130', '131'])).
% 0.96/1.15  thf('133', plain, ((v1_funct_1 @ sk_C)),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('134', plain,
% 0.96/1.15      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('135', plain,
% 0.96/1.15      (![X3 : $i, X4 : $i]:
% 0.96/1.15         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.96/1.15          | (v1_relat_1 @ X3)
% 0.96/1.15          | ~ (v1_relat_1 @ X4))),
% 0.96/1.15      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.96/1.15  thf('136', plain,
% 0.96/1.15      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.96/1.15      inference('sup-', [status(thm)], ['134', '135'])).
% 0.96/1.15  thf('137', plain,
% 0.96/1.15      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.96/1.15      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.96/1.15  thf('138', plain, ((v1_relat_1 @ sk_C)),
% 0.96/1.15      inference('demod', [status(thm)], ['136', '137'])).
% 0.96/1.15  thf('139', plain,
% 0.96/1.15      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 0.96/1.15        | ~ (v2_funct_1 @ sk_D)
% 0.96/1.15        | ((sk_B) != (k1_relat_1 @ sk_D))
% 0.96/1.15        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 0.96/1.15      inference('demod', [status(thm)],
% 0.96/1.15                ['110', '125', '126', '127', '132', '133', '138'])).
% 0.96/1.15  thf('140', plain,
% 0.96/1.15      ((((sk_C) = (k2_funct_1 @ sk_D))
% 0.96/1.15        | ((sk_B) != (k1_relat_1 @ sk_D))
% 0.96/1.15        | ~ (v2_funct_1 @ sk_D))),
% 0.96/1.15      inference('simplify', [status(thm)], ['139'])).
% 0.96/1.15  thf('141', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.96/1.15      inference('demod', [status(thm)], ['104', '105'])).
% 0.96/1.15  thf(t48_funct_1, axiom,
% 0.96/1.15    (![A:$i]:
% 0.96/1.15     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.96/1.15       ( ![B:$i]:
% 0.96/1.15         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.96/1.15           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.96/1.15               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.96/1.15             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.96/1.15  thf('142', plain,
% 0.96/1.15      (![X33 : $i, X34 : $i]:
% 0.96/1.15         (~ (v1_relat_1 @ X33)
% 0.96/1.15          | ~ (v1_funct_1 @ X33)
% 0.96/1.15          | (v2_funct_1 @ X34)
% 0.96/1.15          | ((k2_relat_1 @ X33) != (k1_relat_1 @ X34))
% 0.96/1.15          | ~ (v2_funct_1 @ (k5_relat_1 @ X33 @ X34))
% 0.96/1.15          | ~ (v1_funct_1 @ X34)
% 0.96/1.15          | ~ (v1_relat_1 @ X34))),
% 0.96/1.15      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.96/1.15  thf('143', plain,
% 0.96/1.15      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.96/1.15        | ~ (v1_relat_1 @ sk_D)
% 0.96/1.15        | ~ (v1_funct_1 @ sk_D)
% 0.96/1.15        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.96/1.15        | (v2_funct_1 @ sk_D)
% 0.96/1.15        | ~ (v1_funct_1 @ sk_C)
% 0.96/1.15        | ~ (v1_relat_1 @ sk_C))),
% 0.96/1.15      inference('sup-', [status(thm)], ['141', '142'])).
% 0.96/1.15  thf(fc4_funct_1, axiom,
% 0.96/1.15    (![A:$i]:
% 0.96/1.15     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.96/1.15       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.96/1.15  thf('144', plain, (![X25 : $i]: (v2_funct_1 @ (k6_relat_1 @ X25))),
% 0.96/1.15      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.96/1.15  thf('145', plain, (![X66 : $i]: ((k6_partfun1 @ X66) = (k6_relat_1 @ X66))),
% 0.96/1.15      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.96/1.15  thf('146', plain, (![X25 : $i]: (v2_funct_1 @ (k6_partfun1 @ X25))),
% 0.96/1.15      inference('demod', [status(thm)], ['144', '145'])).
% 0.96/1.15  thf('147', plain, ((v1_relat_1 @ sk_D)),
% 0.96/1.15      inference('demod', [status(thm)], ['7', '8'])).
% 0.96/1.15  thf('148', plain, ((v1_funct_1 @ sk_D)),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('149', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.96/1.15      inference('sup+', [status(thm)], ['130', '131'])).
% 0.96/1.15  thf('150', plain, ((v1_funct_1 @ sk_C)),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('151', plain, ((v1_relat_1 @ sk_C)),
% 0.96/1.15      inference('demod', [status(thm)], ['136', '137'])).
% 0.96/1.15  thf('152', plain, ((((sk_B) != (k1_relat_1 @ sk_D)) | (v2_funct_1 @ sk_D))),
% 0.96/1.15      inference('demod', [status(thm)],
% 0.96/1.15                ['143', '146', '147', '148', '149', '150', '151'])).
% 0.96/1.15  thf('153', plain,
% 0.96/1.15      ((((sk_B) != (k1_relat_1 @ sk_D)) | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 0.96/1.15      inference('clc', [status(thm)], ['140', '152'])).
% 0.96/1.15  thf('154', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 0.96/1.15      inference('sup-', [status(thm)], ['0', '1'])).
% 0.96/1.15  thf('155', plain,
% 0.96/1.15      (![X5 : $i, X6 : $i]:
% 0.96/1.15         (~ (v4_relat_1 @ X5 @ X6)
% 0.96/1.15          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 0.96/1.15          | ~ (v1_relat_1 @ X5))),
% 0.96/1.15      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.96/1.15  thf('156', plain,
% 0.96/1.15      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B))),
% 0.96/1.15      inference('sup-', [status(thm)], ['154', '155'])).
% 0.96/1.15  thf('157', plain, ((v1_relat_1 @ sk_D)),
% 0.96/1.15      inference('demod', [status(thm)], ['7', '8'])).
% 0.96/1.15  thf('158', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 0.96/1.15      inference('demod', [status(thm)], ['156', '157'])).
% 0.96/1.15  thf('159', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.96/1.15      inference('sup+', [status(thm)], ['130', '131'])).
% 0.96/1.15  thf(t147_funct_1, axiom,
% 0.96/1.15    (![A:$i,B:$i]:
% 0.96/1.15     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.96/1.15       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.96/1.15         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.96/1.15  thf('160', plain,
% 0.96/1.15      (![X27 : $i, X28 : $i]:
% 0.96/1.15         (~ (r1_tarski @ X27 @ (k2_relat_1 @ X28))
% 0.96/1.15          | ((k9_relat_1 @ X28 @ (k10_relat_1 @ X28 @ X27)) = (X27))
% 0.96/1.15          | ~ (v1_funct_1 @ X28)
% 0.96/1.15          | ~ (v1_relat_1 @ X28))),
% 0.96/1.15      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.96/1.15  thf('161', plain,
% 0.96/1.15      (![X0 : $i]:
% 0.96/1.15         (~ (r1_tarski @ X0 @ sk_B)
% 0.96/1.15          | ~ (v1_relat_1 @ sk_C)
% 0.96/1.15          | ~ (v1_funct_1 @ sk_C)
% 0.96/1.15          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.96/1.15      inference('sup-', [status(thm)], ['159', '160'])).
% 0.96/1.15  thf('162', plain, ((v1_relat_1 @ sk_C)),
% 0.96/1.15      inference('demod', [status(thm)], ['136', '137'])).
% 0.96/1.15  thf('163', plain, ((v1_funct_1 @ sk_C)),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('164', plain,
% 0.96/1.15      (![X0 : $i]:
% 0.96/1.15         (~ (r1_tarski @ X0 @ sk_B)
% 0.96/1.15          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.96/1.15      inference('demod', [status(thm)], ['161', '162', '163'])).
% 0.96/1.15  thf('165', plain,
% 0.96/1.15      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 0.96/1.15         = (k1_relat_1 @ sk_D))),
% 0.96/1.15      inference('sup-', [status(thm)], ['158', '164'])).
% 0.96/1.15  thf('166', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.96/1.15      inference('demod', [status(thm)], ['104', '105'])).
% 0.96/1.15  thf('167', plain,
% 0.96/1.15      (![X13 : $i, X14 : $i]:
% 0.96/1.15         (~ (v1_relat_1 @ X13)
% 0.96/1.15          | ((k1_relat_1 @ (k5_relat_1 @ X14 @ X13))
% 0.96/1.15              = (k10_relat_1 @ X14 @ (k1_relat_1 @ X13)))
% 0.96/1.15          | ~ (v1_relat_1 @ X14))),
% 0.96/1.15      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.96/1.15  thf('168', plain,
% 0.96/1.15      ((((k1_relat_1 @ (k6_partfun1 @ sk_A))
% 0.96/1.15          = (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 0.96/1.15        | ~ (v1_relat_1 @ sk_C)
% 0.96/1.15        | ~ (v1_relat_1 @ sk_D))),
% 0.96/1.15      inference('sup+', [status(thm)], ['166', '167'])).
% 0.96/1.15  thf('169', plain,
% 0.96/1.15      (![X17 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X17)) = (X17))),
% 0.96/1.15      inference('demod', [status(thm)], ['39', '40'])).
% 0.96/1.15  thf('170', plain, ((v1_relat_1 @ sk_C)),
% 0.96/1.15      inference('demod', [status(thm)], ['136', '137'])).
% 0.96/1.15  thf('171', plain, ((v1_relat_1 @ sk_D)),
% 0.96/1.15      inference('demod', [status(thm)], ['7', '8'])).
% 0.96/1.15  thf('172', plain, (((sk_A) = (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))),
% 0.96/1.15      inference('demod', [status(thm)], ['168', '169', '170', '171'])).
% 0.96/1.15  thf('173', plain, (((k9_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.96/1.15      inference('demod', [status(thm)], ['165', '172'])).
% 0.96/1.15  thf('174', plain,
% 0.96/1.15      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('175', plain,
% 0.96/1.15      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.96/1.15         ((v4_relat_1 @ X42 @ X43)
% 0.96/1.15          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44))))),
% 0.96/1.15      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.96/1.15  thf('176', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.96/1.15      inference('sup-', [status(thm)], ['174', '175'])).
% 0.96/1.15  thf('177', plain,
% 0.96/1.15      (![X15 : $i, X16 : $i]:
% 0.96/1.15         (((X15) = (k7_relat_1 @ X15 @ X16))
% 0.96/1.15          | ~ (v4_relat_1 @ X15 @ X16)
% 0.96/1.15          | ~ (v1_relat_1 @ X15))),
% 0.96/1.15      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.96/1.15  thf('178', plain,
% 0.96/1.15      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.96/1.15      inference('sup-', [status(thm)], ['176', '177'])).
% 0.96/1.15  thf('179', plain, ((v1_relat_1 @ sk_C)),
% 0.96/1.15      inference('demod', [status(thm)], ['136', '137'])).
% 0.96/1.15  thf('180', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.96/1.15      inference('demod', [status(thm)], ['178', '179'])).
% 0.96/1.15  thf('181', plain,
% 0.96/1.15      (![X10 : $i, X11 : $i]:
% 0.96/1.15         (((k2_relat_1 @ (k7_relat_1 @ X10 @ X11)) = (k9_relat_1 @ X10 @ X11))
% 0.96/1.15          | ~ (v1_relat_1 @ X10))),
% 0.96/1.15      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.96/1.15  thf('182', plain,
% 0.96/1.15      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))
% 0.96/1.15        | ~ (v1_relat_1 @ sk_C))),
% 0.96/1.15      inference('sup+', [status(thm)], ['180', '181'])).
% 0.96/1.15  thf('183', plain, ((v1_relat_1 @ sk_C)),
% 0.96/1.15      inference('demod', [status(thm)], ['136', '137'])).
% 0.96/1.15  thf('184', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.96/1.15      inference('demod', [status(thm)], ['182', '183'])).
% 0.96/1.15  thf('185', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.96/1.15      inference('sup+', [status(thm)], ['130', '131'])).
% 0.96/1.15  thf('186', plain, (((sk_B) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.96/1.15      inference('demod', [status(thm)], ['184', '185'])).
% 0.96/1.15  thf('187', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.96/1.15      inference('sup+', [status(thm)], ['173', '186'])).
% 0.96/1.15  thf('188', plain, ((((sk_B) != (sk_B)) | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 0.96/1.15      inference('demod', [status(thm)], ['153', '187'])).
% 0.96/1.15  thf('189', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.96/1.15      inference('simplify', [status(thm)], ['188'])).
% 0.96/1.15  thf('190', plain, ((((k2_funct_1 @ sk_C) = (sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 0.96/1.15      inference('demod', [status(thm)], ['80', '189'])).
% 0.96/1.15  thf('191', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('192', plain, (~ (v2_funct_1 @ sk_D)),
% 0.96/1.15      inference('simplify_reflect-', [status(thm)], ['190', '191'])).
% 0.96/1.15  thf('193', plain, ((((sk_B) != (k1_relat_1 @ sk_D)) | (v2_funct_1 @ sk_D))),
% 0.96/1.15      inference('demod', [status(thm)],
% 0.96/1.15                ['143', '146', '147', '148', '149', '150', '151'])).
% 0.96/1.15  thf('194', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.96/1.15      inference('sup+', [status(thm)], ['173', '186'])).
% 0.96/1.15  thf('195', plain, ((((sk_B) != (sk_B)) | (v2_funct_1 @ sk_D))),
% 0.96/1.15      inference('demod', [status(thm)], ['193', '194'])).
% 0.96/1.15  thf('196', plain, ((v2_funct_1 @ sk_D)),
% 0.96/1.15      inference('simplify', [status(thm)], ['195'])).
% 0.96/1.15  thf('197', plain, ($false), inference('demod', [status(thm)], ['192', '196'])).
% 0.96/1.15  
% 0.96/1.15  % SZS output end Refutation
% 0.96/1.15  
% 0.96/1.16  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
