%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.93qV3bF2pk

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:12 EST 2020

% Result     : Theorem 2.74s
% Output     : Refutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :  378 (2362 expanded)
%              Number of leaves         :   54 ( 742 expanded)
%              Depth                    :   30
%              Number of atoms          : 3117 (40656 expanded)
%              Number of equality atoms :  195 (2625 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ( v4_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15
        = ( k7_relat_1 @ X15 @ X16 ) )
      | ~ ( v4_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

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

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v4_relat_1 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('10',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15
        = ( k7_relat_1 @ X15 @ X16 ) )
      | ~ ( v4_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('16',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('17',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['12','17'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('19',plain,(
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

thf('20',plain,(
    ! [X12: $i] :
      ( ( ( k10_relat_1 @ X12 @ ( k2_relat_1 @ X12 ) )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_D @ sk_B ) @ ( k9_relat_1 @ sk_D @ sk_B ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('24',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('25',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('26',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('27',plain,
    ( ( k10_relat_1 @ sk_D @ ( k9_relat_1 @ sk_D @ sk_B ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['22','23','24','25','26'])).

thf('28',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('29',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) )
        = ( k9_relat_1 @ X10 @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('30',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k9_relat_1 @ sk_D @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('32',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k9_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k10_relat_1 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('35',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X28 @ ( k2_relat_1 @ X29 ) )
      | ( ( k9_relat_1 @ X29 @ ( k10_relat_1 @ X29 @ X28 ) )
        = X28 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k9_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) )
      = ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('40',plain,
    ( ( k9_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( ( k10_relat_1 @ sk_D @ ( k2_relat_1 @ sk_D ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['40','47'])).

thf('49',plain,
    ( ( k10_relat_1 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('50',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('51',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('53',plain,
    ( ( v4_relat_1 @ ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) @ ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( v4_relat_1 @ ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) @ ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['7','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('56',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('57',plain,(
    v4_relat_1 @ ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) @ ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ( v4_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['6','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('60',plain,(
    v4_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15
        = ( k7_relat_1 @ X15 @ X16 ) )
      | ~ ( v4_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('64',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('65',plain,(
    ! [X22: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X22 ) ) @ X22 )
        = X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('66',plain,(
    ! [X58: $i] :
      ( ( k6_partfun1 @ X58 )
      = ( k6_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('67',plain,(
    ! [X22: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X22 ) ) @ X22 )
        = X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X22: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X22 ) ) @ X22 )
        = X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('69',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) )
        = ( k10_relat_1 @ X14 @ ( k1_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X1 @ X0 )
        = ( k7_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = ( k7_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) @ ( k10_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('73',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('74',plain,(
    ! [X58: $i] :
      ( ( k6_partfun1 @ X58 )
      = ( k6_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('75',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X26 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('76',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('77',plain,(
    ! [X58: $i] :
      ( ( k6_partfun1 @ X58 )
      = ( k6_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('78',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X21 ) )
      = X21 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X12: $i] :
      ( ( ( k10_relat_1 @ X12 @ ( k2_relat_1 @ X12 ) )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('82',plain,(
    ! [X58: $i] :
      ( ( k6_partfun1 @ X58 )
      = ( k6_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('83',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X20 ) )
      = X20 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X26 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['80','83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = ( k7_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['72','75','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = ( k7_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = ( k7_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = ( k7_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = ( k7_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D )
      = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['64','92'])).

thf('94',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('95',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('96',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf('98',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('99',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('101',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('103',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k2_relset_1 @ X38 @ X39 @ X37 )
        = ( k2_relat_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('104',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X28 @ ( k2_relat_1 @ X29 ) )
      | ( ( k9_relat_1 @ X29 @ ( k10_relat_1 @ X29 @ X28 ) )
        = X28 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('111',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('113',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['108','113','114'])).

thf('116',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['101','115'])).

thf('117',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) )
        = ( k10_relat_1 @ X14 @ ( k1_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('118',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
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

thf('120',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X45 @ X46 @ X48 @ X49 @ X44 @ X47 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X49 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['118','123'])).

thf('125',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
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

thf('128',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X54 ) ) )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X57 ) ) )
      | ( ( k1_partfun1 @ X53 @ X54 @ X56 @ X57 @ X52 @ X55 )
        = ( k5_relat_1 @ X52 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['126','131'])).

thf('133',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['124','125','134'])).

thf('136',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v4_relat_1 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('137',plain,(
    v4_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ sk_A ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('139',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['124','125','134'])).

thf('141',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('142',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('144',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) @ sk_A ),
    inference(demod,[status(thm)],['139','144'])).

thf('146',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['117','145'])).

thf('147',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['111','112'])).

thf('148',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('149',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) @ sk_A ),
    inference(demod,[status(thm)],['146','147','148'])).

thf('150',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X20 ) )
      = X20 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('151',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ( v4_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( v4_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X26 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( v4_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,(
    v4_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ) @ sk_A ),
    inference('sup-',[status(thm)],['149','154'])).

thf('156',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15
        = ( k7_relat_1 @ X15 @ X16 ) )
      | ~ ( v4_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('157',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ) )
    | ( ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) )
      = ( k7_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X26 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('159',plain,
    ( ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) )
    = ( k7_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) )
        = ( k9_relat_1 @ X10 @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('161',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ) )
      = ( k9_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ) ) ),
    inference('sup+',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X21 ) )
      = X21 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('163',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) )
        = ( k10_relat_1 @ X14 @ ( k1_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('164',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) @ sk_A ),
    inference(demod,[status(thm)],['139','144'])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( v4_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('166',plain,(
    v4_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) @ sk_A ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15
        = ( k7_relat_1 @ X15 @ X16 ) )
      | ~ ( v4_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('168',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) )
    | ( ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
      = ( k7_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X26 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('170',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
    = ( k7_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) )
        = ( k9_relat_1 @ X10 @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('172',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) )
      = ( k9_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) ) ),
    inference('sup+',[status(thm)],['170','171'])).

thf('173',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X21 ) )
      = X21 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('174',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X26 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('175',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    = ( k9_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['172','173','174'])).

thf('176',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
      = ( k9_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['163','175'])).

thf('177',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['111','112'])).

thf('178',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('179',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    = ( k9_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['176','177','178'])).

thf('180',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X26 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('181',plain,
    ( ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) )
    = ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['161','162','179','180'])).

thf('182',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('184',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['182','183'])).

thf('185',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['124','125','134'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('186',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( X40 = X43 )
      | ~ ( r2_relset_1 @ X41 @ X42 @ X40 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('187',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['184','187'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('189',plain,(
    ! [X51: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X51 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('190',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X20 ) )
      = X20 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('192',plain,
    ( ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) )
    = sk_A ),
    inference(demod,[status(thm)],['181','190','191'])).

thf('193',plain,
    ( ( k9_relat_1 @ sk_C @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['116','192'])).

thf('194',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v4_relat_1 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('196',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15
        = ( k7_relat_1 @ X15 @ X16 ) )
      | ~ ( v4_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('198',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['111','112'])).

thf('200',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) )
        = ( k9_relat_1 @ X10 @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('202',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['200','201'])).

thf('203',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['111','112'])).

thf('204',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['202','203'])).

thf('205',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['104','105'])).

thf('206',plain,
    ( sk_B
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['204','205'])).

thf('207',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['193','206'])).

thf('208',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['96','207'])).

thf('209',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['188','189'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('210',plain,(
    ! [X33: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X33 ) @ X33 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('211',plain,(
    ! [X58: $i] :
      ( ( k6_partfun1 @ X58 )
      = ( k6_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('212',plain,(
    ! [X33: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X33 ) @ X33 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(demod,[status(thm)],['210','211'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('213',plain,(
    ! [X32: $i] :
      ( ~ ( v2_funct_1 @ X32 )
      | ( ( k2_relat_1 @ X32 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('214',plain,(
    ! [X25: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('215',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['104','105'])).

thf('216',plain,(
    ! [X25: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('217',plain,(
    ! [X32: $i] :
      ( ~ ( v2_funct_1 @ X32 )
      | ( ( k2_relat_1 @ X32 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('218',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('219',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['217','218'])).

thf('220',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['216','219'])).

thf('221',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['220'])).

thf('222',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['215','221'])).

thf('223',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['111','112'])).

thf('224',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['222','223','224','225'])).

thf('227',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('228',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('229',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['214','228'])).

thf('230',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['111','112'])).

thf('231',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['229','230','231'])).

thf('233',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('234',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['232','233'])).

thf('235',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['213','234'])).

thf('236',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['104','105'])).

thf('237',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('238',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['111','112'])).

thf('239',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['235','236','237','238','239','240'])).

thf('242',plain,(
    ! [X22: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X22 ) ) @ X22 )
        = X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('243',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X18 @ X17 ) @ X19 )
        = ( k5_relat_1 @ X18 @ ( k5_relat_1 @ X17 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('244',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['242','243'])).

thf('245',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X26 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('246',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['244','245'])).

thf('247',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['246'])).

thf('248',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['241','247'])).

thf('249',plain,(
    ! [X25: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('250',plain,(
    ! [X25: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('251',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['235','236','237','238','239','240'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('252',plain,(
    ! [X59: $i] :
      ( ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X59 ) @ ( k2_relat_1 @ X59 ) ) ) )
      | ~ ( v1_funct_1 @ X59 )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('253',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['251','252'])).

thf('254',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['250','253'])).

thf('255',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['111','112'])).

thf('256',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference(demod,[status(thm)],['254','255','256'])).

thf('258',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['249','257'])).

thf('259',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['111','112'])).

thf('260',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['258','259','260'])).

thf('262',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('263',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['261','262'])).

thf('264',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('265',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['263','264'])).

thf('266',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['248','265'])).

thf('267',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['212','266'])).

thf('268',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['104','105'])).

thf('269',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X20 ) )
      = X20 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('270',plain,(
    ! [X22: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X22 ) ) @ X22 )
        = X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('271',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['269','270'])).

thf('272',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X26 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('273',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['271','272'])).

thf('274',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['111','112'])).

thf('275',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('277',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['111','112'])).

thf('278',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['267','268','273','274','275','276','277'])).

thf('279',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X18 @ X17 ) @ X19 )
        = ( k5_relat_1 @ X18 @ ( k5_relat_1 @ X17 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('280',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['278','279'])).

thf('281',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['263','264'])).

thf('282',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['111','112'])).

thf('283',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['280','281','282'])).

thf('284',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['209','283'])).

thf('285',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['194','195'])).

thf('286',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('287',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['285','286'])).

thf('288',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['111','112'])).

thf('289',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['287','288'])).

thf('290',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X21 ) )
      = X21 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('291',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X23 ) @ X24 )
      | ( ( k5_relat_1 @ X23 @ ( k6_relat_1 @ X24 ) )
        = X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('292',plain,(
    ! [X58: $i] :
      ( ( k6_partfun1 @ X58 )
      = ( k6_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('293',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X23 ) @ X24 )
      | ( ( k5_relat_1 @ X23 @ ( k6_partfun1 @ X24 ) )
        = X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(demod,[status(thm)],['291','292'])).

thf('294',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X1 ) )
        = ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['290','293'])).

thf('295',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X26 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('296',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X1 ) )
        = ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['294','295'])).

thf('297',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ ( k6_partfun1 @ sk_A ) )
    = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['289','296'])).

thf('298',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['263','264'])).

thf('299',plain,(
    ! [X32: $i] :
      ( ~ ( v2_funct_1 @ X32 )
      | ( ( k1_relat_1 @ X32 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('300',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('301',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X23 ) @ X24 )
      | ( ( k5_relat_1 @ X23 @ ( k6_partfun1 @ X24 ) )
        = X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(demod,[status(thm)],['291','292'])).

thf('302',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['300','301'])).

thf('303',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['299','302'])).

thf('304',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['298','303'])).

thf('305',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('306',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('307',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['111','112'])).

thf('308',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['304','305','306','307'])).

thf('309',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X18 @ X17 ) @ X19 )
        = ( k5_relat_1 @ X18 @ ( k5_relat_1 @ X17 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('310',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup+',[status(thm)],['308','309'])).

thf('311',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['263','264'])).

thf('312',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X26 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('313',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['310','311','312'])).

thf('314',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['297','313'])).

thf('315',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['304','305','306','307'])).

thf('316',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X26 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('317',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['314','315','316'])).

thf('318',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('319',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['284','317','318'])).

thf('320',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['208','319'])).

thf('321',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('322',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['320','321'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.93qV3bF2pk
% 0.15/0.36  % Computer   : n025.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 11:13:51 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 2.74/2.92  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.74/2.92  % Solved by: fo/fo7.sh
% 2.74/2.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.74/2.92  % done 2555 iterations in 2.443s
% 2.74/2.92  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.74/2.92  % SZS output start Refutation
% 2.74/2.92  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.74/2.92  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.74/2.92  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.74/2.92  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.74/2.92  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.74/2.92  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.74/2.92  thf(sk_A_type, type, sk_A: $i).
% 2.74/2.92  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.74/2.92  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.74/2.92  thf(sk_D_type, type, sk_D: $i).
% 2.74/2.92  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.74/2.92  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.74/2.92  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.74/2.92  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.74/2.92  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.74/2.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.74/2.92  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.74/2.92  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.74/2.92  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.74/2.92  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.74/2.92  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 2.74/2.92  thf(sk_B_type, type, sk_B: $i).
% 2.74/2.92  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.74/2.92  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.74/2.92  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.74/2.92  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.74/2.92  thf(sk_C_type, type, sk_C: $i).
% 2.74/2.92  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 2.74/2.92  thf(d10_xboole_0, axiom,
% 2.74/2.92    (![A:$i,B:$i]:
% 2.74/2.92     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.74/2.92  thf('0', plain,
% 2.74/2.92      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 2.74/2.92      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.74/2.92  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.74/2.92      inference('simplify', [status(thm)], ['0'])).
% 2.74/2.92  thf(d18_relat_1, axiom,
% 2.74/2.92    (![A:$i,B:$i]:
% 2.74/2.92     ( ( v1_relat_1 @ B ) =>
% 2.74/2.92       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 2.74/2.92  thf('2', plain,
% 2.74/2.92      (![X5 : $i, X6 : $i]:
% 2.74/2.92         (~ (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 2.74/2.92          | (v4_relat_1 @ X5 @ X6)
% 2.74/2.92          | ~ (v1_relat_1 @ X5))),
% 2.74/2.92      inference('cnf', [status(esa)], [d18_relat_1])).
% 2.74/2.92  thf('3', plain,
% 2.74/2.92      (![X0 : $i]:
% 2.74/2.92         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 2.74/2.92      inference('sup-', [status(thm)], ['1', '2'])).
% 2.74/2.92  thf(t209_relat_1, axiom,
% 2.74/2.92    (![A:$i,B:$i]:
% 2.74/2.92     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 2.74/2.92       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 2.74/2.92  thf('4', plain,
% 2.74/2.92      (![X15 : $i, X16 : $i]:
% 2.74/2.92         (((X15) = (k7_relat_1 @ X15 @ X16))
% 2.74/2.92          | ~ (v4_relat_1 @ X15 @ X16)
% 2.74/2.92          | ~ (v1_relat_1 @ X15))),
% 2.74/2.92      inference('cnf', [status(esa)], [t209_relat_1])).
% 2.74/2.92  thf('5', plain,
% 2.74/2.92      (![X0 : $i]:
% 2.74/2.92         (~ (v1_relat_1 @ X0)
% 2.74/2.92          | ~ (v1_relat_1 @ X0)
% 2.74/2.92          | ((X0) = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 2.74/2.92      inference('sup-', [status(thm)], ['3', '4'])).
% 2.74/2.92  thf('6', plain,
% 2.74/2.92      (![X0 : $i]:
% 2.74/2.92         (((X0) = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))) | ~ (v1_relat_1 @ X0))),
% 2.74/2.92      inference('simplify', [status(thm)], ['5'])).
% 2.74/2.92  thf('7', plain,
% 2.74/2.92      (![X0 : $i]:
% 2.74/2.92         (((X0) = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))) | ~ (v1_relat_1 @ X0))),
% 2.74/2.92      inference('simplify', [status(thm)], ['5'])).
% 2.74/2.92  thf(t36_funct_2, conjecture,
% 2.74/2.92    (![A:$i,B:$i,C:$i]:
% 2.74/2.92     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.74/2.92         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.74/2.92       ( ![D:$i]:
% 2.74/2.92         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.74/2.92             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.74/2.92           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.74/2.92               ( r2_relset_1 @
% 2.74/2.92                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.74/2.92                 ( k6_partfun1 @ A ) ) & 
% 2.74/2.92               ( v2_funct_1 @ C ) ) =>
% 2.74/2.92             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.74/2.92               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 2.74/2.92  thf(zf_stmt_0, negated_conjecture,
% 2.74/2.92    (~( ![A:$i,B:$i,C:$i]:
% 2.74/2.92        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.74/2.92            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.74/2.92          ( ![D:$i]:
% 2.74/2.92            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.74/2.92                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.74/2.92              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.74/2.92                  ( r2_relset_1 @
% 2.74/2.92                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.74/2.92                    ( k6_partfun1 @ A ) ) & 
% 2.74/2.92                  ( v2_funct_1 @ C ) ) =>
% 2.74/2.92                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.74/2.92                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 2.74/2.92    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 2.74/2.92  thf('8', plain,
% 2.74/2.92      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.74/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.92  thf(cc2_relset_1, axiom,
% 2.74/2.92    (![A:$i,B:$i,C:$i]:
% 2.74/2.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.74/2.92       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.74/2.92  thf('9', plain,
% 2.74/2.92      (![X34 : $i, X35 : $i, X36 : $i]:
% 2.74/2.92         ((v4_relat_1 @ X34 @ X35)
% 2.74/2.92          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 2.74/2.92      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.74/2.92  thf('10', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 2.74/2.92      inference('sup-', [status(thm)], ['8', '9'])).
% 2.74/2.92  thf('11', plain,
% 2.74/2.92      (![X15 : $i, X16 : $i]:
% 2.74/2.92         (((X15) = (k7_relat_1 @ X15 @ X16))
% 2.74/2.92          | ~ (v4_relat_1 @ X15 @ X16)
% 2.74/2.92          | ~ (v1_relat_1 @ X15))),
% 2.74/2.92      inference('cnf', [status(esa)], [t209_relat_1])).
% 2.74/2.92  thf('12', plain,
% 2.74/2.92      ((~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ sk_B)))),
% 2.74/2.92      inference('sup-', [status(thm)], ['10', '11'])).
% 2.74/2.92  thf('13', plain,
% 2.74/2.92      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.74/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.92  thf(cc2_relat_1, axiom,
% 2.74/2.92    (![A:$i]:
% 2.74/2.92     ( ( v1_relat_1 @ A ) =>
% 2.74/2.92       ( ![B:$i]:
% 2.74/2.92         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.74/2.92  thf('14', plain,
% 2.74/2.92      (![X3 : $i, X4 : $i]:
% 2.74/2.92         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 2.74/2.92          | (v1_relat_1 @ X3)
% 2.74/2.92          | ~ (v1_relat_1 @ X4))),
% 2.74/2.92      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.74/2.92  thf('15', plain,
% 2.74/2.92      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 2.74/2.92      inference('sup-', [status(thm)], ['13', '14'])).
% 2.74/2.92  thf(fc6_relat_1, axiom,
% 2.74/2.92    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.74/2.92  thf('16', plain,
% 2.74/2.92      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 2.74/2.92      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.74/2.92  thf('17', plain, ((v1_relat_1 @ sk_D)),
% 2.74/2.92      inference('demod', [status(thm)], ['15', '16'])).
% 2.74/2.92  thf('18', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 2.74/2.92      inference('demod', [status(thm)], ['12', '17'])).
% 2.74/2.92  thf(t148_relat_1, axiom,
% 2.74/2.92    (![A:$i,B:$i]:
% 2.74/2.92     ( ( v1_relat_1 @ B ) =>
% 2.74/2.92       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 2.74/2.92  thf('19', plain,
% 2.74/2.92      (![X10 : $i, X11 : $i]:
% 2.74/2.92         (((k2_relat_1 @ (k7_relat_1 @ X10 @ X11)) = (k9_relat_1 @ X10 @ X11))
% 2.74/2.92          | ~ (v1_relat_1 @ X10))),
% 2.74/2.92      inference('cnf', [status(esa)], [t148_relat_1])).
% 2.74/2.92  thf(t169_relat_1, axiom,
% 2.74/2.92    (![A:$i]:
% 2.74/2.92     ( ( v1_relat_1 @ A ) =>
% 2.74/2.92       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 2.74/2.92  thf('20', plain,
% 2.74/2.92      (![X12 : $i]:
% 2.74/2.92         (((k10_relat_1 @ X12 @ (k2_relat_1 @ X12)) = (k1_relat_1 @ X12))
% 2.74/2.92          | ~ (v1_relat_1 @ X12))),
% 2.74/2.92      inference('cnf', [status(esa)], [t169_relat_1])).
% 2.74/2.92  thf('21', plain,
% 2.74/2.92      (![X0 : $i, X1 : $i]:
% 2.74/2.92         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 2.74/2.92            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 2.74/2.92          | ~ (v1_relat_1 @ X1)
% 2.74/2.92          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 2.74/2.92      inference('sup+', [status(thm)], ['19', '20'])).
% 2.74/2.92  thf('22', plain,
% 2.74/2.92      ((~ (v1_relat_1 @ sk_D)
% 2.74/2.92        | ~ (v1_relat_1 @ sk_D)
% 2.74/2.92        | ((k10_relat_1 @ (k7_relat_1 @ sk_D @ sk_B) @ 
% 2.74/2.92            (k9_relat_1 @ sk_D @ sk_B))
% 2.74/2.92            = (k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_B))))),
% 2.74/2.92      inference('sup-', [status(thm)], ['18', '21'])).
% 2.74/2.92  thf('23', plain, ((v1_relat_1 @ sk_D)),
% 2.74/2.92      inference('demod', [status(thm)], ['15', '16'])).
% 2.74/2.92  thf('24', plain, ((v1_relat_1 @ sk_D)),
% 2.74/2.92      inference('demod', [status(thm)], ['15', '16'])).
% 2.74/2.92  thf('25', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 2.74/2.92      inference('demod', [status(thm)], ['12', '17'])).
% 2.74/2.92  thf('26', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 2.74/2.92      inference('demod', [status(thm)], ['12', '17'])).
% 2.74/2.92  thf('27', plain,
% 2.74/2.92      (((k10_relat_1 @ sk_D @ (k9_relat_1 @ sk_D @ sk_B)) = (k1_relat_1 @ sk_D))),
% 2.74/2.92      inference('demod', [status(thm)], ['22', '23', '24', '25', '26'])).
% 2.74/2.92  thf('28', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 2.74/2.92      inference('demod', [status(thm)], ['12', '17'])).
% 2.74/2.92  thf('29', plain,
% 2.74/2.92      (![X10 : $i, X11 : $i]:
% 2.74/2.92         (((k2_relat_1 @ (k7_relat_1 @ X10 @ X11)) = (k9_relat_1 @ X10 @ X11))
% 2.74/2.92          | ~ (v1_relat_1 @ X10))),
% 2.74/2.92      inference('cnf', [status(esa)], [t148_relat_1])).
% 2.74/2.92  thf('30', plain,
% 2.74/2.92      ((((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ sk_B))
% 2.74/2.92        | ~ (v1_relat_1 @ sk_D))),
% 2.74/2.92      inference('sup+', [status(thm)], ['28', '29'])).
% 2.74/2.92  thf('31', plain, ((v1_relat_1 @ sk_D)),
% 2.74/2.92      inference('demod', [status(thm)], ['15', '16'])).
% 2.74/2.92  thf('32', plain, (((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ sk_B))),
% 2.74/2.92      inference('demod', [status(thm)], ['30', '31'])).
% 2.74/2.92  thf('33', plain,
% 2.74/2.92      (((k10_relat_1 @ sk_D @ (k2_relat_1 @ sk_D)) = (k1_relat_1 @ sk_D))),
% 2.74/2.92      inference('demod', [status(thm)], ['27', '32'])).
% 2.74/2.92  thf('34', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.74/2.92      inference('simplify', [status(thm)], ['0'])).
% 2.74/2.92  thf(t147_funct_1, axiom,
% 2.74/2.92    (![A:$i,B:$i]:
% 2.74/2.92     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.74/2.92       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 2.74/2.92         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 2.74/2.92  thf('35', plain,
% 2.74/2.92      (![X28 : $i, X29 : $i]:
% 2.74/2.92         (~ (r1_tarski @ X28 @ (k2_relat_1 @ X29))
% 2.74/2.92          | ((k9_relat_1 @ X29 @ (k10_relat_1 @ X29 @ X28)) = (X28))
% 2.74/2.92          | ~ (v1_funct_1 @ X29)
% 2.74/2.92          | ~ (v1_relat_1 @ X29))),
% 2.74/2.92      inference('cnf', [status(esa)], [t147_funct_1])).
% 2.74/2.92  thf('36', plain,
% 2.74/2.92      (![X0 : $i]:
% 2.74/2.92         (~ (v1_relat_1 @ X0)
% 2.74/2.92          | ~ (v1_funct_1 @ X0)
% 2.74/2.92          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 2.74/2.92              = (k2_relat_1 @ X0)))),
% 2.74/2.92      inference('sup-', [status(thm)], ['34', '35'])).
% 2.74/2.92  thf('37', plain,
% 2.74/2.92      ((((k9_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)) = (k2_relat_1 @ sk_D))
% 2.74/2.92        | ~ (v1_funct_1 @ sk_D)
% 2.74/2.92        | ~ (v1_relat_1 @ sk_D))),
% 2.74/2.92      inference('sup+', [status(thm)], ['33', '36'])).
% 2.74/2.92  thf('38', plain, ((v1_funct_1 @ sk_D)),
% 2.74/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.92  thf('39', plain, ((v1_relat_1 @ sk_D)),
% 2.74/2.92      inference('demod', [status(thm)], ['15', '16'])).
% 2.74/2.92  thf('40', plain,
% 2.74/2.92      (((k9_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)) = (k2_relat_1 @ sk_D))),
% 2.74/2.92      inference('demod', [status(thm)], ['37', '38', '39'])).
% 2.74/2.92  thf('41', plain,
% 2.74/2.92      (![X0 : $i]:
% 2.74/2.92         (((X0) = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))) | ~ (v1_relat_1 @ X0))),
% 2.74/2.92      inference('simplify', [status(thm)], ['5'])).
% 2.74/2.92  thf('42', plain,
% 2.74/2.92      (![X0 : $i]:
% 2.74/2.92         (((X0) = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))) | ~ (v1_relat_1 @ X0))),
% 2.74/2.92      inference('simplify', [status(thm)], ['5'])).
% 2.74/2.92  thf('43', plain,
% 2.74/2.92      (![X0 : $i, X1 : $i]:
% 2.74/2.92         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 2.74/2.92            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 2.74/2.92          | ~ (v1_relat_1 @ X1)
% 2.74/2.92          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 2.74/2.92      inference('sup+', [status(thm)], ['19', '20'])).
% 2.74/2.92  thf('44', plain,
% 2.74/2.92      (![X0 : $i]:
% 2.74/2.92         (~ (v1_relat_1 @ X0)
% 2.74/2.92          | ~ (v1_relat_1 @ X0)
% 2.74/2.92          | ~ (v1_relat_1 @ X0)
% 2.74/2.92          | ((k10_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ 
% 2.74/2.92              (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 2.74/2.92              = (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)))))),
% 2.74/2.92      inference('sup-', [status(thm)], ['42', '43'])).
% 2.74/2.92  thf('45', plain,
% 2.74/2.92      (![X0 : $i]:
% 2.74/2.92         (((k10_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ 
% 2.74/2.92            (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 2.74/2.92            = (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 2.74/2.92          | ~ (v1_relat_1 @ X0))),
% 2.74/2.92      inference('simplify', [status(thm)], ['44'])).
% 2.74/2.92  thf('46', plain,
% 2.74/2.92      (![X0 : $i]:
% 2.74/2.92         (((k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 2.74/2.92            = (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 2.74/2.92          | ~ (v1_relat_1 @ X0)
% 2.74/2.92          | ~ (v1_relat_1 @ X0))),
% 2.74/2.92      inference('sup+', [status(thm)], ['41', '45'])).
% 2.74/2.92  thf('47', plain,
% 2.74/2.92      (![X0 : $i]:
% 2.74/2.92         (~ (v1_relat_1 @ X0)
% 2.74/2.92          | ((k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 2.74/2.92              = (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)))))),
% 2.74/2.92      inference('simplify', [status(thm)], ['46'])).
% 2.74/2.92  thf('48', plain,
% 2.74/2.92      ((((k10_relat_1 @ sk_D @ (k2_relat_1 @ sk_D))
% 2.74/2.92          = (k1_relat_1 @ (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D))))
% 2.74/2.92        | ~ (v1_relat_1 @ sk_D))),
% 2.74/2.92      inference('sup+', [status(thm)], ['40', '47'])).
% 2.74/2.92  thf('49', plain,
% 2.74/2.92      (((k10_relat_1 @ sk_D @ (k2_relat_1 @ sk_D)) = (k1_relat_1 @ sk_D))),
% 2.74/2.92      inference('demod', [status(thm)], ['27', '32'])).
% 2.74/2.92  thf('50', plain, ((v1_relat_1 @ sk_D)),
% 2.74/2.92      inference('demod', [status(thm)], ['15', '16'])).
% 2.74/2.92  thf('51', plain,
% 2.74/2.92      (((k1_relat_1 @ sk_D)
% 2.74/2.92         = (k1_relat_1 @ (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D))))),
% 2.74/2.92      inference('demod', [status(thm)], ['48', '49', '50'])).
% 2.74/2.92  thf('52', plain,
% 2.74/2.92      (![X0 : $i]:
% 2.74/2.92         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 2.74/2.92      inference('sup-', [status(thm)], ['1', '2'])).
% 2.74/2.92  thf('53', plain,
% 2.74/2.92      (((v4_relat_1 @ (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)) @ 
% 2.74/2.92         (k1_relat_1 @ sk_D))
% 2.74/2.92        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D))))),
% 2.74/2.92      inference('sup+', [status(thm)], ['51', '52'])).
% 2.74/2.92  thf('54', plain,
% 2.74/2.92      ((~ (v1_relat_1 @ sk_D)
% 2.74/2.92        | ~ (v1_relat_1 @ sk_D)
% 2.74/2.92        | (v4_relat_1 @ (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)) @ 
% 2.74/2.92           (k1_relat_1 @ sk_D)))),
% 2.74/2.92      inference('sup-', [status(thm)], ['7', '53'])).
% 2.74/2.92  thf('55', plain, ((v1_relat_1 @ sk_D)),
% 2.74/2.92      inference('demod', [status(thm)], ['15', '16'])).
% 2.74/2.92  thf('56', plain, ((v1_relat_1 @ sk_D)),
% 2.74/2.92      inference('demod', [status(thm)], ['15', '16'])).
% 2.74/2.92  thf('57', plain,
% 2.74/2.92      ((v4_relat_1 @ (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)) @ 
% 2.74/2.92        (k1_relat_1 @ sk_D))),
% 2.74/2.92      inference('demod', [status(thm)], ['54', '55', '56'])).
% 2.74/2.92  thf('58', plain,
% 2.74/2.92      (((v4_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)) | ~ (v1_relat_1 @ sk_D))),
% 2.74/2.92      inference('sup+', [status(thm)], ['6', '57'])).
% 2.74/2.92  thf('59', plain, ((v1_relat_1 @ sk_D)),
% 2.74/2.92      inference('demod', [status(thm)], ['15', '16'])).
% 2.74/2.92  thf('60', plain, ((v4_relat_1 @ sk_D @ (k1_relat_1 @ sk_D))),
% 2.74/2.92      inference('demod', [status(thm)], ['58', '59'])).
% 2.74/2.92  thf('61', plain,
% 2.74/2.92      (![X15 : $i, X16 : $i]:
% 2.74/2.92         (((X15) = (k7_relat_1 @ X15 @ X16))
% 2.74/2.92          | ~ (v4_relat_1 @ X15 @ X16)
% 2.74/2.92          | ~ (v1_relat_1 @ X15))),
% 2.74/2.92      inference('cnf', [status(esa)], [t209_relat_1])).
% 2.74/2.92  thf('62', plain,
% 2.74/2.92      ((~ (v1_relat_1 @ sk_D)
% 2.74/2.92        | ((sk_D) = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D))))),
% 2.74/2.92      inference('sup-', [status(thm)], ['60', '61'])).
% 2.74/2.92  thf('63', plain, ((v1_relat_1 @ sk_D)),
% 2.74/2.92      inference('demod', [status(thm)], ['15', '16'])).
% 2.74/2.92  thf('64', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))),
% 2.74/2.92      inference('demod', [status(thm)], ['62', '63'])).
% 2.74/2.92  thf(t78_relat_1, axiom,
% 2.74/2.92    (![A:$i]:
% 2.74/2.92     ( ( v1_relat_1 @ A ) =>
% 2.74/2.92       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 2.74/2.92  thf('65', plain,
% 2.74/2.92      (![X22 : $i]:
% 2.74/2.92         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X22)) @ X22) = (X22))
% 2.74/2.92          | ~ (v1_relat_1 @ X22))),
% 2.74/2.92      inference('cnf', [status(esa)], [t78_relat_1])).
% 2.74/2.92  thf(redefinition_k6_partfun1, axiom,
% 2.74/2.92    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.74/2.92  thf('66', plain, (![X58 : $i]: ((k6_partfun1 @ X58) = (k6_relat_1 @ X58))),
% 2.74/2.92      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.74/2.92  thf('67', plain,
% 2.74/2.92      (![X22 : $i]:
% 2.74/2.92         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X22)) @ X22) = (X22))
% 2.74/2.92          | ~ (v1_relat_1 @ X22))),
% 2.74/2.92      inference('demod', [status(thm)], ['65', '66'])).
% 2.74/2.92  thf('68', plain,
% 2.74/2.92      (![X22 : $i]:
% 2.74/2.92         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X22)) @ X22) = (X22))
% 2.74/2.92          | ~ (v1_relat_1 @ X22))),
% 2.74/2.92      inference('demod', [status(thm)], ['65', '66'])).
% 2.74/2.92  thf(t182_relat_1, axiom,
% 2.74/2.92    (![A:$i]:
% 2.74/2.92     ( ( v1_relat_1 @ A ) =>
% 2.74/2.92       ( ![B:$i]:
% 2.74/2.92         ( ( v1_relat_1 @ B ) =>
% 2.74/2.92           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 2.74/2.92             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 2.74/2.92  thf('69', plain,
% 2.74/2.92      (![X13 : $i, X14 : $i]:
% 2.74/2.92         (~ (v1_relat_1 @ X13)
% 2.74/2.92          | ((k1_relat_1 @ (k5_relat_1 @ X14 @ X13))
% 2.74/2.92              = (k10_relat_1 @ X14 @ (k1_relat_1 @ X13)))
% 2.74/2.92          | ~ (v1_relat_1 @ X14))),
% 2.74/2.92      inference('cnf', [status(esa)], [t182_relat_1])).
% 2.74/2.92  thf('70', plain,
% 2.74/2.92      (![X0 : $i]:
% 2.74/2.92         (((X0) = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))) | ~ (v1_relat_1 @ X0))),
% 2.74/2.92      inference('simplify', [status(thm)], ['5'])).
% 2.74/2.92  thf('71', plain,
% 2.74/2.92      (![X0 : $i, X1 : $i]:
% 2.74/2.92         (((k5_relat_1 @ X1 @ X0)
% 2.74/2.92            = (k7_relat_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 2.74/2.92               (k10_relat_1 @ X1 @ (k1_relat_1 @ X0))))
% 2.74/2.92          | ~ (v1_relat_1 @ X1)
% 2.74/2.92          | ~ (v1_relat_1 @ X0)
% 2.74/2.92          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 2.74/2.92      inference('sup+', [status(thm)], ['69', '70'])).
% 2.74/2.92  thf('72', plain,
% 2.74/2.92      (![X0 : $i]:
% 2.74/2.92         (~ (v1_relat_1 @ X0)
% 2.74/2.92          | ~ (v1_relat_1 @ X0)
% 2.74/2.92          | ~ (v1_relat_1 @ X0)
% 2.74/2.92          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 2.74/2.92          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0)
% 2.74/2.92              = (k7_relat_1 @ 
% 2.74/2.92                 (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0) @ 
% 2.74/2.92                 (k10_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 2.74/2.92                  (k1_relat_1 @ X0)))))),
% 2.74/2.92      inference('sup-', [status(thm)], ['68', '71'])).
% 2.74/2.92  thf(fc4_funct_1, axiom,
% 2.74/2.92    (![A:$i]:
% 2.74/2.92     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 2.74/2.92       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 2.74/2.92  thf('73', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 2.74/2.92      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.74/2.92  thf('74', plain, (![X58 : $i]: ((k6_partfun1 @ X58) = (k6_relat_1 @ X58))),
% 2.74/2.92      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.74/2.92  thf('75', plain, (![X26 : $i]: (v1_relat_1 @ (k6_partfun1 @ X26))),
% 2.74/2.92      inference('demod', [status(thm)], ['73', '74'])).
% 2.74/2.92  thf(t71_relat_1, axiom,
% 2.74/2.92    (![A:$i]:
% 2.74/2.92     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 2.74/2.92       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 2.74/2.92  thf('76', plain, (![X21 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 2.74/2.92      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.74/2.92  thf('77', plain, (![X58 : $i]: ((k6_partfun1 @ X58) = (k6_relat_1 @ X58))),
% 2.74/2.92      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.74/2.92  thf('78', plain, (![X21 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X21)) = (X21))),
% 2.74/2.92      inference('demod', [status(thm)], ['76', '77'])).
% 2.74/2.92  thf('79', plain,
% 2.74/2.92      (![X12 : $i]:
% 2.74/2.92         (((k10_relat_1 @ X12 @ (k2_relat_1 @ X12)) = (k1_relat_1 @ X12))
% 2.74/2.92          | ~ (v1_relat_1 @ X12))),
% 2.74/2.92      inference('cnf', [status(esa)], [t169_relat_1])).
% 2.74/2.92  thf('80', plain,
% 2.74/2.92      (![X0 : $i]:
% 2.74/2.92         (((k10_relat_1 @ (k6_partfun1 @ X0) @ X0)
% 2.74/2.92            = (k1_relat_1 @ (k6_partfun1 @ X0)))
% 2.74/2.92          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 2.74/2.92      inference('sup+', [status(thm)], ['78', '79'])).
% 2.74/2.92  thf('81', plain, (![X20 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 2.74/2.92      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.74/2.92  thf('82', plain, (![X58 : $i]: ((k6_partfun1 @ X58) = (k6_relat_1 @ X58))),
% 2.74/2.92      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.74/2.92  thf('83', plain, (![X20 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X20)) = (X20))),
% 2.74/2.92      inference('demod', [status(thm)], ['81', '82'])).
% 2.74/2.92  thf('84', plain, (![X26 : $i]: (v1_relat_1 @ (k6_partfun1 @ X26))),
% 2.74/2.92      inference('demod', [status(thm)], ['73', '74'])).
% 2.74/2.92  thf('85', plain,
% 2.74/2.92      (![X0 : $i]: ((k10_relat_1 @ (k6_partfun1 @ X0) @ X0) = (X0))),
% 2.74/2.92      inference('demod', [status(thm)], ['80', '83', '84'])).
% 2.74/2.92  thf('86', plain,
% 2.74/2.92      (![X0 : $i]:
% 2.74/2.92         (~ (v1_relat_1 @ X0)
% 2.74/2.92          | ~ (v1_relat_1 @ X0)
% 2.74/2.92          | ~ (v1_relat_1 @ X0)
% 2.74/2.92          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0)
% 2.74/2.92              = (k7_relat_1 @ 
% 2.74/2.92                 (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0) @ 
% 2.74/2.92                 (k1_relat_1 @ X0))))),
% 2.74/2.92      inference('demod', [status(thm)], ['72', '75', '85'])).
% 2.74/2.92  thf('87', plain,
% 2.74/2.92      (![X0 : $i]:
% 2.74/2.92         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0)
% 2.74/2.92            = (k7_relat_1 @ 
% 2.74/2.92               (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0) @ 
% 2.74/2.92               (k1_relat_1 @ X0)))
% 2.74/2.92          | ~ (v1_relat_1 @ X0))),
% 2.74/2.92      inference('simplify', [status(thm)], ['86'])).
% 2.74/2.92  thf('88', plain,
% 2.74/2.92      (![X0 : $i]:
% 2.74/2.92         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0)
% 2.74/2.92            = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 2.74/2.92          | ~ (v1_relat_1 @ X0)
% 2.74/2.92          | ~ (v1_relat_1 @ X0))),
% 2.74/2.92      inference('sup+', [status(thm)], ['67', '87'])).
% 2.74/2.92  thf('89', plain,
% 2.74/2.92      (![X0 : $i]:
% 2.74/2.92         (~ (v1_relat_1 @ X0)
% 2.74/2.92          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0)
% 2.74/2.92              = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 2.74/2.92      inference('simplify', [status(thm)], ['88'])).
% 2.74/2.92  thf('90', plain,
% 2.74/2.92      (![X0 : $i]:
% 2.74/2.92         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0)
% 2.74/2.92            = (k7_relat_1 @ 
% 2.74/2.92               (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0) @ 
% 2.74/2.92               (k1_relat_1 @ X0)))
% 2.74/2.92          | ~ (v1_relat_1 @ X0))),
% 2.74/2.92      inference('simplify', [status(thm)], ['86'])).
% 2.74/2.92  thf('91', plain,
% 2.74/2.92      (![X0 : $i]:
% 2.74/2.92         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0)
% 2.74/2.92            = (k7_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ 
% 2.74/2.92               (k1_relat_1 @ X0)))
% 2.74/2.92          | ~ (v1_relat_1 @ X0)
% 2.74/2.92          | ~ (v1_relat_1 @ X0))),
% 2.74/2.92      inference('sup+', [status(thm)], ['89', '90'])).
% 2.74/2.92  thf('92', plain,
% 2.74/2.92      (![X0 : $i]:
% 2.74/2.92         (~ (v1_relat_1 @ X0)
% 2.74/2.92          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0)
% 2.74/2.92              = (k7_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ 
% 2.74/2.92                 (k1_relat_1 @ X0))))),
% 2.74/2.92      inference('simplify', [status(thm)], ['91'])).
% 2.74/2.92  thf('93', plain,
% 2.74/2.92      ((((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ sk_D)
% 2.74/2.92          = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))
% 2.74/2.92        | ~ (v1_relat_1 @ sk_D))),
% 2.74/2.92      inference('sup+', [status(thm)], ['64', '92'])).
% 2.74/2.92  thf('94', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))),
% 2.74/2.92      inference('demod', [status(thm)], ['62', '63'])).
% 2.74/2.92  thf('95', plain, ((v1_relat_1 @ sk_D)),
% 2.74/2.92      inference('demod', [status(thm)], ['15', '16'])).
% 2.74/2.92  thf('96', plain,
% 2.74/2.92      (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ sk_D) = (sk_D))),
% 2.74/2.92      inference('demod', [status(thm)], ['93', '94', '95'])).
% 2.74/2.92  thf('97', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 2.74/2.92      inference('sup-', [status(thm)], ['8', '9'])).
% 2.74/2.92  thf('98', plain,
% 2.74/2.92      (![X5 : $i, X6 : $i]:
% 2.74/2.92         (~ (v4_relat_1 @ X5 @ X6)
% 2.74/2.92          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 2.74/2.92          | ~ (v1_relat_1 @ X5))),
% 2.74/2.92      inference('cnf', [status(esa)], [d18_relat_1])).
% 2.74/2.92  thf('99', plain,
% 2.74/2.92      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B))),
% 2.74/2.92      inference('sup-', [status(thm)], ['97', '98'])).
% 2.74/2.92  thf('100', plain, ((v1_relat_1 @ sk_D)),
% 2.74/2.92      inference('demod', [status(thm)], ['15', '16'])).
% 2.74/2.92  thf('101', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 2.74/2.92      inference('demod', [status(thm)], ['99', '100'])).
% 2.74/2.92  thf('102', plain,
% 2.74/2.92      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.74/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.92  thf(redefinition_k2_relset_1, axiom,
% 2.74/2.92    (![A:$i,B:$i,C:$i]:
% 2.74/2.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.74/2.92       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.74/2.92  thf('103', plain,
% 2.74/2.92      (![X37 : $i, X38 : $i, X39 : $i]:
% 2.74/2.92         (((k2_relset_1 @ X38 @ X39 @ X37) = (k2_relat_1 @ X37))
% 2.74/2.92          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 2.74/2.92      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.74/2.92  thf('104', plain,
% 2.74/2.92      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 2.74/2.92      inference('sup-', [status(thm)], ['102', '103'])).
% 2.74/2.92  thf('105', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.74/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.92  thf('106', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.74/2.92      inference('sup+', [status(thm)], ['104', '105'])).
% 2.74/2.92  thf('107', plain,
% 2.74/2.92      (![X28 : $i, X29 : $i]:
% 2.74/2.92         (~ (r1_tarski @ X28 @ (k2_relat_1 @ X29))
% 2.74/2.92          | ((k9_relat_1 @ X29 @ (k10_relat_1 @ X29 @ X28)) = (X28))
% 2.74/2.92          | ~ (v1_funct_1 @ X29)
% 2.74/2.92          | ~ (v1_relat_1 @ X29))),
% 2.74/2.92      inference('cnf', [status(esa)], [t147_funct_1])).
% 2.74/2.92  thf('108', plain,
% 2.74/2.92      (![X0 : $i]:
% 2.74/2.92         (~ (r1_tarski @ X0 @ sk_B)
% 2.74/2.92          | ~ (v1_relat_1 @ sk_C)
% 2.74/2.92          | ~ (v1_funct_1 @ sk_C)
% 2.74/2.92          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 2.74/2.92      inference('sup-', [status(thm)], ['106', '107'])).
% 2.74/2.92  thf('109', plain,
% 2.74/2.92      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.74/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.92  thf('110', plain,
% 2.74/2.92      (![X3 : $i, X4 : $i]:
% 2.74/2.92         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 2.74/2.92          | (v1_relat_1 @ X3)
% 2.74/2.92          | ~ (v1_relat_1 @ X4))),
% 2.74/2.92      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.74/2.92  thf('111', plain,
% 2.74/2.92      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 2.74/2.92      inference('sup-', [status(thm)], ['109', '110'])).
% 2.74/2.92  thf('112', plain,
% 2.74/2.92      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 2.74/2.93      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.74/2.93  thf('113', plain, ((v1_relat_1 @ sk_C)),
% 2.74/2.93      inference('demod', [status(thm)], ['111', '112'])).
% 2.74/2.93  thf('114', plain, ((v1_funct_1 @ sk_C)),
% 2.74/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.93  thf('115', plain,
% 2.74/2.93      (![X0 : $i]:
% 2.74/2.93         (~ (r1_tarski @ X0 @ sk_B)
% 2.74/2.93          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 2.74/2.93      inference('demod', [status(thm)], ['108', '113', '114'])).
% 2.74/2.93  thf('116', plain,
% 2.74/2.93      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 2.74/2.93         = (k1_relat_1 @ sk_D))),
% 2.74/2.93      inference('sup-', [status(thm)], ['101', '115'])).
% 2.74/2.93  thf('117', plain,
% 2.74/2.93      (![X13 : $i, X14 : $i]:
% 2.74/2.93         (~ (v1_relat_1 @ X13)
% 2.74/2.93          | ((k1_relat_1 @ (k5_relat_1 @ X14 @ X13))
% 2.74/2.93              = (k10_relat_1 @ X14 @ (k1_relat_1 @ X13)))
% 2.74/2.93          | ~ (v1_relat_1 @ X14))),
% 2.74/2.93      inference('cnf', [status(esa)], [t182_relat_1])).
% 2.74/2.93  thf('118', plain,
% 2.74/2.93      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.74/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.93  thf('119', plain,
% 2.74/2.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.74/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.93  thf(dt_k1_partfun1, axiom,
% 2.74/2.93    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.74/2.93     ( ( ( v1_funct_1 @ E ) & 
% 2.74/2.93         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.74/2.93         ( v1_funct_1 @ F ) & 
% 2.74/2.93         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.74/2.93       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.74/2.93         ( m1_subset_1 @
% 2.74/2.93           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.74/2.93           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.74/2.93  thf('120', plain,
% 2.74/2.93      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 2.74/2.93         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 2.74/2.93          | ~ (v1_funct_1 @ X44)
% 2.74/2.93          | ~ (v1_funct_1 @ X47)
% 2.74/2.93          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 2.74/2.93          | (m1_subset_1 @ (k1_partfun1 @ X45 @ X46 @ X48 @ X49 @ X44 @ X47) @ 
% 2.74/2.93             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X49))))),
% 2.74/2.93      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.74/2.93  thf('121', plain,
% 2.74/2.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.74/2.93         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.74/2.93           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.74/2.93          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.74/2.93          | ~ (v1_funct_1 @ X1)
% 2.74/2.93          | ~ (v1_funct_1 @ sk_C))),
% 2.74/2.93      inference('sup-', [status(thm)], ['119', '120'])).
% 2.74/2.93  thf('122', plain, ((v1_funct_1 @ sk_C)),
% 2.74/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.93  thf('123', plain,
% 2.74/2.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.74/2.93         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.74/2.93           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.74/2.93          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.74/2.93          | ~ (v1_funct_1 @ X1))),
% 2.74/2.93      inference('demod', [status(thm)], ['121', '122'])).
% 2.74/2.93  thf('124', plain,
% 2.74/2.93      ((~ (v1_funct_1 @ sk_D)
% 2.74/2.93        | (m1_subset_1 @ 
% 2.74/2.93           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.74/2.93           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.74/2.93      inference('sup-', [status(thm)], ['118', '123'])).
% 2.74/2.93  thf('125', plain, ((v1_funct_1 @ sk_D)),
% 2.74/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.93  thf('126', plain,
% 2.74/2.93      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.74/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.93  thf('127', plain,
% 2.74/2.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.74/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.93  thf(redefinition_k1_partfun1, axiom,
% 2.74/2.93    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.74/2.93     ( ( ( v1_funct_1 @ E ) & 
% 2.74/2.93         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.74/2.93         ( v1_funct_1 @ F ) & 
% 2.74/2.93         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.74/2.93       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.74/2.93  thf('128', plain,
% 2.74/2.93      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 2.74/2.93         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X54)))
% 2.74/2.93          | ~ (v1_funct_1 @ X52)
% 2.74/2.93          | ~ (v1_funct_1 @ X55)
% 2.74/2.93          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X57)))
% 2.74/2.93          | ((k1_partfun1 @ X53 @ X54 @ X56 @ X57 @ X52 @ X55)
% 2.74/2.93              = (k5_relat_1 @ X52 @ X55)))),
% 2.74/2.93      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 2.74/2.93  thf('129', plain,
% 2.74/2.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.74/2.93         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.74/2.93            = (k5_relat_1 @ sk_C @ X0))
% 2.74/2.93          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.74/2.93          | ~ (v1_funct_1 @ X0)
% 2.74/2.93          | ~ (v1_funct_1 @ sk_C))),
% 2.74/2.93      inference('sup-', [status(thm)], ['127', '128'])).
% 2.74/2.93  thf('130', plain, ((v1_funct_1 @ sk_C)),
% 2.74/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.93  thf('131', plain,
% 2.74/2.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.74/2.93         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.74/2.93            = (k5_relat_1 @ sk_C @ X0))
% 2.74/2.93          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.74/2.93          | ~ (v1_funct_1 @ X0))),
% 2.74/2.93      inference('demod', [status(thm)], ['129', '130'])).
% 2.74/2.93  thf('132', plain,
% 2.74/2.93      ((~ (v1_funct_1 @ sk_D)
% 2.74/2.93        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.74/2.93            = (k5_relat_1 @ sk_C @ sk_D)))),
% 2.74/2.93      inference('sup-', [status(thm)], ['126', '131'])).
% 2.74/2.93  thf('133', plain, ((v1_funct_1 @ sk_D)),
% 2.74/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.93  thf('134', plain,
% 2.74/2.93      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.74/2.93         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.74/2.93      inference('demod', [status(thm)], ['132', '133'])).
% 2.74/2.93  thf('135', plain,
% 2.74/2.93      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 2.74/2.93        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.74/2.93      inference('demod', [status(thm)], ['124', '125', '134'])).
% 2.74/2.93  thf('136', plain,
% 2.74/2.93      (![X34 : $i, X35 : $i, X36 : $i]:
% 2.74/2.93         ((v4_relat_1 @ X34 @ X35)
% 2.74/2.93          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 2.74/2.93      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.74/2.93  thf('137', plain, ((v4_relat_1 @ (k5_relat_1 @ sk_C @ sk_D) @ sk_A)),
% 2.74/2.93      inference('sup-', [status(thm)], ['135', '136'])).
% 2.74/2.93  thf('138', plain,
% 2.74/2.93      (![X5 : $i, X6 : $i]:
% 2.74/2.93         (~ (v4_relat_1 @ X5 @ X6)
% 2.74/2.93          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 2.74/2.93          | ~ (v1_relat_1 @ X5))),
% 2.74/2.93      inference('cnf', [status(esa)], [d18_relat_1])).
% 2.74/2.93  thf('139', plain,
% 2.74/2.93      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 2.74/2.93        | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ sk_A))),
% 2.74/2.93      inference('sup-', [status(thm)], ['137', '138'])).
% 2.74/2.93  thf('140', plain,
% 2.74/2.93      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 2.74/2.93        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.74/2.93      inference('demod', [status(thm)], ['124', '125', '134'])).
% 2.74/2.93  thf('141', plain,
% 2.74/2.93      (![X3 : $i, X4 : $i]:
% 2.74/2.93         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 2.74/2.93          | (v1_relat_1 @ X3)
% 2.74/2.93          | ~ (v1_relat_1 @ X4))),
% 2.74/2.93      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.74/2.93  thf('142', plain,
% 2.74/2.93      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 2.74/2.93        | (v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))),
% 2.74/2.93      inference('sup-', [status(thm)], ['140', '141'])).
% 2.74/2.93  thf('143', plain,
% 2.74/2.93      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 2.74/2.93      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.74/2.93  thf('144', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))),
% 2.74/2.93      inference('demod', [status(thm)], ['142', '143'])).
% 2.74/2.93  thf('145', plain,
% 2.74/2.93      ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ sk_A)),
% 2.74/2.93      inference('demod', [status(thm)], ['139', '144'])).
% 2.74/2.93  thf('146', plain,
% 2.74/2.93      (((r1_tarski @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)) @ sk_A)
% 2.74/2.93        | ~ (v1_relat_1 @ sk_C)
% 2.74/2.93        | ~ (v1_relat_1 @ sk_D))),
% 2.74/2.93      inference('sup+', [status(thm)], ['117', '145'])).
% 2.74/2.93  thf('147', plain, ((v1_relat_1 @ sk_C)),
% 2.74/2.93      inference('demod', [status(thm)], ['111', '112'])).
% 2.74/2.93  thf('148', plain, ((v1_relat_1 @ sk_D)),
% 2.74/2.93      inference('demod', [status(thm)], ['15', '16'])).
% 2.74/2.93  thf('149', plain,
% 2.74/2.93      ((r1_tarski @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)) @ sk_A)),
% 2.74/2.93      inference('demod', [status(thm)], ['146', '147', '148'])).
% 2.74/2.93  thf('150', plain,
% 2.74/2.93      (![X20 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X20)) = (X20))),
% 2.74/2.93      inference('demod', [status(thm)], ['81', '82'])).
% 2.74/2.93  thf('151', plain,
% 2.74/2.93      (![X5 : $i, X6 : $i]:
% 2.74/2.93         (~ (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 2.74/2.93          | (v4_relat_1 @ X5 @ X6)
% 2.74/2.93          | ~ (v1_relat_1 @ X5))),
% 2.74/2.93      inference('cnf', [status(esa)], [d18_relat_1])).
% 2.74/2.93  thf('152', plain,
% 2.74/2.93      (![X0 : $i, X1 : $i]:
% 2.74/2.93         (~ (r1_tarski @ X0 @ X1)
% 2.74/2.93          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 2.74/2.93          | (v4_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 2.74/2.93      inference('sup-', [status(thm)], ['150', '151'])).
% 2.74/2.93  thf('153', plain, (![X26 : $i]: (v1_relat_1 @ (k6_partfun1 @ X26))),
% 2.74/2.93      inference('demod', [status(thm)], ['73', '74'])).
% 2.74/2.93  thf('154', plain,
% 2.74/2.93      (![X0 : $i, X1 : $i]:
% 2.74/2.93         (~ (r1_tarski @ X0 @ X1) | (v4_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 2.74/2.93      inference('demod', [status(thm)], ['152', '153'])).
% 2.74/2.93  thf('155', plain,
% 2.74/2.93      ((v4_relat_1 @ 
% 2.74/2.93        (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))) @ sk_A)),
% 2.74/2.93      inference('sup-', [status(thm)], ['149', '154'])).
% 2.74/2.93  thf('156', plain,
% 2.74/2.93      (![X15 : $i, X16 : $i]:
% 2.74/2.93         (((X15) = (k7_relat_1 @ X15 @ X16))
% 2.74/2.93          | ~ (v4_relat_1 @ X15 @ X16)
% 2.74/2.93          | ~ (v1_relat_1 @ X15))),
% 2.74/2.93      inference('cnf', [status(esa)], [t209_relat_1])).
% 2.74/2.93  thf('157', plain,
% 2.74/2.93      ((~ (v1_relat_1 @ 
% 2.74/2.93           (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))))
% 2.74/2.93        | ((k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 2.74/2.93            = (k7_relat_1 @ 
% 2.74/2.93               (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))) @ 
% 2.74/2.93               sk_A)))),
% 2.74/2.93      inference('sup-', [status(thm)], ['155', '156'])).
% 2.74/2.93  thf('158', plain, (![X26 : $i]: (v1_relat_1 @ (k6_partfun1 @ X26))),
% 2.74/2.93      inference('demod', [status(thm)], ['73', '74'])).
% 2.74/2.93  thf('159', plain,
% 2.74/2.93      (((k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 2.74/2.93         = (k7_relat_1 @ 
% 2.74/2.93            (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))) @ sk_A))),
% 2.74/2.93      inference('demod', [status(thm)], ['157', '158'])).
% 2.74/2.93  thf('160', plain,
% 2.74/2.93      (![X10 : $i, X11 : $i]:
% 2.74/2.93         (((k2_relat_1 @ (k7_relat_1 @ X10 @ X11)) = (k9_relat_1 @ X10 @ X11))
% 2.74/2.93          | ~ (v1_relat_1 @ X10))),
% 2.74/2.93      inference('cnf', [status(esa)], [t148_relat_1])).
% 2.74/2.93  thf('161', plain,
% 2.74/2.93      ((((k2_relat_1 @ 
% 2.74/2.93          (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))))
% 2.74/2.93          = (k9_relat_1 @ 
% 2.74/2.93             (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))) @ sk_A))
% 2.74/2.93        | ~ (v1_relat_1 @ 
% 2.74/2.93             (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))))),
% 2.74/2.93      inference('sup+', [status(thm)], ['159', '160'])).
% 2.74/2.93  thf('162', plain,
% 2.74/2.93      (![X21 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X21)) = (X21))),
% 2.74/2.93      inference('demod', [status(thm)], ['76', '77'])).
% 2.74/2.93  thf('163', plain,
% 2.74/2.93      (![X13 : $i, X14 : $i]:
% 2.74/2.93         (~ (v1_relat_1 @ X13)
% 2.74/2.93          | ((k1_relat_1 @ (k5_relat_1 @ X14 @ X13))
% 2.74/2.93              = (k10_relat_1 @ X14 @ (k1_relat_1 @ X13)))
% 2.74/2.93          | ~ (v1_relat_1 @ X14))),
% 2.74/2.93      inference('cnf', [status(esa)], [t182_relat_1])).
% 2.74/2.93  thf('164', plain,
% 2.74/2.93      ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ sk_A)),
% 2.74/2.93      inference('demod', [status(thm)], ['139', '144'])).
% 2.74/2.93  thf('165', plain,
% 2.74/2.93      (![X0 : $i, X1 : $i]:
% 2.74/2.93         (~ (r1_tarski @ X0 @ X1) | (v4_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 2.74/2.93      inference('demod', [status(thm)], ['152', '153'])).
% 2.74/2.93  thf('166', plain,
% 2.74/2.93      ((v4_relat_1 @ 
% 2.74/2.93        (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))) @ sk_A)),
% 2.74/2.93      inference('sup-', [status(thm)], ['164', '165'])).
% 2.74/2.93  thf('167', plain,
% 2.74/2.93      (![X15 : $i, X16 : $i]:
% 2.74/2.93         (((X15) = (k7_relat_1 @ X15 @ X16))
% 2.74/2.93          | ~ (v4_relat_1 @ X15 @ X16)
% 2.74/2.93          | ~ (v1_relat_1 @ X15))),
% 2.74/2.93      inference('cnf', [status(esa)], [t209_relat_1])).
% 2.74/2.93  thf('168', plain,
% 2.74/2.93      ((~ (v1_relat_1 @ 
% 2.74/2.93           (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))))
% 2.74/2.93        | ((k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 2.74/2.93            = (k7_relat_1 @ 
% 2.74/2.93               (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))) @ sk_A)))),
% 2.74/2.93      inference('sup-', [status(thm)], ['166', '167'])).
% 2.74/2.93  thf('169', plain, (![X26 : $i]: (v1_relat_1 @ (k6_partfun1 @ X26))),
% 2.74/2.93      inference('demod', [status(thm)], ['73', '74'])).
% 2.74/2.93  thf('170', plain,
% 2.74/2.93      (((k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 2.74/2.93         = (k7_relat_1 @ 
% 2.74/2.93            (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))) @ sk_A))),
% 2.74/2.93      inference('demod', [status(thm)], ['168', '169'])).
% 2.74/2.93  thf('171', plain,
% 2.74/2.93      (![X10 : $i, X11 : $i]:
% 2.74/2.93         (((k2_relat_1 @ (k7_relat_1 @ X10 @ X11)) = (k9_relat_1 @ X10 @ X11))
% 2.74/2.93          | ~ (v1_relat_1 @ X10))),
% 2.74/2.93      inference('cnf', [status(esa)], [t148_relat_1])).
% 2.74/2.93  thf('172', plain,
% 2.74/2.93      ((((k2_relat_1 @ 
% 2.74/2.93          (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))))
% 2.74/2.93          = (k9_relat_1 @ 
% 2.74/2.93             (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))) @ sk_A))
% 2.74/2.93        | ~ (v1_relat_1 @ 
% 2.74/2.93             (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))))),
% 2.74/2.93      inference('sup+', [status(thm)], ['170', '171'])).
% 2.74/2.93  thf('173', plain,
% 2.74/2.93      (![X21 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X21)) = (X21))),
% 2.74/2.93      inference('demod', [status(thm)], ['76', '77'])).
% 2.74/2.93  thf('174', plain, (![X26 : $i]: (v1_relat_1 @ (k6_partfun1 @ X26))),
% 2.74/2.93      inference('demod', [status(thm)], ['73', '74'])).
% 2.74/2.93  thf('175', plain,
% 2.74/2.93      (((k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 2.74/2.93         = (k9_relat_1 @ 
% 2.74/2.93            (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))) @ sk_A))),
% 2.74/2.93      inference('demod', [status(thm)], ['172', '173', '174'])).
% 2.74/2.93  thf('176', plain,
% 2.74/2.93      ((((k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 2.74/2.93          = (k9_relat_1 @ 
% 2.74/2.93             (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))) @ sk_A))
% 2.74/2.93        | ~ (v1_relat_1 @ sk_C)
% 2.74/2.93        | ~ (v1_relat_1 @ sk_D))),
% 2.74/2.93      inference('sup+', [status(thm)], ['163', '175'])).
% 2.74/2.93  thf('177', plain, ((v1_relat_1 @ sk_C)),
% 2.74/2.93      inference('demod', [status(thm)], ['111', '112'])).
% 2.74/2.93  thf('178', plain, ((v1_relat_1 @ sk_D)),
% 2.74/2.93      inference('demod', [status(thm)], ['15', '16'])).
% 2.74/2.93  thf('179', plain,
% 2.74/2.93      (((k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 2.74/2.93         = (k9_relat_1 @ 
% 2.74/2.93            (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))) @ sk_A))),
% 2.74/2.93      inference('demod', [status(thm)], ['176', '177', '178'])).
% 2.74/2.93  thf('180', plain, (![X26 : $i]: (v1_relat_1 @ (k6_partfun1 @ X26))),
% 2.74/2.93      inference('demod', [status(thm)], ['73', '74'])).
% 2.74/2.93  thf('181', plain,
% 2.74/2.93      (((k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))
% 2.74/2.93         = (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))),
% 2.74/2.93      inference('demod', [status(thm)], ['161', '162', '179', '180'])).
% 2.74/2.93  thf('182', plain,
% 2.74/2.93      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.74/2.93        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.74/2.93        (k6_partfun1 @ sk_A))),
% 2.74/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.93  thf('183', plain,
% 2.74/2.93      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.74/2.93         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.74/2.93      inference('demod', [status(thm)], ['132', '133'])).
% 2.74/2.93  thf('184', plain,
% 2.74/2.93      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 2.74/2.93        (k6_partfun1 @ sk_A))),
% 2.74/2.93      inference('demod', [status(thm)], ['182', '183'])).
% 2.74/2.93  thf('185', plain,
% 2.74/2.93      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 2.74/2.93        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.74/2.93      inference('demod', [status(thm)], ['124', '125', '134'])).
% 2.74/2.93  thf(redefinition_r2_relset_1, axiom,
% 2.74/2.93    (![A:$i,B:$i,C:$i,D:$i]:
% 2.74/2.93     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.74/2.93         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.74/2.93       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.74/2.93  thf('186', plain,
% 2.74/2.93      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 2.74/2.93         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 2.74/2.93          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 2.74/2.93          | ((X40) = (X43))
% 2.74/2.93          | ~ (r2_relset_1 @ X41 @ X42 @ X40 @ X43))),
% 2.74/2.93      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.74/2.93  thf('187', plain,
% 2.74/2.93      (![X0 : $i]:
% 2.74/2.93         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 2.74/2.93          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 2.74/2.93          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.74/2.93      inference('sup-', [status(thm)], ['185', '186'])).
% 2.74/2.93  thf('188', plain,
% 2.74/2.93      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 2.74/2.93           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.74/2.93        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 2.74/2.93      inference('sup-', [status(thm)], ['184', '187'])).
% 2.74/2.93  thf(dt_k6_partfun1, axiom,
% 2.74/2.93    (![A:$i]:
% 2.74/2.93     ( ( m1_subset_1 @
% 2.74/2.93         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 2.74/2.93       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 2.74/2.93  thf('189', plain,
% 2.74/2.93      (![X51 : $i]:
% 2.74/2.93         (m1_subset_1 @ (k6_partfun1 @ X51) @ 
% 2.74/2.93          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X51)))),
% 2.74/2.93      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 2.74/2.93  thf('190', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 2.74/2.93      inference('demod', [status(thm)], ['188', '189'])).
% 2.74/2.93  thf('191', plain,
% 2.74/2.93      (![X20 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X20)) = (X20))),
% 2.74/2.93      inference('demod', [status(thm)], ['81', '82'])).
% 2.74/2.93  thf('192', plain, (((k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)) = (sk_A))),
% 2.74/2.93      inference('demod', [status(thm)], ['181', '190', '191'])).
% 2.74/2.93  thf('193', plain, (((k9_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ sk_D))),
% 2.74/2.93      inference('demod', [status(thm)], ['116', '192'])).
% 2.74/2.93  thf('194', plain,
% 2.74/2.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.74/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.93  thf('195', plain,
% 2.74/2.93      (![X34 : $i, X35 : $i, X36 : $i]:
% 2.74/2.93         ((v4_relat_1 @ X34 @ X35)
% 2.74/2.93          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 2.74/2.93      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.74/2.93  thf('196', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 2.74/2.93      inference('sup-', [status(thm)], ['194', '195'])).
% 2.74/2.93  thf('197', plain,
% 2.74/2.93      (![X15 : $i, X16 : $i]:
% 2.74/2.93         (((X15) = (k7_relat_1 @ X15 @ X16))
% 2.74/2.93          | ~ (v4_relat_1 @ X15 @ X16)
% 2.74/2.93          | ~ (v1_relat_1 @ X15))),
% 2.74/2.93      inference('cnf', [status(esa)], [t209_relat_1])).
% 2.74/2.93  thf('198', plain,
% 2.74/2.93      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 2.74/2.93      inference('sup-', [status(thm)], ['196', '197'])).
% 2.74/2.93  thf('199', plain, ((v1_relat_1 @ sk_C)),
% 2.74/2.93      inference('demod', [status(thm)], ['111', '112'])).
% 2.74/2.93  thf('200', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 2.74/2.93      inference('demod', [status(thm)], ['198', '199'])).
% 2.74/2.93  thf('201', plain,
% 2.74/2.93      (![X10 : $i, X11 : $i]:
% 2.74/2.93         (((k2_relat_1 @ (k7_relat_1 @ X10 @ X11)) = (k9_relat_1 @ X10 @ X11))
% 2.74/2.93          | ~ (v1_relat_1 @ X10))),
% 2.74/2.93      inference('cnf', [status(esa)], [t148_relat_1])).
% 2.74/2.93  thf('202', plain,
% 2.74/2.93      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))
% 2.74/2.93        | ~ (v1_relat_1 @ sk_C))),
% 2.74/2.93      inference('sup+', [status(thm)], ['200', '201'])).
% 2.74/2.93  thf('203', plain, ((v1_relat_1 @ sk_C)),
% 2.74/2.93      inference('demod', [status(thm)], ['111', '112'])).
% 2.74/2.93  thf('204', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 2.74/2.93      inference('demod', [status(thm)], ['202', '203'])).
% 2.74/2.93  thf('205', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.74/2.93      inference('sup+', [status(thm)], ['104', '105'])).
% 2.74/2.93  thf('206', plain, (((sk_B) = (k9_relat_1 @ sk_C @ sk_A))),
% 2.74/2.93      inference('demod', [status(thm)], ['204', '205'])).
% 2.74/2.93  thf('207', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 2.74/2.93      inference('sup+', [status(thm)], ['193', '206'])).
% 2.74/2.93  thf('208', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))),
% 2.74/2.93      inference('demod', [status(thm)], ['96', '207'])).
% 2.74/2.93  thf('209', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 2.74/2.93      inference('demod', [status(thm)], ['188', '189'])).
% 2.74/2.93  thf(t61_funct_1, axiom,
% 2.74/2.93    (![A:$i]:
% 2.74/2.93     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.74/2.93       ( ( v2_funct_1 @ A ) =>
% 2.74/2.93         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 2.74/2.93             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 2.74/2.93           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 2.74/2.93             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 2.74/2.93  thf('210', plain,
% 2.74/2.93      (![X33 : $i]:
% 2.74/2.93         (~ (v2_funct_1 @ X33)
% 2.74/2.93          | ((k5_relat_1 @ (k2_funct_1 @ X33) @ X33)
% 2.74/2.93              = (k6_relat_1 @ (k2_relat_1 @ X33)))
% 2.74/2.93          | ~ (v1_funct_1 @ X33)
% 2.74/2.93          | ~ (v1_relat_1 @ X33))),
% 2.74/2.93      inference('cnf', [status(esa)], [t61_funct_1])).
% 2.74/2.93  thf('211', plain, (![X58 : $i]: ((k6_partfun1 @ X58) = (k6_relat_1 @ X58))),
% 2.74/2.93      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.74/2.93  thf('212', plain,
% 2.74/2.93      (![X33 : $i]:
% 2.74/2.93         (~ (v2_funct_1 @ X33)
% 2.74/2.93          | ((k5_relat_1 @ (k2_funct_1 @ X33) @ X33)
% 2.74/2.93              = (k6_partfun1 @ (k2_relat_1 @ X33)))
% 2.74/2.93          | ~ (v1_funct_1 @ X33)
% 2.74/2.93          | ~ (v1_relat_1 @ X33))),
% 2.74/2.93      inference('demod', [status(thm)], ['210', '211'])).
% 2.74/2.93  thf(t55_funct_1, axiom,
% 2.74/2.93    (![A:$i]:
% 2.74/2.93     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.74/2.93       ( ( v2_funct_1 @ A ) =>
% 2.74/2.93         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 2.74/2.93           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.74/2.93  thf('213', plain,
% 2.74/2.93      (![X32 : $i]:
% 2.74/2.93         (~ (v2_funct_1 @ X32)
% 2.74/2.93          | ((k2_relat_1 @ X32) = (k1_relat_1 @ (k2_funct_1 @ X32)))
% 2.74/2.93          | ~ (v1_funct_1 @ X32)
% 2.74/2.93          | ~ (v1_relat_1 @ X32))),
% 2.74/2.93      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.74/2.93  thf(dt_k2_funct_1, axiom,
% 2.74/2.93    (![A:$i]:
% 2.74/2.93     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.74/2.93       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 2.74/2.93         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 2.74/2.93  thf('214', plain,
% 2.74/2.93      (![X25 : $i]:
% 2.74/2.93         ((v1_relat_1 @ (k2_funct_1 @ X25))
% 2.74/2.93          | ~ (v1_funct_1 @ X25)
% 2.74/2.93          | ~ (v1_relat_1 @ X25))),
% 2.74/2.93      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.74/2.93  thf('215', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.74/2.93      inference('sup+', [status(thm)], ['104', '105'])).
% 2.74/2.93  thf('216', plain,
% 2.74/2.93      (![X25 : $i]:
% 2.74/2.93         ((v1_relat_1 @ (k2_funct_1 @ X25))
% 2.74/2.93          | ~ (v1_funct_1 @ X25)
% 2.74/2.93          | ~ (v1_relat_1 @ X25))),
% 2.74/2.93      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.74/2.93  thf('217', plain,
% 2.74/2.93      (![X32 : $i]:
% 2.74/2.93         (~ (v2_funct_1 @ X32)
% 2.74/2.93          | ((k2_relat_1 @ X32) = (k1_relat_1 @ (k2_funct_1 @ X32)))
% 2.74/2.93          | ~ (v1_funct_1 @ X32)
% 2.74/2.93          | ~ (v1_relat_1 @ X32))),
% 2.74/2.93      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.74/2.93  thf('218', plain,
% 2.74/2.93      (![X0 : $i]:
% 2.74/2.93         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 2.74/2.93      inference('sup-', [status(thm)], ['1', '2'])).
% 2.74/2.93  thf('219', plain,
% 2.74/2.93      (![X0 : $i]:
% 2.74/2.93         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 2.74/2.93          | ~ (v1_relat_1 @ X0)
% 2.74/2.93          | ~ (v1_funct_1 @ X0)
% 2.74/2.93          | ~ (v2_funct_1 @ X0)
% 2.74/2.93          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 2.74/2.93      inference('sup+', [status(thm)], ['217', '218'])).
% 2.74/2.93  thf('220', plain,
% 2.74/2.93      (![X0 : $i]:
% 2.74/2.93         (~ (v1_relat_1 @ X0)
% 2.74/2.93          | ~ (v1_funct_1 @ X0)
% 2.74/2.93          | ~ (v2_funct_1 @ X0)
% 2.74/2.93          | ~ (v1_funct_1 @ X0)
% 2.74/2.93          | ~ (v1_relat_1 @ X0)
% 2.74/2.93          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 2.74/2.93      inference('sup-', [status(thm)], ['216', '219'])).
% 2.74/2.93  thf('221', plain,
% 2.74/2.93      (![X0 : $i]:
% 2.74/2.93         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 2.74/2.93          | ~ (v2_funct_1 @ X0)
% 2.74/2.93          | ~ (v1_funct_1 @ X0)
% 2.74/2.93          | ~ (v1_relat_1 @ X0))),
% 2.74/2.93      inference('simplify', [status(thm)], ['220'])).
% 2.74/2.93  thf('222', plain,
% 2.74/2.93      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)
% 2.74/2.93        | ~ (v1_relat_1 @ sk_C)
% 2.74/2.93        | ~ (v1_funct_1 @ sk_C)
% 2.74/2.93        | ~ (v2_funct_1 @ sk_C))),
% 2.74/2.93      inference('sup+', [status(thm)], ['215', '221'])).
% 2.74/2.93  thf('223', plain, ((v1_relat_1 @ sk_C)),
% 2.74/2.93      inference('demod', [status(thm)], ['111', '112'])).
% 2.74/2.93  thf('224', plain, ((v1_funct_1 @ sk_C)),
% 2.74/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.93  thf('225', plain, ((v2_funct_1 @ sk_C)),
% 2.74/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.93  thf('226', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)),
% 2.74/2.93      inference('demod', [status(thm)], ['222', '223', '224', '225'])).
% 2.74/2.93  thf('227', plain,
% 2.74/2.93      (![X5 : $i, X6 : $i]:
% 2.74/2.93         (~ (v4_relat_1 @ X5 @ X6)
% 2.74/2.93          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 2.74/2.93          | ~ (v1_relat_1 @ X5))),
% 2.74/2.93      inference('cnf', [status(esa)], [d18_relat_1])).
% 2.74/2.93  thf('228', plain,
% 2.74/2.93      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.74/2.93        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 2.74/2.93      inference('sup-', [status(thm)], ['226', '227'])).
% 2.74/2.93  thf('229', plain,
% 2.74/2.93      ((~ (v1_relat_1 @ sk_C)
% 2.74/2.93        | ~ (v1_funct_1 @ sk_C)
% 2.74/2.93        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 2.74/2.93      inference('sup-', [status(thm)], ['214', '228'])).
% 2.74/2.93  thf('230', plain, ((v1_relat_1 @ sk_C)),
% 2.74/2.93      inference('demod', [status(thm)], ['111', '112'])).
% 2.74/2.93  thf('231', plain, ((v1_funct_1 @ sk_C)),
% 2.74/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.93  thf('232', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B)),
% 2.74/2.93      inference('demod', [status(thm)], ['229', '230', '231'])).
% 2.74/2.93  thf('233', plain,
% 2.74/2.93      (![X0 : $i, X2 : $i]:
% 2.74/2.93         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.74/2.93      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.74/2.93  thf('234', plain,
% 2.74/2.93      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 2.74/2.93        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 2.74/2.93      inference('sup-', [status(thm)], ['232', '233'])).
% 2.74/2.93  thf('235', plain,
% 2.74/2.93      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C))
% 2.74/2.93        | ~ (v1_relat_1 @ sk_C)
% 2.74/2.93        | ~ (v1_funct_1 @ sk_C)
% 2.74/2.93        | ~ (v2_funct_1 @ sk_C)
% 2.74/2.93        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 2.74/2.93      inference('sup-', [status(thm)], ['213', '234'])).
% 2.74/2.93  thf('236', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.74/2.93      inference('sup+', [status(thm)], ['104', '105'])).
% 2.74/2.93  thf('237', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.74/2.93      inference('simplify', [status(thm)], ['0'])).
% 2.74/2.93  thf('238', plain, ((v1_relat_1 @ sk_C)),
% 2.74/2.93      inference('demod', [status(thm)], ['111', '112'])).
% 2.74/2.93  thf('239', plain, ((v1_funct_1 @ sk_C)),
% 2.74/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.93  thf('240', plain, ((v2_funct_1 @ sk_C)),
% 2.74/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.93  thf('241', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 2.74/2.93      inference('demod', [status(thm)],
% 2.74/2.93                ['235', '236', '237', '238', '239', '240'])).
% 2.74/2.93  thf('242', plain,
% 2.74/2.93      (![X22 : $i]:
% 2.74/2.93         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X22)) @ X22) = (X22))
% 2.74/2.93          | ~ (v1_relat_1 @ X22))),
% 2.74/2.93      inference('demod', [status(thm)], ['65', '66'])).
% 2.74/2.93  thf(t55_relat_1, axiom,
% 2.74/2.93    (![A:$i]:
% 2.74/2.93     ( ( v1_relat_1 @ A ) =>
% 2.74/2.93       ( ![B:$i]:
% 2.74/2.93         ( ( v1_relat_1 @ B ) =>
% 2.74/2.93           ( ![C:$i]:
% 2.74/2.93             ( ( v1_relat_1 @ C ) =>
% 2.74/2.93               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 2.74/2.93                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 2.74/2.93  thf('243', plain,
% 2.74/2.93      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.74/2.93         (~ (v1_relat_1 @ X17)
% 2.74/2.93          | ((k5_relat_1 @ (k5_relat_1 @ X18 @ X17) @ X19)
% 2.74/2.93              = (k5_relat_1 @ X18 @ (k5_relat_1 @ X17 @ X19)))
% 2.74/2.93          | ~ (v1_relat_1 @ X19)
% 2.74/2.93          | ~ (v1_relat_1 @ X18))),
% 2.74/2.93      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.74/2.93  thf('244', plain,
% 2.74/2.93      (![X0 : $i, X1 : $i]:
% 2.74/2.93         (((k5_relat_1 @ X0 @ X1)
% 2.74/2.93            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 2.74/2.93               (k5_relat_1 @ X0 @ X1)))
% 2.74/2.93          | ~ (v1_relat_1 @ X0)
% 2.74/2.93          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 2.74/2.93          | ~ (v1_relat_1 @ X1)
% 2.74/2.93          | ~ (v1_relat_1 @ X0))),
% 2.74/2.93      inference('sup+', [status(thm)], ['242', '243'])).
% 2.74/2.93  thf('245', plain, (![X26 : $i]: (v1_relat_1 @ (k6_partfun1 @ X26))),
% 2.74/2.93      inference('demod', [status(thm)], ['73', '74'])).
% 2.74/2.93  thf('246', plain,
% 2.74/2.93      (![X0 : $i, X1 : $i]:
% 2.74/2.93         (((k5_relat_1 @ X0 @ X1)
% 2.74/2.93            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 2.74/2.93               (k5_relat_1 @ X0 @ X1)))
% 2.74/2.93          | ~ (v1_relat_1 @ X0)
% 2.74/2.93          | ~ (v1_relat_1 @ X1)
% 2.74/2.93          | ~ (v1_relat_1 @ X0))),
% 2.74/2.93      inference('demod', [status(thm)], ['244', '245'])).
% 2.74/2.93  thf('247', plain,
% 2.74/2.93      (![X0 : $i, X1 : $i]:
% 2.74/2.93         (~ (v1_relat_1 @ X1)
% 2.74/2.93          | ~ (v1_relat_1 @ X0)
% 2.74/2.93          | ((k5_relat_1 @ X0 @ X1)
% 2.74/2.93              = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 2.74/2.93                 (k5_relat_1 @ X0 @ X1))))),
% 2.74/2.93      inference('simplify', [status(thm)], ['246'])).
% 2.74/2.93  thf('248', plain,
% 2.74/2.93      (![X0 : $i]:
% 2.74/2.93         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 2.74/2.93            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 2.74/2.93               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 2.74/2.93          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.74/2.93          | ~ (v1_relat_1 @ X0))),
% 2.74/2.93      inference('sup+', [status(thm)], ['241', '247'])).
% 2.74/2.93  thf('249', plain,
% 2.74/2.93      (![X25 : $i]:
% 2.74/2.93         ((v1_funct_1 @ (k2_funct_1 @ X25))
% 2.74/2.93          | ~ (v1_funct_1 @ X25)
% 2.74/2.93          | ~ (v1_relat_1 @ X25))),
% 2.74/2.93      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.74/2.93  thf('250', plain,
% 2.74/2.93      (![X25 : $i]:
% 2.74/2.93         ((v1_relat_1 @ (k2_funct_1 @ X25))
% 2.74/2.93          | ~ (v1_funct_1 @ X25)
% 2.74/2.93          | ~ (v1_relat_1 @ X25))),
% 2.74/2.93      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.74/2.93  thf('251', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 2.74/2.93      inference('demod', [status(thm)],
% 2.74/2.93                ['235', '236', '237', '238', '239', '240'])).
% 2.74/2.93  thf(t3_funct_2, axiom,
% 2.74/2.93    (![A:$i]:
% 2.74/2.93     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.74/2.93       ( ( v1_funct_1 @ A ) & 
% 2.74/2.93         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 2.74/2.93         ( m1_subset_1 @
% 2.74/2.93           A @ 
% 2.74/2.93           ( k1_zfmisc_1 @
% 2.74/2.93             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 2.74/2.93  thf('252', plain,
% 2.74/2.93      (![X59 : $i]:
% 2.74/2.93         ((m1_subset_1 @ X59 @ 
% 2.74/2.93           (k1_zfmisc_1 @ 
% 2.74/2.93            (k2_zfmisc_1 @ (k1_relat_1 @ X59) @ (k2_relat_1 @ X59))))
% 2.74/2.93          | ~ (v1_funct_1 @ X59)
% 2.74/2.93          | ~ (v1_relat_1 @ X59))),
% 2.74/2.93      inference('cnf', [status(esa)], [t3_funct_2])).
% 2.74/2.93  thf('253', plain,
% 2.74/2.93      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.74/2.93         (k1_zfmisc_1 @ 
% 2.74/2.93          (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))
% 2.74/2.93        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.74/2.93        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.74/2.93      inference('sup+', [status(thm)], ['251', '252'])).
% 2.74/2.93  thf('254', plain,
% 2.74/2.93      ((~ (v1_relat_1 @ sk_C)
% 2.74/2.93        | ~ (v1_funct_1 @ sk_C)
% 2.74/2.93        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 2.74/2.93        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.74/2.93           (k1_zfmisc_1 @ 
% 2.74/2.93            (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))))),
% 2.74/2.93      inference('sup-', [status(thm)], ['250', '253'])).
% 2.74/2.93  thf('255', plain, ((v1_relat_1 @ sk_C)),
% 2.74/2.93      inference('demod', [status(thm)], ['111', '112'])).
% 2.74/2.93  thf('256', plain, ((v1_funct_1 @ sk_C)),
% 2.74/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.93  thf('257', plain,
% 2.74/2.93      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 2.74/2.93        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.74/2.93           (k1_zfmisc_1 @ 
% 2.74/2.93            (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))))),
% 2.74/2.93      inference('demod', [status(thm)], ['254', '255', '256'])).
% 2.74/2.93  thf('258', plain,
% 2.74/2.93      ((~ (v1_relat_1 @ sk_C)
% 2.74/2.93        | ~ (v1_funct_1 @ sk_C)
% 2.74/2.93        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.74/2.93           (k1_zfmisc_1 @ 
% 2.74/2.93            (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))))),
% 2.74/2.93      inference('sup-', [status(thm)], ['249', '257'])).
% 2.74/2.93  thf('259', plain, ((v1_relat_1 @ sk_C)),
% 2.74/2.93      inference('demod', [status(thm)], ['111', '112'])).
% 2.74/2.93  thf('260', plain, ((v1_funct_1 @ sk_C)),
% 2.74/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.93  thf('261', plain,
% 2.74/2.93      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.74/2.93        (k1_zfmisc_1 @ 
% 2.74/2.93         (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 2.74/2.93      inference('demod', [status(thm)], ['258', '259', '260'])).
% 2.74/2.93  thf('262', plain,
% 2.74/2.93      (![X3 : $i, X4 : $i]:
% 2.74/2.93         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 2.74/2.93          | (v1_relat_1 @ X3)
% 2.74/2.93          | ~ (v1_relat_1 @ X4))),
% 2.74/2.93      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.74/2.93  thf('263', plain,
% 2.74/2.93      ((~ (v1_relat_1 @ 
% 2.74/2.93           (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 2.74/2.93        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 2.74/2.93      inference('sup-', [status(thm)], ['261', '262'])).
% 2.74/2.93  thf('264', plain,
% 2.74/2.93      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 2.74/2.93      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.74/2.93  thf('265', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 2.74/2.93      inference('demod', [status(thm)], ['263', '264'])).
% 2.74/2.93  thf('266', plain,
% 2.74/2.93      (![X0 : $i]:
% 2.74/2.93         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 2.74/2.93            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 2.74/2.93               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 2.74/2.93          | ~ (v1_relat_1 @ X0))),
% 2.74/2.93      inference('demod', [status(thm)], ['248', '265'])).
% 2.74/2.93  thf('267', plain,
% 2.74/2.93      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 2.74/2.93          = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 2.74/2.93             (k6_partfun1 @ (k2_relat_1 @ sk_C))))
% 2.74/2.93        | ~ (v1_relat_1 @ sk_C)
% 2.74/2.93        | ~ (v1_funct_1 @ sk_C)
% 2.74/2.93        | ~ (v2_funct_1 @ sk_C)
% 2.74/2.93        | ~ (v1_relat_1 @ sk_C))),
% 2.74/2.93      inference('sup+', [status(thm)], ['212', '266'])).
% 2.74/2.93  thf('268', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.74/2.93      inference('sup+', [status(thm)], ['104', '105'])).
% 2.74/2.93  thf('269', plain,
% 2.74/2.93      (![X20 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X20)) = (X20))),
% 2.74/2.93      inference('demod', [status(thm)], ['81', '82'])).
% 2.74/2.93  thf('270', plain,
% 2.74/2.93      (![X22 : $i]:
% 2.74/2.93         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X22)) @ X22) = (X22))
% 2.74/2.93          | ~ (v1_relat_1 @ X22))),
% 2.74/2.93      inference('demod', [status(thm)], ['65', '66'])).
% 2.74/2.93  thf('271', plain,
% 2.74/2.93      (![X0 : $i]:
% 2.74/2.93         (((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 2.74/2.93            = (k6_partfun1 @ X0))
% 2.74/2.93          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 2.74/2.93      inference('sup+', [status(thm)], ['269', '270'])).
% 2.74/2.93  thf('272', plain, (![X26 : $i]: (v1_relat_1 @ (k6_partfun1 @ X26))),
% 2.74/2.93      inference('demod', [status(thm)], ['73', '74'])).
% 2.74/2.93  thf('273', plain,
% 2.74/2.93      (![X0 : $i]:
% 2.74/2.93         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 2.74/2.93           = (k6_partfun1 @ X0))),
% 2.74/2.93      inference('demod', [status(thm)], ['271', '272'])).
% 2.74/2.93  thf('274', plain, ((v1_relat_1 @ sk_C)),
% 2.74/2.93      inference('demod', [status(thm)], ['111', '112'])).
% 2.74/2.93  thf('275', plain, ((v1_funct_1 @ sk_C)),
% 2.74/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.93  thf('276', plain, ((v2_funct_1 @ sk_C)),
% 2.74/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.93  thf('277', plain, ((v1_relat_1 @ sk_C)),
% 2.74/2.93      inference('demod', [status(thm)], ['111', '112'])).
% 2.74/2.93  thf('278', plain,
% 2.74/2.93      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 2.74/2.93      inference('demod', [status(thm)],
% 2.74/2.93                ['267', '268', '273', '274', '275', '276', '277'])).
% 2.74/2.93  thf('279', plain,
% 2.74/2.93      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.74/2.93         (~ (v1_relat_1 @ X17)
% 2.74/2.93          | ((k5_relat_1 @ (k5_relat_1 @ X18 @ X17) @ X19)
% 2.74/2.93              = (k5_relat_1 @ X18 @ (k5_relat_1 @ X17 @ X19)))
% 2.74/2.93          | ~ (v1_relat_1 @ X19)
% 2.74/2.93          | ~ (v1_relat_1 @ X18))),
% 2.74/2.93      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.74/2.93  thf('280', plain,
% 2.74/2.93      (![X0 : $i]:
% 2.74/2.93         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 2.74/2.93            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 2.74/2.93          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.74/2.93          | ~ (v1_relat_1 @ X0)
% 2.74/2.93          | ~ (v1_relat_1 @ sk_C))),
% 2.74/2.93      inference('sup+', [status(thm)], ['278', '279'])).
% 2.74/2.93  thf('281', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 2.74/2.93      inference('demod', [status(thm)], ['263', '264'])).
% 2.74/2.93  thf('282', plain, ((v1_relat_1 @ sk_C)),
% 2.74/2.93      inference('demod', [status(thm)], ['111', '112'])).
% 2.74/2.93  thf('283', plain,
% 2.74/2.93      (![X0 : $i]:
% 2.74/2.93         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 2.74/2.93            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 2.74/2.93          | ~ (v1_relat_1 @ X0))),
% 2.74/2.93      inference('demod', [status(thm)], ['280', '281', '282'])).
% 2.74/2.93  thf('284', plain,
% 2.74/2.93      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 2.74/2.93          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 2.74/2.93        | ~ (v1_relat_1 @ sk_D))),
% 2.74/2.93      inference('sup+', [status(thm)], ['209', '283'])).
% 2.74/2.93  thf('285', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 2.74/2.93      inference('sup-', [status(thm)], ['194', '195'])).
% 2.74/2.93  thf('286', plain,
% 2.74/2.93      (![X5 : $i, X6 : $i]:
% 2.74/2.93         (~ (v4_relat_1 @ X5 @ X6)
% 2.74/2.93          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 2.74/2.93          | ~ (v1_relat_1 @ X5))),
% 2.74/2.93      inference('cnf', [status(esa)], [d18_relat_1])).
% 2.74/2.93  thf('287', plain,
% 2.74/2.93      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 2.74/2.93      inference('sup-', [status(thm)], ['285', '286'])).
% 2.74/2.93  thf('288', plain, ((v1_relat_1 @ sk_C)),
% 2.74/2.93      inference('demod', [status(thm)], ['111', '112'])).
% 2.74/2.93  thf('289', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 2.74/2.93      inference('demod', [status(thm)], ['287', '288'])).
% 2.74/2.93  thf('290', plain,
% 2.74/2.93      (![X21 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X21)) = (X21))),
% 2.74/2.93      inference('demod', [status(thm)], ['76', '77'])).
% 2.74/2.93  thf(t79_relat_1, axiom,
% 2.74/2.93    (![A:$i,B:$i]:
% 2.74/2.93     ( ( v1_relat_1 @ B ) =>
% 2.74/2.93       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 2.74/2.93         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 2.74/2.93  thf('291', plain,
% 2.74/2.93      (![X23 : $i, X24 : $i]:
% 2.74/2.93         (~ (r1_tarski @ (k2_relat_1 @ X23) @ X24)
% 2.74/2.93          | ((k5_relat_1 @ X23 @ (k6_relat_1 @ X24)) = (X23))
% 2.74/2.93          | ~ (v1_relat_1 @ X23))),
% 2.74/2.93      inference('cnf', [status(esa)], [t79_relat_1])).
% 2.74/2.93  thf('292', plain, (![X58 : $i]: ((k6_partfun1 @ X58) = (k6_relat_1 @ X58))),
% 2.74/2.93      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.74/2.93  thf('293', plain,
% 2.74/2.93      (![X23 : $i, X24 : $i]:
% 2.74/2.93         (~ (r1_tarski @ (k2_relat_1 @ X23) @ X24)
% 2.74/2.93          | ((k5_relat_1 @ X23 @ (k6_partfun1 @ X24)) = (X23))
% 2.74/2.93          | ~ (v1_relat_1 @ X23))),
% 2.74/2.93      inference('demod', [status(thm)], ['291', '292'])).
% 2.74/2.93  thf('294', plain,
% 2.74/2.93      (![X0 : $i, X1 : $i]:
% 2.74/2.93         (~ (r1_tarski @ X0 @ X1)
% 2.74/2.93          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 2.74/2.93          | ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X1))
% 2.74/2.93              = (k6_partfun1 @ X0)))),
% 2.74/2.93      inference('sup-', [status(thm)], ['290', '293'])).
% 2.74/2.93  thf('295', plain, (![X26 : $i]: (v1_relat_1 @ (k6_partfun1 @ X26))),
% 2.74/2.93      inference('demod', [status(thm)], ['73', '74'])).
% 2.74/2.93  thf('296', plain,
% 2.74/2.93      (![X0 : $i, X1 : $i]:
% 2.74/2.93         (~ (r1_tarski @ X0 @ X1)
% 2.74/2.93          | ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X1))
% 2.74/2.93              = (k6_partfun1 @ X0)))),
% 2.74/2.93      inference('demod', [status(thm)], ['294', '295'])).
% 2.74/2.93  thf('297', plain,
% 2.74/2.93      (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ 
% 2.74/2.93         (k6_partfun1 @ sk_A)) = (k6_partfun1 @ (k1_relat_1 @ sk_C)))),
% 2.74/2.93      inference('sup-', [status(thm)], ['289', '296'])).
% 2.74/2.93  thf('298', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 2.74/2.93      inference('demod', [status(thm)], ['263', '264'])).
% 2.74/2.93  thf('299', plain,
% 2.74/2.93      (![X32 : $i]:
% 2.74/2.93         (~ (v2_funct_1 @ X32)
% 2.74/2.93          | ((k1_relat_1 @ X32) = (k2_relat_1 @ (k2_funct_1 @ X32)))
% 2.74/2.93          | ~ (v1_funct_1 @ X32)
% 2.74/2.93          | ~ (v1_relat_1 @ X32))),
% 2.74/2.93      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.74/2.93  thf('300', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.74/2.93      inference('simplify', [status(thm)], ['0'])).
% 2.74/2.93  thf('301', plain,
% 2.74/2.93      (![X23 : $i, X24 : $i]:
% 2.74/2.93         (~ (r1_tarski @ (k2_relat_1 @ X23) @ X24)
% 2.74/2.93          | ((k5_relat_1 @ X23 @ (k6_partfun1 @ X24)) = (X23))
% 2.74/2.93          | ~ (v1_relat_1 @ X23))),
% 2.74/2.93      inference('demod', [status(thm)], ['291', '292'])).
% 2.74/2.93  thf('302', plain,
% 2.74/2.93      (![X0 : $i]:
% 2.74/2.93         (~ (v1_relat_1 @ X0)
% 2.74/2.93          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) = (X0)))),
% 2.74/2.93      inference('sup-', [status(thm)], ['300', '301'])).
% 2.74/2.93  thf('303', plain,
% 2.74/2.93      (![X0 : $i]:
% 2.74/2.93         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 2.74/2.93            = (k2_funct_1 @ X0))
% 2.74/2.93          | ~ (v1_relat_1 @ X0)
% 2.74/2.93          | ~ (v1_funct_1 @ X0)
% 2.74/2.93          | ~ (v2_funct_1 @ X0)
% 2.74/2.93          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 2.74/2.93      inference('sup+', [status(thm)], ['299', '302'])).
% 2.74/2.93  thf('304', plain,
% 2.74/2.93      ((~ (v2_funct_1 @ sk_C)
% 2.74/2.93        | ~ (v1_funct_1 @ sk_C)
% 2.74/2.93        | ~ (v1_relat_1 @ sk_C)
% 2.74/2.93        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 2.74/2.93            (k6_partfun1 @ (k1_relat_1 @ sk_C))) = (k2_funct_1 @ sk_C)))),
% 2.74/2.93      inference('sup-', [status(thm)], ['298', '303'])).
% 2.74/2.93  thf('305', plain, ((v2_funct_1 @ sk_C)),
% 2.74/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.93  thf('306', plain, ((v1_funct_1 @ sk_C)),
% 2.74/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.93  thf('307', plain, ((v1_relat_1 @ sk_C)),
% 2.74/2.93      inference('demod', [status(thm)], ['111', '112'])).
% 2.74/2.93  thf('308', plain,
% 2.74/2.93      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 2.74/2.93         = (k2_funct_1 @ sk_C))),
% 2.74/2.93      inference('demod', [status(thm)], ['304', '305', '306', '307'])).
% 2.74/2.93  thf('309', plain,
% 2.74/2.93      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.74/2.93         (~ (v1_relat_1 @ X17)
% 2.74/2.93          | ((k5_relat_1 @ (k5_relat_1 @ X18 @ X17) @ X19)
% 2.74/2.93              = (k5_relat_1 @ X18 @ (k5_relat_1 @ X17 @ X19)))
% 2.74/2.93          | ~ (v1_relat_1 @ X19)
% 2.74/2.93          | ~ (v1_relat_1 @ X18))),
% 2.74/2.93      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.74/2.93  thf('310', plain,
% 2.74/2.93      (![X0 : $i]:
% 2.74/2.93         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 2.74/2.93            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 2.74/2.93               (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ X0)))
% 2.74/2.93          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.74/2.93          | ~ (v1_relat_1 @ X0)
% 2.74/2.93          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C))))),
% 2.74/2.93      inference('sup+', [status(thm)], ['308', '309'])).
% 2.74/2.93  thf('311', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 2.74/2.93      inference('demod', [status(thm)], ['263', '264'])).
% 2.74/2.93  thf('312', plain, (![X26 : $i]: (v1_relat_1 @ (k6_partfun1 @ X26))),
% 2.74/2.93      inference('demod', [status(thm)], ['73', '74'])).
% 2.74/2.93  thf('313', plain,
% 2.74/2.93      (![X0 : $i]:
% 2.74/2.93         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 2.74/2.93            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 2.74/2.93               (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ X0)))
% 2.74/2.93          | ~ (v1_relat_1 @ X0))),
% 2.74/2.93      inference('demod', [status(thm)], ['310', '311', '312'])).
% 2.74/2.93  thf('314', plain,
% 2.74/2.93      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 2.74/2.93          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 2.74/2.93             (k6_partfun1 @ (k1_relat_1 @ sk_C))))
% 2.74/2.93        | ~ (v1_relat_1 @ (k6_partfun1 @ sk_A)))),
% 2.74/2.93      inference('sup+', [status(thm)], ['297', '313'])).
% 2.74/2.93  thf('315', plain,
% 2.74/2.93      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 2.74/2.93         = (k2_funct_1 @ sk_C))),
% 2.74/2.93      inference('demod', [status(thm)], ['304', '305', '306', '307'])).
% 2.74/2.93  thf('316', plain, (![X26 : $i]: (v1_relat_1 @ (k6_partfun1 @ X26))),
% 2.74/2.93      inference('demod', [status(thm)], ['73', '74'])).
% 2.74/2.93  thf('317', plain,
% 2.74/2.93      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 2.74/2.93         = (k2_funct_1 @ sk_C))),
% 2.74/2.93      inference('demod', [status(thm)], ['314', '315', '316'])).
% 2.74/2.93  thf('318', plain, ((v1_relat_1 @ sk_D)),
% 2.74/2.93      inference('demod', [status(thm)], ['15', '16'])).
% 2.74/2.93  thf('319', plain,
% 2.74/2.93      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (k2_funct_1 @ sk_C))),
% 2.74/2.93      inference('demod', [status(thm)], ['284', '317', '318'])).
% 2.74/2.93  thf('320', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 2.74/2.93      inference('sup+', [status(thm)], ['208', '319'])).
% 2.74/2.93  thf('321', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 2.74/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.93  thf('322', plain, ($false),
% 2.74/2.93      inference('simplify_reflect-', [status(thm)], ['320', '321'])).
% 2.74/2.93  
% 2.74/2.93  % SZS output end Refutation
% 2.74/2.93  
% 2.74/2.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
