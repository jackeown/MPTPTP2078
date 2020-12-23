%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8NdVjlWnFq

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  202 (2189 expanded)
%              Number of leaves         :   35 ( 679 expanded)
%              Depth                    :   35
%              Number of atoms          : 1504 (30689 expanded)
%              Number of equality atoms :   63 (1114 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(t31_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( v2_funct_1 @ C )
            & ( ( k2_relset_1 @ A @ B @ C )
              = B ) )
         => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
            & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
            & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('6',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X16: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('8',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('9',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('14',plain,(
    ! [X16: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
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

thf('15',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k1_relat_1 @ X19 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('16',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k10_relat_1 @ X17 @ X18 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X17 ) @ X18 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('17',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('18',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k2_relat_1 @ X19 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('19',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('22',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('26',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k2_relat_1 @ X19 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['27'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('29',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X8 ) @ X9 )
      | ( v4_relat_1 @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['24','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('36',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf('39',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v4_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k1_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['19','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('43',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('46',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['18','46'])).

thf('48',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['22','23'])).

thf('49',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('50',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('51',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['47','48','49','50','51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('55',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14
        = ( k7_relat_1 @ X14 @ X15 ) )
      | ~ ( v4_relat_1 @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('58',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k9_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['53','60'])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('64',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k10_relat_1 @ sk_C @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['16','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('68',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('71',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['15','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('73',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['71','72','73','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('77',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( m1_subset_1 @ ( k8_relset_1 @ X21 @ X22 @ X20 @ X23 ) @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relset_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('80',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k8_relset_1 @ X28 @ X29 @ X27 @ X30 )
        = ( k10_relat_1 @ X27 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','81'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('83',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('84',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference('sup+',[status(thm)],['75','84'])).

thf('86',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k1_relat_1 @ X19 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('87',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X31 ) @ X32 )
      | ( v1_funct_2 @ X31 @ ( k1_relat_1 @ X31 ) @ X32 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['47','48','49','50','51','52'])).

thf('91',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('94',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['89','90','91','92','93'])).

thf('95',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','94'])).

thf('96',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('97',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','98'])).

thf('100',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('101',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('104',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('106',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['12','104','105'])).

thf('107',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','106'])).

thf('108',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference('sup+',[status(thm)],['75','84'])).

thf('109',plain,(
    ! [X16: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('110',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('111',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('112',plain,
    ( ( k10_relat_1 @ sk_C @ sk_B )
    = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['71','72','73','74'])).

thf('114',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k9_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('116',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X31 ) @ X32 )
      | ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X31 ) @ X32 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 )
      | ( m1_subset_1 @ ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['114','117'])).

thf('119',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['22','23'])).

thf('120',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('121',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k2_relat_1 @ X19 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ X0 )
        = ( k7_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = ( k7_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['120','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ X0 )
        = ( k7_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['119','125'])).

thf('127',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('128',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['126','127','128','129'])).

thf('131',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['126','127','128','129'])).

thf('132',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['47','48','49','50','51','52'])).

thf('133',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['126','127','128','129'])).

thf('134',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['126','127','128','129'])).

thf('135',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('136',plain,(
    ! [X16: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('137',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('138',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['71','72','73','74'])).

thf('139',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('141',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X31 ) @ X32 )
      | ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X31 ) @ X32 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['139','142'])).

thf('144',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['47','48','49','50','51','52'])).

thf('145',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['136','145'])).

thf('147',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('148',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['146','147','148'])).

thf('150',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['135','149'])).

thf('151',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('152',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['150','151','152'])).

thf('154',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('155',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('157',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['118','130','131','132','133','134','157','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','159'])).

thf('161',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('162',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['160','161','162'])).

thf('164',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['108','163'])).

thf('165',plain,(
    $false ),
    inference(demod,[status(thm)],['107','164'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8NdVjlWnFq
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:28:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.58  % Solved by: fo/fo7.sh
% 0.21/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.58  % done 251 iterations in 0.120s
% 0.21/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.58  % SZS output start Refutation
% 0.21/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.58  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.58  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.58  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.58  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.58  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.58  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.58  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.58  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.58  thf(t31_funct_2, conjecture,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.58       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.21/0.58         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.21/0.58           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.21/0.58           ( m1_subset_1 @
% 0.21/0.58             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.21/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.58    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.58        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.58            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.58          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.21/0.58            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.21/0.58              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.21/0.58              ( m1_subset_1 @
% 0.21/0.58                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 0.21/0.58    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 0.21/0.58  thf('0', plain,
% 0.21/0.58      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.58        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.21/0.58        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.58             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('1', plain,
% 0.21/0.58      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.58           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.21/0.58         <= (~
% 0.21/0.58             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.58               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.21/0.58      inference('split', [status(esa)], ['0'])).
% 0.21/0.58  thf('2', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(cc2_relat_1, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( v1_relat_1 @ A ) =>
% 0.21/0.58       ( ![B:$i]:
% 0.21/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.58  thf('3', plain,
% 0.21/0.58      (![X6 : $i, X7 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.21/0.58          | (v1_relat_1 @ X6)
% 0.21/0.58          | ~ (v1_relat_1 @ X7))),
% 0.21/0.58      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.58  thf('4', plain,
% 0.21/0.58      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.21/0.58      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.58  thf(fc6_relat_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.58  thf('5', plain,
% 0.21/0.58      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.21/0.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.58  thf('6', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.58      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.58  thf(dt_k2_funct_1, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.58       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.21/0.58         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.21/0.58  thf('7', plain,
% 0.21/0.58      (![X16 : $i]:
% 0.21/0.58         ((v1_funct_1 @ (k2_funct_1 @ X16))
% 0.21/0.58          | ~ (v1_funct_1 @ X16)
% 0.21/0.58          | ~ (v1_relat_1 @ X16))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.58  thf('8', plain,
% 0.21/0.58      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.21/0.58         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.21/0.58      inference('split', [status(esa)], ['0'])).
% 0.21/0.58  thf('9', plain,
% 0.21/0.58      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 0.21/0.58         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.58  thf('10', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('11', plain,
% 0.21/0.58      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.21/0.58      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.58  thf('12', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['6', '11'])).
% 0.21/0.58  thf('13', plain,
% 0.21/0.58      (![X16 : $i]:
% 0.21/0.58         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 0.21/0.58          | ~ (v1_funct_1 @ X16)
% 0.21/0.58          | ~ (v1_relat_1 @ X16))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.58  thf('14', plain,
% 0.21/0.58      (![X16 : $i]:
% 0.21/0.58         ((v1_funct_1 @ (k2_funct_1 @ X16))
% 0.21/0.58          | ~ (v1_funct_1 @ X16)
% 0.21/0.58          | ~ (v1_relat_1 @ X16))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.58  thf(t55_funct_1, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.58       ( ( v2_funct_1 @ A ) =>
% 0.21/0.58         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.21/0.58           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.21/0.58  thf('15', plain,
% 0.21/0.58      (![X19 : $i]:
% 0.21/0.58         (~ (v2_funct_1 @ X19)
% 0.21/0.58          | ((k1_relat_1 @ X19) = (k2_relat_1 @ (k2_funct_1 @ X19)))
% 0.21/0.58          | ~ (v1_funct_1 @ X19)
% 0.21/0.58          | ~ (v1_relat_1 @ X19))),
% 0.21/0.58      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.21/0.58  thf(t155_funct_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.58       ( ( v2_funct_1 @ B ) =>
% 0.21/0.58         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.21/0.58  thf('16', plain,
% 0.21/0.58      (![X17 : $i, X18 : $i]:
% 0.21/0.58         (~ (v2_funct_1 @ X17)
% 0.21/0.58          | ((k10_relat_1 @ X17 @ X18)
% 0.21/0.58              = (k9_relat_1 @ (k2_funct_1 @ X17) @ X18))
% 0.21/0.58          | ~ (v1_funct_1 @ X17)
% 0.21/0.58          | ~ (v1_relat_1 @ X17))),
% 0.21/0.58      inference('cnf', [status(esa)], [t155_funct_1])).
% 0.21/0.58  thf('17', plain,
% 0.21/0.58      (![X16 : $i]:
% 0.21/0.58         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 0.21/0.58          | ~ (v1_funct_1 @ X16)
% 0.21/0.58          | ~ (v1_relat_1 @ X16))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.58  thf('18', plain,
% 0.21/0.58      (![X19 : $i]:
% 0.21/0.58         (~ (v2_funct_1 @ X19)
% 0.21/0.58          | ((k2_relat_1 @ X19) = (k1_relat_1 @ (k2_funct_1 @ X19)))
% 0.21/0.58          | ~ (v1_funct_1 @ X19)
% 0.21/0.58          | ~ (v1_relat_1 @ X19))),
% 0.21/0.58      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.21/0.58  thf('19', plain,
% 0.21/0.58      (![X16 : $i]:
% 0.21/0.58         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 0.21/0.58          | ~ (v1_funct_1 @ X16)
% 0.21/0.58          | ~ (v1_relat_1 @ X16))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.58  thf('20', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.58       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.58  thf('21', plain,
% 0.21/0.58      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.58         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 0.21/0.58          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.21/0.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.58  thf('22', plain,
% 0.21/0.58      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.21/0.58      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.58  thf('23', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('24', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.21/0.58      inference('sup+', [status(thm)], ['22', '23'])).
% 0.21/0.58  thf('25', plain,
% 0.21/0.58      (![X16 : $i]:
% 0.21/0.58         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 0.21/0.58          | ~ (v1_funct_1 @ X16)
% 0.21/0.58          | ~ (v1_relat_1 @ X16))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.58  thf('26', plain,
% 0.21/0.58      (![X19 : $i]:
% 0.21/0.58         (~ (v2_funct_1 @ X19)
% 0.21/0.58          | ((k2_relat_1 @ X19) = (k1_relat_1 @ (k2_funct_1 @ X19)))
% 0.21/0.58          | ~ (v1_funct_1 @ X19)
% 0.21/0.58          | ~ (v1_relat_1 @ X19))),
% 0.21/0.58      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.21/0.58  thf(d10_xboole_0, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.58  thf('27', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.58  thf('28', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.58      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.58  thf(d18_relat_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( v1_relat_1 @ B ) =>
% 0.21/0.58       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.58  thf('29', plain,
% 0.21/0.58      (![X8 : $i, X9 : $i]:
% 0.21/0.58         (~ (r1_tarski @ (k1_relat_1 @ X8) @ X9)
% 0.21/0.58          | (v4_relat_1 @ X8 @ X9)
% 0.21/0.58          | ~ (v1_relat_1 @ X8))),
% 0.21/0.58      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.21/0.58  thf('30', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.58  thf('31', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.21/0.58          | ~ (v1_relat_1 @ X0)
% 0.21/0.58          | ~ (v1_funct_1 @ X0)
% 0.21/0.58          | ~ (v2_funct_1 @ X0)
% 0.21/0.58          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['26', '30'])).
% 0.21/0.58  thf('32', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ X0)
% 0.21/0.58          | ~ (v1_funct_1 @ X0)
% 0.21/0.58          | ~ (v2_funct_1 @ X0)
% 0.21/0.58          | ~ (v1_funct_1 @ X0)
% 0.21/0.58          | ~ (v1_relat_1 @ X0)
% 0.21/0.58          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['25', '31'])).
% 0.21/0.58  thf('33', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.21/0.58          | ~ (v2_funct_1 @ X0)
% 0.21/0.58          | ~ (v1_funct_1 @ X0)
% 0.21/0.58          | ~ (v1_relat_1 @ X0))),
% 0.21/0.58      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.58  thf('34', plain,
% 0.21/0.58      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)
% 0.21/0.58        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.58        | ~ (v2_funct_1 @ sk_C))),
% 0.21/0.58      inference('sup+', [status(thm)], ['24', '33'])).
% 0.21/0.58  thf('35', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.58      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.58  thf('36', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('37', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('38', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)),
% 0.21/0.58      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 0.21/0.58  thf('39', plain,
% 0.21/0.58      (![X8 : $i, X9 : $i]:
% 0.21/0.58         (~ (v4_relat_1 @ X8 @ X9)
% 0.21/0.58          | (r1_tarski @ (k1_relat_1 @ X8) @ X9)
% 0.21/0.58          | ~ (v1_relat_1 @ X8))),
% 0.21/0.58      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.21/0.58  thf('40', plain,
% 0.21/0.58      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.58        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 0.21/0.58      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.58  thf('41', plain,
% 0.21/0.58      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.58        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 0.21/0.58      inference('sup-', [status(thm)], ['19', '40'])).
% 0.21/0.58  thf('42', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.58      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.58  thf('43', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('44', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B)),
% 0.21/0.58      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.21/0.58  thf('45', plain,
% 0.21/0.58      (![X0 : $i, X2 : $i]:
% 0.21/0.58         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.58  thf('46', plain,
% 0.21/0.58      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.21/0.58        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.58  thf('47', plain,
% 0.21/0.58      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C))
% 0.21/0.58        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.58        | ~ (v2_funct_1 @ sk_C)
% 0.21/0.58        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['18', '46'])).
% 0.21/0.58  thf('48', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.21/0.58      inference('sup+', [status(thm)], ['22', '23'])).
% 0.21/0.58  thf('49', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.58      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.58  thf('50', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.58      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.58  thf('51', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('52', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('53', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.58      inference('demod', [status(thm)], ['47', '48', '49', '50', '51', '52'])).
% 0.21/0.58  thf('54', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.58  thf(t209_relat_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.21/0.58       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.21/0.58  thf('55', plain,
% 0.21/0.58      (![X14 : $i, X15 : $i]:
% 0.21/0.58         (((X14) = (k7_relat_1 @ X14 @ X15))
% 0.21/0.58          | ~ (v4_relat_1 @ X14 @ X15)
% 0.21/0.58          | ~ (v1_relat_1 @ X14))),
% 0.21/0.58      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.21/0.58  thf('56', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ X0)
% 0.21/0.58          | ~ (v1_relat_1 @ X0)
% 0.21/0.58          | ((X0) = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.58  thf('57', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (((X0) = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))) | ~ (v1_relat_1 @ X0))),
% 0.21/0.58      inference('simplify', [status(thm)], ['56'])).
% 0.21/0.58  thf(t148_relat_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( v1_relat_1 @ B ) =>
% 0.21/0.58       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.21/0.58  thf('58', plain,
% 0.21/0.58      (![X12 : $i, X13 : $i]:
% 0.21/0.58         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 0.21/0.58          | ~ (v1_relat_1 @ X12))),
% 0.21/0.58      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.58  thf('59', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.21/0.58          | ~ (v1_relat_1 @ X0)
% 0.21/0.58          | ~ (v1_relat_1 @ X0))),
% 0.21/0.58      inference('sup+', [status(thm)], ['57', '58'])).
% 0.21/0.58  thf('60', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ X0)
% 0.21/0.58          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.21/0.58      inference('simplify', [status(thm)], ['59'])).
% 0.21/0.58  thf('61', plain,
% 0.21/0.58      ((((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.58          = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B))
% 0.21/0.58        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['53', '60'])).
% 0.21/0.58  thf('62', plain,
% 0.21/0.58      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.58        | ((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.58            = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['17', '61'])).
% 0.21/0.58  thf('63', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.58      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.58  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('65', plain,
% 0.21/0.58      (((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.58         = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B))),
% 0.21/0.58      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.21/0.58  thf('66', plain,
% 0.21/0.58      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k10_relat_1 @ sk_C @ sk_B))
% 0.21/0.58        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.58        | ~ (v2_funct_1 @ sk_C))),
% 0.21/0.58      inference('sup+', [status(thm)], ['16', '65'])).
% 0.21/0.58  thf('67', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.58      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.58  thf('68', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('69', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('70', plain,
% 0.21/0.58      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k10_relat_1 @ sk_C @ sk_B))),
% 0.21/0.58      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 0.21/0.58  thf('71', plain,
% 0.21/0.58      ((((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_B))
% 0.21/0.58        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.58        | ~ (v2_funct_1 @ sk_C))),
% 0.21/0.58      inference('sup+', [status(thm)], ['15', '70'])).
% 0.21/0.58  thf('72', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.58      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.58  thf('73', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('74', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('75', plain, (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_B))),
% 0.21/0.58      inference('demod', [status(thm)], ['71', '72', '73', '74'])).
% 0.21/0.58  thf('76', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(dt_k8_relset_1, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.58       ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.58  thf('77', plain,
% 0.21/0.58      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.21/0.58          | (m1_subset_1 @ (k8_relset_1 @ X21 @ X22 @ X20 @ X23) @ 
% 0.21/0.58             (k1_zfmisc_1 @ X21)))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_k8_relset_1])).
% 0.21/0.58  thf('78', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (m1_subset_1 @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.21/0.58          (k1_zfmisc_1 @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['76', '77'])).
% 0.21/0.58  thf('79', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(redefinition_k8_relset_1, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.58       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.21/0.58  thf('80', plain,
% 0.21/0.58      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.21/0.58          | ((k8_relset_1 @ X28 @ X29 @ X27 @ X30) = (k10_relat_1 @ X27 @ X30)))),
% 0.21/0.58      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.21/0.58  thf('81', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['79', '80'])).
% 0.21/0.58  thf('82', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (m1_subset_1 @ (k10_relat_1 @ sk_C @ X0) @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.58      inference('demod', [status(thm)], ['78', '81'])).
% 0.21/0.58  thf(t3_subset, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.58  thf('83', plain,
% 0.21/0.58      (![X3 : $i, X4 : $i]:
% 0.21/0.58         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.21/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.58  thf('84', plain,
% 0.21/0.58      (![X0 : $i]: (r1_tarski @ (k10_relat_1 @ sk_C @ X0) @ sk_A)),
% 0.21/0.58      inference('sup-', [status(thm)], ['82', '83'])).
% 0.21/0.58  thf('85', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.21/0.58      inference('sup+', [status(thm)], ['75', '84'])).
% 0.21/0.58  thf('86', plain,
% 0.21/0.58      (![X19 : $i]:
% 0.21/0.58         (~ (v2_funct_1 @ X19)
% 0.21/0.58          | ((k1_relat_1 @ X19) = (k2_relat_1 @ (k2_funct_1 @ X19)))
% 0.21/0.58          | ~ (v1_funct_1 @ X19)
% 0.21/0.58          | ~ (v1_relat_1 @ X19))),
% 0.21/0.58      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.21/0.58  thf(t4_funct_2, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.58       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.21/0.58         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.21/0.58           ( m1_subset_1 @
% 0.21/0.58             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.21/0.58  thf('87', plain,
% 0.21/0.58      (![X31 : $i, X32 : $i]:
% 0.21/0.58         (~ (r1_tarski @ (k2_relat_1 @ X31) @ X32)
% 0.21/0.58          | (v1_funct_2 @ X31 @ (k1_relat_1 @ X31) @ X32)
% 0.21/0.58          | ~ (v1_funct_1 @ X31)
% 0.21/0.58          | ~ (v1_relat_1 @ X31))),
% 0.21/0.58      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.21/0.58  thf('88', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.21/0.58          | ~ (v1_relat_1 @ X0)
% 0.21/0.58          | ~ (v1_funct_1 @ X0)
% 0.21/0.58          | ~ (v2_funct_1 @ X0)
% 0.21/0.58          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.58          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.58          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 0.21/0.58             (k1_relat_1 @ (k2_funct_1 @ X0)) @ X1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['86', '87'])).
% 0.21/0.58  thf('89', plain,
% 0.21/0.58      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.58         (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)
% 0.21/0.58        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.58        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.58        | ~ (v2_funct_1 @ sk_C)
% 0.21/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.58        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.58      inference('sup-', [status(thm)], ['85', '88'])).
% 0.21/0.58  thf('90', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.58      inference('demod', [status(thm)], ['47', '48', '49', '50', '51', '52'])).
% 0.21/0.58  thf('91', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('92', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('93', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.58      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.58  thf('94', plain,
% 0.21/0.58      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.21/0.58        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.58        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.58      inference('demod', [status(thm)], ['89', '90', '91', '92', '93'])).
% 0.21/0.58  thf('95', plain,
% 0.21/0.58      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.58        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.58        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['14', '94'])).
% 0.21/0.58  thf('96', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.58      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.58  thf('97', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('98', plain,
% 0.21/0.58      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.58        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 0.21/0.58      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.21/0.58  thf('99', plain,
% 0.21/0.58      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.58        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['13', '98'])).
% 0.21/0.58  thf('100', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.58      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.58  thf('101', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('102', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 0.21/0.58      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.21/0.58  thf('103', plain,
% 0.21/0.58      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 0.21/0.58         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.21/0.58      inference('split', [status(esa)], ['0'])).
% 0.21/0.58  thf('104', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['102', '103'])).
% 0.21/0.58  thf('105', plain,
% 0.21/0.58      (~
% 0.21/0.58       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.58         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 0.21/0.58       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 0.21/0.58       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.58      inference('split', [status(esa)], ['0'])).
% 0.21/0.58  thf('106', plain,
% 0.21/0.58      (~
% 0.21/0.58       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.58         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.21/0.58      inference('sat_resolution*', [status(thm)], ['12', '104', '105'])).
% 0.21/0.58  thf('107', plain,
% 0.21/0.58      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.58          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.58      inference('simpl_trail', [status(thm)], ['1', '106'])).
% 0.21/0.58  thf('108', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.21/0.58      inference('sup+', [status(thm)], ['75', '84'])).
% 0.21/0.58  thf('109', plain,
% 0.21/0.58      (![X16 : $i]:
% 0.21/0.58         ((v1_funct_1 @ (k2_funct_1 @ X16))
% 0.21/0.58          | ~ (v1_funct_1 @ X16)
% 0.21/0.58          | ~ (v1_relat_1 @ X16))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.58  thf('110', plain,
% 0.21/0.58      (((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.58         = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B))),
% 0.21/0.58      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.21/0.58  thf('111', plain,
% 0.21/0.58      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k10_relat_1 @ sk_C @ sk_B))),
% 0.21/0.58      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 0.21/0.58  thf('112', plain,
% 0.21/0.58      (((k10_relat_1 @ sk_C @ sk_B) = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B))),
% 0.21/0.58      inference('demod', [status(thm)], ['110', '111'])).
% 0.21/0.58  thf('113', plain, (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_B))),
% 0.21/0.58      inference('demod', [status(thm)], ['71', '72', '73', '74'])).
% 0.21/0.58  thf('114', plain,
% 0.21/0.58      (((k1_relat_1 @ sk_C) = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B))),
% 0.21/0.58      inference('demod', [status(thm)], ['112', '113'])).
% 0.21/0.58  thf('115', plain,
% 0.21/0.58      (![X12 : $i, X13 : $i]:
% 0.21/0.58         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 0.21/0.58          | ~ (v1_relat_1 @ X12))),
% 0.21/0.58      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.58  thf('116', plain,
% 0.21/0.58      (![X31 : $i, X32 : $i]:
% 0.21/0.58         (~ (r1_tarski @ (k2_relat_1 @ X31) @ X32)
% 0.21/0.58          | (m1_subset_1 @ X31 @ 
% 0.21/0.58             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X31) @ X32)))
% 0.21/0.58          | ~ (v1_funct_1 @ X31)
% 0.21/0.58          | ~ (v1_relat_1 @ X31))),
% 0.21/0.58      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.21/0.58  thf('117', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.58         (~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 0.21/0.58          | ~ (v1_relat_1 @ X1)
% 0.21/0.58          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.21/0.58          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 0.21/0.58          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.21/0.58             (k1_zfmisc_1 @ 
% 0.21/0.58              (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['115', '116'])).
% 0.21/0.58  thf('118', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0)
% 0.21/0.58          | (m1_subset_1 @ (k7_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B) @ 
% 0.21/0.58             (k1_zfmisc_1 @ 
% 0.21/0.58              (k2_zfmisc_1 @ 
% 0.21/0.58               (k1_relat_1 @ (k7_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)) @ X0)))
% 0.21/0.58          | ~ (v1_funct_1 @ (k7_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B))
% 0.21/0.58          | ~ (v1_relat_1 @ (k7_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B))
% 0.21/0.58          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['114', '117'])).
% 0.21/0.58  thf('119', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.21/0.58      inference('sup+', [status(thm)], ['22', '23'])).
% 0.21/0.58  thf('120', plain,
% 0.21/0.58      (![X16 : $i]:
% 0.21/0.58         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 0.21/0.58          | ~ (v1_funct_1 @ X16)
% 0.21/0.58          | ~ (v1_relat_1 @ X16))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.58  thf('121', plain,
% 0.21/0.58      (![X19 : $i]:
% 0.21/0.58         (~ (v2_funct_1 @ X19)
% 0.21/0.58          | ((k2_relat_1 @ X19) = (k1_relat_1 @ (k2_funct_1 @ X19)))
% 0.21/0.58          | ~ (v1_funct_1 @ X19)
% 0.21/0.58          | ~ (v1_relat_1 @ X19))),
% 0.21/0.58      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.21/0.58  thf('122', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (((X0) = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))) | ~ (v1_relat_1 @ X0))),
% 0.21/0.58      inference('simplify', [status(thm)], ['56'])).
% 0.21/0.58  thf('123', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (((k2_funct_1 @ X0)
% 0.21/0.58            = (k7_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.21/0.58          | ~ (v1_relat_1 @ X0)
% 0.21/0.58          | ~ (v1_funct_1 @ X0)
% 0.21/0.58          | ~ (v2_funct_1 @ X0)
% 0.21/0.58          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['121', '122'])).
% 0.21/0.58  thf('124', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ X0)
% 0.21/0.58          | ~ (v1_funct_1 @ X0)
% 0.21/0.58          | ~ (v2_funct_1 @ X0)
% 0.21/0.58          | ~ (v1_funct_1 @ X0)
% 0.21/0.58          | ~ (v1_relat_1 @ X0)
% 0.21/0.58          | ((k2_funct_1 @ X0)
% 0.21/0.58              = (k7_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['120', '123'])).
% 0.21/0.58  thf('125', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (((k2_funct_1 @ X0)
% 0.21/0.58            = (k7_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.21/0.58          | ~ (v2_funct_1 @ X0)
% 0.21/0.58          | ~ (v1_funct_1 @ X0)
% 0.21/0.58          | ~ (v1_relat_1 @ X0))),
% 0.21/0.58      inference('simplify', [status(thm)], ['124'])).
% 0.21/0.58  thf('126', plain,
% 0.21/0.58      ((((k2_funct_1 @ sk_C) = (k7_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B))
% 0.21/0.58        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.58        | ~ (v2_funct_1 @ sk_C))),
% 0.21/0.58      inference('sup+', [status(thm)], ['119', '125'])).
% 0.21/0.58  thf('127', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.58      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.58  thf('128', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('129', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('130', plain,
% 0.21/0.58      (((k2_funct_1 @ sk_C) = (k7_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B))),
% 0.21/0.58      inference('demod', [status(thm)], ['126', '127', '128', '129'])).
% 0.21/0.58  thf('131', plain,
% 0.21/0.58      (((k2_funct_1 @ sk_C) = (k7_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B))),
% 0.21/0.58      inference('demod', [status(thm)], ['126', '127', '128', '129'])).
% 0.21/0.58  thf('132', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.58      inference('demod', [status(thm)], ['47', '48', '49', '50', '51', '52'])).
% 0.21/0.58  thf('133', plain,
% 0.21/0.58      (((k2_funct_1 @ sk_C) = (k7_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B))),
% 0.21/0.58      inference('demod', [status(thm)], ['126', '127', '128', '129'])).
% 0.21/0.58  thf('134', plain,
% 0.21/0.58      (((k2_funct_1 @ sk_C) = (k7_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B))),
% 0.21/0.58      inference('demod', [status(thm)], ['126', '127', '128', '129'])).
% 0.21/0.58  thf('135', plain,
% 0.21/0.58      (![X16 : $i]:
% 0.21/0.58         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 0.21/0.58          | ~ (v1_funct_1 @ X16)
% 0.21/0.58          | ~ (v1_relat_1 @ X16))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.58  thf('136', plain,
% 0.21/0.58      (![X16 : $i]:
% 0.21/0.58         ((v1_funct_1 @ (k2_funct_1 @ X16))
% 0.21/0.58          | ~ (v1_funct_1 @ X16)
% 0.21/0.58          | ~ (v1_relat_1 @ X16))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.58  thf('137', plain,
% 0.21/0.58      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k10_relat_1 @ sk_C @ sk_B))),
% 0.21/0.58      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 0.21/0.58  thf('138', plain, (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_B))),
% 0.21/0.58      inference('demod', [status(thm)], ['71', '72', '73', '74'])).
% 0.21/0.58  thf('139', plain,
% 0.21/0.58      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.21/0.58      inference('demod', [status(thm)], ['137', '138'])).
% 0.21/0.58  thf('140', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.58      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.58  thf('141', plain,
% 0.21/0.58      (![X31 : $i, X32 : $i]:
% 0.21/0.58         (~ (r1_tarski @ (k2_relat_1 @ X31) @ X32)
% 0.21/0.58          | (m1_subset_1 @ X31 @ 
% 0.21/0.58             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X31) @ X32)))
% 0.21/0.58          | ~ (v1_funct_1 @ X31)
% 0.21/0.58          | ~ (v1_relat_1 @ X31))),
% 0.21/0.58      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.21/0.58  thf('142', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ X0)
% 0.21/0.58          | ~ (v1_funct_1 @ X0)
% 0.21/0.58          | (m1_subset_1 @ X0 @ 
% 0.21/0.58             (k1_zfmisc_1 @ 
% 0.21/0.58              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['140', '141'])).
% 0.21/0.58  thf('143', plain,
% 0.21/0.58      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.58         (k1_zfmisc_1 @ 
% 0.21/0.58          (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.21/0.58           (k1_relat_1 @ sk_C))))
% 0.21/0.58        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.58        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['139', '142'])).
% 0.21/0.58  thf('144', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.58      inference('demod', [status(thm)], ['47', '48', '49', '50', '51', '52'])).
% 0.21/0.58  thf('145', plain,
% 0.21/0.58      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.58         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C))))
% 0.21/0.58        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.58        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.58      inference('demod', [status(thm)], ['143', '144'])).
% 0.21/0.58  thf('146', plain,
% 0.21/0.58      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.58        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.58        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.58           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C)))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['136', '145'])).
% 0.21/0.58  thf('147', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.58      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.58  thf('148', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('149', plain,
% 0.21/0.58      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.58        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.58           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C)))))),
% 0.21/0.58      inference('demod', [status(thm)], ['146', '147', '148'])).
% 0.21/0.58  thf('150', plain,
% 0.21/0.58      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.58        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.58           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C)))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['135', '149'])).
% 0.21/0.58  thf('151', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.58      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.58  thf('152', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('153', plain,
% 0.21/0.58      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C))))),
% 0.21/0.58      inference('demod', [status(thm)], ['150', '151', '152'])).
% 0.21/0.58  thf('154', plain,
% 0.21/0.58      (![X6 : $i, X7 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.21/0.58          | (v1_relat_1 @ X6)
% 0.21/0.58          | ~ (v1_relat_1 @ X7))),
% 0.21/0.58      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.58  thf('155', plain,
% 0.21/0.58      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C)))
% 0.21/0.58        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['153', '154'])).
% 0.21/0.58  thf('156', plain,
% 0.21/0.58      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.21/0.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.58  thf('157', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.21/0.58      inference('demod', [status(thm)], ['155', '156'])).
% 0.21/0.58  thf('158', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.21/0.58      inference('demod', [status(thm)], ['155', '156'])).
% 0.21/0.58  thf('159', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0)
% 0.21/0.58          | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.58             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.21/0.58          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.58      inference('demod', [status(thm)],
% 0.21/0.58                ['118', '130', '131', '132', '133', '134', '157', '158'])).
% 0.21/0.58  thf('160', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ sk_C)
% 0.21/0.58          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.58          | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.58             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.21/0.58          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['109', '159'])).
% 0.21/0.58  thf('161', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.58      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.58  thf('162', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('163', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.58           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.21/0.58          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 0.21/0.58      inference('demod', [status(thm)], ['160', '161', '162'])).
% 0.21/0.58  thf('164', plain,
% 0.21/0.58      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['108', '163'])).
% 0.21/0.58  thf('165', plain, ($false), inference('demod', [status(thm)], ['107', '164'])).
% 0.21/0.58  
% 0.21/0.58  % SZS output end Refutation
% 0.21/0.58  
% 0.42/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
