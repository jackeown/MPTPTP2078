%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VmspXFOjIw

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 518 expanded)
%              Number of leaves         :   32 ( 168 expanded)
%              Depth                    :   23
%              Number of atoms          : 1081 (8325 expanded)
%              Number of equality atoms :   41 ( 298 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('4',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X5: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X10 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('12',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k1_relat_1 @ X10 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k10_relat_1 @ X8 @ X9 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X8 ) @ X9 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('14',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('15',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X10 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('23',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v4_relat_1 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('24',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3
        = ( k7_relat_1 @ X3 @ X4 ) )
      | ~ ( v4_relat_1 @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('28',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) )
        = ( k9_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('30',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('32',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t152_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )).

thf('33',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( r1_tarski @ ( k10_relat_1 @ X6 @ ( k9_relat_1 @ X6 @ X7 ) ) @ X7 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf('34',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('36',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf('39',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['21','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('41',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['12','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('46',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['44','45','46','47'])).

thf('49',plain,(
    ! [X5: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('50',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('52',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('53',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('57',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_B )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('59',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( k10_relat_1 @ sk_C @ sk_B )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('62',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k1_relat_1 @ X10 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('63',plain,
    ( ( k10_relat_1 @ sk_C @ sk_B )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('64',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_B )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('66',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( k10_relat_1 @ sk_C @ sk_B )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['64','65','66','67'])).

thf('69',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['61','68'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('70',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X21 )
      | ( v1_funct_2 @ X20 @ ( k1_relat_1 @ X20 ) @ X21 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('74',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('78',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ),
    inference('sup-',[status(thm)],['48','79'])).

thf('81',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['11','80'])).

thf('82',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['53','54'])).

thf('83',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('84',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['81','82','83','84','85'])).

thf('87',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('88',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('90',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','88','89'])).

thf('91',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','90'])).

thf('92',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X10 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('93',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['44','45','46','47'])).

thf('94',plain,(
    ! [X5: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('95',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('96',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['61','68'])).

thf('97',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X21 )
      | ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X20 ) @ X21 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('101',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['94','102'])).

thf('104',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('105',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['93','106'])).

thf('108',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['92','107'])).

thf('109',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['53','54'])).

thf('110',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('111',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['108','109','110','111','112'])).

thf('114',plain,(
    $false ),
    inference(demod,[status(thm)],['91','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VmspXFOjIw
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 13:31:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 107 iterations in 0.070s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.55  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.55  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.55  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.55  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.55  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.55  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.55  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.55  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.55  thf(t31_funct_2, conjecture,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.55       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.21/0.55         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.21/0.55           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.21/0.55           ( m1_subset_1 @
% 0.21/0.55             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.55        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.55            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.55          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.21/0.55            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.21/0.55              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.21/0.55              ( m1_subset_1 @
% 0.21/0.55                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 0.21/0.55  thf('0', plain,
% 0.21/0.55      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.55        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.21/0.55        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.55             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.21/0.55         <= (~
% 0.21/0.55             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.55               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(cc1_relset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.55       ( v1_relat_1 @ C ) ))).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.55         ((v1_relat_1 @ X11)
% 0.21/0.55          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.21/0.55      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.55  thf('4', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.55  thf(dt_k2_funct_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.55       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.21/0.55         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (![X5 : $i]:
% 0.21/0.55         ((v1_funct_1 @ (k2_funct_1 @ X5))
% 0.21/0.55          | ~ (v1_funct_1 @ X5)
% 0.21/0.55          | ~ (v1_relat_1 @ X5))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.21/0.55         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 0.21/0.55         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.55  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.21/0.55      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.55  thf('10', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['4', '9'])).
% 0.21/0.55  thf(t55_funct_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.55       ( ( v2_funct_1 @ A ) =>
% 0.21/0.55         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.21/0.55           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (![X10 : $i]:
% 0.21/0.55         (~ (v2_funct_1 @ X10)
% 0.21/0.55          | ((k2_relat_1 @ X10) = (k1_relat_1 @ (k2_funct_1 @ X10)))
% 0.21/0.55          | ~ (v1_funct_1 @ X10)
% 0.21/0.55          | ~ (v1_relat_1 @ X10))),
% 0.21/0.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (![X10 : $i]:
% 0.21/0.55         (~ (v2_funct_1 @ X10)
% 0.21/0.55          | ((k1_relat_1 @ X10) = (k2_relat_1 @ (k2_funct_1 @ X10)))
% 0.21/0.55          | ~ (v1_funct_1 @ X10)
% 0.21/0.55          | ~ (v1_relat_1 @ X10))),
% 0.21/0.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.21/0.55  thf(t155_funct_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.55       ( ( v2_funct_1 @ B ) =>
% 0.21/0.55         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      (![X8 : $i, X9 : $i]:
% 0.21/0.55         (~ (v2_funct_1 @ X8)
% 0.21/0.55          | ((k10_relat_1 @ X8 @ X9) = (k9_relat_1 @ (k2_funct_1 @ X8) @ X9))
% 0.21/0.55          | ~ (v1_funct_1 @ X8)
% 0.21/0.55          | ~ (v1_relat_1 @ X8))),
% 0.21/0.55      inference('cnf', [status(esa)], [t155_funct_1])).
% 0.21/0.55  thf('14', plain,
% 0.21/0.55      (![X5 : $i]:
% 0.21/0.55         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 0.21/0.55          | ~ (v1_funct_1 @ X5)
% 0.21/0.55          | ~ (v1_relat_1 @ X5))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      (![X10 : $i]:
% 0.21/0.55         (~ (v2_funct_1 @ X10)
% 0.21/0.55          | ((k2_relat_1 @ X10) = (k1_relat_1 @ (k2_funct_1 @ X10)))
% 0.21/0.55          | ~ (v1_funct_1 @ X10)
% 0.21/0.55          | ~ (v1_relat_1 @ X10))),
% 0.21/0.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.21/0.55  thf(t146_relat_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ A ) =>
% 0.21/0.55       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.21/0.55  thf('16', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0))
% 0.21/0.55          | ~ (v1_relat_1 @ X0))),
% 0.21/0.55      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.21/0.55  thf('17', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.21/0.55            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v2_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['15', '16'])).
% 0.21/0.55  thf('18', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v2_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.21/0.55              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['14', '17'])).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.21/0.55            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.21/0.55          | ~ (v2_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.55  thf('20', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((k10_relat_1 @ X0 @ (k2_relat_1 @ X0))
% 0.21/0.55            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v2_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v2_funct_1 @ X0))),
% 0.21/0.55      inference('sup+', [status(thm)], ['13', '19'])).
% 0.21/0.55  thf('21', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v2_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | ((k10_relat_1 @ X0 @ (k2_relat_1 @ X0))
% 0.21/0.55              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.21/0.55      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.55  thf('22', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(cc2_relset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.55       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.55  thf('23', plain,
% 0.21/0.55      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.55         ((v4_relat_1 @ X14 @ X15)
% 0.21/0.55          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.21/0.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.55  thf('24', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.21/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.55  thf(t209_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.21/0.55       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.21/0.55  thf('25', plain,
% 0.21/0.55      (![X3 : $i, X4 : $i]:
% 0.21/0.55         (((X3) = (k7_relat_1 @ X3 @ X4))
% 0.21/0.55          | ~ (v4_relat_1 @ X3 @ X4)
% 0.21/0.55          | ~ (v1_relat_1 @ X3))),
% 0.21/0.55      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.21/0.55  thf('26', plain,
% 0.21/0.55      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.55  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.55  thf('28', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.55  thf(t148_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ B ) =>
% 0.21/0.55       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.21/0.55  thf('29', plain,
% 0.21/0.55      (![X1 : $i, X2 : $i]:
% 0.21/0.55         (((k2_relat_1 @ (k7_relat_1 @ X1 @ X2)) = (k9_relat_1 @ X1 @ X2))
% 0.21/0.55          | ~ (v1_relat_1 @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.55  thf('30', plain,
% 0.21/0.55      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))
% 0.21/0.55        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.55      inference('sup+', [status(thm)], ['28', '29'])).
% 0.21/0.55  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.55  thf('32', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.55  thf(t152_funct_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.55       ( ( v2_funct_1 @ B ) =>
% 0.21/0.55         ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ))).
% 0.21/0.55  thf('33', plain,
% 0.21/0.55      (![X6 : $i, X7 : $i]:
% 0.21/0.55         (~ (v2_funct_1 @ X6)
% 0.21/0.55          | (r1_tarski @ (k10_relat_1 @ X6 @ (k9_relat_1 @ X6 @ X7)) @ X7)
% 0.21/0.55          | ~ (v1_funct_1 @ X6)
% 0.21/0.55          | ~ (v1_relat_1 @ X6))),
% 0.21/0.55      inference('cnf', [status(esa)], [t152_funct_1])).
% 0.21/0.55  thf('34', plain,
% 0.21/0.55      (((r1_tarski @ (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) @ sk_A)
% 0.21/0.55        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.55        | ~ (v2_funct_1 @ sk_C))),
% 0.21/0.55      inference('sup+', [status(thm)], ['32', '33'])).
% 0.21/0.55  thf('35', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.55  thf('36', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('37', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('38', plain,
% 0.21/0.55      ((r1_tarski @ (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) @ sk_A)),
% 0.21/0.55      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 0.21/0.55  thf('39', plain,
% 0.21/0.55      (((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)
% 0.21/0.55        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.55        | ~ (v2_funct_1 @ sk_C))),
% 0.21/0.55      inference('sup+', [status(thm)], ['21', '38'])).
% 0.21/0.55  thf('40', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.55  thf('41', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('42', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('43', plain, ((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)),
% 0.21/0.55      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 0.21/0.55  thf('44', plain,
% 0.21/0.55      (((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)
% 0.21/0.55        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.55        | ~ (v2_funct_1 @ sk_C))),
% 0.21/0.55      inference('sup+', [status(thm)], ['12', '43'])).
% 0.21/0.55  thf('45', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.55  thf('46', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('47', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('48', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.21/0.55      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 0.21/0.55  thf('49', plain,
% 0.21/0.55      (![X5 : $i]:
% 0.21/0.55         ((v1_funct_1 @ (k2_funct_1 @ X5))
% 0.21/0.55          | ~ (v1_funct_1 @ X5)
% 0.21/0.55          | ~ (v1_relat_1 @ X5))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.55  thf('50', plain,
% 0.21/0.55      (![X5 : $i]:
% 0.21/0.55         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 0.21/0.55          | ~ (v1_funct_1 @ X5)
% 0.21/0.55          | ~ (v1_relat_1 @ X5))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.55  thf('51', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.55       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.55  thf('52', plain,
% 0.21/0.55      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.55         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.21/0.55          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.21/0.55      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.55  thf('53', plain,
% 0.21/0.55      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.21/0.55      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.55  thf('54', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('55', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.21/0.55      inference('sup+', [status(thm)], ['53', '54'])).
% 0.21/0.55  thf('56', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v2_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | ((k10_relat_1 @ X0 @ (k2_relat_1 @ X0))
% 0.21/0.55              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.21/0.55      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.55  thf('57', plain,
% 0.21/0.55      ((((k10_relat_1 @ sk_C @ sk_B) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.21/0.55        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.55        | ~ (v2_funct_1 @ sk_C))),
% 0.21/0.55      inference('sup+', [status(thm)], ['55', '56'])).
% 0.21/0.55  thf('58', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.55  thf('59', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('60', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('61', plain,
% 0.21/0.55      (((k10_relat_1 @ sk_C @ sk_B) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.55      inference('demod', [status(thm)], ['57', '58', '59', '60'])).
% 0.21/0.55  thf('62', plain,
% 0.21/0.55      (![X10 : $i]:
% 0.21/0.55         (~ (v2_funct_1 @ X10)
% 0.21/0.55          | ((k1_relat_1 @ X10) = (k2_relat_1 @ (k2_funct_1 @ X10)))
% 0.21/0.55          | ~ (v1_funct_1 @ X10)
% 0.21/0.55          | ~ (v1_relat_1 @ X10))),
% 0.21/0.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.21/0.55  thf('63', plain,
% 0.21/0.55      (((k10_relat_1 @ sk_C @ sk_B) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.55      inference('demod', [status(thm)], ['57', '58', '59', '60'])).
% 0.21/0.55  thf('64', plain,
% 0.21/0.55      ((((k10_relat_1 @ sk_C @ sk_B) = (k1_relat_1 @ sk_C))
% 0.21/0.55        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.55        | ~ (v2_funct_1 @ sk_C))),
% 0.21/0.55      inference('sup+', [status(thm)], ['62', '63'])).
% 0.21/0.55  thf('65', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.55  thf('66', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('67', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('68', plain, (((k10_relat_1 @ sk_C @ sk_B) = (k1_relat_1 @ sk_C))),
% 0.21/0.55      inference('demod', [status(thm)], ['64', '65', '66', '67'])).
% 0.21/0.55  thf('69', plain,
% 0.21/0.55      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.55      inference('demod', [status(thm)], ['61', '68'])).
% 0.21/0.55  thf(t4_funct_2, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.55       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.21/0.55         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.21/0.55           ( m1_subset_1 @
% 0.21/0.55             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.21/0.55  thf('70', plain,
% 0.21/0.55      (![X20 : $i, X21 : $i]:
% 0.21/0.55         (~ (r1_tarski @ (k2_relat_1 @ X20) @ X21)
% 0.21/0.55          | (v1_funct_2 @ X20 @ (k1_relat_1 @ X20) @ X21)
% 0.21/0.55          | ~ (v1_funct_1 @ X20)
% 0.21/0.55          | ~ (v1_relat_1 @ X20))),
% 0.21/0.55      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.21/0.55  thf('71', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.55          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.55          | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.55             (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['69', '70'])).
% 0.21/0.55  thf('72', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ sk_C)
% 0.21/0.55          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.55          | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.55             (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.55          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['50', '71'])).
% 0.21/0.55  thf('73', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.55  thf('74', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('75', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.55           (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.55          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 0.21/0.55      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.21/0.55  thf('76', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ sk_C)
% 0.21/0.55          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.55          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0)
% 0.21/0.55          | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.55             (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['49', '75'])).
% 0.21/0.55  thf('77', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.55  thf('78', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('79', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0)
% 0.21/0.55          | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.55             (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0))),
% 0.21/0.55      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.21/0.55  thf('80', plain,
% 0.21/0.55      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.55        (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)),
% 0.21/0.55      inference('sup-', [status(thm)], ['48', '79'])).
% 0.21/0.55  thf('81', plain,
% 0.21/0.55      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_A)
% 0.21/0.55        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.55        | ~ (v2_funct_1 @ sk_C))),
% 0.21/0.55      inference('sup+', [status(thm)], ['11', '80'])).
% 0.21/0.55  thf('82', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.21/0.55      inference('sup+', [status(thm)], ['53', '54'])).
% 0.21/0.55  thf('83', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.55  thf('84', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('85', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('86', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 0.21/0.55      inference('demod', [status(thm)], ['81', '82', '83', '84', '85'])).
% 0.21/0.55  thf('87', plain,
% 0.21/0.55      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 0.21/0.55         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('88', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['86', '87'])).
% 0.21/0.55  thf('89', plain,
% 0.21/0.55      (~
% 0.21/0.55       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.55         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 0.21/0.55       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 0.21/0.55       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('90', plain,
% 0.21/0.55      (~
% 0.21/0.55       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.55         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.21/0.55      inference('sat_resolution*', [status(thm)], ['10', '88', '89'])).
% 0.21/0.55  thf('91', plain,
% 0.21/0.55      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.55          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.55      inference('simpl_trail', [status(thm)], ['1', '90'])).
% 0.21/0.55  thf('92', plain,
% 0.21/0.55      (![X10 : $i]:
% 0.21/0.55         (~ (v2_funct_1 @ X10)
% 0.21/0.55          | ((k2_relat_1 @ X10) = (k1_relat_1 @ (k2_funct_1 @ X10)))
% 0.21/0.55          | ~ (v1_funct_1 @ X10)
% 0.21/0.55          | ~ (v1_relat_1 @ X10))),
% 0.21/0.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.21/0.55  thf('93', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.21/0.55      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 0.21/0.55  thf('94', plain,
% 0.21/0.55      (![X5 : $i]:
% 0.21/0.55         ((v1_funct_1 @ (k2_funct_1 @ X5))
% 0.21/0.55          | ~ (v1_funct_1 @ X5)
% 0.21/0.55          | ~ (v1_relat_1 @ X5))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.55  thf('95', plain,
% 0.21/0.55      (![X5 : $i]:
% 0.21/0.55         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 0.21/0.55          | ~ (v1_funct_1 @ X5)
% 0.21/0.55          | ~ (v1_relat_1 @ X5))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.55  thf('96', plain,
% 0.21/0.55      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.55      inference('demod', [status(thm)], ['61', '68'])).
% 0.21/0.55  thf('97', plain,
% 0.21/0.55      (![X20 : $i, X21 : $i]:
% 0.21/0.55         (~ (r1_tarski @ (k2_relat_1 @ X20) @ X21)
% 0.21/0.55          | (m1_subset_1 @ X20 @ 
% 0.21/0.55             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X20) @ X21)))
% 0.21/0.55          | ~ (v1_funct_1 @ X20)
% 0.21/0.55          | ~ (v1_relat_1 @ X20))),
% 0.21/0.55      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.21/0.55  thf('98', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.55          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.55          | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.55             (k1_zfmisc_1 @ 
% 0.21/0.55              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['96', '97'])).
% 0.21/0.55  thf('99', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ sk_C)
% 0.21/0.55          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.55          | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.55             (k1_zfmisc_1 @ 
% 0.21/0.55              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)))
% 0.21/0.55          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.55          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['95', '98'])).
% 0.21/0.55  thf('100', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.55  thf('101', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('102', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.55           (k1_zfmisc_1 @ 
% 0.21/0.55            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)))
% 0.21/0.55          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.55          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 0.21/0.55      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.21/0.55  thf('103', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ sk_C)
% 0.21/0.55          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.55          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0)
% 0.21/0.55          | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.55             (k1_zfmisc_1 @ 
% 0.21/0.55              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['94', '102'])).
% 0.21/0.55  thf('104', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.55  thf('105', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('106', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0)
% 0.21/0.55          | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.55             (k1_zfmisc_1 @ 
% 0.21/0.55              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0))))),
% 0.21/0.55      inference('demod', [status(thm)], ['103', '104', '105'])).
% 0.21/0.55  thf('107', plain,
% 0.21/0.55      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.55        (k1_zfmisc_1 @ 
% 0.21/0.55         (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['93', '106'])).
% 0.21/0.55  thf('108', plain,
% 0.21/0.55      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.55         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ sk_A)))
% 0.21/0.55        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.55        | ~ (v2_funct_1 @ sk_C))),
% 0.21/0.55      inference('sup+', [status(thm)], ['92', '107'])).
% 0.21/0.55  thf('109', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.21/0.55      inference('sup+', [status(thm)], ['53', '54'])).
% 0.21/0.55  thf('110', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.55  thf('111', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('112', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('113', plain,
% 0.21/0.55      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['108', '109', '110', '111', '112'])).
% 0.21/0.55  thf('114', plain, ($false), inference('demod', [status(thm)], ['91', '113'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
