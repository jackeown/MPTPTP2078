%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ddbQtw5YWj

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:38 EST 2020

% Result     : Theorem 2.02s
% Output     : Refutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 119 expanded)
%              Number of leaves         :   27 (  49 expanded)
%              Depth                    :   18
%              Number of atoms          :  648 ( 865 expanded)
%              Number of equality atoms :   36 (  50 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k7_relat_1 @ X28 @ X27 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X27 ) @ X28 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('1',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X12: $i] :
      ( ( ( k9_relat_1 @ X12 @ ( k1_relat_1 @ X12 ) )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X24: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(t162_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i,C: $i] :
            ( ( r1_tarski @ B @ C )
           => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
              = ( k9_relat_1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t162_relat_1])).

thf('7',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('9',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X29 ) @ X30 )
      | ( ( k7_relat_1 @ X29 @ X30 )
        = X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k7_relat_1 @ X28 @ X27 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X27 ) @ X28 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('15',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X25 @ ( k6_relat_1 @ X26 ) ) @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('18',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['13','19'])).

thf(t157_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ C @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( r1_tarski @ ( k9_relat_1 @ X16 @ X17 ) @ ( k9_relat_1 @ X15 @ X17 ) )
      | ~ ( r1_tarski @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t157_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
      | ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) @ ( k9_relat_1 @ ( k6_relat_1 @ sk_C ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('24',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) @ ( k9_relat_1 @ ( k6_relat_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    r1_tarski @ sk_B @ ( k9_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup+',[status(thm)],['6','25'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) )
        = ( k9_relat_1 @ X13 @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( r1_tarski @ ( k2_relat_1 @ X22 ) @ ( k2_relat_1 @ X21 ) )
      | ~ ( r1_tarski @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k7_relat_1 @ X28 @ X27 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X27 ) @ X28 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('32',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X25 @ ( k6_relat_1 @ X26 ) ) @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('33',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('35',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','37'])).

thf('39',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('40',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ! [X24: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('43',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['30','41','42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['27','44'])).

thf('46',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('48',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( sk_B
    = ( k9_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['26','49'])).

thf(t159_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k9_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k9_relat_1 @ C @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('51',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( ( k9_relat_1 @ ( k5_relat_1 @ X19 @ X18 ) @ X20 )
        = ( k9_relat_1 @ X18 @ ( k9_relat_1 @ X19 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t159_relat_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ X0 ) @ sk_B )
        = ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ X0 ) @ sk_B )
        = ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k7_relat_1 @ X0 @ sk_C ) @ sk_B )
        = ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X0 @ sk_C ) @ sk_B )
        = ( k9_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ( k9_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B )
 != ( k9_relat_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( ( k9_relat_1 @ sk_A @ sk_B )
     != ( k9_relat_1 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ( k9_relat_1 @ sk_A @ sk_B )
 != ( k9_relat_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    $false ),
    inference(simplify,[status(thm)],['60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ddbQtw5YWj
% 0.16/0.37  % Computer   : n009.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 10:24:56 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 2.02/2.21  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.02/2.21  % Solved by: fo/fo7.sh
% 2.02/2.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.02/2.21  % done 3141 iterations in 1.724s
% 2.02/2.21  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.02/2.21  % SZS output start Refutation
% 2.02/2.21  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.02/2.21  thf(sk_A_type, type, sk_A: $i).
% 2.02/2.21  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.02/2.21  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.02/2.21  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.02/2.21  thf(sk_C_type, type, sk_C: $i).
% 2.02/2.21  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.02/2.21  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.02/2.21  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 2.02/2.21  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.02/2.21  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.02/2.21  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.02/2.21  thf(sk_B_type, type, sk_B: $i).
% 2.02/2.21  thf(t94_relat_1, axiom,
% 2.02/2.21    (![A:$i,B:$i]:
% 2.02/2.21     ( ( v1_relat_1 @ B ) =>
% 2.02/2.21       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 2.02/2.21  thf('0', plain,
% 2.02/2.21      (![X27 : $i, X28 : $i]:
% 2.02/2.21         (((k7_relat_1 @ X28 @ X27) = (k5_relat_1 @ (k6_relat_1 @ X27) @ X28))
% 2.02/2.21          | ~ (v1_relat_1 @ X28))),
% 2.02/2.21      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.02/2.21  thf(t71_relat_1, axiom,
% 2.02/2.21    (![A:$i]:
% 2.02/2.21     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 2.02/2.21       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 2.02/2.21  thf('1', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 2.02/2.21      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.02/2.21  thf(t146_relat_1, axiom,
% 2.02/2.21    (![A:$i]:
% 2.02/2.21     ( ( v1_relat_1 @ A ) =>
% 2.02/2.21       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 2.02/2.21  thf('2', plain,
% 2.02/2.21      (![X12 : $i]:
% 2.02/2.21         (((k9_relat_1 @ X12 @ (k1_relat_1 @ X12)) = (k2_relat_1 @ X12))
% 2.02/2.21          | ~ (v1_relat_1 @ X12))),
% 2.02/2.21      inference('cnf', [status(esa)], [t146_relat_1])).
% 2.02/2.21  thf('3', plain,
% 2.02/2.21      (![X0 : $i]:
% 2.02/2.21         (((k9_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 2.02/2.21            = (k2_relat_1 @ (k6_relat_1 @ X0)))
% 2.02/2.21          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.02/2.21      inference('sup+', [status(thm)], ['1', '2'])).
% 2.02/2.21  thf('4', plain, (![X24 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 2.02/2.21      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.02/2.21  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 2.02/2.21  thf('5', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 2.02/2.21      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.02/2.21  thf('6', plain, (![X0 : $i]: ((k9_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 2.02/2.21      inference('demod', [status(thm)], ['3', '4', '5'])).
% 2.02/2.21  thf(t162_relat_1, conjecture,
% 2.02/2.21    (![A:$i]:
% 2.02/2.21     ( ( v1_relat_1 @ A ) =>
% 2.02/2.21       ( ![B:$i,C:$i]:
% 2.02/2.21         ( ( r1_tarski @ B @ C ) =>
% 2.02/2.21           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 2.02/2.21             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 2.02/2.21  thf(zf_stmt_0, negated_conjecture,
% 2.02/2.21    (~( ![A:$i]:
% 2.02/2.21        ( ( v1_relat_1 @ A ) =>
% 2.02/2.21          ( ![B:$i,C:$i]:
% 2.02/2.21            ( ( r1_tarski @ B @ C ) =>
% 2.02/2.21              ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 2.02/2.21                ( k9_relat_1 @ A @ B ) ) ) ) ) )),
% 2.02/2.21    inference('cnf.neg', [status(esa)], [t162_relat_1])).
% 2.02/2.21  thf('7', plain, ((r1_tarski @ sk_B @ sk_C)),
% 2.02/2.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.02/2.21  thf('8', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 2.02/2.21      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.02/2.21  thf(t97_relat_1, axiom,
% 2.02/2.21    (![A:$i,B:$i]:
% 2.02/2.21     ( ( v1_relat_1 @ B ) =>
% 2.02/2.21       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 2.02/2.21         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 2.02/2.21  thf('9', plain,
% 2.02/2.21      (![X29 : $i, X30 : $i]:
% 2.02/2.21         (~ (r1_tarski @ (k1_relat_1 @ X29) @ X30)
% 2.02/2.21          | ((k7_relat_1 @ X29 @ X30) = (X29))
% 2.02/2.21          | ~ (v1_relat_1 @ X29))),
% 2.02/2.21      inference('cnf', [status(esa)], [t97_relat_1])).
% 2.02/2.21  thf('10', plain,
% 2.02/2.21      (![X0 : $i, X1 : $i]:
% 2.02/2.21         (~ (r1_tarski @ X0 @ X1)
% 2.02/2.21          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.02/2.21          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 2.02/2.21      inference('sup-', [status(thm)], ['8', '9'])).
% 2.02/2.21  thf('11', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 2.02/2.21      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.02/2.21  thf('12', plain,
% 2.02/2.21      (![X0 : $i, X1 : $i]:
% 2.02/2.21         (~ (r1_tarski @ X0 @ X1)
% 2.02/2.21          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 2.02/2.21      inference('demod', [status(thm)], ['10', '11'])).
% 2.02/2.21  thf('13', plain,
% 2.02/2.21      (((k7_relat_1 @ (k6_relat_1 @ sk_B) @ sk_C) = (k6_relat_1 @ sk_B))),
% 2.02/2.21      inference('sup-', [status(thm)], ['7', '12'])).
% 2.02/2.21  thf('14', plain,
% 2.02/2.21      (![X27 : $i, X28 : $i]:
% 2.02/2.21         (((k7_relat_1 @ X28 @ X27) = (k5_relat_1 @ (k6_relat_1 @ X27) @ X28))
% 2.02/2.21          | ~ (v1_relat_1 @ X28))),
% 2.02/2.21      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.02/2.21  thf(t76_relat_1, axiom,
% 2.02/2.21    (![A:$i,B:$i]:
% 2.02/2.21     ( ( v1_relat_1 @ B ) =>
% 2.02/2.21       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 2.02/2.21         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 2.02/2.21  thf('15', plain,
% 2.02/2.21      (![X25 : $i, X26 : $i]:
% 2.02/2.21         ((r1_tarski @ (k5_relat_1 @ X25 @ (k6_relat_1 @ X26)) @ X25)
% 2.02/2.21          | ~ (v1_relat_1 @ X25))),
% 2.02/2.21      inference('cnf', [status(esa)], [t76_relat_1])).
% 2.02/2.21  thf('16', plain,
% 2.02/2.21      (![X0 : $i, X1 : $i]:
% 2.02/2.21         ((r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 2.02/2.21           (k6_relat_1 @ X0))
% 2.02/2.21          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 2.02/2.21          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.02/2.21      inference('sup+', [status(thm)], ['14', '15'])).
% 2.02/2.21  thf('17', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 2.02/2.21      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.02/2.21  thf('18', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 2.02/2.21      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.02/2.21  thf('19', plain,
% 2.02/2.21      (![X0 : $i, X1 : $i]:
% 2.02/2.21         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ (k6_relat_1 @ X0))),
% 2.02/2.21      inference('demod', [status(thm)], ['16', '17', '18'])).
% 2.02/2.21  thf('20', plain, ((r1_tarski @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_C))),
% 2.02/2.21      inference('sup+', [status(thm)], ['13', '19'])).
% 2.02/2.21  thf(t157_relat_1, axiom,
% 2.02/2.21    (![A:$i,B:$i]:
% 2.02/2.21     ( ( v1_relat_1 @ B ) =>
% 2.02/2.21       ( ![C:$i]:
% 2.02/2.21         ( ( v1_relat_1 @ C ) =>
% 2.02/2.21           ( ( r1_tarski @ B @ C ) =>
% 2.02/2.21             ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ C @ A ) ) ) ) ) ))).
% 2.02/2.21  thf('21', plain,
% 2.02/2.21      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.02/2.21         (~ (v1_relat_1 @ X15)
% 2.02/2.21          | (r1_tarski @ (k9_relat_1 @ X16 @ X17) @ (k9_relat_1 @ X15 @ X17))
% 2.02/2.21          | ~ (r1_tarski @ X16 @ X15)
% 2.02/2.21          | ~ (v1_relat_1 @ X16))),
% 2.02/2.21      inference('cnf', [status(esa)], [t157_relat_1])).
% 2.02/2.21  thf('22', plain,
% 2.02/2.21      (![X0 : $i]:
% 2.02/2.21         (~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 2.02/2.21          | (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ sk_B) @ X0) @ 
% 2.02/2.21             (k9_relat_1 @ (k6_relat_1 @ sk_C) @ X0))
% 2.02/2.21          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_C)))),
% 2.02/2.21      inference('sup-', [status(thm)], ['20', '21'])).
% 2.02/2.21  thf('23', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 2.02/2.21      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.02/2.21  thf('24', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 2.02/2.21      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.02/2.21  thf('25', plain,
% 2.02/2.21      (![X0 : $i]:
% 2.02/2.21         (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ sk_B) @ X0) @ 
% 2.02/2.21          (k9_relat_1 @ (k6_relat_1 @ sk_C) @ X0))),
% 2.02/2.21      inference('demod', [status(thm)], ['22', '23', '24'])).
% 2.02/2.21  thf('26', plain,
% 2.02/2.21      ((r1_tarski @ sk_B @ (k9_relat_1 @ (k6_relat_1 @ sk_C) @ sk_B))),
% 2.02/2.21      inference('sup+', [status(thm)], ['6', '25'])).
% 2.02/2.21  thf(t148_relat_1, axiom,
% 2.02/2.21    (![A:$i,B:$i]:
% 2.02/2.21     ( ( v1_relat_1 @ B ) =>
% 2.02/2.21       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 2.02/2.21  thf('27', plain,
% 2.02/2.21      (![X13 : $i, X14 : $i]:
% 2.02/2.21         (((k2_relat_1 @ (k7_relat_1 @ X13 @ X14)) = (k9_relat_1 @ X13 @ X14))
% 2.02/2.21          | ~ (v1_relat_1 @ X13))),
% 2.02/2.21      inference('cnf', [status(esa)], [t148_relat_1])).
% 2.02/2.21  thf('28', plain,
% 2.02/2.21      (![X0 : $i, X1 : $i]:
% 2.02/2.21         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ (k6_relat_1 @ X0))),
% 2.02/2.21      inference('demod', [status(thm)], ['16', '17', '18'])).
% 2.02/2.21  thf(t25_relat_1, axiom,
% 2.02/2.21    (![A:$i]:
% 2.02/2.21     ( ( v1_relat_1 @ A ) =>
% 2.02/2.21       ( ![B:$i]:
% 2.02/2.21         ( ( v1_relat_1 @ B ) =>
% 2.02/2.21           ( ( r1_tarski @ A @ B ) =>
% 2.02/2.21             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 2.02/2.21               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 2.02/2.21  thf('29', plain,
% 2.02/2.21      (![X21 : $i, X22 : $i]:
% 2.02/2.21         (~ (v1_relat_1 @ X21)
% 2.02/2.21          | (r1_tarski @ (k2_relat_1 @ X22) @ (k2_relat_1 @ X21))
% 2.02/2.21          | ~ (r1_tarski @ X22 @ X21)
% 2.02/2.21          | ~ (v1_relat_1 @ X22))),
% 2.02/2.21      inference('cnf', [status(esa)], [t25_relat_1])).
% 2.02/2.21  thf('30', plain,
% 2.02/2.21      (![X0 : $i, X1 : $i]:
% 2.02/2.21         (~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.02/2.21          | (r1_tarski @ 
% 2.02/2.21             (k2_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 2.02/2.21             (k2_relat_1 @ (k6_relat_1 @ X0)))
% 2.02/2.21          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.02/2.21      inference('sup-', [status(thm)], ['28', '29'])).
% 2.02/2.21  thf('31', plain,
% 2.02/2.21      (![X27 : $i, X28 : $i]:
% 2.02/2.21         (((k7_relat_1 @ X28 @ X27) = (k5_relat_1 @ (k6_relat_1 @ X27) @ X28))
% 2.02/2.21          | ~ (v1_relat_1 @ X28))),
% 2.02/2.21      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.02/2.21  thf('32', plain,
% 2.02/2.21      (![X25 : $i, X26 : $i]:
% 2.02/2.21         ((r1_tarski @ (k5_relat_1 @ X25 @ (k6_relat_1 @ X26)) @ X25)
% 2.02/2.21          | ~ (v1_relat_1 @ X25))),
% 2.02/2.21      inference('cnf', [status(esa)], [t76_relat_1])).
% 2.02/2.21  thf(t3_subset, axiom,
% 2.02/2.21    (![A:$i,B:$i]:
% 2.02/2.21     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.02/2.21  thf('33', plain,
% 2.02/2.21      (![X6 : $i, X8 : $i]:
% 2.02/2.21         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 2.02/2.21      inference('cnf', [status(esa)], [t3_subset])).
% 2.02/2.21  thf('34', plain,
% 2.02/2.21      (![X0 : $i, X1 : $i]:
% 2.02/2.21         (~ (v1_relat_1 @ X0)
% 2.02/2.21          | (m1_subset_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ 
% 2.02/2.21             (k1_zfmisc_1 @ X0)))),
% 2.02/2.21      inference('sup-', [status(thm)], ['32', '33'])).
% 2.02/2.21  thf(cc2_relat_1, axiom,
% 2.02/2.21    (![A:$i]:
% 2.02/2.21     ( ( v1_relat_1 @ A ) =>
% 2.02/2.21       ( ![B:$i]:
% 2.02/2.21         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.02/2.21  thf('35', plain,
% 2.02/2.21      (![X9 : $i, X10 : $i]:
% 2.02/2.21         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 2.02/2.21          | (v1_relat_1 @ X9)
% 2.02/2.21          | ~ (v1_relat_1 @ X10))),
% 2.02/2.21      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.02/2.21  thf('36', plain,
% 2.02/2.21      (![X0 : $i, X1 : $i]:
% 2.02/2.21         (~ (v1_relat_1 @ X0)
% 2.02/2.21          | ~ (v1_relat_1 @ X0)
% 2.02/2.21          | (v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 2.02/2.21      inference('sup-', [status(thm)], ['34', '35'])).
% 2.02/2.21  thf('37', plain,
% 2.02/2.21      (![X0 : $i, X1 : $i]:
% 2.02/2.21         ((v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 2.02/2.21          | ~ (v1_relat_1 @ X0))),
% 2.02/2.21      inference('simplify', [status(thm)], ['36'])).
% 2.02/2.21  thf('38', plain,
% 2.02/2.21      (![X0 : $i, X1 : $i]:
% 2.02/2.21         ((v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.02/2.21          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 2.02/2.21          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.02/2.21      inference('sup+', [status(thm)], ['31', '37'])).
% 2.02/2.21  thf('39', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 2.02/2.21      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.02/2.21  thf('40', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 2.02/2.21      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.02/2.21  thf('41', plain,
% 2.02/2.21      (![X0 : $i, X1 : $i]:
% 2.02/2.21         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.02/2.21      inference('demod', [status(thm)], ['38', '39', '40'])).
% 2.02/2.21  thf('42', plain, (![X24 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 2.02/2.21      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.02/2.21  thf('43', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 2.02/2.21      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.02/2.21  thf('44', plain,
% 2.02/2.21      (![X0 : $i, X1 : $i]:
% 2.02/2.21         (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ X0)),
% 2.02/2.21      inference('demod', [status(thm)], ['30', '41', '42', '43'])).
% 2.02/2.21  thf('45', plain,
% 2.02/2.21      (![X0 : $i, X1 : $i]:
% 2.02/2.21         ((r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0)
% 2.02/2.21          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 2.02/2.21      inference('sup+', [status(thm)], ['27', '44'])).
% 2.02/2.21  thf('46', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 2.02/2.21      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.02/2.21  thf('47', plain,
% 2.02/2.21      (![X0 : $i, X1 : $i]:
% 2.02/2.21         (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0)),
% 2.02/2.21      inference('demod', [status(thm)], ['45', '46'])).
% 2.02/2.21  thf(d10_xboole_0, axiom,
% 2.02/2.21    (![A:$i,B:$i]:
% 2.02/2.21     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.02/2.21  thf('48', plain,
% 2.02/2.21      (![X0 : $i, X2 : $i]:
% 2.02/2.21         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.02/2.21      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.02/2.21  thf('49', plain,
% 2.02/2.21      (![X0 : $i, X1 : $i]:
% 2.02/2.21         (~ (r1_tarski @ X0 @ (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.02/2.21          | ((X0) = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 2.02/2.21      inference('sup-', [status(thm)], ['47', '48'])).
% 2.02/2.21  thf('50', plain, (((sk_B) = (k9_relat_1 @ (k6_relat_1 @ sk_C) @ sk_B))),
% 2.02/2.21      inference('sup-', [status(thm)], ['26', '49'])).
% 2.02/2.21  thf(t159_relat_1, axiom,
% 2.02/2.21    (![A:$i,B:$i]:
% 2.02/2.21     ( ( v1_relat_1 @ B ) =>
% 2.02/2.21       ( ![C:$i]:
% 2.02/2.21         ( ( v1_relat_1 @ C ) =>
% 2.02/2.21           ( ( k9_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 2.02/2.21             ( k9_relat_1 @ C @ ( k9_relat_1 @ B @ A ) ) ) ) ) ))).
% 2.02/2.21  thf('51', plain,
% 2.02/2.21      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.02/2.21         (~ (v1_relat_1 @ X18)
% 2.02/2.21          | ((k9_relat_1 @ (k5_relat_1 @ X19 @ X18) @ X20)
% 2.02/2.21              = (k9_relat_1 @ X18 @ (k9_relat_1 @ X19 @ X20)))
% 2.02/2.21          | ~ (v1_relat_1 @ X19))),
% 2.02/2.21      inference('cnf', [status(esa)], [t159_relat_1])).
% 2.02/2.21  thf('52', plain,
% 2.02/2.21      (![X0 : $i]:
% 2.02/2.21         (((k9_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C) @ X0) @ sk_B)
% 2.02/2.21            = (k9_relat_1 @ X0 @ sk_B))
% 2.02/2.21          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_C))
% 2.02/2.21          | ~ (v1_relat_1 @ X0))),
% 2.02/2.21      inference('sup+', [status(thm)], ['50', '51'])).
% 2.02/2.21  thf('53', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 2.02/2.21      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.02/2.21  thf('54', plain,
% 2.02/2.21      (![X0 : $i]:
% 2.02/2.21         (((k9_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C) @ X0) @ sk_B)
% 2.02/2.21            = (k9_relat_1 @ X0 @ sk_B))
% 2.02/2.21          | ~ (v1_relat_1 @ X0))),
% 2.02/2.21      inference('demod', [status(thm)], ['52', '53'])).
% 2.02/2.21  thf('55', plain,
% 2.02/2.21      (![X0 : $i]:
% 2.02/2.21         (((k9_relat_1 @ (k7_relat_1 @ X0 @ sk_C) @ sk_B)
% 2.02/2.21            = (k9_relat_1 @ X0 @ sk_B))
% 2.02/2.21          | ~ (v1_relat_1 @ X0)
% 2.02/2.21          | ~ (v1_relat_1 @ X0))),
% 2.02/2.21      inference('sup+', [status(thm)], ['0', '54'])).
% 2.02/2.21  thf('56', plain,
% 2.02/2.21      (![X0 : $i]:
% 2.02/2.21         (~ (v1_relat_1 @ X0)
% 2.02/2.21          | ((k9_relat_1 @ (k7_relat_1 @ X0 @ sk_C) @ sk_B)
% 2.02/2.21              = (k9_relat_1 @ X0 @ sk_B)))),
% 2.02/2.21      inference('simplify', [status(thm)], ['55'])).
% 2.02/2.21  thf('57', plain,
% 2.02/2.21      (((k9_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B)
% 2.02/2.21         != (k9_relat_1 @ sk_A @ sk_B))),
% 2.02/2.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.02/2.21  thf('58', plain,
% 2.02/2.21      ((((k9_relat_1 @ sk_A @ sk_B) != (k9_relat_1 @ sk_A @ sk_B))
% 2.02/2.21        | ~ (v1_relat_1 @ sk_A))),
% 2.02/2.21      inference('sup-', [status(thm)], ['56', '57'])).
% 2.02/2.21  thf('59', plain, ((v1_relat_1 @ sk_A)),
% 2.02/2.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.02/2.21  thf('60', plain,
% 2.02/2.21      (((k9_relat_1 @ sk_A @ sk_B) != (k9_relat_1 @ sk_A @ sk_B))),
% 2.02/2.21      inference('demod', [status(thm)], ['58', '59'])).
% 2.02/2.21  thf('61', plain, ($false), inference('simplify', [status(thm)], ['60'])).
% 2.02/2.21  
% 2.02/2.21  % SZS output end Refutation
% 2.02/2.21  
% 2.05/2.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
