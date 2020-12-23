%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fe1jmO25C7

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:39 EST 2020

% Result     : Theorem 6.93s
% Output     : Refutation 6.93s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 213 expanded)
%              Number of leaves         :   32 (  82 expanded)
%              Depth                    :   22
%              Number of atoms          : 1005 (1659 expanded)
%              Number of equality atoms :   63 ( 118 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k7_relat_1 @ X35 @ X34 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X34 ) @ X35 ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('1',plain,(
    ! [X25: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X16: $i] :
      ( ( ( k9_relat_1 @ X16 @ ( k1_relat_1 @ X16 ) )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X26: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
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
    r1_tarski @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X25: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('9',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X36 ) @ X37 )
      | ( ( k7_relat_1 @ X36 @ X37 )
        = X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ sk_B_1 ) @ sk_C_1 )
    = ( k6_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k7_relat_1 @ X35 @ X34 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X34 ) @ X35 ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('15',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X28 ) @ X27 ) @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ( X0
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( X1
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ~ ( r1_tarski @ ( k6_relat_1 @ sk_B_1 ) @ ( k6_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B_1 ) )
    | ( ( k6_relat_1 @ sk_B_1 )
      = ( k5_relat_1 @ ( k6_relat_1 @ sk_C_1 ) @ ( k6_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('24',plain,
    ( ( k6_relat_1 @ sk_B_1 )
    = ( k5_relat_1 @ ( k6_relat_1 @ sk_C_1 ) @ ( k6_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['20','22','23'])).

thf('25',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X27 @ ( k6_relat_1 @ X28 ) ) @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('26',plain,
    ( ( r1_tarski @ ( k6_relat_1 @ sk_B_1 ) @ ( k6_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('28',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_B_1 ) @ ( k6_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t157_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ C @ A ) ) ) ) ) )).

thf('29',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( r1_tarski @ ( k9_relat_1 @ X20 @ X21 ) @ ( k9_relat_1 @ X19 @ X21 ) )
      | ~ ( r1_tarski @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t157_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B_1 ) )
      | ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ sk_B_1 ) @ X0 ) @ ( k9_relat_1 @ ( k6_relat_1 @ sk_C_1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('32',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ sk_B_1 ) @ X0 ) @ ( k9_relat_1 @ ( k6_relat_1 @ sk_C_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    r1_tarski @ sk_B_1 @ ( k9_relat_1 @ ( k6_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['6','33'])).

thf('35',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('36',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ sk_C_1 ) @ sk_B_1 ) @ sk_B_1 )
    | ( ( k9_relat_1 @ ( k6_relat_1 @ sk_C_1 ) @ sk_B_1 )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k7_relat_1 @ X35 @ X34 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X34 ) @ X35 ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('38',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ sk_B_1 ) @ sk_C_1 )
    = ( k6_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('39',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) )
        = ( k9_relat_1 @ X17 @ X18 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('40',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ sk_B_1 ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ sk_B_1 ) @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X26: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('42',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('43',plain,
    ( sk_B_1
    = ( k9_relat_1 @ ( k6_relat_1 @ sk_B_1 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf(t159_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k9_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k9_relat_1 @ C @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('44',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ( ( k9_relat_1 @ ( k5_relat_1 @ X23 @ X22 ) @ X24 )
        = ( k9_relat_1 @ X22 @ ( k9_relat_1 @ X23 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t159_relat_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B_1 ) @ X0 ) @ sk_C_1 )
        = ( k9_relat_1 @ X0 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B_1 ) @ X0 ) @ sk_C_1 )
        = ( k9_relat_1 @ X0 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k7_relat_1 @ X0 @ sk_B_1 ) @ sk_C_1 )
        = ( k9_relat_1 @ X0 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X0 @ sk_B_1 ) @ sk_C_1 )
        = ( k9_relat_1 @ X0 @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k7_relat_1 @ X35 @ X34 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X34 ) @ X35 ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('51',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X27 @ ( k6_relat_1 @ X28 ) ) @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('54',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( r1_tarski @ ( k9_relat_1 @ X20 @ X21 ) @ ( k9_relat_1 @ X19 @ X21 ) )
      | ~ ( r1_tarski @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t157_relat_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 ) @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 ) @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('61',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('63',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ X10 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('64',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('65',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf(t86_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('69',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X29 @ ( k1_relat_1 @ ( k7_relat_1 @ X31 @ X30 ) ) )
      | ( r2_hidden @ X29 @ X30 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r2_hidden @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X25: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('72',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['63','73'])).

thf('75',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8
        = ( k4_tarski @ ( sk_C @ X8 ) @ ( sk_D @ X8 ) ) )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( ( sk_B @ X1 )
        = ( k4_tarski @ ( sk_C @ ( sk_B @ X1 ) ) @ ( sk_D @ ( sk_B @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ( ( sk_B @ X10 )
       != ( k4_tarski @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( v1_relat_1 @ X1 ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','78'])).

thf('80',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 ) @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['59','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B_1 ) @ ( k9_relat_1 @ ( k6_relat_1 @ sk_B_1 ) @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','82'])).

thf('84',plain,
    ( sk_B_1
    = ( k9_relat_1 @ ( k6_relat_1 @ sk_B_1 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('85',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ( k9_relat_1 @ ( k6_relat_1 @ sk_C_1 ) @ sk_B_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['36','86'])).

thf('88',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ( ( k9_relat_1 @ ( k5_relat_1 @ X23 @ X22 ) @ X24 )
        = ( k9_relat_1 @ X22 @ ( k9_relat_1 @ X23 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t159_relat_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C_1 ) @ X0 ) @ sk_B_1 )
        = ( k9_relat_1 @ X0 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C_1 ) @ X0 ) @ sk_B_1 )
        = ( k9_relat_1 @ X0 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k7_relat_1 @ X0 @ sk_C_1 ) @ sk_B_1 )
        = ( k9_relat_1 @ X0 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X0 @ sk_C_1 ) @ sk_B_1 )
        = ( k9_relat_1 @ X0 @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ( k9_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) @ sk_B_1 )
 != ( k9_relat_1 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( ( k9_relat_1 @ sk_A @ sk_B_1 )
     != ( k9_relat_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ( k9_relat_1 @ sk_A @ sk_B_1 )
 != ( k9_relat_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    $false ),
    inference(simplify,[status(thm)],['97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fe1jmO25C7
% 0.15/0.34  % Computer   : n017.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 20:59:32 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.34  % Running portfolio for 600 s
% 0.15/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 6.93/7.12  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.93/7.12  % Solved by: fo/fo7.sh
% 6.93/7.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.93/7.12  % done 9429 iterations in 6.659s
% 6.93/7.12  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.93/7.12  % SZS output start Refutation
% 6.93/7.12  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.93/7.12  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 6.93/7.12  thf(sk_D_type, type, sk_D: $i > $i).
% 6.93/7.12  thf(sk_A_type, type, sk_A: $i).
% 6.93/7.12  thf(sk_B_1_type, type, sk_B_1: $i).
% 6.93/7.12  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 6.93/7.12  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 6.93/7.12  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 6.93/7.12  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.93/7.12  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 6.93/7.12  thf(sk_C_1_type, type, sk_C_1: $i).
% 6.93/7.12  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.93/7.12  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 6.93/7.12  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 6.93/7.12  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 6.93/7.12  thf(sk_C_type, type, sk_C: $i > $i).
% 6.93/7.12  thf(sk_B_type, type, sk_B: $i > $i).
% 6.93/7.12  thf(t94_relat_1, axiom,
% 6.93/7.12    (![A:$i,B:$i]:
% 6.93/7.12     ( ( v1_relat_1 @ B ) =>
% 6.93/7.12       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 6.93/7.12  thf('0', plain,
% 6.93/7.12      (![X34 : $i, X35 : $i]:
% 6.93/7.12         (((k7_relat_1 @ X35 @ X34) = (k5_relat_1 @ (k6_relat_1 @ X34) @ X35))
% 6.93/7.12          | ~ (v1_relat_1 @ X35))),
% 6.93/7.12      inference('cnf', [status(esa)], [t94_relat_1])).
% 6.93/7.12  thf(t71_relat_1, axiom,
% 6.93/7.12    (![A:$i]:
% 6.93/7.12     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 6.93/7.12       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 6.93/7.12  thf('1', plain, (![X25 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 6.93/7.12      inference('cnf', [status(esa)], [t71_relat_1])).
% 6.93/7.12  thf(t146_relat_1, axiom,
% 6.93/7.12    (![A:$i]:
% 6.93/7.12     ( ( v1_relat_1 @ A ) =>
% 6.93/7.12       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 6.93/7.12  thf('2', plain,
% 6.93/7.12      (![X16 : $i]:
% 6.93/7.12         (((k9_relat_1 @ X16 @ (k1_relat_1 @ X16)) = (k2_relat_1 @ X16))
% 6.93/7.12          | ~ (v1_relat_1 @ X16))),
% 6.93/7.12      inference('cnf', [status(esa)], [t146_relat_1])).
% 6.93/7.12  thf('3', plain,
% 6.93/7.12      (![X0 : $i]:
% 6.93/7.12         (((k9_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 6.93/7.12            = (k2_relat_1 @ (k6_relat_1 @ X0)))
% 6.93/7.12          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 6.93/7.12      inference('sup+', [status(thm)], ['1', '2'])).
% 6.93/7.12  thf('4', plain, (![X26 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 6.93/7.12      inference('cnf', [status(esa)], [t71_relat_1])).
% 6.93/7.12  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 6.93/7.12  thf('5', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.93/7.12      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.93/7.12  thf('6', plain, (![X0 : $i]: ((k9_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 6.93/7.12      inference('demod', [status(thm)], ['3', '4', '5'])).
% 6.93/7.12  thf(t162_relat_1, conjecture,
% 6.93/7.12    (![A:$i]:
% 6.93/7.12     ( ( v1_relat_1 @ A ) =>
% 6.93/7.12       ( ![B:$i,C:$i]:
% 6.93/7.12         ( ( r1_tarski @ B @ C ) =>
% 6.93/7.12           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 6.93/7.12             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 6.93/7.12  thf(zf_stmt_0, negated_conjecture,
% 6.93/7.12    (~( ![A:$i]:
% 6.93/7.12        ( ( v1_relat_1 @ A ) =>
% 6.93/7.12          ( ![B:$i,C:$i]:
% 6.93/7.12            ( ( r1_tarski @ B @ C ) =>
% 6.93/7.12              ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 6.93/7.12                ( k9_relat_1 @ A @ B ) ) ) ) ) )),
% 6.93/7.12    inference('cnf.neg', [status(esa)], [t162_relat_1])).
% 6.93/7.12  thf('7', plain, ((r1_tarski @ sk_B_1 @ sk_C_1)),
% 6.93/7.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.12  thf('8', plain, (![X25 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 6.93/7.12      inference('cnf', [status(esa)], [t71_relat_1])).
% 6.93/7.12  thf(t97_relat_1, axiom,
% 6.93/7.12    (![A:$i,B:$i]:
% 6.93/7.12     ( ( v1_relat_1 @ B ) =>
% 6.93/7.12       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 6.93/7.12         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 6.93/7.12  thf('9', plain,
% 6.93/7.12      (![X36 : $i, X37 : $i]:
% 6.93/7.12         (~ (r1_tarski @ (k1_relat_1 @ X36) @ X37)
% 6.93/7.12          | ((k7_relat_1 @ X36 @ X37) = (X36))
% 6.93/7.12          | ~ (v1_relat_1 @ X36))),
% 6.93/7.12      inference('cnf', [status(esa)], [t97_relat_1])).
% 6.93/7.12  thf('10', plain,
% 6.93/7.12      (![X0 : $i, X1 : $i]:
% 6.93/7.12         (~ (r1_tarski @ X0 @ X1)
% 6.93/7.12          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 6.93/7.12          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 6.93/7.12      inference('sup-', [status(thm)], ['8', '9'])).
% 6.93/7.12  thf('11', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.93/7.12      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.93/7.12  thf('12', plain,
% 6.93/7.12      (![X0 : $i, X1 : $i]:
% 6.93/7.12         (~ (r1_tarski @ X0 @ X1)
% 6.93/7.12          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 6.93/7.12      inference('demod', [status(thm)], ['10', '11'])).
% 6.93/7.12  thf('13', plain,
% 6.93/7.12      (((k7_relat_1 @ (k6_relat_1 @ sk_B_1) @ sk_C_1) = (k6_relat_1 @ sk_B_1))),
% 6.93/7.12      inference('sup-', [status(thm)], ['7', '12'])).
% 6.93/7.12  thf('14', plain,
% 6.93/7.12      (![X34 : $i, X35 : $i]:
% 6.93/7.12         (((k7_relat_1 @ X35 @ X34) = (k5_relat_1 @ (k6_relat_1 @ X34) @ X35))
% 6.93/7.12          | ~ (v1_relat_1 @ X35))),
% 6.93/7.12      inference('cnf', [status(esa)], [t94_relat_1])).
% 6.93/7.12  thf(t76_relat_1, axiom,
% 6.93/7.12    (![A:$i,B:$i]:
% 6.93/7.12     ( ( v1_relat_1 @ B ) =>
% 6.93/7.12       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 6.93/7.12         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 6.93/7.12  thf('15', plain,
% 6.93/7.12      (![X27 : $i, X28 : $i]:
% 6.93/7.12         ((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X28) @ X27) @ X27)
% 6.93/7.12          | ~ (v1_relat_1 @ X27))),
% 6.93/7.12      inference('cnf', [status(esa)], [t76_relat_1])).
% 6.93/7.12  thf(d10_xboole_0, axiom,
% 6.93/7.12    (![A:$i,B:$i]:
% 6.93/7.12     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.93/7.12  thf('16', plain,
% 6.93/7.12      (![X0 : $i, X2 : $i]:
% 6.93/7.12         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 6.93/7.12      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.93/7.12  thf('17', plain,
% 6.93/7.12      (![X0 : $i, X1 : $i]:
% 6.93/7.12         (~ (v1_relat_1 @ X0)
% 6.93/7.12          | ~ (r1_tarski @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 6.93/7.12          | ((X0) = (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 6.93/7.12      inference('sup-', [status(thm)], ['15', '16'])).
% 6.93/7.12  thf('18', plain,
% 6.93/7.12      (![X0 : $i, X1 : $i]:
% 6.93/7.12         (~ (r1_tarski @ X1 @ (k7_relat_1 @ X1 @ X0))
% 6.93/7.12          | ~ (v1_relat_1 @ X1)
% 6.93/7.12          | ((X1) = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 6.93/7.12          | ~ (v1_relat_1 @ X1))),
% 6.93/7.12      inference('sup-', [status(thm)], ['14', '17'])).
% 6.93/7.12  thf('19', plain,
% 6.93/7.12      (![X0 : $i, X1 : $i]:
% 6.93/7.12         (((X1) = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 6.93/7.12          | ~ (v1_relat_1 @ X1)
% 6.93/7.12          | ~ (r1_tarski @ X1 @ (k7_relat_1 @ X1 @ X0)))),
% 6.93/7.12      inference('simplify', [status(thm)], ['18'])).
% 6.93/7.12  thf('20', plain,
% 6.93/7.12      ((~ (r1_tarski @ (k6_relat_1 @ sk_B_1) @ (k6_relat_1 @ sk_B_1))
% 6.93/7.12        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B_1))
% 6.93/7.12        | ((k6_relat_1 @ sk_B_1)
% 6.93/7.12            = (k5_relat_1 @ (k6_relat_1 @ sk_C_1) @ (k6_relat_1 @ sk_B_1))))),
% 6.93/7.12      inference('sup-', [status(thm)], ['13', '19'])).
% 6.93/7.12  thf('21', plain,
% 6.93/7.12      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 6.93/7.12      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.93/7.12  thf('22', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 6.93/7.12      inference('simplify', [status(thm)], ['21'])).
% 6.93/7.12  thf('23', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.93/7.12      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.93/7.12  thf('24', plain,
% 6.93/7.12      (((k6_relat_1 @ sk_B_1)
% 6.93/7.12         = (k5_relat_1 @ (k6_relat_1 @ sk_C_1) @ (k6_relat_1 @ sk_B_1)))),
% 6.93/7.12      inference('demod', [status(thm)], ['20', '22', '23'])).
% 6.93/7.12  thf('25', plain,
% 6.93/7.12      (![X27 : $i, X28 : $i]:
% 6.93/7.12         ((r1_tarski @ (k5_relat_1 @ X27 @ (k6_relat_1 @ X28)) @ X27)
% 6.93/7.12          | ~ (v1_relat_1 @ X27))),
% 6.93/7.12      inference('cnf', [status(esa)], [t76_relat_1])).
% 6.93/7.12  thf('26', plain,
% 6.93/7.12      (((r1_tarski @ (k6_relat_1 @ sk_B_1) @ (k6_relat_1 @ sk_C_1))
% 6.93/7.12        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_C_1)))),
% 6.93/7.12      inference('sup+', [status(thm)], ['24', '25'])).
% 6.93/7.12  thf('27', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.93/7.12      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.93/7.12  thf('28', plain,
% 6.93/7.12      ((r1_tarski @ (k6_relat_1 @ sk_B_1) @ (k6_relat_1 @ sk_C_1))),
% 6.93/7.12      inference('demod', [status(thm)], ['26', '27'])).
% 6.93/7.12  thf(t157_relat_1, axiom,
% 6.93/7.12    (![A:$i,B:$i]:
% 6.93/7.12     ( ( v1_relat_1 @ B ) =>
% 6.93/7.12       ( ![C:$i]:
% 6.93/7.12         ( ( v1_relat_1 @ C ) =>
% 6.93/7.12           ( ( r1_tarski @ B @ C ) =>
% 6.93/7.12             ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ C @ A ) ) ) ) ) ))).
% 6.93/7.12  thf('29', plain,
% 6.93/7.12      (![X19 : $i, X20 : $i, X21 : $i]:
% 6.93/7.12         (~ (v1_relat_1 @ X19)
% 6.93/7.12          | (r1_tarski @ (k9_relat_1 @ X20 @ X21) @ (k9_relat_1 @ X19 @ X21))
% 6.93/7.12          | ~ (r1_tarski @ X20 @ X19)
% 6.93/7.12          | ~ (v1_relat_1 @ X20))),
% 6.93/7.12      inference('cnf', [status(esa)], [t157_relat_1])).
% 6.93/7.12  thf('30', plain,
% 6.93/7.12      (![X0 : $i]:
% 6.93/7.12         (~ (v1_relat_1 @ (k6_relat_1 @ sk_B_1))
% 6.93/7.12          | (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ sk_B_1) @ X0) @ 
% 6.93/7.12             (k9_relat_1 @ (k6_relat_1 @ sk_C_1) @ X0))
% 6.93/7.12          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_C_1)))),
% 6.93/7.12      inference('sup-', [status(thm)], ['28', '29'])).
% 6.93/7.12  thf('31', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.93/7.12      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.93/7.12  thf('32', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.93/7.12      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.93/7.12  thf('33', plain,
% 6.93/7.12      (![X0 : $i]:
% 6.93/7.12         (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ sk_B_1) @ X0) @ 
% 6.93/7.12          (k9_relat_1 @ (k6_relat_1 @ sk_C_1) @ X0))),
% 6.93/7.12      inference('demod', [status(thm)], ['30', '31', '32'])).
% 6.93/7.12  thf('34', plain,
% 6.93/7.12      ((r1_tarski @ sk_B_1 @ (k9_relat_1 @ (k6_relat_1 @ sk_C_1) @ sk_B_1))),
% 6.93/7.12      inference('sup+', [status(thm)], ['6', '33'])).
% 6.93/7.12  thf('35', plain,
% 6.93/7.12      (![X0 : $i, X2 : $i]:
% 6.93/7.12         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 6.93/7.12      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.93/7.12  thf('36', plain,
% 6.93/7.12      ((~ (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ sk_C_1) @ sk_B_1) @ sk_B_1)
% 6.93/7.12        | ((k9_relat_1 @ (k6_relat_1 @ sk_C_1) @ sk_B_1) = (sk_B_1)))),
% 6.93/7.12      inference('sup-', [status(thm)], ['34', '35'])).
% 6.93/7.12  thf('37', plain,
% 6.93/7.12      (![X34 : $i, X35 : $i]:
% 6.93/7.12         (((k7_relat_1 @ X35 @ X34) = (k5_relat_1 @ (k6_relat_1 @ X34) @ X35))
% 6.93/7.12          | ~ (v1_relat_1 @ X35))),
% 6.93/7.12      inference('cnf', [status(esa)], [t94_relat_1])).
% 6.93/7.12  thf('38', plain,
% 6.93/7.12      (((k7_relat_1 @ (k6_relat_1 @ sk_B_1) @ sk_C_1) = (k6_relat_1 @ sk_B_1))),
% 6.93/7.12      inference('sup-', [status(thm)], ['7', '12'])).
% 6.93/7.12  thf(t148_relat_1, axiom,
% 6.93/7.12    (![A:$i,B:$i]:
% 6.93/7.12     ( ( v1_relat_1 @ B ) =>
% 6.93/7.12       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 6.93/7.12  thf('39', plain,
% 6.93/7.12      (![X17 : $i, X18 : $i]:
% 6.93/7.12         (((k2_relat_1 @ (k7_relat_1 @ X17 @ X18)) = (k9_relat_1 @ X17 @ X18))
% 6.93/7.12          | ~ (v1_relat_1 @ X17))),
% 6.93/7.12      inference('cnf', [status(esa)], [t148_relat_1])).
% 6.93/7.12  thf('40', plain,
% 6.93/7.12      ((((k2_relat_1 @ (k6_relat_1 @ sk_B_1))
% 6.93/7.12          = (k9_relat_1 @ (k6_relat_1 @ sk_B_1) @ sk_C_1))
% 6.93/7.12        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B_1)))),
% 6.93/7.12      inference('sup+', [status(thm)], ['38', '39'])).
% 6.93/7.12  thf('41', plain, (![X26 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 6.93/7.12      inference('cnf', [status(esa)], [t71_relat_1])).
% 6.93/7.12  thf('42', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.93/7.12      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.93/7.12  thf('43', plain,
% 6.93/7.12      (((sk_B_1) = (k9_relat_1 @ (k6_relat_1 @ sk_B_1) @ sk_C_1))),
% 6.93/7.12      inference('demod', [status(thm)], ['40', '41', '42'])).
% 6.93/7.12  thf(t159_relat_1, axiom,
% 6.93/7.12    (![A:$i,B:$i]:
% 6.93/7.12     ( ( v1_relat_1 @ B ) =>
% 6.93/7.12       ( ![C:$i]:
% 6.93/7.12         ( ( v1_relat_1 @ C ) =>
% 6.93/7.12           ( ( k9_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 6.93/7.12             ( k9_relat_1 @ C @ ( k9_relat_1 @ B @ A ) ) ) ) ) ))).
% 6.93/7.12  thf('44', plain,
% 6.93/7.12      (![X22 : $i, X23 : $i, X24 : $i]:
% 6.93/7.12         (~ (v1_relat_1 @ X22)
% 6.93/7.12          | ((k9_relat_1 @ (k5_relat_1 @ X23 @ X22) @ X24)
% 6.93/7.12              = (k9_relat_1 @ X22 @ (k9_relat_1 @ X23 @ X24)))
% 6.93/7.12          | ~ (v1_relat_1 @ X23))),
% 6.93/7.12      inference('cnf', [status(esa)], [t159_relat_1])).
% 6.93/7.12  thf('45', plain,
% 6.93/7.12      (![X0 : $i]:
% 6.93/7.12         (((k9_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B_1) @ X0) @ sk_C_1)
% 6.93/7.12            = (k9_relat_1 @ X0 @ sk_B_1))
% 6.93/7.12          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B_1))
% 6.93/7.12          | ~ (v1_relat_1 @ X0))),
% 6.93/7.12      inference('sup+', [status(thm)], ['43', '44'])).
% 6.93/7.12  thf('46', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.93/7.12      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.93/7.12  thf('47', plain,
% 6.93/7.12      (![X0 : $i]:
% 6.93/7.12         (((k9_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B_1) @ X0) @ sk_C_1)
% 6.93/7.12            = (k9_relat_1 @ X0 @ sk_B_1))
% 6.93/7.12          | ~ (v1_relat_1 @ X0))),
% 6.93/7.12      inference('demod', [status(thm)], ['45', '46'])).
% 6.93/7.12  thf('48', plain,
% 6.93/7.12      (![X0 : $i]:
% 6.93/7.12         (((k9_relat_1 @ (k7_relat_1 @ X0 @ sk_B_1) @ sk_C_1)
% 6.93/7.12            = (k9_relat_1 @ X0 @ sk_B_1))
% 6.93/7.12          | ~ (v1_relat_1 @ X0)
% 6.93/7.12          | ~ (v1_relat_1 @ X0))),
% 6.93/7.12      inference('sup+', [status(thm)], ['37', '47'])).
% 6.93/7.12  thf('49', plain,
% 6.93/7.12      (![X0 : $i]:
% 6.93/7.12         (~ (v1_relat_1 @ X0)
% 6.93/7.12          | ((k9_relat_1 @ (k7_relat_1 @ X0 @ sk_B_1) @ sk_C_1)
% 6.93/7.12              = (k9_relat_1 @ X0 @ sk_B_1)))),
% 6.93/7.12      inference('simplify', [status(thm)], ['48'])).
% 6.93/7.12  thf('50', plain,
% 6.93/7.12      (![X34 : $i, X35 : $i]:
% 6.93/7.12         (((k7_relat_1 @ X35 @ X34) = (k5_relat_1 @ (k6_relat_1 @ X34) @ X35))
% 6.93/7.12          | ~ (v1_relat_1 @ X35))),
% 6.93/7.12      inference('cnf', [status(esa)], [t94_relat_1])).
% 6.93/7.12  thf('51', plain,
% 6.93/7.12      (![X27 : $i, X28 : $i]:
% 6.93/7.12         ((r1_tarski @ (k5_relat_1 @ X27 @ (k6_relat_1 @ X28)) @ X27)
% 6.93/7.12          | ~ (v1_relat_1 @ X27))),
% 6.93/7.12      inference('cnf', [status(esa)], [t76_relat_1])).
% 6.93/7.12  thf('52', plain,
% 6.93/7.12      (![X0 : $i, X1 : $i]:
% 6.93/7.12         ((r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 6.93/7.12           (k6_relat_1 @ X0))
% 6.93/7.12          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 6.93/7.12          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 6.93/7.12      inference('sup+', [status(thm)], ['50', '51'])).
% 6.93/7.12  thf('53', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.93/7.12      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.93/7.12  thf('54', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.93/7.12      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.93/7.12  thf('55', plain,
% 6.93/7.12      (![X0 : $i, X1 : $i]:
% 6.93/7.12         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ (k6_relat_1 @ X0))),
% 6.93/7.12      inference('demod', [status(thm)], ['52', '53', '54'])).
% 6.93/7.12  thf('56', plain,
% 6.93/7.12      (![X19 : $i, X20 : $i, X21 : $i]:
% 6.93/7.12         (~ (v1_relat_1 @ X19)
% 6.93/7.12          | (r1_tarski @ (k9_relat_1 @ X20 @ X21) @ (k9_relat_1 @ X19 @ X21))
% 6.93/7.12          | ~ (r1_tarski @ X20 @ X19)
% 6.93/7.12          | ~ (v1_relat_1 @ X20))),
% 6.93/7.12      inference('cnf', [status(esa)], [t157_relat_1])).
% 6.93/7.12  thf('57', plain,
% 6.93/7.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.93/7.12         (~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 6.93/7.12          | (r1_tarski @ 
% 6.93/7.12             (k9_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2) @ 
% 6.93/7.12             (k9_relat_1 @ (k6_relat_1 @ X0) @ X2))
% 6.93/7.12          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 6.93/7.12      inference('sup-', [status(thm)], ['55', '56'])).
% 6.93/7.12  thf('58', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.93/7.12      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.93/7.12  thf('59', plain,
% 6.93/7.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.93/7.12         (~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 6.93/7.12          | (r1_tarski @ 
% 6.93/7.12             (k9_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2) @ 
% 6.93/7.12             (k9_relat_1 @ (k6_relat_1 @ X0) @ X2)))),
% 6.93/7.12      inference('demod', [status(thm)], ['57', '58'])).
% 6.93/7.12  thf('60', plain,
% 6.93/7.12      (![X0 : $i, X1 : $i]:
% 6.93/7.12         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ (k6_relat_1 @ X0))),
% 6.93/7.12      inference('demod', [status(thm)], ['52', '53', '54'])).
% 6.93/7.12  thf(t12_xboole_1, axiom,
% 6.93/7.12    (![A:$i,B:$i]:
% 6.93/7.12     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 6.93/7.12  thf('61', plain,
% 6.93/7.12      (![X6 : $i, X7 : $i]:
% 6.93/7.12         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 6.93/7.12      inference('cnf', [status(esa)], [t12_xboole_1])).
% 6.93/7.12  thf('62', plain,
% 6.93/7.12      (![X0 : $i, X1 : $i]:
% 6.93/7.12         ((k2_xboole_0 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 6.93/7.12           (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 6.93/7.12      inference('sup-', [status(thm)], ['60', '61'])).
% 6.93/7.12  thf(d1_relat_1, axiom,
% 6.93/7.12    (![A:$i]:
% 6.93/7.12     ( ( v1_relat_1 @ A ) <=>
% 6.93/7.12       ( ![B:$i]:
% 6.93/7.12         ( ~( ( r2_hidden @ B @ A ) & 
% 6.93/7.12              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 6.93/7.12  thf('63', plain,
% 6.93/7.12      (![X10 : $i]: ((v1_relat_1 @ X10) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 6.93/7.12      inference('cnf', [status(esa)], [d1_relat_1])).
% 6.93/7.12  thf('64', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 6.93/7.12      inference('simplify', [status(thm)], ['21'])).
% 6.93/7.12  thf(t11_xboole_1, axiom,
% 6.93/7.12    (![A:$i,B:$i,C:$i]:
% 6.93/7.12     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 6.93/7.12  thf('65', plain,
% 6.93/7.12      (![X3 : $i, X4 : $i, X5 : $i]:
% 6.93/7.12         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 6.93/7.12      inference('cnf', [status(esa)], [t11_xboole_1])).
% 6.93/7.12  thf('66', plain,
% 6.93/7.12      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 6.93/7.12      inference('sup-', [status(thm)], ['64', '65'])).
% 6.93/7.12  thf('67', plain,
% 6.93/7.12      (![X0 : $i, X1 : $i]:
% 6.93/7.12         (~ (r1_tarski @ X0 @ X1)
% 6.93/7.12          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 6.93/7.12      inference('demod', [status(thm)], ['10', '11'])).
% 6.93/7.12  thf('68', plain,
% 6.93/7.12      (![X0 : $i, X1 : $i]:
% 6.93/7.12         ((k7_relat_1 @ (k6_relat_1 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 6.93/7.12           = (k6_relat_1 @ X1))),
% 6.93/7.12      inference('sup-', [status(thm)], ['66', '67'])).
% 6.93/7.12  thf(t86_relat_1, axiom,
% 6.93/7.12    (![A:$i,B:$i,C:$i]:
% 6.93/7.12     ( ( v1_relat_1 @ C ) =>
% 6.93/7.12       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 6.93/7.12         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 6.93/7.12  thf('69', plain,
% 6.93/7.12      (![X29 : $i, X30 : $i, X31 : $i]:
% 6.93/7.12         (~ (r2_hidden @ X29 @ (k1_relat_1 @ (k7_relat_1 @ X31 @ X30)))
% 6.93/7.12          | (r2_hidden @ X29 @ X30)
% 6.93/7.12          | ~ (v1_relat_1 @ X31))),
% 6.93/7.12      inference('cnf', [status(esa)], [t86_relat_1])).
% 6.93/7.12  thf('70', plain,
% 6.93/7.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.93/7.12         (~ (r2_hidden @ X2 @ (k1_relat_1 @ (k6_relat_1 @ X0)))
% 6.93/7.12          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 6.93/7.12          | (r2_hidden @ X2 @ (k2_xboole_0 @ X0 @ X1)))),
% 6.93/7.12      inference('sup-', [status(thm)], ['68', '69'])).
% 6.93/7.12  thf('71', plain, (![X25 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 6.93/7.12      inference('cnf', [status(esa)], [t71_relat_1])).
% 6.93/7.12  thf('72', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.93/7.12      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.93/7.12  thf('73', plain,
% 6.93/7.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.93/7.12         (~ (r2_hidden @ X2 @ X0) | (r2_hidden @ X2 @ (k2_xboole_0 @ X0 @ X1)))),
% 6.93/7.12      inference('demod', [status(thm)], ['70', '71', '72'])).
% 6.93/7.12  thf('74', plain,
% 6.93/7.12      (![X0 : $i, X1 : $i]:
% 6.93/7.12         ((v1_relat_1 @ X0)
% 6.93/7.12          | (r2_hidden @ (sk_B @ X0) @ (k2_xboole_0 @ X0 @ X1)))),
% 6.93/7.12      inference('sup-', [status(thm)], ['63', '73'])).
% 6.93/7.12  thf('75', plain,
% 6.93/7.12      (![X8 : $i, X9 : $i]:
% 6.93/7.12         (((X8) = (k4_tarski @ (sk_C @ X8) @ (sk_D @ X8)))
% 6.93/7.12          | ~ (r2_hidden @ X8 @ X9)
% 6.93/7.12          | ~ (v1_relat_1 @ X9))),
% 6.93/7.12      inference('cnf', [status(esa)], [d1_relat_1])).
% 6.93/7.12  thf('76', plain,
% 6.93/7.12      (![X0 : $i, X1 : $i]:
% 6.93/7.12         ((v1_relat_1 @ X1)
% 6.93/7.12          | ~ (v1_relat_1 @ (k2_xboole_0 @ X1 @ X0))
% 6.93/7.12          | ((sk_B @ X1)
% 6.93/7.12              = (k4_tarski @ (sk_C @ (sk_B @ X1)) @ (sk_D @ (sk_B @ X1)))))),
% 6.93/7.12      inference('sup-', [status(thm)], ['74', '75'])).
% 6.93/7.12  thf('77', plain,
% 6.93/7.12      (![X10 : $i, X11 : $i, X12 : $i]:
% 6.93/7.12         ((v1_relat_1 @ X10) | ((sk_B @ X10) != (k4_tarski @ X11 @ X12)))),
% 6.93/7.12      inference('cnf', [status(esa)], [d1_relat_1])).
% 6.93/7.12  thf('78', plain,
% 6.93/7.12      (![X0 : $i, X1 : $i]:
% 6.93/7.12         (~ (v1_relat_1 @ (k2_xboole_0 @ X1 @ X0)) | (v1_relat_1 @ X1))),
% 6.93/7.12      inference('clc', [status(thm)], ['76', '77'])).
% 6.93/7.12  thf('79', plain,
% 6.93/7.12      (![X0 : $i, X1 : $i]:
% 6.93/7.12         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 6.93/7.12          | (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 6.93/7.12      inference('sup-', [status(thm)], ['62', '78'])).
% 6.93/7.12  thf('80', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.93/7.12      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.93/7.12  thf('81', plain,
% 6.93/7.12      (![X0 : $i, X1 : $i]:
% 6.93/7.12         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 6.93/7.12      inference('demod', [status(thm)], ['79', '80'])).
% 6.93/7.12  thf('82', plain,
% 6.93/7.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.93/7.12         (r1_tarski @ 
% 6.93/7.12          (k9_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2) @ 
% 6.93/7.12          (k9_relat_1 @ (k6_relat_1 @ X0) @ X2))),
% 6.93/7.12      inference('demod', [status(thm)], ['59', '81'])).
% 6.93/7.12  thf('83', plain,
% 6.93/7.12      (![X0 : $i]:
% 6.93/7.12         ((r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ sk_B_1) @ 
% 6.93/7.12           (k9_relat_1 @ (k6_relat_1 @ sk_B_1) @ sk_C_1))
% 6.93/7.12          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 6.93/7.12      inference('sup+', [status(thm)], ['49', '82'])).
% 6.93/7.12  thf('84', plain,
% 6.93/7.12      (((sk_B_1) = (k9_relat_1 @ (k6_relat_1 @ sk_B_1) @ sk_C_1))),
% 6.93/7.12      inference('demod', [status(thm)], ['40', '41', '42'])).
% 6.93/7.12  thf('85', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.93/7.12      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.93/7.12  thf('86', plain,
% 6.93/7.12      (![X0 : $i]:
% 6.93/7.12         (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ sk_B_1) @ sk_B_1)),
% 6.93/7.12      inference('demod', [status(thm)], ['83', '84', '85'])).
% 6.93/7.12  thf('87', plain,
% 6.93/7.12      (((k9_relat_1 @ (k6_relat_1 @ sk_C_1) @ sk_B_1) = (sk_B_1))),
% 6.93/7.12      inference('demod', [status(thm)], ['36', '86'])).
% 6.93/7.12  thf('88', plain,
% 6.93/7.12      (![X22 : $i, X23 : $i, X24 : $i]:
% 6.93/7.12         (~ (v1_relat_1 @ X22)
% 6.93/7.12          | ((k9_relat_1 @ (k5_relat_1 @ X23 @ X22) @ X24)
% 6.93/7.12              = (k9_relat_1 @ X22 @ (k9_relat_1 @ X23 @ X24)))
% 6.93/7.12          | ~ (v1_relat_1 @ X23))),
% 6.93/7.12      inference('cnf', [status(esa)], [t159_relat_1])).
% 6.93/7.12  thf('89', plain,
% 6.93/7.12      (![X0 : $i]:
% 6.93/7.12         (((k9_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C_1) @ X0) @ sk_B_1)
% 6.93/7.12            = (k9_relat_1 @ X0 @ sk_B_1))
% 6.93/7.12          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_C_1))
% 6.93/7.12          | ~ (v1_relat_1 @ X0))),
% 6.93/7.12      inference('sup+', [status(thm)], ['87', '88'])).
% 6.93/7.12  thf('90', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 6.93/7.12      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.93/7.12  thf('91', plain,
% 6.93/7.12      (![X0 : $i]:
% 6.93/7.12         (((k9_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C_1) @ X0) @ sk_B_1)
% 6.93/7.12            = (k9_relat_1 @ X0 @ sk_B_1))
% 6.93/7.12          | ~ (v1_relat_1 @ X0))),
% 6.93/7.12      inference('demod', [status(thm)], ['89', '90'])).
% 6.93/7.12  thf('92', plain,
% 6.93/7.12      (![X0 : $i]:
% 6.93/7.12         (((k9_relat_1 @ (k7_relat_1 @ X0 @ sk_C_1) @ sk_B_1)
% 6.93/7.12            = (k9_relat_1 @ X0 @ sk_B_1))
% 6.93/7.12          | ~ (v1_relat_1 @ X0)
% 6.93/7.12          | ~ (v1_relat_1 @ X0))),
% 6.93/7.12      inference('sup+', [status(thm)], ['0', '91'])).
% 6.93/7.12  thf('93', plain,
% 6.93/7.12      (![X0 : $i]:
% 6.93/7.12         (~ (v1_relat_1 @ X0)
% 6.93/7.12          | ((k9_relat_1 @ (k7_relat_1 @ X0 @ sk_C_1) @ sk_B_1)
% 6.93/7.12              = (k9_relat_1 @ X0 @ sk_B_1)))),
% 6.93/7.12      inference('simplify', [status(thm)], ['92'])).
% 6.93/7.12  thf('94', plain,
% 6.93/7.12      (((k9_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1) @ sk_B_1)
% 6.93/7.12         != (k9_relat_1 @ sk_A @ sk_B_1))),
% 6.93/7.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.12  thf('95', plain,
% 6.93/7.12      ((((k9_relat_1 @ sk_A @ sk_B_1) != (k9_relat_1 @ sk_A @ sk_B_1))
% 6.93/7.12        | ~ (v1_relat_1 @ sk_A))),
% 6.93/7.12      inference('sup-', [status(thm)], ['93', '94'])).
% 6.93/7.12  thf('96', plain, ((v1_relat_1 @ sk_A)),
% 6.93/7.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.12  thf('97', plain,
% 6.93/7.12      (((k9_relat_1 @ sk_A @ sk_B_1) != (k9_relat_1 @ sk_A @ sk_B_1))),
% 6.93/7.12      inference('demod', [status(thm)], ['95', '96'])).
% 6.93/7.12  thf('98', plain, ($false), inference('simplify', [status(thm)], ['97'])).
% 6.93/7.12  
% 6.93/7.12  % SZS output end Refutation
% 6.93/7.12  
% 6.99/7.13  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
