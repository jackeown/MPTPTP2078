%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KPDOAHb4qh

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:24 EST 2020

% Result     : Theorem 2.45s
% Output     : Refutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 378 expanded)
%              Number of leaves         :   25 ( 136 expanded)
%              Depth                    :   33
%              Number of atoms          : 1197 (3305 expanded)
%              Number of equality atoms :   60 ( 191 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t146_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
         => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t146_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t181_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X18 @ X17 ) @ X19 )
        = ( k10_relat_1 @ X18 @ ( k10_relat_1 @ X17 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) )
        = ( k9_relat_1 @ X9 @ ( k2_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X13: $i] :
      ( ( ( k10_relat_1 @ X13 @ ( k2_relat_1 @ X13 ) )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k2_relat_1 @ X1 ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k2_relat_1 @ X1 ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X21 @ X20 ) )
        = ( k10_relat_1 @ X21 @ ( k1_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('10',plain,(
    ! [X23: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('11',plain,(
    ! [X13: $i] :
      ( ( ( k10_relat_1 @ X13 @ ( k2_relat_1 @ X13 ) )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X22: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('14',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ! [X13: $i] :
      ( ( ( k10_relat_1 @ X13 @ ( k2_relat_1 @ X13 ) )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('17',plain,(
    ! [X13: $i] :
      ( ( ( k10_relat_1 @ X13 @ ( k2_relat_1 @ X13 ) )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('18',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X11 @ X12 ) @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('19',plain,(
    ! [X22: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('20',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X11 @ X12 ) @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('24',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ X0 @ X1 ) ) @ X2 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ X0 @ X2 ) ) @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ X0 @ X2 ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['16','30'])).

thf('32',plain,(
    ! [X22: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('36',plain,(
    ! [X23: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['31','32','34','35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(t178_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('46',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X16 )
      | ( r1_tarski @ ( k10_relat_1 @ X16 @ X14 ) @ ( k10_relat_1 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ sk_A ) @ ( k10_relat_1 @ X0 @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','47'])).

thf('49',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('50',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X22: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('52',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X11 @ X12 ) @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('53',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X22: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('57',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( X0
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( sk_A
    = ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['50','58'])).

thf('60',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('61',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X18 @ X17 ) @ X19 )
        = ( k10_relat_1 @ X18 @ ( k10_relat_1 @ X17 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf('62',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X11 @ X12 ) @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k10_relat_1 @ X0 @ X2 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k10_relat_1 @ X0 @ X2 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['59','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('69',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('71',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) @ sk_A )
    | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) @ sk_A )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['9','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('74',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X16 )
      | ( r1_tarski @ ( k10_relat_1 @ X16 @ X14 ) @ ( k10_relat_1 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ sk_A ) @ ( k10_relat_1 @ X0 @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('79',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( X0
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('81',plain,
    ( sk_A
    = ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('83',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('84',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['72','81','82','83','84'])).

thf('86',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X11 @ X12 ) @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
      | ( r1_tarski @ ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','87'])).

thf('89',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ X0 ) )
      | ( sk_A
        = ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    | ( sk_A
      = ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ ( k6_relat_1 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['7','93'])).

thf('95',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['72','81','82','83','84'])).

thf('96',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('97',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('99',plain,(
    ! [X23: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('100',plain,
    ( sk_A
    = ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['94','95','96','97','98','99'])).

thf('101',plain,
    ( ( sk_A
      = ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','100'])).

thf('102',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('103',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( sk_A
    = ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('105',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X26 @ ( k10_relat_1 @ X26 @ X27 ) ) @ X27 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('106',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_A ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X22: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('108',plain,(
    ! [X8: $i] :
      ( ( ( k9_relat_1 @ X8 @ ( k1_relat_1 @ X8 ) )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X23: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('111',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('114',plain,(
    ! [X25: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('115',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['106','112','113','114'])).

thf('116',plain,(
    $false ),
    inference(demod,[status(thm)],['0','115'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KPDOAHb4qh
% 0.15/0.38  % Computer   : n019.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 20:48:07 EST 2020
% 0.15/0.39  % CPUTime    : 
% 0.15/0.39  % Running portfolio for 600 s
% 0.15/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.39  % Number of cores: 8
% 0.15/0.39  % Python version: Python 3.6.8
% 0.24/0.39  % Running in FO mode
% 2.45/2.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.45/2.64  % Solved by: fo/fo7.sh
% 2.45/2.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.45/2.64  % done 2289 iterations in 2.141s
% 2.45/2.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.45/2.64  % SZS output start Refutation
% 2.45/2.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.45/2.64  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.45/2.64  thf(sk_A_type, type, sk_A: $i).
% 2.45/2.64  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 2.45/2.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.45/2.64  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.45/2.64  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.45/2.64  thf(sk_B_type, type, sk_B: $i).
% 2.45/2.64  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.45/2.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.45/2.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.45/2.64  thf(t146_funct_1, conjecture,
% 2.45/2.64    (![A:$i,B:$i]:
% 2.45/2.64     ( ( v1_relat_1 @ B ) =>
% 2.45/2.64       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 2.45/2.64         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 2.45/2.64  thf(zf_stmt_0, negated_conjecture,
% 2.45/2.64    (~( ![A:$i,B:$i]:
% 2.45/2.64        ( ( v1_relat_1 @ B ) =>
% 2.45/2.64          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 2.45/2.64            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 2.45/2.64    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 2.45/2.64  thf('0', plain,
% 2.45/2.64      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 2.45/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.45/2.64  thf(t181_relat_1, axiom,
% 2.45/2.64    (![A:$i,B:$i]:
% 2.45/2.64     ( ( v1_relat_1 @ B ) =>
% 2.45/2.64       ( ![C:$i]:
% 2.45/2.64         ( ( v1_relat_1 @ C ) =>
% 2.45/2.64           ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 2.45/2.64             ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 2.45/2.64  thf('1', plain,
% 2.45/2.64      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.45/2.64         (~ (v1_relat_1 @ X17)
% 2.45/2.64          | ((k10_relat_1 @ (k5_relat_1 @ X18 @ X17) @ X19)
% 2.45/2.64              = (k10_relat_1 @ X18 @ (k10_relat_1 @ X17 @ X19)))
% 2.45/2.64          | ~ (v1_relat_1 @ X18))),
% 2.45/2.64      inference('cnf', [status(esa)], [t181_relat_1])).
% 2.45/2.64  thf(dt_k5_relat_1, axiom,
% 2.45/2.64    (![A:$i,B:$i]:
% 2.45/2.64     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 2.45/2.64       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 2.45/2.64  thf('2', plain,
% 2.45/2.64      (![X6 : $i, X7 : $i]:
% 2.45/2.64         (~ (v1_relat_1 @ X6)
% 2.45/2.64          | ~ (v1_relat_1 @ X7)
% 2.45/2.64          | (v1_relat_1 @ (k5_relat_1 @ X6 @ X7)))),
% 2.45/2.64      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 2.45/2.64  thf(t160_relat_1, axiom,
% 2.45/2.64    (![A:$i]:
% 2.45/2.64     ( ( v1_relat_1 @ A ) =>
% 2.45/2.64       ( ![B:$i]:
% 2.45/2.64         ( ( v1_relat_1 @ B ) =>
% 2.45/2.64           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 2.45/2.64             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 2.45/2.64  thf('3', plain,
% 2.45/2.64      (![X9 : $i, X10 : $i]:
% 2.45/2.64         (~ (v1_relat_1 @ X9)
% 2.45/2.64          | ((k2_relat_1 @ (k5_relat_1 @ X10 @ X9))
% 2.45/2.64              = (k9_relat_1 @ X9 @ (k2_relat_1 @ X10)))
% 2.45/2.64          | ~ (v1_relat_1 @ X10))),
% 2.45/2.64      inference('cnf', [status(esa)], [t160_relat_1])).
% 2.45/2.64  thf(t169_relat_1, axiom,
% 2.45/2.64    (![A:$i]:
% 2.45/2.64     ( ( v1_relat_1 @ A ) =>
% 2.45/2.64       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 2.45/2.64  thf('4', plain,
% 2.45/2.64      (![X13 : $i]:
% 2.45/2.64         (((k10_relat_1 @ X13 @ (k2_relat_1 @ X13)) = (k1_relat_1 @ X13))
% 2.45/2.64          | ~ (v1_relat_1 @ X13))),
% 2.45/2.64      inference('cnf', [status(esa)], [t169_relat_1])).
% 2.45/2.64  thf('5', plain,
% 2.45/2.64      (![X0 : $i, X1 : $i]:
% 2.45/2.64         (((k10_relat_1 @ (k5_relat_1 @ X0 @ X1) @ 
% 2.45/2.64            (k9_relat_1 @ X1 @ (k2_relat_1 @ X0)))
% 2.45/2.64            = (k1_relat_1 @ (k5_relat_1 @ X0 @ X1)))
% 2.45/2.64          | ~ (v1_relat_1 @ X0)
% 2.45/2.64          | ~ (v1_relat_1 @ X1)
% 2.45/2.64          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 2.45/2.64      inference('sup+', [status(thm)], ['3', '4'])).
% 2.45/2.64  thf('6', plain,
% 2.45/2.64      (![X0 : $i, X1 : $i]:
% 2.45/2.64         (~ (v1_relat_1 @ X0)
% 2.45/2.64          | ~ (v1_relat_1 @ X1)
% 2.45/2.64          | ~ (v1_relat_1 @ X0)
% 2.45/2.64          | ~ (v1_relat_1 @ X1)
% 2.45/2.64          | ((k10_relat_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 2.45/2.64              (k9_relat_1 @ X0 @ (k2_relat_1 @ X1)))
% 2.45/2.64              = (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 2.45/2.64      inference('sup-', [status(thm)], ['2', '5'])).
% 2.45/2.64  thf('7', plain,
% 2.45/2.64      (![X0 : $i, X1 : $i]:
% 2.45/2.64         (((k10_relat_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 2.45/2.64            (k9_relat_1 @ X0 @ (k2_relat_1 @ X1)))
% 2.45/2.64            = (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 2.45/2.64          | ~ (v1_relat_1 @ X1)
% 2.45/2.64          | ~ (v1_relat_1 @ X0))),
% 2.45/2.64      inference('simplify', [status(thm)], ['6'])).
% 2.45/2.64  thf('8', plain,
% 2.45/2.64      (![X6 : $i, X7 : $i]:
% 2.45/2.64         (~ (v1_relat_1 @ X6)
% 2.45/2.64          | ~ (v1_relat_1 @ X7)
% 2.45/2.64          | (v1_relat_1 @ (k5_relat_1 @ X6 @ X7)))),
% 2.45/2.64      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 2.45/2.64  thf(t182_relat_1, axiom,
% 2.45/2.64    (![A:$i]:
% 2.45/2.64     ( ( v1_relat_1 @ A ) =>
% 2.45/2.64       ( ![B:$i]:
% 2.45/2.64         ( ( v1_relat_1 @ B ) =>
% 2.45/2.64           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 2.45/2.64             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 2.45/2.64  thf('9', plain,
% 2.45/2.64      (![X20 : $i, X21 : $i]:
% 2.45/2.64         (~ (v1_relat_1 @ X20)
% 2.45/2.64          | ((k1_relat_1 @ (k5_relat_1 @ X21 @ X20))
% 2.45/2.64              = (k10_relat_1 @ X21 @ (k1_relat_1 @ X20)))
% 2.45/2.64          | ~ (v1_relat_1 @ X21))),
% 2.45/2.64      inference('cnf', [status(esa)], [t182_relat_1])).
% 2.45/2.64  thf(t71_relat_1, axiom,
% 2.45/2.64    (![A:$i]:
% 2.45/2.64     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 2.45/2.64       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 2.45/2.64  thf('10', plain, (![X23 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 2.45/2.64      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.45/2.64  thf('11', plain,
% 2.45/2.64      (![X13 : $i]:
% 2.45/2.64         (((k10_relat_1 @ X13 @ (k2_relat_1 @ X13)) = (k1_relat_1 @ X13))
% 2.45/2.64          | ~ (v1_relat_1 @ X13))),
% 2.45/2.64      inference('cnf', [status(esa)], [t169_relat_1])).
% 2.45/2.64  thf('12', plain,
% 2.45/2.64      (![X0 : $i]:
% 2.45/2.64         (((k10_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 2.45/2.64            = (k1_relat_1 @ (k6_relat_1 @ X0)))
% 2.45/2.64          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.45/2.64      inference('sup+', [status(thm)], ['10', '11'])).
% 2.45/2.64  thf('13', plain, (![X22 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 2.45/2.64      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.45/2.64  thf(fc3_funct_1, axiom,
% 2.45/2.64    (![A:$i]:
% 2.45/2.64     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 2.45/2.64       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 2.45/2.64  thf('14', plain, (![X24 : $i]: (v1_relat_1 @ (k6_relat_1 @ X24))),
% 2.45/2.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.45/2.64  thf('15', plain,
% 2.45/2.64      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 2.45/2.64      inference('demod', [status(thm)], ['12', '13', '14'])).
% 2.45/2.64  thf('16', plain,
% 2.45/2.64      (![X13 : $i]:
% 2.45/2.64         (((k10_relat_1 @ X13 @ (k2_relat_1 @ X13)) = (k1_relat_1 @ X13))
% 2.45/2.64          | ~ (v1_relat_1 @ X13))),
% 2.45/2.64      inference('cnf', [status(esa)], [t169_relat_1])).
% 2.45/2.64  thf('17', plain,
% 2.45/2.64      (![X13 : $i]:
% 2.45/2.64         (((k10_relat_1 @ X13 @ (k2_relat_1 @ X13)) = (k1_relat_1 @ X13))
% 2.45/2.64          | ~ (v1_relat_1 @ X13))),
% 2.45/2.64      inference('cnf', [status(esa)], [t169_relat_1])).
% 2.45/2.64  thf(t167_relat_1, axiom,
% 2.45/2.64    (![A:$i,B:$i]:
% 2.45/2.64     ( ( v1_relat_1 @ B ) =>
% 2.45/2.64       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 2.45/2.64  thf('18', plain,
% 2.45/2.64      (![X11 : $i, X12 : $i]:
% 2.45/2.64         ((r1_tarski @ (k10_relat_1 @ X11 @ X12) @ (k1_relat_1 @ X11))
% 2.45/2.64          | ~ (v1_relat_1 @ X11))),
% 2.45/2.64      inference('cnf', [status(esa)], [t167_relat_1])).
% 2.45/2.64  thf('19', plain, (![X22 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 2.45/2.64      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.45/2.64  thf('20', plain,
% 2.45/2.64      (![X11 : $i, X12 : $i]:
% 2.45/2.64         ((r1_tarski @ (k10_relat_1 @ X11 @ X12) @ (k1_relat_1 @ X11))
% 2.45/2.64          | ~ (v1_relat_1 @ X11))),
% 2.45/2.64      inference('cnf', [status(esa)], [t167_relat_1])).
% 2.45/2.64  thf('21', plain,
% 2.45/2.64      (![X0 : $i, X1 : $i]:
% 2.45/2.64         ((r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)
% 2.45/2.64          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.45/2.64      inference('sup+', [status(thm)], ['19', '20'])).
% 2.45/2.64  thf('22', plain, (![X24 : $i]: (v1_relat_1 @ (k6_relat_1 @ X24))),
% 2.45/2.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.45/2.64  thf('23', plain,
% 2.45/2.64      (![X0 : $i, X1 : $i]:
% 2.45/2.64         (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)),
% 2.45/2.64      inference('demod', [status(thm)], ['21', '22'])).
% 2.45/2.64  thf(t1_xboole_1, axiom,
% 2.45/2.64    (![A:$i,B:$i,C:$i]:
% 2.45/2.64     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 2.45/2.64       ( r1_tarski @ A @ C ) ))).
% 2.45/2.64  thf('24', plain,
% 2.45/2.64      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.45/2.64         (~ (r1_tarski @ X3 @ X4)
% 2.45/2.64          | ~ (r1_tarski @ X4 @ X5)
% 2.45/2.64          | (r1_tarski @ X3 @ X5))),
% 2.45/2.64      inference('cnf', [status(esa)], [t1_xboole_1])).
% 2.45/2.64  thf('25', plain,
% 2.45/2.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.45/2.64         ((r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X2)
% 2.45/2.64          | ~ (r1_tarski @ X0 @ X2))),
% 2.45/2.64      inference('sup-', [status(thm)], ['23', '24'])).
% 2.45/2.64  thf('26', plain,
% 2.45/2.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.45/2.64         (~ (v1_relat_1 @ X0)
% 2.45/2.64          | (r1_tarski @ 
% 2.45/2.64             (k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ X0 @ X1)) @ X2) @ 
% 2.45/2.64             (k1_relat_1 @ X0)))),
% 2.45/2.64      inference('sup-', [status(thm)], ['18', '25'])).
% 2.45/2.64  thf(d10_xboole_0, axiom,
% 2.45/2.64    (![A:$i,B:$i]:
% 2.45/2.64     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.45/2.64  thf('27', plain,
% 2.45/2.64      (![X0 : $i, X2 : $i]:
% 2.45/2.64         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.45/2.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.45/2.64  thf('28', plain,
% 2.45/2.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.45/2.64         (~ (v1_relat_1 @ X0)
% 2.45/2.64          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ 
% 2.45/2.64               (k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ X0 @ X2)) @ X1))
% 2.45/2.64          | ((k1_relat_1 @ X0)
% 2.45/2.64              = (k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ X0 @ X2)) @ X1)))),
% 2.45/2.64      inference('sup-', [status(thm)], ['26', '27'])).
% 2.45/2.64  thf('29', plain,
% 2.45/2.64      (![X0 : $i, X1 : $i]:
% 2.45/2.64         (~ (r1_tarski @ (k1_relat_1 @ X0) @ 
% 2.45/2.64             (k10_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X1))
% 2.45/2.64          | ~ (v1_relat_1 @ X0)
% 2.45/2.64          | ((k1_relat_1 @ X0)
% 2.45/2.64              = (k10_relat_1 @ 
% 2.45/2.64                 (k6_relat_1 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))) @ X1))
% 2.45/2.64          | ~ (v1_relat_1 @ X0))),
% 2.45/2.64      inference('sup-', [status(thm)], ['17', '28'])).
% 2.45/2.64  thf('30', plain,
% 2.45/2.64      (![X0 : $i, X1 : $i]:
% 2.45/2.64         (((k1_relat_1 @ X0)
% 2.45/2.64            = (k10_relat_1 @ 
% 2.45/2.64               (k6_relat_1 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))) @ X1))
% 2.45/2.64          | ~ (v1_relat_1 @ X0)
% 2.45/2.64          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ 
% 2.45/2.64               (k10_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X1)))),
% 2.45/2.64      inference('simplify', [status(thm)], ['29'])).
% 2.45/2.64  thf('31', plain,
% 2.45/2.64      (![X0 : $i]:
% 2.45/2.64         (~ (r1_tarski @ (k1_relat_1 @ X0) @ 
% 2.45/2.64             (k1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0))))
% 2.45/2.64          | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 2.45/2.64          | ~ (v1_relat_1 @ X0)
% 2.45/2.64          | ((k1_relat_1 @ X0)
% 2.45/2.64              = (k10_relat_1 @ 
% 2.45/2.64                 (k6_relat_1 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))) @ 
% 2.45/2.64                 (k2_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0))))))),
% 2.45/2.64      inference('sup-', [status(thm)], ['16', '30'])).
% 2.45/2.64  thf('32', plain, (![X22 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 2.45/2.64      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.45/2.64  thf('33', plain,
% 2.45/2.64      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 2.45/2.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.45/2.64  thf('34', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.45/2.64      inference('simplify', [status(thm)], ['33'])).
% 2.45/2.64  thf('35', plain, (![X24 : $i]: (v1_relat_1 @ (k6_relat_1 @ X24))),
% 2.45/2.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.45/2.64  thf('36', plain, (![X23 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 2.45/2.64      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.45/2.64  thf('37', plain,
% 2.45/2.64      (![X0 : $i]:
% 2.45/2.64         (~ (v1_relat_1 @ X0)
% 2.45/2.64          | ((k1_relat_1 @ X0)
% 2.45/2.64              = (k10_relat_1 @ 
% 2.45/2.64                 (k6_relat_1 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))) @ 
% 2.45/2.64                 (k1_relat_1 @ X0))))),
% 2.45/2.64      inference('demod', [status(thm)], ['31', '32', '34', '35', '36'])).
% 2.45/2.64  thf('38', plain,
% 2.45/2.64      (![X0 : $i, X1 : $i]:
% 2.45/2.64         (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)),
% 2.45/2.64      inference('demod', [status(thm)], ['21', '22'])).
% 2.45/2.64  thf('39', plain,
% 2.45/2.64      (![X0 : $i]:
% 2.45/2.64         ((r1_tarski @ (k1_relat_1 @ X0) @ 
% 2.45/2.64           (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 2.45/2.64          | ~ (v1_relat_1 @ X0))),
% 2.45/2.64      inference('sup+', [status(thm)], ['37', '38'])).
% 2.45/2.64  thf('40', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 2.45/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.45/2.64  thf('41', plain,
% 2.45/2.64      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.45/2.64         (~ (r1_tarski @ X3 @ X4)
% 2.45/2.64          | ~ (r1_tarski @ X4 @ X5)
% 2.45/2.64          | (r1_tarski @ X3 @ X5))),
% 2.45/2.64      inference('cnf', [status(esa)], [t1_xboole_1])).
% 2.45/2.64  thf('42', plain,
% 2.45/2.64      (![X0 : $i]:
% 2.45/2.64         ((r1_tarski @ sk_A @ X0) | ~ (r1_tarski @ (k1_relat_1 @ sk_B) @ X0))),
% 2.45/2.64      inference('sup-', [status(thm)], ['40', '41'])).
% 2.45/2.64  thf('43', plain,
% 2.45/2.64      ((~ (v1_relat_1 @ sk_B)
% 2.45/2.64        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))))),
% 2.45/2.64      inference('sup-', [status(thm)], ['39', '42'])).
% 2.45/2.64  thf('44', plain, ((v1_relat_1 @ sk_B)),
% 2.45/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.45/2.64  thf('45', plain,
% 2.45/2.64      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 2.45/2.64      inference('demod', [status(thm)], ['43', '44'])).
% 2.45/2.64  thf(t178_relat_1, axiom,
% 2.45/2.64    (![A:$i,B:$i,C:$i]:
% 2.45/2.64     ( ( v1_relat_1 @ C ) =>
% 2.45/2.64       ( ( r1_tarski @ A @ B ) =>
% 2.45/2.64         ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 2.45/2.64  thf('46', plain,
% 2.45/2.64      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.45/2.64         (~ (r1_tarski @ X14 @ X15)
% 2.45/2.64          | ~ (v1_relat_1 @ X16)
% 2.45/2.64          | (r1_tarski @ (k10_relat_1 @ X16 @ X14) @ (k10_relat_1 @ X16 @ X15)))),
% 2.45/2.64      inference('cnf', [status(esa)], [t178_relat_1])).
% 2.45/2.64  thf('47', plain,
% 2.45/2.64      (![X0 : $i]:
% 2.45/2.64         ((r1_tarski @ (k10_relat_1 @ X0 @ sk_A) @ 
% 2.45/2.64           (k10_relat_1 @ X0 @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))))
% 2.45/2.64          | ~ (v1_relat_1 @ X0))),
% 2.45/2.64      inference('sup-', [status(thm)], ['45', '46'])).
% 2.45/2.64  thf('48', plain,
% 2.45/2.64      (((r1_tarski @ sk_A @ 
% 2.45/2.64         (k10_relat_1 @ (k6_relat_1 @ sk_A) @ 
% 2.45/2.64          (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))))
% 2.45/2.64        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 2.45/2.64      inference('sup+', [status(thm)], ['15', '47'])).
% 2.45/2.64  thf('49', plain, (![X24 : $i]: (v1_relat_1 @ (k6_relat_1 @ X24))),
% 2.45/2.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.45/2.64  thf('50', plain,
% 2.45/2.64      ((r1_tarski @ sk_A @ 
% 2.45/2.64        (k10_relat_1 @ (k6_relat_1 @ sk_A) @ 
% 2.45/2.64         (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))))),
% 2.45/2.64      inference('demod', [status(thm)], ['48', '49'])).
% 2.45/2.64  thf('51', plain, (![X22 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 2.45/2.64      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.45/2.64  thf('52', plain,
% 2.45/2.64      (![X11 : $i, X12 : $i]:
% 2.45/2.64         ((r1_tarski @ (k10_relat_1 @ X11 @ X12) @ (k1_relat_1 @ X11))
% 2.45/2.64          | ~ (v1_relat_1 @ X11))),
% 2.45/2.64      inference('cnf', [status(esa)], [t167_relat_1])).
% 2.45/2.64  thf('53', plain,
% 2.45/2.64      (![X0 : $i, X2 : $i]:
% 2.45/2.64         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.45/2.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.45/2.64  thf('54', plain,
% 2.45/2.64      (![X0 : $i, X1 : $i]:
% 2.45/2.64         (~ (v1_relat_1 @ X0)
% 2.45/2.64          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 2.45/2.64          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1)))),
% 2.45/2.64      inference('sup-', [status(thm)], ['52', '53'])).
% 2.45/2.64  thf('55', plain,
% 2.45/2.64      (![X0 : $i, X1 : $i]:
% 2.45/2.64         (~ (r1_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 2.45/2.64          | ((k1_relat_1 @ (k6_relat_1 @ X0))
% 2.45/2.64              = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 2.45/2.64          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.45/2.64      inference('sup-', [status(thm)], ['51', '54'])).
% 2.45/2.64  thf('56', plain, (![X22 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 2.45/2.64      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.45/2.64  thf('57', plain, (![X24 : $i]: (v1_relat_1 @ (k6_relat_1 @ X24))),
% 2.45/2.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.45/2.64  thf('58', plain,
% 2.45/2.64      (![X0 : $i, X1 : $i]:
% 2.45/2.64         (~ (r1_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 2.45/2.64          | ((X0) = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 2.45/2.64      inference('demod', [status(thm)], ['55', '56', '57'])).
% 2.45/2.64  thf('59', plain,
% 2.45/2.64      (((sk_A)
% 2.45/2.64         = (k10_relat_1 @ (k6_relat_1 @ sk_A) @ 
% 2.45/2.64            (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))))),
% 2.45/2.64      inference('sup-', [status(thm)], ['50', '58'])).
% 2.45/2.64  thf('60', plain,
% 2.45/2.64      (![X6 : $i, X7 : $i]:
% 2.45/2.64         (~ (v1_relat_1 @ X6)
% 2.45/2.64          | ~ (v1_relat_1 @ X7)
% 2.45/2.64          | (v1_relat_1 @ (k5_relat_1 @ X6 @ X7)))),
% 2.45/2.64      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 2.45/2.64  thf('61', plain,
% 2.45/2.64      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.45/2.64         (~ (v1_relat_1 @ X17)
% 2.45/2.64          | ((k10_relat_1 @ (k5_relat_1 @ X18 @ X17) @ X19)
% 2.45/2.64              = (k10_relat_1 @ X18 @ (k10_relat_1 @ X17 @ X19)))
% 2.45/2.64          | ~ (v1_relat_1 @ X18))),
% 2.45/2.64      inference('cnf', [status(esa)], [t181_relat_1])).
% 2.45/2.64  thf('62', plain,
% 2.45/2.64      (![X11 : $i, X12 : $i]:
% 2.45/2.64         ((r1_tarski @ (k10_relat_1 @ X11 @ X12) @ (k1_relat_1 @ X11))
% 2.45/2.64          | ~ (v1_relat_1 @ X11))),
% 2.45/2.64      inference('cnf', [status(esa)], [t167_relat_1])).
% 2.45/2.64  thf('63', plain,
% 2.45/2.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.45/2.64         ((r1_tarski @ (k10_relat_1 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 2.45/2.64           (k1_relat_1 @ (k5_relat_1 @ X2 @ X1)))
% 2.45/2.64          | ~ (v1_relat_1 @ X2)
% 2.45/2.64          | ~ (v1_relat_1 @ X1)
% 2.45/2.64          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1)))),
% 2.45/2.64      inference('sup+', [status(thm)], ['61', '62'])).
% 2.45/2.64  thf('64', plain,
% 2.45/2.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.45/2.64         (~ (v1_relat_1 @ X0)
% 2.45/2.64          | ~ (v1_relat_1 @ X1)
% 2.45/2.64          | ~ (v1_relat_1 @ X0)
% 2.45/2.64          | ~ (v1_relat_1 @ X1)
% 2.45/2.64          | (r1_tarski @ (k10_relat_1 @ X1 @ (k10_relat_1 @ X0 @ X2)) @ 
% 2.45/2.64             (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 2.45/2.64      inference('sup-', [status(thm)], ['60', '63'])).
% 2.45/2.64  thf('65', plain,
% 2.45/2.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.45/2.64         ((r1_tarski @ (k10_relat_1 @ X1 @ (k10_relat_1 @ X0 @ X2)) @ 
% 2.45/2.64           (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 2.45/2.64          | ~ (v1_relat_1 @ X1)
% 2.45/2.64          | ~ (v1_relat_1 @ X0))),
% 2.45/2.64      inference('simplify', [status(thm)], ['64'])).
% 2.45/2.64  thf('66', plain,
% 2.45/2.64      (((r1_tarski @ sk_A @ 
% 2.45/2.64         (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)))
% 2.45/2.64        | ~ (v1_relat_1 @ sk_B)
% 2.45/2.64        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 2.45/2.64      inference('sup+', [status(thm)], ['59', '65'])).
% 2.45/2.64  thf('67', plain, ((v1_relat_1 @ sk_B)),
% 2.45/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.45/2.64  thf('68', plain, (![X24 : $i]: (v1_relat_1 @ (k6_relat_1 @ X24))),
% 2.45/2.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.45/2.64  thf('69', plain,
% 2.45/2.64      ((r1_tarski @ sk_A @ 
% 2.45/2.64        (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)))),
% 2.45/2.64      inference('demod', [status(thm)], ['66', '67', '68'])).
% 2.45/2.64  thf('70', plain,
% 2.45/2.64      (![X0 : $i, X2 : $i]:
% 2.45/2.64         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.45/2.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.45/2.64  thf('71', plain,
% 2.45/2.64      ((~ (r1_tarski @ 
% 2.45/2.64           (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) @ sk_A)
% 2.45/2.64        | ((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) = (sk_A)))),
% 2.45/2.64      inference('sup-', [status(thm)], ['69', '70'])).
% 2.45/2.64  thf('72', plain,
% 2.45/2.64      ((~ (r1_tarski @ 
% 2.45/2.64           (k10_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)) @ sk_A)
% 2.45/2.64        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 2.45/2.64        | ~ (v1_relat_1 @ sk_B)
% 2.45/2.64        | ((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) = (sk_A)))),
% 2.45/2.64      inference('sup-', [status(thm)], ['9', '71'])).
% 2.45/2.64  thf('73', plain,
% 2.45/2.64      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 2.45/2.64      inference('demod', [status(thm)], ['12', '13', '14'])).
% 2.45/2.64  thf('74', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 2.45/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.45/2.64  thf('75', plain,
% 2.45/2.64      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.45/2.64         (~ (r1_tarski @ X14 @ X15)
% 2.45/2.64          | ~ (v1_relat_1 @ X16)
% 2.45/2.64          | (r1_tarski @ (k10_relat_1 @ X16 @ X14) @ (k10_relat_1 @ X16 @ X15)))),
% 2.45/2.64      inference('cnf', [status(esa)], [t178_relat_1])).
% 2.45/2.64  thf('76', plain,
% 2.45/2.64      (![X0 : $i]:
% 2.45/2.64         ((r1_tarski @ (k10_relat_1 @ X0 @ sk_A) @ 
% 2.45/2.64           (k10_relat_1 @ X0 @ (k1_relat_1 @ sk_B)))
% 2.45/2.64          | ~ (v1_relat_1 @ X0))),
% 2.45/2.64      inference('sup-', [status(thm)], ['74', '75'])).
% 2.45/2.64  thf('77', plain,
% 2.45/2.64      (((r1_tarski @ sk_A @ 
% 2.45/2.64         (k10_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)))
% 2.45/2.64        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 2.45/2.64      inference('sup+', [status(thm)], ['73', '76'])).
% 2.45/2.64  thf('78', plain, (![X24 : $i]: (v1_relat_1 @ (k6_relat_1 @ X24))),
% 2.45/2.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.45/2.64  thf('79', plain,
% 2.45/2.64      ((r1_tarski @ sk_A @ 
% 2.45/2.64        (k10_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 2.45/2.64      inference('demod', [status(thm)], ['77', '78'])).
% 2.45/2.64  thf('80', plain,
% 2.45/2.64      (![X0 : $i, X1 : $i]:
% 2.45/2.64         (~ (r1_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 2.45/2.64          | ((X0) = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 2.45/2.64      inference('demod', [status(thm)], ['55', '56', '57'])).
% 2.45/2.64  thf('81', plain,
% 2.45/2.64      (((sk_A) = (k10_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 2.45/2.64      inference('sup-', [status(thm)], ['79', '80'])).
% 2.45/2.64  thf('82', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.45/2.64      inference('simplify', [status(thm)], ['33'])).
% 2.45/2.64  thf('83', plain, (![X24 : $i]: (v1_relat_1 @ (k6_relat_1 @ X24))),
% 2.45/2.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.45/2.64  thf('84', plain, ((v1_relat_1 @ sk_B)),
% 2.45/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.45/2.64  thf('85', plain,
% 2.45/2.64      (((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) = (sk_A))),
% 2.45/2.64      inference('demod', [status(thm)], ['72', '81', '82', '83', '84'])).
% 2.45/2.64  thf('86', plain,
% 2.45/2.64      (![X11 : $i, X12 : $i]:
% 2.45/2.64         ((r1_tarski @ (k10_relat_1 @ X11 @ X12) @ (k1_relat_1 @ X11))
% 2.45/2.64          | ~ (v1_relat_1 @ X11))),
% 2.45/2.64      inference('cnf', [status(esa)], [t167_relat_1])).
% 2.45/2.64  thf('87', plain,
% 2.45/2.64      (![X0 : $i]:
% 2.45/2.64         ((r1_tarski @ 
% 2.45/2.64           (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ X0) @ 
% 2.45/2.64           sk_A)
% 2.45/2.64          | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)))),
% 2.45/2.64      inference('sup+', [status(thm)], ['85', '86'])).
% 2.45/2.64  thf('88', plain,
% 2.45/2.64      (![X0 : $i]:
% 2.45/2.64         (~ (v1_relat_1 @ sk_B)
% 2.45/2.64          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 2.45/2.64          | (r1_tarski @ 
% 2.45/2.64             (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ X0) @ 
% 2.45/2.64             sk_A))),
% 2.45/2.64      inference('sup-', [status(thm)], ['8', '87'])).
% 2.45/2.64  thf('89', plain, ((v1_relat_1 @ sk_B)),
% 2.45/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.45/2.64  thf('90', plain, (![X24 : $i]: (v1_relat_1 @ (k6_relat_1 @ X24))),
% 2.45/2.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.45/2.64  thf('91', plain,
% 2.45/2.64      (![X0 : $i]:
% 2.45/2.64         (r1_tarski @ 
% 2.45/2.64          (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ X0) @ sk_A)),
% 2.45/2.64      inference('demod', [status(thm)], ['88', '89', '90'])).
% 2.45/2.64  thf('92', plain,
% 2.45/2.64      (![X0 : $i, X2 : $i]:
% 2.45/2.64         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.45/2.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.45/2.64  thf('93', plain,
% 2.45/2.64      (![X0 : $i]:
% 2.45/2.64         (~ (r1_tarski @ sk_A @ 
% 2.45/2.64             (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ X0))
% 2.45/2.64          | ((sk_A)
% 2.45/2.64              = (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ X0)))),
% 2.45/2.64      inference('sup-', [status(thm)], ['91', '92'])).
% 2.45/2.64  thf('94', plain,
% 2.45/2.64      ((~ (r1_tarski @ sk_A @ 
% 2.45/2.64           (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)))
% 2.45/2.64        | ~ (v1_relat_1 @ sk_B)
% 2.45/2.64        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 2.45/2.64        | ((sk_A)
% 2.45/2.64            = (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ 
% 2.45/2.64               (k9_relat_1 @ sk_B @ (k2_relat_1 @ (k6_relat_1 @ sk_A))))))),
% 2.45/2.64      inference('sup-', [status(thm)], ['7', '93'])).
% 2.45/2.64  thf('95', plain,
% 2.45/2.64      (((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) = (sk_A))),
% 2.45/2.64      inference('demod', [status(thm)], ['72', '81', '82', '83', '84'])).
% 2.45/2.64  thf('96', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.45/2.64      inference('simplify', [status(thm)], ['33'])).
% 2.45/2.64  thf('97', plain, ((v1_relat_1 @ sk_B)),
% 2.45/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.45/2.64  thf('98', plain, (![X24 : $i]: (v1_relat_1 @ (k6_relat_1 @ X24))),
% 2.45/2.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.45/2.64  thf('99', plain, (![X23 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 2.45/2.64      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.45/2.64  thf('100', plain,
% 2.45/2.64      (((sk_A)
% 2.45/2.64         = (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ 
% 2.45/2.64            (k9_relat_1 @ sk_B @ sk_A)))),
% 2.45/2.64      inference('demod', [status(thm)], ['94', '95', '96', '97', '98', '99'])).
% 2.45/2.64  thf('101', plain,
% 2.45/2.64      ((((sk_A)
% 2.45/2.64          = (k10_relat_1 @ (k6_relat_1 @ sk_A) @ 
% 2.45/2.64             (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))
% 2.45/2.64        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 2.45/2.64        | ~ (v1_relat_1 @ sk_B))),
% 2.45/2.64      inference('sup+', [status(thm)], ['1', '100'])).
% 2.45/2.64  thf('102', plain, (![X24 : $i]: (v1_relat_1 @ (k6_relat_1 @ X24))),
% 2.45/2.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.45/2.64  thf('103', plain, ((v1_relat_1 @ sk_B)),
% 2.45/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.45/2.64  thf('104', plain,
% 2.45/2.64      (((sk_A)
% 2.45/2.64         = (k10_relat_1 @ (k6_relat_1 @ sk_A) @ 
% 2.45/2.64            (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 2.45/2.64      inference('demod', [status(thm)], ['101', '102', '103'])).
% 2.45/2.64  thf(t145_funct_1, axiom,
% 2.45/2.64    (![A:$i,B:$i]:
% 2.45/2.64     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.45/2.64       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 2.45/2.64  thf('105', plain,
% 2.45/2.64      (![X26 : $i, X27 : $i]:
% 2.45/2.64         ((r1_tarski @ (k9_relat_1 @ X26 @ (k10_relat_1 @ X26 @ X27)) @ X27)
% 2.45/2.64          | ~ (v1_funct_1 @ X26)
% 2.45/2.64          | ~ (v1_relat_1 @ X26))),
% 2.45/2.64      inference('cnf', [status(esa)], [t145_funct_1])).
% 2.45/2.64  thf('106', plain,
% 2.45/2.64      (((r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ sk_A) @ sk_A) @ 
% 2.45/2.64         (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 2.45/2.64        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 2.45/2.64        | ~ (v1_funct_1 @ (k6_relat_1 @ sk_A)))),
% 2.45/2.64      inference('sup+', [status(thm)], ['104', '105'])).
% 2.45/2.64  thf('107', plain, (![X22 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 2.45/2.64      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.45/2.64  thf(t146_relat_1, axiom,
% 2.45/2.64    (![A:$i]:
% 2.45/2.64     ( ( v1_relat_1 @ A ) =>
% 2.45/2.64       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 2.45/2.64  thf('108', plain,
% 2.45/2.64      (![X8 : $i]:
% 2.45/2.64         (((k9_relat_1 @ X8 @ (k1_relat_1 @ X8)) = (k2_relat_1 @ X8))
% 2.45/2.64          | ~ (v1_relat_1 @ X8))),
% 2.45/2.64      inference('cnf', [status(esa)], [t146_relat_1])).
% 2.45/2.64  thf('109', plain,
% 2.45/2.64      (![X0 : $i]:
% 2.45/2.64         (((k9_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 2.45/2.64            = (k2_relat_1 @ (k6_relat_1 @ X0)))
% 2.45/2.64          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.45/2.64      inference('sup+', [status(thm)], ['107', '108'])).
% 2.45/2.64  thf('110', plain, (![X23 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 2.45/2.64      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.45/2.64  thf('111', plain, (![X24 : $i]: (v1_relat_1 @ (k6_relat_1 @ X24))),
% 2.45/2.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.45/2.64  thf('112', plain,
% 2.45/2.64      (![X0 : $i]: ((k9_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 2.45/2.64      inference('demod', [status(thm)], ['109', '110', '111'])).
% 2.45/2.64  thf('113', plain, (![X24 : $i]: (v1_relat_1 @ (k6_relat_1 @ X24))),
% 2.45/2.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.45/2.64  thf('114', plain, (![X25 : $i]: (v1_funct_1 @ (k6_relat_1 @ X25))),
% 2.45/2.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.45/2.64  thf('115', plain,
% 2.45/2.64      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 2.45/2.64      inference('demod', [status(thm)], ['106', '112', '113', '114'])).
% 2.45/2.64  thf('116', plain, ($false), inference('demod', [status(thm)], ['0', '115'])).
% 2.45/2.64  
% 2.45/2.64  % SZS output end Refutation
% 2.45/2.64  
% 2.45/2.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
