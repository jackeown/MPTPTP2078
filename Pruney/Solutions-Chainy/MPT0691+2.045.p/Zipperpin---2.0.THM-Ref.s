%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JWj8bgbt6s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:23 EST 2020

% Result     : Theorem 0.66s
% Output     : Refutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :  198 (1411 expanded)
%              Number of leaves         :   28 ( 493 expanded)
%              Depth                    :   39
%              Number of atoms          : 1743 (12279 expanded)
%              Number of equality atoms :  118 ( 971 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

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

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X47 @ X46 ) @ X48 )
        = ( k3_xboole_0 @ X46 @ ( k10_relat_1 @ X47 @ X48 ) ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('2',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k7_relat_1 @ X43 @ X42 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X42 ) @ X43 ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_relat_1 @ X24 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k7_relat_1 @ X43 @ X42 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X42 ) @ X43 ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X26: $i] :
      ( ( ( k9_relat_1 @ X26 @ ( k1_relat_1 @ X26 ) )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t159_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k9_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k9_relat_1 @ C @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('10',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ( ( k9_relat_1 @ ( k5_relat_1 @ X28 @ X27 ) @ X29 )
        = ( k9_relat_1 @ X27 @ ( k9_relat_1 @ X28 @ X29 ) ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t159_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k9_relat_1 @ X1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','12'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('14',plain,(
    ! [X38: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X38 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('15',plain,(
    ! [X39: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X39 ) )
      = X39 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('16',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X0 )
        = ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X0 )
        = ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('20',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k7_relat_1 @ X43 @ X42 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X42 ) @ X43 ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('21',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v1_relat_1 @ X36 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X37 @ X36 ) )
        = ( k10_relat_1 @ X37 @ ( k1_relat_1 @ X36 ) ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('23',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X38: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X38 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('25',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X44 ) @ X45 )
      | ( ( k7_relat_1 @ X44 @ X45 )
        = X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k7_relat_1 @ X43 @ X42 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X42 ) @ X43 ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('31',plain,(
    ! [X38: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X38 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('32',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v1_relat_1 @ X36 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X37 @ X36 ) )
        = ( k10_relat_1 @ X37 @ ( k1_relat_1 @ X36 ) ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','35'])).

thf('37',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('38',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    = ( k10_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_A ) ),
    inference('sup+',[status(thm)],['29','39'])).

thf('41',plain,(
    ! [X38: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X38 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('42',plain,
    ( sk_A
    = ( k10_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X38: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X38 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t89_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ) )).

thf('44',plain,(
    ! [X40: $i,X41: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X40 @ X41 ) ) @ ( k1_relat_1 @ X40 ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t89_relat_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ X0 )
      = ( k6_relat_1 @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k7_relat_1 @ X43 @ X42 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X42 ) @ X43 ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('53',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v1_relat_1 @ X36 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X37 @ X36 ) )
        = ( k10_relat_1 @ X37 @ ( k1_relat_1 @ X36 ) ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('55',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ( X0
        = ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['53','59'])).

thf('61',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X1 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['52','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X1 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ ( k1_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ( ( k1_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['51','64'])).

thf('66',plain,(
    ! [X38: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X38 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('67',plain,(
    ! [X38: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X38 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('68',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('69',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('71',plain,(
    ! [X38: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X38 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('72',plain,(
    ! [X38: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X38 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['65','66','67','69','70','71','72'])).

thf('74',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('75',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X44 ) @ X45 )
      | ( ( k7_relat_1 @ X44 @ X45 )
        = X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X47 @ X46 ) @ X48 )
        = ( k3_xboole_0 @ X46 @ ( k10_relat_1 @ X47 @ X48 ) ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X0 @ X1 )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ X1 )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['73','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['65','66','67','69','70','71','72'])).

thf('82',plain,(
    ! [X38: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X38 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('83',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['80','81','82','83'])).

thf('85',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X47 @ X46 ) @ X48 )
        = ( k3_xboole_0 @ X46 @ ( k10_relat_1 @ X47 @ X48 ) ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('86',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k7_relat_1 @ X43 @ X42 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X42 ) @ X43 ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t181_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('87',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X34 @ X33 ) @ X35 )
        = ( k10_relat_1 @ X34 @ ( k10_relat_1 @ X33 @ X35 ) ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('88',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X30 @ X31 ) @ ( k1_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k1_relat_1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['86','90'])).

thf('92',plain,(
    ! [X38: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X38 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('93',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 ) )
      | ( X0
        = ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( X2
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['85','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ( X0
        = ( k10_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['84','99'])).

thf('101',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ( X0
        = ( k10_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
    | ( sk_A
      = ( k10_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','102'])).

thf('104',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('105',plain,
    ( sk_A
    = ( k10_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X30 @ X31 ) @ ( k1_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('107',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_A ) ) @ sk_A )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_A ) )
      = ( k10_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_A ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['105','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('111',plain,(
    ! [X38: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X38 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('112',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X30 @ X31 ) @ ( k1_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('117',plain,
    ( sk_A
    = ( k10_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('118',plain,
    ( ( ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
      = sk_A )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['109','110','115','116','117'])).

thf('119',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    | ( ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['22','118'])).

thf('120',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('121',plain,
    ( ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
      = sk_A )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['21','121'])).

thf('123',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('124',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('126',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['20','125'])).

thf('127',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X26: $i] :
      ( ( ( k9_relat_1 @ X26 @ ( k1_relat_1 @ X26 ) )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('130',plain,
    ( ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','130'])).

thf('132',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['18','133'])).

thf('135',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('137',plain,(
    ! [X32: $i] :
      ( ( ( k10_relat_1 @ X32 @ ( k2_relat_1 @ X32 ) )
        = ( k1_relat_1 @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('138',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['136','137'])).

thf('139',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['126','127'])).

thf('140',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['7','140'])).

thf('142',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','143'])).

thf('145',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X39: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X39 ) )
      = X39 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('148',plain,(
    ! [X32: $i] :
      ( ( ( k10_relat_1 @ X32 @ ( k2_relat_1 @ X32 ) )
        = ( k1_relat_1 @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X38: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X38 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('151',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['149','150','151'])).

thf('153',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X47 @ X46 ) @ X48 )
        = ( k3_xboole_0 @ X46 @ ( k10_relat_1 @ X47 @ X48 ) ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('154',plain,(
    ! [X40: $i,X41: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X40 @ X41 ) ) @ ( k1_relat_1 @ X40 ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t89_relat_1])).

thf('155',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X30 @ X31 ) @ ( k1_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('156',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('157',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['154','157'])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('160',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['153','160'])).

thf('162',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['152','162'])).

thf('164',plain,(
    ! [X38: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X38 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('165',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['163','164','165'])).

thf('167',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['146','166'])).

thf('168',plain,(
    $false ),
    inference(demod,[status(thm)],['0','167'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JWj8bgbt6s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:32:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.66/0.90  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.66/0.90  % Solved by: fo/fo7.sh
% 0.66/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.66/0.90  % done 1047 iterations in 0.452s
% 0.66/0.90  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.66/0.90  % SZS output start Refutation
% 0.66/0.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.66/0.90  thf(sk_B_type, type, sk_B: $i).
% 0.66/0.90  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.66/0.90  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.66/0.90  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.66/0.90  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.66/0.90  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.66/0.90  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.66/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.66/0.90  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.66/0.90  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.66/0.90  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.66/0.90  thf(t146_funct_1, conjecture,
% 0.66/0.90    (![A:$i,B:$i]:
% 0.66/0.90     ( ( v1_relat_1 @ B ) =>
% 0.66/0.90       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.66/0.90         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.66/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.66/0.90    (~( ![A:$i,B:$i]:
% 0.66/0.90        ( ( v1_relat_1 @ B ) =>
% 0.66/0.90          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.66/0.90            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 0.66/0.90    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 0.66/0.90  thf('0', plain,
% 0.66/0.90      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.66/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.90  thf(t139_funct_1, axiom,
% 0.66/0.90    (![A:$i,B:$i,C:$i]:
% 0.66/0.90     ( ( v1_relat_1 @ C ) =>
% 0.66/0.90       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.66/0.90         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.66/0.90  thf('1', plain,
% 0.66/0.90      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.66/0.90         (((k10_relat_1 @ (k7_relat_1 @ X47 @ X46) @ X48)
% 0.66/0.90            = (k3_xboole_0 @ X46 @ (k10_relat_1 @ X47 @ X48)))
% 0.66/0.90          | ~ (v1_relat_1 @ X47))),
% 0.66/0.90      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.66/0.90  thf(t94_relat_1, axiom,
% 0.66/0.90    (![A:$i,B:$i]:
% 0.66/0.90     ( ( v1_relat_1 @ B ) =>
% 0.66/0.90       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.66/0.90  thf('2', plain,
% 0.66/0.90      (![X42 : $i, X43 : $i]:
% 0.66/0.90         (((k7_relat_1 @ X43 @ X42) = (k5_relat_1 @ (k6_relat_1 @ X42) @ X43))
% 0.66/0.90          | ~ (v1_relat_1 @ X43))),
% 0.66/0.90      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.66/0.90  thf(dt_k5_relat_1, axiom,
% 0.66/0.90    (![A:$i,B:$i]:
% 0.66/0.90     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.66/0.90       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.66/0.90  thf('3', plain,
% 0.66/0.90      (![X23 : $i, X24 : $i]:
% 0.66/0.90         (~ (v1_relat_1 @ X23)
% 0.66/0.90          | ~ (v1_relat_1 @ X24)
% 0.66/0.90          | (v1_relat_1 @ (k5_relat_1 @ X23 @ X24)))),
% 0.66/0.90      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.66/0.90  thf('4', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.66/0.90          | ~ (v1_relat_1 @ X1)
% 0.66/0.90          | ~ (v1_relat_1 @ X1)
% 0.66/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.66/0.90      inference('sup+', [status(thm)], ['2', '3'])).
% 0.66/0.90  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.66/0.90  thf('5', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 0.66/0.90      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.66/0.90  thf('6', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.66/0.90          | ~ (v1_relat_1 @ X1)
% 0.66/0.90          | ~ (v1_relat_1 @ X1))),
% 0.66/0.90      inference('demod', [status(thm)], ['4', '5'])).
% 0.66/0.90  thf('7', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.66/0.90      inference('simplify', [status(thm)], ['6'])).
% 0.66/0.90  thf('8', plain,
% 0.66/0.90      (![X42 : $i, X43 : $i]:
% 0.66/0.90         (((k7_relat_1 @ X43 @ X42) = (k5_relat_1 @ (k6_relat_1 @ X42) @ X43))
% 0.66/0.90          | ~ (v1_relat_1 @ X43))),
% 0.66/0.90      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.66/0.90  thf(t146_relat_1, axiom,
% 0.66/0.90    (![A:$i]:
% 0.66/0.90     ( ( v1_relat_1 @ A ) =>
% 0.66/0.90       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.66/0.90  thf('9', plain,
% 0.66/0.90      (![X26 : $i]:
% 0.66/0.90         (((k9_relat_1 @ X26 @ (k1_relat_1 @ X26)) = (k2_relat_1 @ X26))
% 0.66/0.90          | ~ (v1_relat_1 @ X26))),
% 0.66/0.90      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.66/0.90  thf(t159_relat_1, axiom,
% 0.66/0.90    (![A:$i,B:$i]:
% 0.66/0.90     ( ( v1_relat_1 @ B ) =>
% 0.66/0.90       ( ![C:$i]:
% 0.66/0.90         ( ( v1_relat_1 @ C ) =>
% 0.66/0.90           ( ( k9_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.66/0.90             ( k9_relat_1 @ C @ ( k9_relat_1 @ B @ A ) ) ) ) ) ))).
% 0.66/0.90  thf('10', plain,
% 0.66/0.90      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.66/0.90         (~ (v1_relat_1 @ X27)
% 0.66/0.90          | ((k9_relat_1 @ (k5_relat_1 @ X28 @ X27) @ X29)
% 0.66/0.90              = (k9_relat_1 @ X27 @ (k9_relat_1 @ X28 @ X29)))
% 0.66/0.90          | ~ (v1_relat_1 @ X28))),
% 0.66/0.90      inference('cnf', [status(esa)], [t159_relat_1])).
% 0.66/0.90  thf('11', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         (((k9_relat_1 @ (k5_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.66/0.90            = (k9_relat_1 @ X1 @ (k2_relat_1 @ X0)))
% 0.66/0.90          | ~ (v1_relat_1 @ X0)
% 0.66/0.90          | ~ (v1_relat_1 @ X0)
% 0.66/0.90          | ~ (v1_relat_1 @ X1))),
% 0.66/0.90      inference('sup+', [status(thm)], ['9', '10'])).
% 0.66/0.90  thf('12', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         (~ (v1_relat_1 @ X1)
% 0.66/0.90          | ~ (v1_relat_1 @ X0)
% 0.66/0.90          | ((k9_relat_1 @ (k5_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.66/0.90              = (k9_relat_1 @ X1 @ (k2_relat_1 @ X0))))),
% 0.66/0.90      inference('simplify', [status(thm)], ['11'])).
% 0.66/0.90  thf('13', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         (((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.66/0.90            (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.66/0.90            = (k9_relat_1 @ X1 @ (k2_relat_1 @ (k6_relat_1 @ X0))))
% 0.66/0.90          | ~ (v1_relat_1 @ X1)
% 0.66/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.66/0.90          | ~ (v1_relat_1 @ X1))),
% 0.66/0.90      inference('sup+', [status(thm)], ['8', '12'])).
% 0.66/0.90  thf(t71_relat_1, axiom,
% 0.66/0.90    (![A:$i]:
% 0.66/0.90     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.66/0.90       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.66/0.90  thf('14', plain, (![X38 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X38)) = (X38))),
% 0.66/0.90      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.66/0.90  thf('15', plain, (![X39 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X39)) = (X39))),
% 0.66/0.90      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.66/0.90  thf('16', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 0.66/0.90      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.66/0.90  thf('17', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         (((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X0) = (k9_relat_1 @ X1 @ X0))
% 0.66/0.90          | ~ (v1_relat_1 @ X1)
% 0.66/0.90          | ~ (v1_relat_1 @ X1))),
% 0.66/0.90      inference('demod', [status(thm)], ['13', '14', '15', '16'])).
% 0.66/0.90  thf('18', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         (~ (v1_relat_1 @ X1)
% 0.66/0.90          | ((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X0)
% 0.66/0.90              = (k9_relat_1 @ X1 @ X0)))),
% 0.66/0.90      inference('simplify', [status(thm)], ['17'])).
% 0.66/0.90  thf('19', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.66/0.90      inference('simplify', [status(thm)], ['6'])).
% 0.66/0.90  thf('20', plain,
% 0.66/0.90      (![X42 : $i, X43 : $i]:
% 0.66/0.90         (((k7_relat_1 @ X43 @ X42) = (k5_relat_1 @ (k6_relat_1 @ X42) @ X43))
% 0.66/0.90          | ~ (v1_relat_1 @ X43))),
% 0.66/0.90      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.66/0.90  thf(t182_relat_1, axiom,
% 0.66/0.90    (![A:$i]:
% 0.66/0.90     ( ( v1_relat_1 @ A ) =>
% 0.66/0.90       ( ![B:$i]:
% 0.66/0.90         ( ( v1_relat_1 @ B ) =>
% 0.66/0.90           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.66/0.90             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.66/0.90  thf('21', plain,
% 0.66/0.90      (![X36 : $i, X37 : $i]:
% 0.66/0.90         (~ (v1_relat_1 @ X36)
% 0.66/0.90          | ((k1_relat_1 @ (k5_relat_1 @ X37 @ X36))
% 0.66/0.90              = (k10_relat_1 @ X37 @ (k1_relat_1 @ X36)))
% 0.66/0.90          | ~ (v1_relat_1 @ X37))),
% 0.66/0.90      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.66/0.90  thf('22', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.66/0.90      inference('simplify', [status(thm)], ['6'])).
% 0.66/0.90  thf('23', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.66/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.90  thf('24', plain, (![X38 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X38)) = (X38))),
% 0.66/0.90      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.66/0.90  thf(t97_relat_1, axiom,
% 0.66/0.90    (![A:$i,B:$i]:
% 0.66/0.90     ( ( v1_relat_1 @ B ) =>
% 0.66/0.90       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.66/0.90         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.66/0.90  thf('25', plain,
% 0.66/0.90      (![X44 : $i, X45 : $i]:
% 0.66/0.90         (~ (r1_tarski @ (k1_relat_1 @ X44) @ X45)
% 0.66/0.90          | ((k7_relat_1 @ X44 @ X45) = (X44))
% 0.66/0.90          | ~ (v1_relat_1 @ X44))),
% 0.66/0.90      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.66/0.90  thf('26', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         (~ (r1_tarski @ X0 @ X1)
% 0.66/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.66/0.90          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.66/0.90      inference('sup-', [status(thm)], ['24', '25'])).
% 0.66/0.90  thf('27', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 0.66/0.90      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.66/0.90  thf('28', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         (~ (r1_tarski @ X0 @ X1)
% 0.66/0.90          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.66/0.90      inference('demod', [status(thm)], ['26', '27'])).
% 0.66/0.90  thf('29', plain,
% 0.66/0.90      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.66/0.90         = (k6_relat_1 @ sk_A))),
% 0.66/0.90      inference('sup-', [status(thm)], ['23', '28'])).
% 0.66/0.90  thf('30', plain,
% 0.66/0.90      (![X42 : $i, X43 : $i]:
% 0.66/0.90         (((k7_relat_1 @ X43 @ X42) = (k5_relat_1 @ (k6_relat_1 @ X42) @ X43))
% 0.66/0.90          | ~ (v1_relat_1 @ X43))),
% 0.66/0.90      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.66/0.90  thf('31', plain, (![X38 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X38)) = (X38))),
% 0.66/0.90      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.66/0.90  thf('32', plain,
% 0.66/0.90      (![X36 : $i, X37 : $i]:
% 0.66/0.90         (~ (v1_relat_1 @ X36)
% 0.66/0.90          | ((k1_relat_1 @ (k5_relat_1 @ X37 @ X36))
% 0.66/0.90              = (k10_relat_1 @ X37 @ (k1_relat_1 @ X36)))
% 0.66/0.90          | ~ (v1_relat_1 @ X37))),
% 0.66/0.90      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.66/0.90  thf('33', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.66/0.90            = (k10_relat_1 @ X1 @ X0))
% 0.66/0.90          | ~ (v1_relat_1 @ X1)
% 0.66/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.66/0.90      inference('sup+', [status(thm)], ['31', '32'])).
% 0.66/0.90  thf('34', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 0.66/0.90      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.66/0.90  thf('35', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.66/0.90            = (k10_relat_1 @ X1 @ X0))
% 0.66/0.90          | ~ (v1_relat_1 @ X1))),
% 0.66/0.90      inference('demod', [status(thm)], ['33', '34'])).
% 0.66/0.90  thf('36', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.66/0.90            = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.66/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.66/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.66/0.90      inference('sup+', [status(thm)], ['30', '35'])).
% 0.66/0.90  thf('37', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 0.66/0.90      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.66/0.90  thf('38', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 0.66/0.90      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.66/0.90  thf('39', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.66/0.90           = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.66/0.90      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.66/0.90  thf('40', plain,
% 0.66/0.90      (((k1_relat_1 @ (k6_relat_1 @ sk_A))
% 0.66/0.90         = (k10_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_A))),
% 0.66/0.90      inference('sup+', [status(thm)], ['29', '39'])).
% 0.66/0.90  thf('41', plain, (![X38 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X38)) = (X38))),
% 0.66/0.90      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.66/0.90  thf('42', plain,
% 0.66/0.90      (((sk_A) = (k10_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_A))),
% 0.66/0.90      inference('demod', [status(thm)], ['40', '41'])).
% 0.66/0.90  thf('43', plain, (![X38 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X38)) = (X38))),
% 0.66/0.90      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.66/0.90  thf(t89_relat_1, axiom,
% 0.66/0.90    (![A:$i,B:$i]:
% 0.66/0.90     ( ( v1_relat_1 @ B ) =>
% 0.66/0.90       ( r1_tarski @
% 0.66/0.90         ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ))).
% 0.66/0.90  thf('44', plain,
% 0.66/0.90      (![X40 : $i, X41 : $i]:
% 0.66/0.90         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X40 @ X41)) @ 
% 0.66/0.90           (k1_relat_1 @ X40))
% 0.66/0.90          | ~ (v1_relat_1 @ X40))),
% 0.66/0.90      inference('cnf', [status(esa)], [t89_relat_1])).
% 0.66/0.90  thf('45', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)) @ 
% 0.66/0.90           X0)
% 0.66/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.66/0.90      inference('sup+', [status(thm)], ['43', '44'])).
% 0.66/0.90  thf('46', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 0.66/0.90      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.66/0.90  thf('47', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)) @ X0)),
% 0.66/0.90      inference('demod', [status(thm)], ['45', '46'])).
% 0.66/0.90  thf('48', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.66/0.90           = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.66/0.90      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.66/0.90  thf('49', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0)),
% 0.66/0.90      inference('demod', [status(thm)], ['47', '48'])).
% 0.66/0.90  thf('50', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         (~ (r1_tarski @ X0 @ X1)
% 0.66/0.90          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.66/0.90      inference('demod', [status(thm)], ['26', '27'])).
% 0.66/0.90  thf('51', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         ((k7_relat_1 @ 
% 0.66/0.90           (k6_relat_1 @ (k10_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ X0)
% 0.66/0.90           = (k6_relat_1 @ (k10_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.66/0.90      inference('sup-', [status(thm)], ['49', '50'])).
% 0.66/0.90  thf('52', plain,
% 0.66/0.90      (![X42 : $i, X43 : $i]:
% 0.66/0.90         (((k7_relat_1 @ X43 @ X42) = (k5_relat_1 @ (k6_relat_1 @ X42) @ X43))
% 0.66/0.90          | ~ (v1_relat_1 @ X43))),
% 0.66/0.90      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.66/0.90  thf('53', plain,
% 0.66/0.90      (![X36 : $i, X37 : $i]:
% 0.66/0.90         (~ (v1_relat_1 @ X36)
% 0.66/0.90          | ((k1_relat_1 @ (k5_relat_1 @ X37 @ X36))
% 0.66/0.90              = (k10_relat_1 @ X37 @ (k1_relat_1 @ X36)))
% 0.66/0.90          | ~ (v1_relat_1 @ X37))),
% 0.66/0.90      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.66/0.90  thf('54', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)) @ X0)),
% 0.66/0.90      inference('demod', [status(thm)], ['45', '46'])).
% 0.66/0.90  thf(d10_xboole_0, axiom,
% 0.66/0.90    (![A:$i,B:$i]:
% 0.66/0.90     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.66/0.90  thf('55', plain,
% 0.66/0.90      (![X1 : $i, X3 : $i]:
% 0.66/0.90         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.66/0.90      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.66/0.90  thf('56', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         (~ (r1_tarski @ X0 @ 
% 0.66/0.90             (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.66/0.90          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))))),
% 0.66/0.90      inference('sup-', [status(thm)], ['54', '55'])).
% 0.66/0.90  thf('57', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.66/0.90           = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.66/0.90      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.66/0.90  thf('58', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.66/0.90           = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.66/0.90      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.66/0.90  thf('59', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         (~ (r1_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.66/0.90          | ((X0) = (k10_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.66/0.90      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.66/0.90  thf('60', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         (~ (r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.66/0.90             (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 0.66/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.66/0.90          | ~ (v1_relat_1 @ X0)
% 0.66/0.90          | ((k1_relat_1 @ X0)
% 0.66/0.90              = (k10_relat_1 @ (k6_relat_1 @ X1) @ (k1_relat_1 @ X0))))),
% 0.66/0.90      inference('sup-', [status(thm)], ['53', '59'])).
% 0.66/0.90  thf('61', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 0.66/0.90      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.66/0.90  thf('62', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         (~ (r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.66/0.90             (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 0.66/0.90          | ~ (v1_relat_1 @ X0)
% 0.66/0.90          | ((k1_relat_1 @ X0)
% 0.66/0.90              = (k10_relat_1 @ (k6_relat_1 @ X1) @ (k1_relat_1 @ X0))))),
% 0.66/0.90      inference('demod', [status(thm)], ['60', '61'])).
% 0.66/0.90  thf('63', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         (~ (r1_tarski @ (k1_relat_1 @ X1) @ 
% 0.66/0.90             (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.66/0.90          | ~ (v1_relat_1 @ X1)
% 0.66/0.90          | ((k1_relat_1 @ X1)
% 0.66/0.90              = (k10_relat_1 @ (k6_relat_1 @ X0) @ (k1_relat_1 @ X1)))
% 0.66/0.90          | ~ (v1_relat_1 @ X1))),
% 0.66/0.90      inference('sup-', [status(thm)], ['52', '62'])).
% 0.66/0.90  thf('64', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         (((k1_relat_1 @ X1)
% 0.66/0.90            = (k10_relat_1 @ (k6_relat_1 @ X0) @ (k1_relat_1 @ X1)))
% 0.66/0.90          | ~ (v1_relat_1 @ X1)
% 0.66/0.90          | ~ (r1_tarski @ (k1_relat_1 @ X1) @ 
% 0.66/0.90               (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.66/0.90      inference('simplify', [status(thm)], ['63'])).
% 0.66/0.90  thf('65', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         (~ (r1_tarski @ 
% 0.66/0.90             (k1_relat_1 @ 
% 0.66/0.90              (k6_relat_1 @ (k10_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 0.66/0.90             (k1_relat_1 @ 
% 0.66/0.90              (k6_relat_1 @ (k10_relat_1 @ (k6_relat_1 @ X1) @ X0))))
% 0.66/0.90          | ~ (v1_relat_1 @ 
% 0.66/0.90               (k6_relat_1 @ (k10_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 0.66/0.90          | ((k1_relat_1 @ 
% 0.66/0.90              (k6_relat_1 @ (k10_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 0.66/0.90              = (k10_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.66/0.90                 (k1_relat_1 @ 
% 0.66/0.90                  (k6_relat_1 @ (k10_relat_1 @ (k6_relat_1 @ X1) @ X0))))))),
% 0.66/0.90      inference('sup-', [status(thm)], ['51', '64'])).
% 0.66/0.90  thf('66', plain, (![X38 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X38)) = (X38))),
% 0.66/0.90      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.66/0.90  thf('67', plain, (![X38 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X38)) = (X38))),
% 0.66/0.90      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.66/0.90  thf('68', plain,
% 0.66/0.90      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.66/0.90      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.66/0.90  thf('69', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.66/0.90      inference('simplify', [status(thm)], ['68'])).
% 0.66/0.90  thf('70', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 0.66/0.90      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.66/0.90  thf('71', plain, (![X38 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X38)) = (X38))),
% 0.66/0.90      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.66/0.90  thf('72', plain, (![X38 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X38)) = (X38))),
% 0.66/0.90      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.66/0.90  thf('73', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         ((k10_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.66/0.90           = (k10_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.66/0.90              (k10_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.66/0.90      inference('demod', [status(thm)],
% 0.66/0.90                ['65', '66', '67', '69', '70', '71', '72'])).
% 0.66/0.90  thf('74', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.66/0.90      inference('simplify', [status(thm)], ['68'])).
% 0.66/0.90  thf('75', plain,
% 0.66/0.90      (![X44 : $i, X45 : $i]:
% 0.66/0.90         (~ (r1_tarski @ (k1_relat_1 @ X44) @ X45)
% 0.66/0.90          | ((k7_relat_1 @ X44 @ X45) = (X44))
% 0.66/0.90          | ~ (v1_relat_1 @ X44))),
% 0.66/0.90      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.66/0.90  thf('76', plain,
% 0.66/0.90      (![X0 : $i]:
% 0.66/0.90         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 0.66/0.90      inference('sup-', [status(thm)], ['74', '75'])).
% 0.66/0.90  thf('77', plain,
% 0.66/0.90      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.66/0.90         (((k10_relat_1 @ (k7_relat_1 @ X47 @ X46) @ X48)
% 0.66/0.90            = (k3_xboole_0 @ X46 @ (k10_relat_1 @ X47 @ X48)))
% 0.66/0.90          | ~ (v1_relat_1 @ X47))),
% 0.66/0.90      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.66/0.90  thf('78', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         (((k10_relat_1 @ X0 @ X1)
% 0.66/0.90            = (k3_xboole_0 @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1)))
% 0.66/0.90          | ~ (v1_relat_1 @ X0)
% 0.66/0.90          | ~ (v1_relat_1 @ X0))),
% 0.66/0.90      inference('sup+', [status(thm)], ['76', '77'])).
% 0.66/0.90  thf('79', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         (~ (v1_relat_1 @ X0)
% 0.66/0.90          | ((k10_relat_1 @ X0 @ X1)
% 0.66/0.90              = (k3_xboole_0 @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))))),
% 0.66/0.90      inference('simplify', [status(thm)], ['78'])).
% 0.66/0.90  thf('80', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         (((k10_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.66/0.90            (k10_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.66/0.90            = (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.66/0.90               (k10_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 0.66/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.66/0.90      inference('sup+', [status(thm)], ['73', '79'])).
% 0.66/0.90  thf('81', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         ((k10_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.66/0.90           = (k10_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.66/0.90              (k10_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.66/0.90      inference('demod', [status(thm)],
% 0.66/0.90                ['65', '66', '67', '69', '70', '71', '72'])).
% 0.66/0.90  thf('82', plain, (![X38 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X38)) = (X38))),
% 0.66/0.90      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.66/0.90  thf('83', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 0.66/0.90      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.66/0.90  thf('84', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         ((k10_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.66/0.90           = (k3_xboole_0 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.66/0.90      inference('demod', [status(thm)], ['80', '81', '82', '83'])).
% 0.66/0.90  thf('85', plain,
% 0.66/0.90      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.66/0.90         (((k10_relat_1 @ (k7_relat_1 @ X47 @ X46) @ X48)
% 0.66/0.90            = (k3_xboole_0 @ X46 @ (k10_relat_1 @ X47 @ X48)))
% 0.66/0.90          | ~ (v1_relat_1 @ X47))),
% 0.66/0.90      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.66/0.90  thf('86', plain,
% 0.66/0.90      (![X42 : $i, X43 : $i]:
% 0.66/0.90         (((k7_relat_1 @ X43 @ X42) = (k5_relat_1 @ (k6_relat_1 @ X42) @ X43))
% 0.66/0.90          | ~ (v1_relat_1 @ X43))),
% 0.66/0.90      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.66/0.90  thf(t181_relat_1, axiom,
% 0.66/0.90    (![A:$i,B:$i]:
% 0.66/0.90     ( ( v1_relat_1 @ B ) =>
% 0.66/0.90       ( ![C:$i]:
% 0.66/0.90         ( ( v1_relat_1 @ C ) =>
% 0.66/0.90           ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.66/0.90             ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.66/0.90  thf('87', plain,
% 0.66/0.90      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.66/0.90         (~ (v1_relat_1 @ X33)
% 0.66/0.90          | ((k10_relat_1 @ (k5_relat_1 @ X34 @ X33) @ X35)
% 0.66/0.90              = (k10_relat_1 @ X34 @ (k10_relat_1 @ X33 @ X35)))
% 0.66/0.90          | ~ (v1_relat_1 @ X34))),
% 0.66/0.90      inference('cnf', [status(esa)], [t181_relat_1])).
% 0.66/0.90  thf(t167_relat_1, axiom,
% 0.66/0.90    (![A:$i,B:$i]:
% 0.66/0.90     ( ( v1_relat_1 @ B ) =>
% 0.66/0.90       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.66/0.90  thf('88', plain,
% 0.66/0.90      (![X30 : $i, X31 : $i]:
% 0.66/0.90         ((r1_tarski @ (k10_relat_1 @ X30 @ X31) @ (k1_relat_1 @ X30))
% 0.66/0.90          | ~ (v1_relat_1 @ X30))),
% 0.66/0.90      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.66/0.90  thf('89', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.90         ((r1_tarski @ (k10_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 0.66/0.90           (k1_relat_1 @ X2))
% 0.66/0.90          | ~ (v1_relat_1 @ X2)
% 0.66/0.90          | ~ (v1_relat_1 @ X1)
% 0.66/0.90          | ~ (v1_relat_1 @ X2))),
% 0.66/0.90      inference('sup+', [status(thm)], ['87', '88'])).
% 0.66/0.90  thf('90', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.90         (~ (v1_relat_1 @ X1)
% 0.66/0.90          | ~ (v1_relat_1 @ X2)
% 0.66/0.90          | (r1_tarski @ (k10_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 0.66/0.90             (k1_relat_1 @ X2)))),
% 0.66/0.90      inference('simplify', [status(thm)], ['89'])).
% 0.66/0.90  thf('91', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.90         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 0.66/0.90           (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.66/0.90          | ~ (v1_relat_1 @ X1)
% 0.66/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.66/0.90          | ~ (v1_relat_1 @ X1))),
% 0.66/0.90      inference('sup+', [status(thm)], ['86', '90'])).
% 0.66/0.90  thf('92', plain, (![X38 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X38)) = (X38))),
% 0.66/0.90      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.66/0.90  thf('93', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 0.66/0.90      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.66/0.90  thf('94', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.90         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ X0)
% 0.66/0.90          | ~ (v1_relat_1 @ X1)
% 0.66/0.90          | ~ (v1_relat_1 @ X1))),
% 0.66/0.90      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.66/0.90  thf('95', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.90         (~ (v1_relat_1 @ X1)
% 0.66/0.90          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ X0))),
% 0.66/0.90      inference('simplify', [status(thm)], ['94'])).
% 0.66/0.90  thf('96', plain,
% 0.66/0.90      (![X1 : $i, X3 : $i]:
% 0.66/0.90         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.66/0.90      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.66/0.90  thf('97', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.90         (~ (v1_relat_1 @ X2)
% 0.66/0.90          | ~ (r1_tarski @ X0 @ (k10_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1))
% 0.66/0.90          | ((X0) = (k10_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1)))),
% 0.66/0.90      inference('sup-', [status(thm)], ['95', '96'])).
% 0.66/0.90  thf('98', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.90         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)))
% 0.66/0.90          | ~ (v1_relat_1 @ X1)
% 0.66/0.90          | ((X2) = (k10_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0))
% 0.66/0.90          | ~ (v1_relat_1 @ X1))),
% 0.66/0.90      inference('sup-', [status(thm)], ['85', '97'])).
% 0.66/0.90  thf('99', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.90         (((X2) = (k10_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0))
% 0.66/0.90          | ~ (v1_relat_1 @ X1)
% 0.66/0.90          | ~ (r1_tarski @ X2 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))))),
% 0.66/0.90      inference('simplify', [status(thm)], ['98'])).
% 0.66/0.90  thf('100', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         (~ (r1_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.66/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.66/0.90          | ((X0) = (k10_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0)))),
% 0.66/0.90      inference('sup-', [status(thm)], ['84', '99'])).
% 0.66/0.90  thf('101', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 0.66/0.90      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.66/0.90  thf('102', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         (~ (r1_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.66/0.90          | ((X0) = (k10_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0)))),
% 0.66/0.90      inference('demod', [status(thm)], ['100', '101'])).
% 0.66/0.90  thf('103', plain,
% 0.66/0.90      ((~ (r1_tarski @ sk_A @ sk_A)
% 0.66/0.90        | ((sk_A)
% 0.66/0.90            = (k10_relat_1 @ 
% 0.66/0.90               (k7_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_A) @ sk_A)))),
% 0.66/0.90      inference('sup-', [status(thm)], ['42', '102'])).
% 0.66/0.90  thf('104', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.66/0.90      inference('simplify', [status(thm)], ['68'])).
% 0.66/0.90  thf('105', plain,
% 0.66/0.90      (((sk_A)
% 0.66/0.90         = (k10_relat_1 @ 
% 0.66/0.90            (k7_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_A) @ sk_A))),
% 0.66/0.90      inference('demod', [status(thm)], ['103', '104'])).
% 0.66/0.90  thf('106', plain,
% 0.66/0.90      (![X30 : $i, X31 : $i]:
% 0.66/0.90         ((r1_tarski @ (k10_relat_1 @ X30 @ X31) @ (k1_relat_1 @ X30))
% 0.66/0.90          | ~ (v1_relat_1 @ X30))),
% 0.66/0.90      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.66/0.90  thf('107', plain,
% 0.66/0.90      (![X1 : $i, X3 : $i]:
% 0.66/0.90         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.66/0.90      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.66/0.90  thf('108', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         (~ (v1_relat_1 @ X0)
% 0.66/0.90          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 0.66/0.90          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1)))),
% 0.66/0.90      inference('sup-', [status(thm)], ['106', '107'])).
% 0.66/0.90  thf('109', plain,
% 0.66/0.90      ((~ (r1_tarski @ 
% 0.66/0.90           (k1_relat_1 @ 
% 0.66/0.90            (k7_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_A)) @ 
% 0.66/0.90           sk_A)
% 0.66/0.90        | ((k1_relat_1 @ 
% 0.66/0.90            (k7_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_A))
% 0.66/0.90            = (k10_relat_1 @ 
% 0.66/0.90               (k7_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_A) @ sk_A))
% 0.66/0.90        | ~ (v1_relat_1 @ 
% 0.66/0.90             (k7_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_A)))),
% 0.66/0.90      inference('sup-', [status(thm)], ['105', '108'])).
% 0.66/0.90  thf('110', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.66/0.90           = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.66/0.90      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.66/0.90  thf('111', plain, (![X38 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X38)) = (X38))),
% 0.66/0.90      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.66/0.90  thf('112', plain,
% 0.66/0.90      (![X30 : $i, X31 : $i]:
% 0.66/0.90         ((r1_tarski @ (k10_relat_1 @ X30 @ X31) @ (k1_relat_1 @ X30))
% 0.66/0.90          | ~ (v1_relat_1 @ X30))),
% 0.66/0.90      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.66/0.90  thf('113', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         ((r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)
% 0.66/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.66/0.90      inference('sup+', [status(thm)], ['111', '112'])).
% 0.66/0.90  thf('114', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 0.66/0.90      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.66/0.90  thf('115', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)),
% 0.66/0.90      inference('demod', [status(thm)], ['113', '114'])).
% 0.66/0.90  thf('116', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.66/0.90           = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.66/0.90      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.66/0.90  thf('117', plain,
% 0.66/0.90      (((sk_A)
% 0.66/0.90         = (k10_relat_1 @ 
% 0.66/0.90            (k7_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_A) @ sk_A))),
% 0.66/0.90      inference('demod', [status(thm)], ['103', '104'])).
% 0.66/0.90  thf('118', plain,
% 0.66/0.90      ((((k10_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)) = (sk_A))
% 0.66/0.90        | ~ (v1_relat_1 @ 
% 0.66/0.90             (k7_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_A)))),
% 0.66/0.90      inference('demod', [status(thm)], ['109', '110', '115', '116', '117'])).
% 0.66/0.90  thf('119', plain,
% 0.66/0.90      ((~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 0.66/0.90        | ((k10_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)) = (sk_A)))),
% 0.66/0.90      inference('sup-', [status(thm)], ['22', '118'])).
% 0.66/0.90  thf('120', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 0.66/0.90      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.66/0.90  thf('121', plain,
% 0.66/0.90      (((k10_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)) = (sk_A))),
% 0.66/0.90      inference('demod', [status(thm)], ['119', '120'])).
% 0.66/0.90  thf('122', plain,
% 0.66/0.90      ((((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) = (sk_A))
% 0.66/0.90        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 0.66/0.90        | ~ (v1_relat_1 @ sk_B))),
% 0.66/0.90      inference('sup+', [status(thm)], ['21', '121'])).
% 0.66/0.90  thf('123', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 0.66/0.90      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.66/0.90  thf('124', plain, ((v1_relat_1 @ sk_B)),
% 0.66/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.90  thf('125', plain,
% 0.66/0.90      (((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) = (sk_A))),
% 0.66/0.90      inference('demod', [status(thm)], ['122', '123', '124'])).
% 0.66/0.90  thf('126', plain,
% 0.66/0.90      ((((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))
% 0.66/0.90        | ~ (v1_relat_1 @ sk_B))),
% 0.66/0.90      inference('sup+', [status(thm)], ['20', '125'])).
% 0.66/0.90  thf('127', plain, ((v1_relat_1 @ sk_B)),
% 0.66/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.90  thf('128', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.66/0.90      inference('demod', [status(thm)], ['126', '127'])).
% 0.66/0.90  thf('129', plain,
% 0.66/0.90      (![X26 : $i]:
% 0.66/0.90         (((k9_relat_1 @ X26 @ (k1_relat_1 @ X26)) = (k2_relat_1 @ X26))
% 0.66/0.90          | ~ (v1_relat_1 @ X26))),
% 0.66/0.90      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.66/0.90  thf('130', plain,
% 0.66/0.90      ((((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.66/0.90          = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.66/0.90        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.66/0.90      inference('sup+', [status(thm)], ['128', '129'])).
% 0.66/0.90  thf('131', plain,
% 0.66/0.90      ((~ (v1_relat_1 @ sk_B)
% 0.66/0.90        | ((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.66/0.90            = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.66/0.90      inference('sup-', [status(thm)], ['19', '130'])).
% 0.66/0.90  thf('132', plain, ((v1_relat_1 @ sk_B)),
% 0.66/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.90  thf('133', plain,
% 0.66/0.90      (((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.66/0.90         = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.66/0.90      inference('demod', [status(thm)], ['131', '132'])).
% 0.66/0.90  thf('134', plain,
% 0.66/0.90      ((((k9_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.66/0.90        | ~ (v1_relat_1 @ sk_B))),
% 0.66/0.90      inference('sup+', [status(thm)], ['18', '133'])).
% 0.66/0.90  thf('135', plain, ((v1_relat_1 @ sk_B)),
% 0.66/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.90  thf('136', plain,
% 0.66/0.90      (((k9_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.66/0.90      inference('demod', [status(thm)], ['134', '135'])).
% 0.66/0.90  thf(t169_relat_1, axiom,
% 0.66/0.90    (![A:$i]:
% 0.66/0.90     ( ( v1_relat_1 @ A ) =>
% 0.66/0.90       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.66/0.90  thf('137', plain,
% 0.66/0.90      (![X32 : $i]:
% 0.66/0.90         (((k10_relat_1 @ X32 @ (k2_relat_1 @ X32)) = (k1_relat_1 @ X32))
% 0.66/0.90          | ~ (v1_relat_1 @ X32))),
% 0.66/0.90      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.66/0.90  thf('138', plain,
% 0.66/0.90      ((((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A))
% 0.66/0.90          = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.66/0.90        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.66/0.90      inference('sup+', [status(thm)], ['136', '137'])).
% 0.66/0.90  thf('139', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.66/0.90      inference('demod', [status(thm)], ['126', '127'])).
% 0.66/0.90  thf('140', plain,
% 0.66/0.90      ((((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A))
% 0.66/0.90          = (sk_A))
% 0.66/0.90        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.66/0.90      inference('demod', [status(thm)], ['138', '139'])).
% 0.66/0.90  thf('141', plain,
% 0.66/0.90      ((~ (v1_relat_1 @ sk_B)
% 0.66/0.90        | ((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.66/0.90            (k9_relat_1 @ sk_B @ sk_A)) = (sk_A)))),
% 0.66/0.90      inference('sup-', [status(thm)], ['7', '140'])).
% 0.66/0.90  thf('142', plain, ((v1_relat_1 @ sk_B)),
% 0.66/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.90  thf('143', plain,
% 0.66/0.90      (((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A))
% 0.66/0.90         = (sk_A))),
% 0.66/0.90      inference('demod', [status(thm)], ['141', '142'])).
% 0.66/0.90  thf('144', plain,
% 0.66/0.90      ((((k3_xboole_0 @ sk_A @ 
% 0.66/0.90          (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))) = (sk_A))
% 0.66/0.90        | ~ (v1_relat_1 @ sk_B))),
% 0.66/0.90      inference('sup+', [status(thm)], ['1', '143'])).
% 0.66/0.90  thf('145', plain, ((v1_relat_1 @ sk_B)),
% 0.66/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.90  thf('146', plain,
% 0.66/0.90      (((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.66/0.90         = (sk_A))),
% 0.66/0.90      inference('demod', [status(thm)], ['144', '145'])).
% 0.66/0.90  thf('147', plain, (![X39 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X39)) = (X39))),
% 0.66/0.90      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.66/0.90  thf('148', plain,
% 0.66/0.90      (![X32 : $i]:
% 0.66/0.90         (((k10_relat_1 @ X32 @ (k2_relat_1 @ X32)) = (k1_relat_1 @ X32))
% 0.66/0.90          | ~ (v1_relat_1 @ X32))),
% 0.66/0.90      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.66/0.90  thf('149', plain,
% 0.66/0.90      (![X0 : $i]:
% 0.66/0.90         (((k10_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 0.66/0.90            = (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.66/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.66/0.90      inference('sup+', [status(thm)], ['147', '148'])).
% 0.66/0.90  thf('150', plain, (![X38 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X38)) = (X38))),
% 0.66/0.90      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.66/0.90  thf('151', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 0.66/0.90      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.66/0.90  thf('152', plain,
% 0.66/0.90      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.66/0.90      inference('demod', [status(thm)], ['149', '150', '151'])).
% 0.66/0.90  thf('153', plain,
% 0.66/0.90      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.66/0.90         (((k10_relat_1 @ (k7_relat_1 @ X47 @ X46) @ X48)
% 0.66/0.90            = (k3_xboole_0 @ X46 @ (k10_relat_1 @ X47 @ X48)))
% 0.66/0.90          | ~ (v1_relat_1 @ X47))),
% 0.66/0.90      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.66/0.90  thf('154', plain,
% 0.66/0.90      (![X40 : $i, X41 : $i]:
% 0.66/0.90         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X40 @ X41)) @ 
% 0.66/0.90           (k1_relat_1 @ X40))
% 0.66/0.90          | ~ (v1_relat_1 @ X40))),
% 0.66/0.90      inference('cnf', [status(esa)], [t89_relat_1])).
% 0.66/0.90  thf('155', plain,
% 0.66/0.90      (![X30 : $i, X31 : $i]:
% 0.66/0.90         ((r1_tarski @ (k10_relat_1 @ X30 @ X31) @ (k1_relat_1 @ X30))
% 0.66/0.90          | ~ (v1_relat_1 @ X30))),
% 0.66/0.90      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.66/0.90  thf(t1_xboole_1, axiom,
% 0.66/0.90    (![A:$i,B:$i,C:$i]:
% 0.66/0.90     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.66/0.90       ( r1_tarski @ A @ C ) ))).
% 0.66/0.90  thf('156', plain,
% 0.66/0.90      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.66/0.90         (~ (r1_tarski @ X4 @ X5)
% 0.66/0.90          | ~ (r1_tarski @ X5 @ X6)
% 0.66/0.90          | (r1_tarski @ X4 @ X6))),
% 0.66/0.90      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.66/0.90  thf('157', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.90         (~ (v1_relat_1 @ X0)
% 0.66/0.90          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ X2)
% 0.66/0.90          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ X2))),
% 0.66/0.90      inference('sup-', [status(thm)], ['155', '156'])).
% 0.66/0.90  thf('158', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.90         (~ (v1_relat_1 @ X0)
% 0.66/0.90          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X2) @ 
% 0.66/0.90             (k1_relat_1 @ X0))
% 0.66/0.90          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1)))),
% 0.66/0.90      inference('sup-', [status(thm)], ['154', '157'])).
% 0.66/0.90  thf('159', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.66/0.90      inference('simplify', [status(thm)], ['6'])).
% 0.66/0.90  thf('160', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.90         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X2) @ 
% 0.66/0.90           (k1_relat_1 @ X0))
% 0.66/0.90          | ~ (v1_relat_1 @ X0))),
% 0.66/0.90      inference('clc', [status(thm)], ['158', '159'])).
% 0.66/0.90  thf('161', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.90         ((r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 0.66/0.90           (k1_relat_1 @ X1))
% 0.66/0.90          | ~ (v1_relat_1 @ X1)
% 0.66/0.90          | ~ (v1_relat_1 @ X1))),
% 0.66/0.90      inference('sup+', [status(thm)], ['153', '160'])).
% 0.66/0.90  thf('162', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.90         (~ (v1_relat_1 @ X1)
% 0.66/0.90          | (r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 0.66/0.90             (k1_relat_1 @ X1)))),
% 0.66/0.90      inference('simplify', [status(thm)], ['161'])).
% 0.66/0.90  thf('163', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.66/0.90           (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.66/0.90          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.66/0.90      inference('sup+', [status(thm)], ['152', '162'])).
% 0.66/0.90  thf('164', plain, (![X38 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X38)) = (X38))),
% 0.66/0.90      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.66/0.90  thf('165', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 0.66/0.90      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.66/0.90  thf('166', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.66/0.90      inference('demod', [status(thm)], ['163', '164', '165'])).
% 0.66/0.90  thf('167', plain,
% 0.66/0.90      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.66/0.90      inference('sup+', [status(thm)], ['146', '166'])).
% 0.66/0.90  thf('168', plain, ($false), inference('demod', [status(thm)], ['0', '167'])).
% 0.66/0.90  
% 0.66/0.90  % SZS output end Refutation
% 0.66/0.90  
% 0.66/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
