%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WgsrOSpga2

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:07 EST 2020

% Result     : Theorem 38.27s
% Output     : Refutation 38.27s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 683 expanded)
%              Number of leaves         :   24 ( 208 expanded)
%              Depth                    :   32
%              Number of atoms          : 1375 (7214 expanded)
%              Number of equality atoms :   64 ( 380 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('0',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( v2_funct_1 @ X39 )
      | ( ( k10_relat_1 @ X39 @ X40 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X39 ) @ X40 ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf(t164_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
            & ( v2_funct_1 @ B ) )
         => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t164_funct_1])).

thf('1',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X32: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X32 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('3',plain,(
    ! [X32: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X32 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('4',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( v2_funct_1 @ X39 )
      | ( ( k10_relat_1 @ X39 @ X40 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X39 ) @ X40 ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('5',plain,(
    ! [X32: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X32 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('6',plain,(
    ! [X32: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X32 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('7',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X18 @ X19 ) @ ( k2_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf(t154_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k9_relat_1 @ B @ A )
          = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('8',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v2_funct_1 @ X37 )
      | ( ( k9_relat_1 @ X37 @ X38 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X37 ) @ X38 ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( r1_tarski @ X33 @ ( k1_relat_1 @ X34 ) )
      | ( r1_tarski @ X33 @ ( k10_relat_1 @ X34 @ ( k9_relat_1 @ X34 @ X33 ) ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('13',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ X14 @ X15 )
      | ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('20',plain,(
    ! [X20: $i] :
      ( ( ( k9_relat_1 @ X20 @ ( k1_relat_1 @ X20 ) )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('24',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X27 @ X28 ) @ ( k1_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('25',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('30',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ X14 @ X15 )
      | ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('36',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('37',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) )
    = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
      = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','37'])).

thf('39',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('41',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','41','42'])).

thf('44',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('45',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ X35 @ ( k2_relat_1 @ X36 ) )
      | ( ( k9_relat_1 @ X36 @ ( k10_relat_1 @ X36 @ X35 ) )
        = X35 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ! [X32: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X32 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('52',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v2_funct_1 @ X37 )
      | ( ( k9_relat_1 @ X37 @ X38 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X37 ) @ X38 ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('53',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X27 @ X28 ) @ ( k1_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k2_relat_1 @ sk_B ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) )
      = ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['50','58'])).

thf('60',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('61',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k2_relat_1 @ sk_B ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) )
      = ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','60','61','62','63'])).

thf('65',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) )
      = ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['65','66','67','68'])).

thf('70',plain,(
    ! [X20: $i] :
      ( ( ( k9_relat_1 @ X20 @ ( k1_relat_1 @ X20 ) )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('71',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k2_relat_1 @ sk_B ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k2_relat_1 @ sk_B ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k2_relat_1 @ sk_B ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['4','75'])).

thf('77',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','41','42'])).

thf('78',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['76','77','78','79','80'])).

thf('82',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ X35 @ ( k2_relat_1 @ X36 ) )
      | ( ( k9_relat_1 @ X36 @ ( k10_relat_1 @ X36 @ X35 ) )
        = X35 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v2_funct_1 @ X37 )
      | ( ( k9_relat_1 @ X37 @ X38 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X37 ) @ X38 ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('85',plain,(
    ! [X32: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X32 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('86',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['65','66','67','68'])).

thf('87',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X27 @ X28 ) @ ( k1_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ X35 @ ( k2_relat_1 @ X36 ) )
      | ( ( k9_relat_1 @ X36 @ ( k10_relat_1 @ X36 @ X35 ) )
        = X35 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) ) )
        = ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) ) )
      = ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ X0 ) ) )
        = ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['84','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('100',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('102',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['102','103','104','105'])).

thf('107',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X18 @ X19 ) @ ( k2_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('108',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ X14 @ X15 )
      | ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['106','109'])).

thf('111',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ X14 @ X15 )
      | ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_B @ X0 ) @ X1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B )
      | ( r1_tarski @ ( k9_relat_1 @ sk_B @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['99','114'])).

thf('116',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_B @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['115','116','117','118'])).

thf('120',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ X35 @ ( k2_relat_1 @ X36 ) )
      | ( ( k9_relat_1 @ X36 @ ( k10_relat_1 @ X36 @ X35 ) )
        = X35 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ X0 ) ) )
        = ( k9_relat_1 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ X0 ) ) )
      = ( k9_relat_1 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['121','122','123'])).

thf('125',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_B @ X0 )
      = ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['98','124','125','126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['83','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','129'])).

thf('131',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['2','133'])).

thf('135',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('138',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['1','137'])).

thf('139',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','138'])).

thf('140',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['139','140','141','142'])).

thf('144',plain,(
    ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['143','144'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WgsrOSpga2
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:57:03 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 38.27/38.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 38.27/38.45  % Solved by: fo/fo7.sh
% 38.27/38.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 38.27/38.45  % done 36880 iterations in 37.990s
% 38.27/38.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 38.27/38.45  % SZS output start Refutation
% 38.27/38.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 38.27/38.45  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 38.27/38.45  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 38.27/38.45  thf(sk_B_type, type, sk_B: $i).
% 38.27/38.45  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 38.27/38.45  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 38.27/38.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 38.27/38.45  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 38.27/38.45  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 38.27/38.45  thf(sk_A_type, type, sk_A: $i).
% 38.27/38.45  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 38.27/38.45  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 38.27/38.45  thf(t155_funct_1, axiom,
% 38.27/38.45    (![A:$i,B:$i]:
% 38.27/38.45     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 38.27/38.45       ( ( v2_funct_1 @ B ) =>
% 38.27/38.45         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 38.27/38.45  thf('0', plain,
% 38.27/38.45      (![X39 : $i, X40 : $i]:
% 38.27/38.45         (~ (v2_funct_1 @ X39)
% 38.27/38.45          | ((k10_relat_1 @ X39 @ X40)
% 38.27/38.45              = (k9_relat_1 @ (k2_funct_1 @ X39) @ X40))
% 38.27/38.45          | ~ (v1_funct_1 @ X39)
% 38.27/38.45          | ~ (v1_relat_1 @ X39))),
% 38.27/38.45      inference('cnf', [status(esa)], [t155_funct_1])).
% 38.27/38.45  thf(t164_funct_1, conjecture,
% 38.27/38.45    (![A:$i,B:$i]:
% 38.27/38.45     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 38.27/38.45       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 38.27/38.45         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 38.27/38.45  thf(zf_stmt_0, negated_conjecture,
% 38.27/38.45    (~( ![A:$i,B:$i]:
% 38.27/38.45        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 38.27/38.45          ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 38.27/38.45            ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ) )),
% 38.27/38.45    inference('cnf.neg', [status(esa)], [t164_funct_1])).
% 38.27/38.45  thf('1', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf(dt_k2_funct_1, axiom,
% 38.27/38.45    (![A:$i]:
% 38.27/38.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 38.27/38.45       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 38.27/38.45         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 38.27/38.45  thf('2', plain,
% 38.27/38.45      (![X32 : $i]:
% 38.27/38.45         ((v1_funct_1 @ (k2_funct_1 @ X32))
% 38.27/38.45          | ~ (v1_funct_1 @ X32)
% 38.27/38.45          | ~ (v1_relat_1 @ X32))),
% 38.27/38.45      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 38.27/38.45  thf('3', plain,
% 38.27/38.45      (![X32 : $i]:
% 38.27/38.45         ((v1_relat_1 @ (k2_funct_1 @ X32))
% 38.27/38.45          | ~ (v1_funct_1 @ X32)
% 38.27/38.45          | ~ (v1_relat_1 @ X32))),
% 38.27/38.45      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 38.27/38.45  thf('4', plain,
% 38.27/38.45      (![X39 : $i, X40 : $i]:
% 38.27/38.45         (~ (v2_funct_1 @ X39)
% 38.27/38.45          | ((k10_relat_1 @ X39 @ X40)
% 38.27/38.45              = (k9_relat_1 @ (k2_funct_1 @ X39) @ X40))
% 38.27/38.45          | ~ (v1_funct_1 @ X39)
% 38.27/38.45          | ~ (v1_relat_1 @ X39))),
% 38.27/38.45      inference('cnf', [status(esa)], [t155_funct_1])).
% 38.27/38.45  thf('5', plain,
% 38.27/38.45      (![X32 : $i]:
% 38.27/38.45         ((v1_relat_1 @ (k2_funct_1 @ X32))
% 38.27/38.45          | ~ (v1_funct_1 @ X32)
% 38.27/38.45          | ~ (v1_relat_1 @ X32))),
% 38.27/38.45      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 38.27/38.45  thf('6', plain,
% 38.27/38.45      (![X32 : $i]:
% 38.27/38.45         ((v1_relat_1 @ (k2_funct_1 @ X32))
% 38.27/38.45          | ~ (v1_funct_1 @ X32)
% 38.27/38.45          | ~ (v1_relat_1 @ X32))),
% 38.27/38.45      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 38.27/38.45  thf(t144_relat_1, axiom,
% 38.27/38.45    (![A:$i,B:$i]:
% 38.27/38.45     ( ( v1_relat_1 @ B ) =>
% 38.27/38.45       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 38.27/38.45  thf('7', plain,
% 38.27/38.45      (![X18 : $i, X19 : $i]:
% 38.27/38.45         ((r1_tarski @ (k9_relat_1 @ X18 @ X19) @ (k2_relat_1 @ X18))
% 38.27/38.45          | ~ (v1_relat_1 @ X18))),
% 38.27/38.45      inference('cnf', [status(esa)], [t144_relat_1])).
% 38.27/38.45  thf(t154_funct_1, axiom,
% 38.27/38.45    (![A:$i,B:$i]:
% 38.27/38.45     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 38.27/38.45       ( ( v2_funct_1 @ B ) =>
% 38.27/38.45         ( ( k9_relat_1 @ B @ A ) = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 38.27/38.45  thf('8', plain,
% 38.27/38.45      (![X37 : $i, X38 : $i]:
% 38.27/38.45         (~ (v2_funct_1 @ X37)
% 38.27/38.45          | ((k9_relat_1 @ X37 @ X38)
% 38.27/38.45              = (k10_relat_1 @ (k2_funct_1 @ X37) @ X38))
% 38.27/38.45          | ~ (v1_funct_1 @ X37)
% 38.27/38.45          | ~ (v1_relat_1 @ X37))),
% 38.27/38.45      inference('cnf', [status(esa)], [t154_funct_1])).
% 38.27/38.45  thf(d10_xboole_0, axiom,
% 38.27/38.45    (![A:$i,B:$i]:
% 38.27/38.45     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 38.27/38.45  thf('9', plain,
% 38.27/38.45      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 38.27/38.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 38.27/38.45  thf('10', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 38.27/38.45      inference('simplify', [status(thm)], ['9'])).
% 38.27/38.45  thf(t146_funct_1, axiom,
% 38.27/38.45    (![A:$i,B:$i]:
% 38.27/38.45     ( ( v1_relat_1 @ B ) =>
% 38.27/38.45       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 38.27/38.45         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 38.27/38.45  thf('11', plain,
% 38.27/38.45      (![X33 : $i, X34 : $i]:
% 38.27/38.45         (~ (r1_tarski @ X33 @ (k1_relat_1 @ X34))
% 38.27/38.45          | (r1_tarski @ X33 @ (k10_relat_1 @ X34 @ (k9_relat_1 @ X34 @ X33)))
% 38.27/38.45          | ~ (v1_relat_1 @ X34))),
% 38.27/38.45      inference('cnf', [status(esa)], [t146_funct_1])).
% 38.27/38.45  thf('12', plain,
% 38.27/38.45      (![X0 : $i]:
% 38.27/38.45         (~ (v1_relat_1 @ X0)
% 38.27/38.45          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 38.27/38.45             (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))))),
% 38.27/38.45      inference('sup-', [status(thm)], ['10', '11'])).
% 38.27/38.45  thf(t1_xboole_1, axiom,
% 38.27/38.45    (![A:$i,B:$i,C:$i]:
% 38.27/38.45     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 38.27/38.45       ( r1_tarski @ A @ C ) ))).
% 38.27/38.45  thf('13', plain,
% 38.27/38.45      (![X13 : $i, X14 : $i, X15 : $i]:
% 38.27/38.45         (~ (r1_tarski @ X13 @ X14)
% 38.27/38.45          | ~ (r1_tarski @ X14 @ X15)
% 38.27/38.45          | (r1_tarski @ X13 @ X15))),
% 38.27/38.45      inference('cnf', [status(esa)], [t1_xboole_1])).
% 38.27/38.45  thf('14', plain,
% 38.27/38.45      (![X0 : $i, X1 : $i]:
% 38.27/38.45         (~ (v1_relat_1 @ X0)
% 38.27/38.45          | (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 38.27/38.45          | ~ (r1_tarski @ 
% 38.27/38.45               (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))) @ X1))),
% 38.27/38.45      inference('sup-', [status(thm)], ['12', '13'])).
% 38.27/38.45  thf('15', plain,
% 38.27/38.45      (![X0 : $i, X1 : $i]:
% 38.27/38.45         (~ (r1_tarski @ 
% 38.27/38.45             (k9_relat_1 @ X0 @ 
% 38.27/38.45              (k9_relat_1 @ (k2_funct_1 @ X0) @ 
% 38.27/38.45               (k1_relat_1 @ (k2_funct_1 @ X0)))) @ 
% 38.27/38.45             X1)
% 38.27/38.45          | ~ (v1_relat_1 @ X0)
% 38.27/38.45          | ~ (v1_funct_1 @ X0)
% 38.27/38.45          | ~ (v2_funct_1 @ X0)
% 38.27/38.45          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ X1)
% 38.27/38.45          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 38.27/38.45      inference('sup-', [status(thm)], ['8', '14'])).
% 38.27/38.45  thf('16', plain,
% 38.27/38.45      (![X0 : $i]:
% 38.27/38.45         (~ (v1_relat_1 @ X0)
% 38.27/38.45          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 38.27/38.45          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 38.27/38.45          | ~ (v2_funct_1 @ X0)
% 38.27/38.45          | ~ (v1_funct_1 @ X0)
% 38.27/38.45          | ~ (v1_relat_1 @ X0))),
% 38.27/38.45      inference('sup-', [status(thm)], ['7', '15'])).
% 38.27/38.45  thf('17', plain,
% 38.27/38.45      (![X0 : $i]:
% 38.27/38.45         (~ (v1_funct_1 @ X0)
% 38.27/38.45          | ~ (v2_funct_1 @ X0)
% 38.27/38.45          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 38.27/38.45          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 38.27/38.45          | ~ (v1_relat_1 @ X0))),
% 38.27/38.45      inference('simplify', [status(thm)], ['16'])).
% 38.27/38.45  thf('18', plain,
% 38.27/38.45      (![X0 : $i]:
% 38.27/38.45         (~ (v1_relat_1 @ X0)
% 38.27/38.45          | ~ (v1_funct_1 @ X0)
% 38.27/38.45          | ~ (v1_relat_1 @ X0)
% 38.27/38.45          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 38.27/38.45          | ~ (v2_funct_1 @ X0)
% 38.27/38.45          | ~ (v1_funct_1 @ X0))),
% 38.27/38.45      inference('sup-', [status(thm)], ['6', '17'])).
% 38.27/38.45  thf('19', plain,
% 38.27/38.45      (![X0 : $i]:
% 38.27/38.45         (~ (v2_funct_1 @ X0)
% 38.27/38.45          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 38.27/38.45          | ~ (v1_funct_1 @ X0)
% 38.27/38.45          | ~ (v1_relat_1 @ X0))),
% 38.27/38.45      inference('simplify', [status(thm)], ['18'])).
% 38.27/38.45  thf(t146_relat_1, axiom,
% 38.27/38.45    (![A:$i]:
% 38.27/38.45     ( ( v1_relat_1 @ A ) =>
% 38.27/38.45       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 38.27/38.45  thf('20', plain,
% 38.27/38.45      (![X20 : $i]:
% 38.27/38.45         (((k9_relat_1 @ X20 @ (k1_relat_1 @ X20)) = (k2_relat_1 @ X20))
% 38.27/38.45          | ~ (v1_relat_1 @ X20))),
% 38.27/38.45      inference('cnf', [status(esa)], [t146_relat_1])).
% 38.27/38.45  thf('21', plain,
% 38.27/38.45      (![X0 : $i]:
% 38.27/38.45         (~ (v1_relat_1 @ X0)
% 38.27/38.45          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 38.27/38.45             (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))))),
% 38.27/38.45      inference('sup-', [status(thm)], ['10', '11'])).
% 38.27/38.45  thf('22', plain,
% 38.27/38.45      (![X0 : $i]:
% 38.27/38.45         ((r1_tarski @ (k1_relat_1 @ X0) @ 
% 38.27/38.45           (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 38.27/38.45          | ~ (v1_relat_1 @ X0)
% 38.27/38.45          | ~ (v1_relat_1 @ X0))),
% 38.27/38.45      inference('sup+', [status(thm)], ['20', '21'])).
% 38.27/38.45  thf('23', plain,
% 38.27/38.45      (![X0 : $i]:
% 38.27/38.45         (~ (v1_relat_1 @ X0)
% 38.27/38.45          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 38.27/38.45             (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 38.27/38.45      inference('simplify', [status(thm)], ['22'])).
% 38.27/38.45  thf(t167_relat_1, axiom,
% 38.27/38.45    (![A:$i,B:$i]:
% 38.27/38.45     ( ( v1_relat_1 @ B ) =>
% 38.27/38.45       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 38.27/38.45  thf('24', plain,
% 38.27/38.45      (![X27 : $i, X28 : $i]:
% 38.27/38.45         ((r1_tarski @ (k10_relat_1 @ X27 @ X28) @ (k1_relat_1 @ X27))
% 38.27/38.45          | ~ (v1_relat_1 @ X27))),
% 38.27/38.45      inference('cnf', [status(esa)], [t167_relat_1])).
% 38.27/38.45  thf('25', plain,
% 38.27/38.45      (![X8 : $i, X10 : $i]:
% 38.27/38.45         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 38.27/38.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 38.27/38.45  thf('26', plain,
% 38.27/38.45      (![X0 : $i, X1 : $i]:
% 38.27/38.45         (~ (v1_relat_1 @ X0)
% 38.27/38.45          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 38.27/38.45          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1)))),
% 38.27/38.45      inference('sup-', [status(thm)], ['24', '25'])).
% 38.27/38.45  thf('27', plain,
% 38.27/38.45      (![X0 : $i]:
% 38.27/38.45         (~ (v1_relat_1 @ X0)
% 38.27/38.45          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 38.27/38.45          | ~ (v1_relat_1 @ X0))),
% 38.27/38.45      inference('sup-', [status(thm)], ['23', '26'])).
% 38.27/38.45  thf('28', plain,
% 38.27/38.45      (![X0 : $i]:
% 38.27/38.45         (((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 38.27/38.45          | ~ (v1_relat_1 @ X0))),
% 38.27/38.45      inference('simplify', [status(thm)], ['27'])).
% 38.27/38.45  thf('29', plain,
% 38.27/38.45      (![X0 : $i]:
% 38.27/38.45         (~ (v1_relat_1 @ X0)
% 38.27/38.45          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 38.27/38.45             (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 38.27/38.45      inference('simplify', [status(thm)], ['22'])).
% 38.27/38.45  thf('30', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('31', plain,
% 38.27/38.45      (![X13 : $i, X14 : $i, X15 : $i]:
% 38.27/38.45         (~ (r1_tarski @ X13 @ X14)
% 38.27/38.45          | ~ (r1_tarski @ X14 @ X15)
% 38.27/38.45          | (r1_tarski @ X13 @ X15))),
% 38.27/38.45      inference('cnf', [status(esa)], [t1_xboole_1])).
% 38.27/38.45  thf('32', plain,
% 38.27/38.45      (![X0 : $i]:
% 38.27/38.45         ((r1_tarski @ sk_A @ X0) | ~ (r1_tarski @ (k1_relat_1 @ sk_B) @ X0))),
% 38.27/38.45      inference('sup-', [status(thm)], ['30', '31'])).
% 38.27/38.45  thf('33', plain,
% 38.27/38.45      ((~ (v1_relat_1 @ sk_B)
% 38.27/38.45        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))))),
% 38.27/38.45      inference('sup-', [status(thm)], ['29', '32'])).
% 38.27/38.45  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('35', plain,
% 38.27/38.45      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 38.27/38.45      inference('demod', [status(thm)], ['33', '34'])).
% 38.27/38.45  thf(t12_xboole_1, axiom,
% 38.27/38.45    (![A:$i,B:$i]:
% 38.27/38.45     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 38.27/38.45  thf('36', plain,
% 38.27/38.45      (![X11 : $i, X12 : $i]:
% 38.27/38.45         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 38.27/38.45      inference('cnf', [status(esa)], [t12_xboole_1])).
% 38.27/38.45  thf('37', plain,
% 38.27/38.45      (((k2_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))
% 38.27/38.45         = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 38.27/38.45      inference('sup-', [status(thm)], ['35', '36'])).
% 38.27/38.45  thf('38', plain,
% 38.27/38.45      ((((k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B))
% 38.27/38.45          = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))
% 38.27/38.45        | ~ (v1_relat_1 @ sk_B))),
% 38.27/38.45      inference('sup+', [status(thm)], ['28', '37'])).
% 38.27/38.45  thf('39', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('40', plain,
% 38.27/38.45      (![X11 : $i, X12 : $i]:
% 38.27/38.45         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 38.27/38.45      inference('cnf', [status(esa)], [t12_xboole_1])).
% 38.27/38.45  thf('41', plain,
% 38.27/38.45      (((k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (k1_relat_1 @ sk_B))),
% 38.27/38.45      inference('sup-', [status(thm)], ['39', '40'])).
% 38.27/38.45  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('43', plain,
% 38.27/38.45      (((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 38.27/38.45      inference('demod', [status(thm)], ['38', '41', '42'])).
% 38.27/38.45  thf('44', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 38.27/38.45      inference('simplify', [status(thm)], ['9'])).
% 38.27/38.45  thf(t147_funct_1, axiom,
% 38.27/38.45    (![A:$i,B:$i]:
% 38.27/38.45     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 38.27/38.45       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 38.27/38.45         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 38.27/38.45  thf('45', plain,
% 38.27/38.45      (![X35 : $i, X36 : $i]:
% 38.27/38.45         (~ (r1_tarski @ X35 @ (k2_relat_1 @ X36))
% 38.27/38.45          | ((k9_relat_1 @ X36 @ (k10_relat_1 @ X36 @ X35)) = (X35))
% 38.27/38.45          | ~ (v1_funct_1 @ X36)
% 38.27/38.45          | ~ (v1_relat_1 @ X36))),
% 38.27/38.45      inference('cnf', [status(esa)], [t147_funct_1])).
% 38.27/38.45  thf('46', plain,
% 38.27/38.45      (![X0 : $i]:
% 38.27/38.45         (~ (v1_relat_1 @ X0)
% 38.27/38.45          | ~ (v1_funct_1 @ X0)
% 38.27/38.45          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 38.27/38.45              = (k2_relat_1 @ X0)))),
% 38.27/38.45      inference('sup-', [status(thm)], ['44', '45'])).
% 38.27/38.45  thf('47', plain,
% 38.27/38.45      ((((k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)) = (k2_relat_1 @ sk_B))
% 38.27/38.45        | ~ (v1_funct_1 @ sk_B)
% 38.27/38.45        | ~ (v1_relat_1 @ sk_B))),
% 38.27/38.45      inference('sup+', [status(thm)], ['43', '46'])).
% 38.27/38.45  thf('48', plain, ((v1_funct_1 @ sk_B)),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('49', plain, ((v1_relat_1 @ sk_B)),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('50', plain,
% 38.27/38.45      (((k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)) = (k2_relat_1 @ sk_B))),
% 38.27/38.45      inference('demod', [status(thm)], ['47', '48', '49'])).
% 38.27/38.45  thf('51', plain,
% 38.27/38.45      (![X32 : $i]:
% 38.27/38.45         ((v1_relat_1 @ (k2_funct_1 @ X32))
% 38.27/38.45          | ~ (v1_funct_1 @ X32)
% 38.27/38.45          | ~ (v1_relat_1 @ X32))),
% 38.27/38.45      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 38.27/38.45  thf('52', plain,
% 38.27/38.45      (![X37 : $i, X38 : $i]:
% 38.27/38.45         (~ (v2_funct_1 @ X37)
% 38.27/38.45          | ((k9_relat_1 @ X37 @ X38)
% 38.27/38.45              = (k10_relat_1 @ (k2_funct_1 @ X37) @ X38))
% 38.27/38.45          | ~ (v1_funct_1 @ X37)
% 38.27/38.45          | ~ (v1_relat_1 @ X37))),
% 38.27/38.45      inference('cnf', [status(esa)], [t154_funct_1])).
% 38.27/38.45  thf('53', plain,
% 38.27/38.45      (![X27 : $i, X28 : $i]:
% 38.27/38.45         ((r1_tarski @ (k10_relat_1 @ X27 @ X28) @ (k1_relat_1 @ X27))
% 38.27/38.45          | ~ (v1_relat_1 @ X27))),
% 38.27/38.45      inference('cnf', [status(esa)], [t167_relat_1])).
% 38.27/38.45  thf('54', plain,
% 38.27/38.45      (![X0 : $i, X1 : $i]:
% 38.27/38.45         ((r1_tarski @ (k9_relat_1 @ X1 @ X0) @ 
% 38.27/38.45           (k1_relat_1 @ (k2_funct_1 @ X1)))
% 38.27/38.45          | ~ (v1_relat_1 @ X1)
% 38.27/38.45          | ~ (v1_funct_1 @ X1)
% 38.27/38.45          | ~ (v2_funct_1 @ X1)
% 38.27/38.45          | ~ (v1_relat_1 @ (k2_funct_1 @ X1)))),
% 38.27/38.45      inference('sup+', [status(thm)], ['52', '53'])).
% 38.27/38.45  thf('55', plain,
% 38.27/38.45      (![X0 : $i, X1 : $i]:
% 38.27/38.45         (~ (v1_relat_1 @ X0)
% 38.27/38.45          | ~ (v1_funct_1 @ X0)
% 38.27/38.45          | ~ (v2_funct_1 @ X0)
% 38.27/38.45          | ~ (v1_funct_1 @ X0)
% 38.27/38.45          | ~ (v1_relat_1 @ X0)
% 38.27/38.45          | (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ 
% 38.27/38.45             (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 38.27/38.45      inference('sup-', [status(thm)], ['51', '54'])).
% 38.27/38.45  thf('56', plain,
% 38.27/38.45      (![X0 : $i, X1 : $i]:
% 38.27/38.45         ((r1_tarski @ (k9_relat_1 @ X0 @ X1) @ 
% 38.27/38.45           (k1_relat_1 @ (k2_funct_1 @ X0)))
% 38.27/38.45          | ~ (v2_funct_1 @ X0)
% 38.27/38.45          | ~ (v1_funct_1 @ X0)
% 38.27/38.45          | ~ (v1_relat_1 @ X0))),
% 38.27/38.45      inference('simplify', [status(thm)], ['55'])).
% 38.27/38.45  thf('57', plain,
% 38.27/38.45      (![X8 : $i, X10 : $i]:
% 38.27/38.45         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 38.27/38.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 38.27/38.45  thf('58', plain,
% 38.27/38.45      (![X0 : $i, X1 : $i]:
% 38.27/38.45         (~ (v1_relat_1 @ X0)
% 38.27/38.45          | ~ (v1_funct_1 @ X0)
% 38.27/38.45          | ~ (v2_funct_1 @ X0)
% 38.27/38.45          | ~ (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 38.27/38.45               (k9_relat_1 @ X0 @ X1))
% 38.27/38.45          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k9_relat_1 @ X0 @ X1)))),
% 38.27/38.45      inference('sup-', [status(thm)], ['56', '57'])).
% 38.27/38.45  thf('59', plain,
% 38.27/38.45      ((~ (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_B)) @ (k2_relat_1 @ sk_B))
% 38.27/38.45        | ((k1_relat_1 @ (k2_funct_1 @ sk_B))
% 38.27/38.45            = (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))
% 38.27/38.45        | ~ (v2_funct_1 @ sk_B)
% 38.27/38.45        | ~ (v1_funct_1 @ sk_B)
% 38.27/38.45        | ~ (v1_relat_1 @ sk_B))),
% 38.27/38.45      inference('sup-', [status(thm)], ['50', '58'])).
% 38.27/38.45  thf('60', plain,
% 38.27/38.45      (((k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)) = (k2_relat_1 @ sk_B))),
% 38.27/38.45      inference('demod', [status(thm)], ['47', '48', '49'])).
% 38.27/38.45  thf('61', plain, ((v2_funct_1 @ sk_B)),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('62', plain, ((v1_funct_1 @ sk_B)),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('63', plain, ((v1_relat_1 @ sk_B)),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('64', plain,
% 38.27/38.45      ((~ (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_B)) @ (k2_relat_1 @ sk_B))
% 38.27/38.45        | ((k1_relat_1 @ (k2_funct_1 @ sk_B)) = (k2_relat_1 @ sk_B)))),
% 38.27/38.45      inference('demod', [status(thm)], ['59', '60', '61', '62', '63'])).
% 38.27/38.45  thf('65', plain,
% 38.27/38.45      ((~ (v1_relat_1 @ sk_B)
% 38.27/38.45        | ~ (v1_funct_1 @ sk_B)
% 38.27/38.45        | ~ (v2_funct_1 @ sk_B)
% 38.27/38.45        | ((k1_relat_1 @ (k2_funct_1 @ sk_B)) = (k2_relat_1 @ sk_B)))),
% 38.27/38.45      inference('sup-', [status(thm)], ['19', '64'])).
% 38.27/38.45  thf('66', plain, ((v1_relat_1 @ sk_B)),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('67', plain, ((v1_funct_1 @ sk_B)),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('68', plain, ((v2_funct_1 @ sk_B)),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('69', plain,
% 38.27/38.45      (((k1_relat_1 @ (k2_funct_1 @ sk_B)) = (k2_relat_1 @ sk_B))),
% 38.27/38.45      inference('demod', [status(thm)], ['65', '66', '67', '68'])).
% 38.27/38.45  thf('70', plain,
% 38.27/38.45      (![X20 : $i]:
% 38.27/38.45         (((k9_relat_1 @ X20 @ (k1_relat_1 @ X20)) = (k2_relat_1 @ X20))
% 38.27/38.45          | ~ (v1_relat_1 @ X20))),
% 38.27/38.45      inference('cnf', [status(esa)], [t146_relat_1])).
% 38.27/38.45  thf('71', plain,
% 38.27/38.45      ((((k9_relat_1 @ (k2_funct_1 @ sk_B) @ (k2_relat_1 @ sk_B))
% 38.27/38.45          = (k2_relat_1 @ (k2_funct_1 @ sk_B)))
% 38.27/38.45        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 38.27/38.45      inference('sup+', [status(thm)], ['69', '70'])).
% 38.27/38.45  thf('72', plain,
% 38.27/38.45      ((~ (v1_relat_1 @ sk_B)
% 38.27/38.45        | ~ (v1_funct_1 @ sk_B)
% 38.27/38.45        | ((k9_relat_1 @ (k2_funct_1 @ sk_B) @ (k2_relat_1 @ sk_B))
% 38.27/38.45            = (k2_relat_1 @ (k2_funct_1 @ sk_B))))),
% 38.27/38.45      inference('sup-', [status(thm)], ['5', '71'])).
% 38.27/38.45  thf('73', plain, ((v1_relat_1 @ sk_B)),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('74', plain, ((v1_funct_1 @ sk_B)),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('75', plain,
% 38.27/38.45      (((k9_relat_1 @ (k2_funct_1 @ sk_B) @ (k2_relat_1 @ sk_B))
% 38.27/38.45         = (k2_relat_1 @ (k2_funct_1 @ sk_B)))),
% 38.27/38.45      inference('demod', [status(thm)], ['72', '73', '74'])).
% 38.27/38.45  thf('76', plain,
% 38.27/38.45      ((((k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))
% 38.27/38.45          = (k2_relat_1 @ (k2_funct_1 @ sk_B)))
% 38.27/38.45        | ~ (v1_relat_1 @ sk_B)
% 38.27/38.45        | ~ (v1_funct_1 @ sk_B)
% 38.27/38.45        | ~ (v2_funct_1 @ sk_B))),
% 38.27/38.45      inference('sup+', [status(thm)], ['4', '75'])).
% 38.27/38.45  thf('77', plain,
% 38.27/38.45      (((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 38.27/38.45      inference('demod', [status(thm)], ['38', '41', '42'])).
% 38.27/38.45  thf('78', plain, ((v1_relat_1 @ sk_B)),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('79', plain, ((v1_funct_1 @ sk_B)),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('80', plain, ((v2_funct_1 @ sk_B)),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('81', plain,
% 38.27/38.45      (((k1_relat_1 @ sk_B) = (k2_relat_1 @ (k2_funct_1 @ sk_B)))),
% 38.27/38.45      inference('demod', [status(thm)], ['76', '77', '78', '79', '80'])).
% 38.27/38.45  thf('82', plain,
% 38.27/38.45      (![X35 : $i, X36 : $i]:
% 38.27/38.45         (~ (r1_tarski @ X35 @ (k2_relat_1 @ X36))
% 38.27/38.45          | ((k9_relat_1 @ X36 @ (k10_relat_1 @ X36 @ X35)) = (X35))
% 38.27/38.45          | ~ (v1_funct_1 @ X36)
% 38.27/38.45          | ~ (v1_relat_1 @ X36))),
% 38.27/38.45      inference('cnf', [status(esa)], [t147_funct_1])).
% 38.27/38.45  thf('83', plain,
% 38.27/38.45      (![X0 : $i]:
% 38.27/38.45         (~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_B))
% 38.27/38.45          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 38.27/38.45          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 38.27/38.45          | ((k9_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 38.27/38.45              (k10_relat_1 @ (k2_funct_1 @ sk_B) @ X0)) = (X0)))),
% 38.27/38.45      inference('sup-', [status(thm)], ['81', '82'])).
% 38.27/38.45  thf('84', plain,
% 38.27/38.45      (![X37 : $i, X38 : $i]:
% 38.27/38.45         (~ (v2_funct_1 @ X37)
% 38.27/38.45          | ((k9_relat_1 @ X37 @ X38)
% 38.27/38.45              = (k10_relat_1 @ (k2_funct_1 @ X37) @ X38))
% 38.27/38.45          | ~ (v1_funct_1 @ X37)
% 38.27/38.45          | ~ (v1_relat_1 @ X37))),
% 38.27/38.45      inference('cnf', [status(esa)], [t154_funct_1])).
% 38.27/38.45  thf('85', plain,
% 38.27/38.45      (![X32 : $i]:
% 38.27/38.45         ((v1_relat_1 @ (k2_funct_1 @ X32))
% 38.27/38.45          | ~ (v1_funct_1 @ X32)
% 38.27/38.45          | ~ (v1_relat_1 @ X32))),
% 38.27/38.45      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 38.27/38.45  thf('86', plain,
% 38.27/38.45      (((k1_relat_1 @ (k2_funct_1 @ sk_B)) = (k2_relat_1 @ sk_B))),
% 38.27/38.45      inference('demod', [status(thm)], ['65', '66', '67', '68'])).
% 38.27/38.45  thf('87', plain,
% 38.27/38.45      (![X27 : $i, X28 : $i]:
% 38.27/38.45         ((r1_tarski @ (k10_relat_1 @ X27 @ X28) @ (k1_relat_1 @ X27))
% 38.27/38.45          | ~ (v1_relat_1 @ X27))),
% 38.27/38.45      inference('cnf', [status(esa)], [t167_relat_1])).
% 38.27/38.45  thf('88', plain,
% 38.27/38.45      (![X0 : $i]:
% 38.27/38.45         ((r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ 
% 38.27/38.45           (k2_relat_1 @ sk_B))
% 38.27/38.45          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 38.27/38.45      inference('sup+', [status(thm)], ['86', '87'])).
% 38.27/38.45  thf('89', plain,
% 38.27/38.45      (![X0 : $i]:
% 38.27/38.45         (~ (v1_relat_1 @ sk_B)
% 38.27/38.45          | ~ (v1_funct_1 @ sk_B)
% 38.27/38.45          | (r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ 
% 38.27/38.45             (k2_relat_1 @ sk_B)))),
% 38.27/38.45      inference('sup-', [status(thm)], ['85', '88'])).
% 38.27/38.45  thf('90', plain, ((v1_relat_1 @ sk_B)),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('91', plain, ((v1_funct_1 @ sk_B)),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('92', plain,
% 38.27/38.45      (![X0 : $i]:
% 38.27/38.45         (r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ 
% 38.27/38.45          (k2_relat_1 @ sk_B))),
% 38.27/38.45      inference('demod', [status(thm)], ['89', '90', '91'])).
% 38.27/38.45  thf('93', plain,
% 38.27/38.45      (![X35 : $i, X36 : $i]:
% 38.27/38.45         (~ (r1_tarski @ X35 @ (k2_relat_1 @ X36))
% 38.27/38.45          | ((k9_relat_1 @ X36 @ (k10_relat_1 @ X36 @ X35)) = (X35))
% 38.27/38.45          | ~ (v1_funct_1 @ X36)
% 38.27/38.45          | ~ (v1_relat_1 @ X36))),
% 38.27/38.45      inference('cnf', [status(esa)], [t147_funct_1])).
% 38.27/38.45  thf('94', plain,
% 38.27/38.45      (![X0 : $i]:
% 38.27/38.45         (~ (v1_relat_1 @ sk_B)
% 38.27/38.45          | ~ (v1_funct_1 @ sk_B)
% 38.27/38.45          | ((k9_relat_1 @ sk_B @ 
% 38.27/38.45              (k10_relat_1 @ sk_B @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ X0)))
% 38.27/38.45              = (k10_relat_1 @ (k2_funct_1 @ sk_B) @ X0)))),
% 38.27/38.45      inference('sup-', [status(thm)], ['92', '93'])).
% 38.27/38.45  thf('95', plain, ((v1_relat_1 @ sk_B)),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('96', plain, ((v1_funct_1 @ sk_B)),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('97', plain,
% 38.27/38.45      (![X0 : $i]:
% 38.27/38.45         ((k9_relat_1 @ sk_B @ 
% 38.27/38.45           (k10_relat_1 @ sk_B @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ X0)))
% 38.27/38.45           = (k10_relat_1 @ (k2_funct_1 @ sk_B) @ X0))),
% 38.27/38.45      inference('demod', [status(thm)], ['94', '95', '96'])).
% 38.27/38.45  thf('98', plain,
% 38.27/38.45      (![X0 : $i]:
% 38.27/38.45         (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ X0)))
% 38.27/38.45            = (k10_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 38.27/38.45          | ~ (v1_relat_1 @ sk_B)
% 38.27/38.45          | ~ (v1_funct_1 @ sk_B)
% 38.27/38.45          | ~ (v2_funct_1 @ sk_B))),
% 38.27/38.45      inference('sup+', [status(thm)], ['84', '97'])).
% 38.27/38.45  thf('99', plain,
% 38.27/38.45      (![X0 : $i]:
% 38.27/38.45         (~ (v2_funct_1 @ X0)
% 38.27/38.45          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 38.27/38.45          | ~ (v1_funct_1 @ X0)
% 38.27/38.45          | ~ (v1_relat_1 @ X0))),
% 38.27/38.45      inference('simplify', [status(thm)], ['18'])).
% 38.27/38.45  thf('100', plain,
% 38.27/38.45      (((k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)) = (k2_relat_1 @ sk_B))),
% 38.27/38.45      inference('demod', [status(thm)], ['47', '48', '49'])).
% 38.27/38.45  thf('101', plain,
% 38.27/38.45      (![X0 : $i, X1 : $i]:
% 38.27/38.45         ((r1_tarski @ (k9_relat_1 @ X0 @ X1) @ 
% 38.27/38.45           (k1_relat_1 @ (k2_funct_1 @ X0)))
% 38.27/38.45          | ~ (v2_funct_1 @ X0)
% 38.27/38.45          | ~ (v1_funct_1 @ X0)
% 38.27/38.45          | ~ (v1_relat_1 @ X0))),
% 38.27/38.45      inference('simplify', [status(thm)], ['55'])).
% 38.27/38.45  thf('102', plain,
% 38.27/38.45      (((r1_tarski @ (k2_relat_1 @ sk_B) @ (k1_relat_1 @ (k2_funct_1 @ sk_B)))
% 38.27/38.45        | ~ (v1_relat_1 @ sk_B)
% 38.27/38.45        | ~ (v1_funct_1 @ sk_B)
% 38.27/38.45        | ~ (v2_funct_1 @ sk_B))),
% 38.27/38.45      inference('sup+', [status(thm)], ['100', '101'])).
% 38.27/38.45  thf('103', plain, ((v1_relat_1 @ sk_B)),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('104', plain, ((v1_funct_1 @ sk_B)),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('105', plain, ((v2_funct_1 @ sk_B)),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('106', plain,
% 38.27/38.45      ((r1_tarski @ (k2_relat_1 @ sk_B) @ (k1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 38.27/38.45      inference('demod', [status(thm)], ['102', '103', '104', '105'])).
% 38.27/38.45  thf('107', plain,
% 38.27/38.45      (![X18 : $i, X19 : $i]:
% 38.27/38.45         ((r1_tarski @ (k9_relat_1 @ X18 @ X19) @ (k2_relat_1 @ X18))
% 38.27/38.45          | ~ (v1_relat_1 @ X18))),
% 38.27/38.45      inference('cnf', [status(esa)], [t144_relat_1])).
% 38.27/38.45  thf('108', plain,
% 38.27/38.45      (![X13 : $i, X14 : $i, X15 : $i]:
% 38.27/38.45         (~ (r1_tarski @ X13 @ X14)
% 38.27/38.45          | ~ (r1_tarski @ X14 @ X15)
% 38.27/38.45          | (r1_tarski @ X13 @ X15))),
% 38.27/38.45      inference('cnf', [status(esa)], [t1_xboole_1])).
% 38.27/38.45  thf('109', plain,
% 38.27/38.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 38.27/38.45         (~ (v1_relat_1 @ X0)
% 38.27/38.45          | (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ X2)
% 38.27/38.45          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X2))),
% 38.27/38.45      inference('sup-', [status(thm)], ['107', '108'])).
% 38.27/38.45  thf('110', plain,
% 38.27/38.45      (![X0 : $i]:
% 38.27/38.45         ((r1_tarski @ (k9_relat_1 @ sk_B @ X0) @ 
% 38.27/38.45           (k1_relat_1 @ (k2_funct_1 @ sk_B)))
% 38.27/38.45          | ~ (v1_relat_1 @ sk_B))),
% 38.27/38.45      inference('sup-', [status(thm)], ['106', '109'])).
% 38.27/38.45  thf('111', plain, ((v1_relat_1 @ sk_B)),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('112', plain,
% 38.27/38.45      (![X0 : $i]:
% 38.27/38.45         (r1_tarski @ (k9_relat_1 @ sk_B @ X0) @ 
% 38.27/38.45          (k1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 38.27/38.45      inference('demod', [status(thm)], ['110', '111'])).
% 38.27/38.45  thf('113', plain,
% 38.27/38.45      (![X13 : $i, X14 : $i, X15 : $i]:
% 38.27/38.45         (~ (r1_tarski @ X13 @ X14)
% 38.27/38.45          | ~ (r1_tarski @ X14 @ X15)
% 38.27/38.45          | (r1_tarski @ X13 @ X15))),
% 38.27/38.45      inference('cnf', [status(esa)], [t1_xboole_1])).
% 38.27/38.45  thf('114', plain,
% 38.27/38.45      (![X0 : $i, X1 : $i]:
% 38.27/38.45         ((r1_tarski @ (k9_relat_1 @ sk_B @ X0) @ X1)
% 38.27/38.45          | ~ (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_B)) @ X1))),
% 38.27/38.45      inference('sup-', [status(thm)], ['112', '113'])).
% 38.27/38.45  thf('115', plain,
% 38.27/38.45      (![X0 : $i]:
% 38.27/38.45         (~ (v1_relat_1 @ sk_B)
% 38.27/38.45          | ~ (v1_funct_1 @ sk_B)
% 38.27/38.45          | ~ (v2_funct_1 @ sk_B)
% 38.27/38.45          | (r1_tarski @ (k9_relat_1 @ sk_B @ X0) @ (k2_relat_1 @ sk_B)))),
% 38.27/38.45      inference('sup-', [status(thm)], ['99', '114'])).
% 38.27/38.45  thf('116', plain, ((v1_relat_1 @ sk_B)),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('117', plain, ((v1_funct_1 @ sk_B)),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('118', plain, ((v2_funct_1 @ sk_B)),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('119', plain,
% 38.27/38.45      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ sk_B @ X0) @ (k2_relat_1 @ sk_B))),
% 38.27/38.45      inference('demod', [status(thm)], ['115', '116', '117', '118'])).
% 38.27/38.45  thf('120', plain,
% 38.27/38.45      (![X35 : $i, X36 : $i]:
% 38.27/38.45         (~ (r1_tarski @ X35 @ (k2_relat_1 @ X36))
% 38.27/38.45          | ((k9_relat_1 @ X36 @ (k10_relat_1 @ X36 @ X35)) = (X35))
% 38.27/38.45          | ~ (v1_funct_1 @ X36)
% 38.27/38.45          | ~ (v1_relat_1 @ X36))),
% 38.27/38.45      inference('cnf', [status(esa)], [t147_funct_1])).
% 38.27/38.45  thf('121', plain,
% 38.27/38.45      (![X0 : $i]:
% 38.27/38.45         (~ (v1_relat_1 @ sk_B)
% 38.27/38.45          | ~ (v1_funct_1 @ sk_B)
% 38.27/38.45          | ((k9_relat_1 @ sk_B @ 
% 38.27/38.45              (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ X0)))
% 38.27/38.45              = (k9_relat_1 @ sk_B @ X0)))),
% 38.27/38.45      inference('sup-', [status(thm)], ['119', '120'])).
% 38.27/38.45  thf('122', plain, ((v1_relat_1 @ sk_B)),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('123', plain, ((v1_funct_1 @ sk_B)),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('124', plain,
% 38.27/38.45      (![X0 : $i]:
% 38.27/38.45         ((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ X0)))
% 38.27/38.45           = (k9_relat_1 @ sk_B @ X0))),
% 38.27/38.45      inference('demod', [status(thm)], ['121', '122', '123'])).
% 38.27/38.45  thf('125', plain, ((v1_relat_1 @ sk_B)),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('126', plain, ((v1_funct_1 @ sk_B)),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('127', plain, ((v2_funct_1 @ sk_B)),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('128', plain,
% 38.27/38.45      (![X0 : $i]:
% 38.27/38.45         ((k9_relat_1 @ sk_B @ X0) = (k10_relat_1 @ (k2_funct_1 @ sk_B) @ X0))),
% 38.27/38.45      inference('demod', [status(thm)], ['98', '124', '125', '126', '127'])).
% 38.27/38.45  thf('129', plain,
% 38.27/38.45      (![X0 : $i]:
% 38.27/38.45         (~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_B))
% 38.27/38.45          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 38.27/38.45          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 38.27/38.45          | ((k9_relat_1 @ (k2_funct_1 @ sk_B) @ (k9_relat_1 @ sk_B @ X0))
% 38.27/38.45              = (X0)))),
% 38.27/38.45      inference('demod', [status(thm)], ['83', '128'])).
% 38.27/38.45  thf('130', plain,
% 38.27/38.45      (![X0 : $i]:
% 38.27/38.45         (~ (v1_relat_1 @ sk_B)
% 38.27/38.45          | ~ (v1_funct_1 @ sk_B)
% 38.27/38.45          | ((k9_relat_1 @ (k2_funct_1 @ sk_B) @ (k9_relat_1 @ sk_B @ X0))
% 38.27/38.45              = (X0))
% 38.27/38.45          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 38.27/38.45          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_B)))),
% 38.27/38.45      inference('sup-', [status(thm)], ['3', '129'])).
% 38.27/38.45  thf('131', plain, ((v1_relat_1 @ sk_B)),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('132', plain, ((v1_funct_1 @ sk_B)),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('133', plain,
% 38.27/38.45      (![X0 : $i]:
% 38.27/38.45         (((k9_relat_1 @ (k2_funct_1 @ sk_B) @ (k9_relat_1 @ sk_B @ X0)) = (X0))
% 38.27/38.45          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 38.27/38.45          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_B)))),
% 38.27/38.45      inference('demod', [status(thm)], ['130', '131', '132'])).
% 38.27/38.45  thf('134', plain,
% 38.27/38.45      (![X0 : $i]:
% 38.27/38.45         (~ (v1_relat_1 @ sk_B)
% 38.27/38.45          | ~ (v1_funct_1 @ sk_B)
% 38.27/38.45          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_B))
% 38.27/38.45          | ((k9_relat_1 @ (k2_funct_1 @ sk_B) @ (k9_relat_1 @ sk_B @ X0))
% 38.27/38.45              = (X0)))),
% 38.27/38.45      inference('sup-', [status(thm)], ['2', '133'])).
% 38.27/38.45  thf('135', plain, ((v1_relat_1 @ sk_B)),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('136', plain, ((v1_funct_1 @ sk_B)),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('137', plain,
% 38.27/38.45      (![X0 : $i]:
% 38.27/38.45         (~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_B))
% 38.27/38.45          | ((k9_relat_1 @ (k2_funct_1 @ sk_B) @ (k9_relat_1 @ sk_B @ X0))
% 38.27/38.45              = (X0)))),
% 38.27/38.45      inference('demod', [status(thm)], ['134', '135', '136'])).
% 38.27/38.45  thf('138', plain,
% 38.27/38.45      (((k9_relat_1 @ (k2_funct_1 @ sk_B) @ (k9_relat_1 @ sk_B @ sk_A))
% 38.27/38.45         = (sk_A))),
% 38.27/38.45      inference('sup-', [status(thm)], ['1', '137'])).
% 38.27/38.45  thf('139', plain,
% 38.27/38.45      ((((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) = (sk_A))
% 38.27/38.45        | ~ (v1_relat_1 @ sk_B)
% 38.27/38.45        | ~ (v1_funct_1 @ sk_B)
% 38.27/38.45        | ~ (v2_funct_1 @ sk_B))),
% 38.27/38.45      inference('sup+', [status(thm)], ['0', '138'])).
% 38.27/38.45  thf('140', plain, ((v1_relat_1 @ sk_B)),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('141', plain, ((v1_funct_1 @ sk_B)),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('142', plain, ((v2_funct_1 @ sk_B)),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('143', plain,
% 38.27/38.45      (((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 38.27/38.45      inference('demod', [status(thm)], ['139', '140', '141', '142'])).
% 38.27/38.45  thf('144', plain,
% 38.27/38.45      (((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) != (sk_A))),
% 38.27/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.27/38.45  thf('145', plain, ($false),
% 38.27/38.45      inference('simplify_reflect-', [status(thm)], ['143', '144'])).
% 38.27/38.45  
% 38.27/38.45  % SZS output end Refutation
% 38.27/38.45  
% 38.27/38.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
