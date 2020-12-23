%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0935+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.f6zYW9FFls

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   29 (  35 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :  216 ( 302 expanded)
%              Number of equality atoms :   17 (  24 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t96_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k1_relat_1 @ ( k1_relat_1 @ ( k2_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ ( k3_mcart_1 @ D @ E @ F ) ) ) )
      = ( k2_tarski @ A @ D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( k1_relat_1 @ ( k1_relat_1 @ ( k2_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ ( k3_mcart_1 @ D @ E @ F ) ) ) )
        = ( k2_tarski @ A @ D ) ) ),
    inference('cnf.neg',[status(esa)],[t96_mcart_1])).

thf('0',plain,(
    ( k1_relat_1 @ ( k1_relat_1 @ ( k2_tarski @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_mcart_1 @ sk_D @ sk_E @ sk_F ) ) ) )
 != ( k2_tarski @ sk_A @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(t24_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( v1_relat_1 @ E )
     => ( ( E
          = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ C @ D ) ) )
       => ( ( ( k1_relat_1 @ E )
            = ( k2_tarski @ A @ C ) )
          & ( ( k2_relat_1 @ E )
            = ( k2_tarski @ B @ D ) ) ) ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X11
       != ( k2_tarski @ ( k4_tarski @ X7 @ X8 ) @ ( k4_tarski @ X9 @ X10 ) ) )
      | ( ( k1_relat_1 @ X11 )
        = ( k2_tarski @ X7 @ X9 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t24_relat_1])).

thf('4',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X7 @ X8 ) @ ( k4_tarski @ X9 @ X10 ) ) )
      | ( ( k1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X7 @ X8 ) @ ( k4_tarski @ X9 @ X10 ) ) )
        = ( k2_tarski @ X7 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(fc7_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ C @ D ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X3 @ X4 ) @ ( k4_tarski @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[fc7_relat_1])).

thf('6',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X7 @ X8 ) @ ( k4_tarski @ X9 @ X10 ) ) )
      = ( k2_tarski @ X7 @ X9 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k1_relat_1 @ ( k2_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k4_tarski @ X3 @ X4 ) ) )
      = ( k2_tarski @ ( k4_tarski @ X2 @ X1 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['2','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k1_relat_1 @ ( k2_tarski @ ( k3_mcart_1 @ X4 @ X3 @ X5 ) @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) )
      = ( k2_tarski @ ( k4_tarski @ X4 @ X3 ) @ ( k4_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','7'])).

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X7 @ X8 ) @ ( k4_tarski @ X9 @ X10 ) ) )
      = ( k2_tarski @ X7 @ X9 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('10',plain,(
    ( k2_tarski @ sk_A @ sk_D )
 != ( k2_tarski @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['0','8','9'])).

thf('11',plain,(
    $false ),
    inference(simplify,[status(thm)],['10'])).


%------------------------------------------------------------------------------
