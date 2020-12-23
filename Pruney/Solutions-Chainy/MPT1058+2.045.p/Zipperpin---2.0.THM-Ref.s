%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.94m8iFYbBG

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:43 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 227 expanded)
%              Number of leaves         :   25 (  74 expanded)
%              Depth                    :   20
%              Number of atoms          : 1034 (2640 expanded)
%              Number of equality atoms :   33 ( 114 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('0',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X25 @ ( k10_relat_1 @ X25 @ X26 ) ) @ X26 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf(t175_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
         => ( ( k10_relat_1 @ A @ C )
            = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i,C: $i] :
            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
           => ( ( k10_relat_1 @ A @ C )
              = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t175_funct_2])).

thf('1',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t162_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X10 @ X9 ) @ X8 )
        = ( k9_relat_1 @ X10 @ X8 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t162_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X0 @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) )
        = ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc8_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X11: $i] :
      ( ( ( k10_relat_1 @ X11 @ ( k2_relat_1 @ X11 ) )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t170_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ B @ ( k2_relat_1 @ B ) ) ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X12 @ X13 ) @ ( k10_relat_1 @ X12 @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t170_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('10',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X21 @ ( k1_relat_1 @ X22 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X22 @ X21 ) )
        = X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) ) )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) ) )
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t103_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k7_relat_1 @ C @ A ) ) ) ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X7 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X7 @ X6 ) @ X5 )
        = ( k7_relat_1 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t103_relat_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) )
        = ( k7_relat_1 @ X0 @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t89_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ) )).

thf('16',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X19 @ X20 ) ) @ ( k1_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t89_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['12','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf(t163_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('24',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X27 @ ( k1_relat_1 @ X28 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X28 @ X27 ) @ X29 )
      | ( r1_tarski @ X27 @ ( k10_relat_1 @ X28 @ X29 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ X0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ( r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,
    ( ~ ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) @ ( k10_relat_1 @ sk_A @ sk_C ) )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C )
      = ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('42',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X17 @ X18 ) @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t179_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('43',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( r1_tarski @ ( k10_relat_1 @ X15 @ X16 ) @ ( k10_relat_1 @ X14 @ X16 ) )
      | ~ ( r1_tarski @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t179_relat_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k10_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k10_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k10_relat_1 @ X0 @ X2 ) ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) )
        = ( k7_relat_1 @ X0 @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('50',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('51',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('52',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X21 @ ( k1_relat_1 @ X22 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X22 @ X21 ) )
        = X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('53',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
      = ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
      = ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
    = ( k10_relat_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
      = ( k10_relat_1 @ sk_A @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['49','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
    = ( k10_relat_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X21 @ ( k1_relat_1 @ X22 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X22 @ X21 ) )
        = X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_A @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_A @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['48','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_A @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_A @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) @ sk_C ) ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['47','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_A @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) @ sk_C ) ) )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('69',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
    = ( k10_relat_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('70',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X19 @ X20 ) ) @ ( k1_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t89_relat_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_A @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ X0 ) ) @ ( k10_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_A @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ X0 ) ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_A @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ X0 ) ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) @ sk_C ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['67','74'])).

thf('76',plain,
    ( ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C )
    = ( k10_relat_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['41','75'])).

thf('77',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['76','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.94m8iFYbBG
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:39:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.60/0.82  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.60/0.82  % Solved by: fo/fo7.sh
% 0.60/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.82  % done 287 iterations in 0.363s
% 0.60/0.82  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.60/0.82  % SZS output start Refutation
% 0.60/0.82  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.60/0.82  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.60/0.82  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.60/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.82  thf(sk_C_type, type, sk_C: $i).
% 0.60/0.82  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.82  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.60/0.82  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.60/0.82  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.60/0.82  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.60/0.82  thf(t145_funct_1, axiom,
% 0.60/0.82    (![A:$i,B:$i]:
% 0.60/0.82     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.60/0.82       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 0.60/0.82  thf('0', plain,
% 0.60/0.82      (![X25 : $i, X26 : $i]:
% 0.60/0.82         ((r1_tarski @ (k9_relat_1 @ X25 @ (k10_relat_1 @ X25 @ X26)) @ X26)
% 0.60/0.82          | ~ (v1_funct_1 @ X25)
% 0.60/0.82          | ~ (v1_relat_1 @ X25))),
% 0.60/0.82      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.60/0.82  thf(t175_funct_2, conjecture,
% 0.60/0.82    (![A:$i]:
% 0.60/0.82     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.60/0.82       ( ![B:$i,C:$i]:
% 0.60/0.82         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.60/0.82           ( ( k10_relat_1 @ A @ C ) =
% 0.60/0.82             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.60/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.82    (~( ![A:$i]:
% 0.60/0.82        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.60/0.82          ( ![B:$i,C:$i]:
% 0.60/0.82            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.60/0.82              ( ( k10_relat_1 @ A @ C ) =
% 0.60/0.82                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.60/0.82    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.60/0.82  thf('1', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf(t162_relat_1, axiom,
% 0.60/0.82    (![A:$i]:
% 0.60/0.82     ( ( v1_relat_1 @ A ) =>
% 0.60/0.82       ( ![B:$i,C:$i]:
% 0.60/0.82         ( ( r1_tarski @ B @ C ) =>
% 0.60/0.82           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 0.60/0.82             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 0.60/0.82  thf('2', plain,
% 0.60/0.82      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.60/0.82         (~ (r1_tarski @ X8 @ X9)
% 0.60/0.82          | ((k9_relat_1 @ (k7_relat_1 @ X10 @ X9) @ X8)
% 0.60/0.82              = (k9_relat_1 @ X10 @ X8))
% 0.60/0.82          | ~ (v1_relat_1 @ X10))),
% 0.60/0.82      inference('cnf', [status(esa)], [t162_relat_1])).
% 0.60/0.82  thf('3', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         (~ (v1_relat_1 @ X0)
% 0.60/0.82          | ((k9_relat_1 @ (k7_relat_1 @ X0 @ sk_B) @ 
% 0.60/0.82              (k10_relat_1 @ sk_A @ sk_C))
% 0.60/0.82              = (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_A @ sk_C))))),
% 0.60/0.82      inference('sup-', [status(thm)], ['1', '2'])).
% 0.60/0.82  thf(fc8_funct_1, axiom,
% 0.60/0.82    (![A:$i,B:$i]:
% 0.60/0.82     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.60/0.82       ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) & 
% 0.60/0.82         ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 0.60/0.82  thf('4', plain,
% 0.60/0.82      (![X23 : $i, X24 : $i]:
% 0.60/0.82         (~ (v1_funct_1 @ X23)
% 0.60/0.82          | ~ (v1_relat_1 @ X23)
% 0.60/0.82          | (v1_funct_1 @ (k7_relat_1 @ X23 @ X24)))),
% 0.60/0.82      inference('cnf', [status(esa)], [fc8_funct_1])).
% 0.60/0.82  thf(dt_k7_relat_1, axiom,
% 0.60/0.82    (![A:$i,B:$i]:
% 0.60/0.82     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.60/0.82  thf('5', plain,
% 0.60/0.82      (![X3 : $i, X4 : $i]:
% 0.60/0.82         (~ (v1_relat_1 @ X3) | (v1_relat_1 @ (k7_relat_1 @ X3 @ X4)))),
% 0.60/0.82      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.60/0.82  thf(t169_relat_1, axiom,
% 0.60/0.82    (![A:$i]:
% 0.60/0.82     ( ( v1_relat_1 @ A ) =>
% 0.60/0.82       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.60/0.82  thf('6', plain,
% 0.60/0.82      (![X11 : $i]:
% 0.60/0.82         (((k10_relat_1 @ X11 @ (k2_relat_1 @ X11)) = (k1_relat_1 @ X11))
% 0.60/0.82          | ~ (v1_relat_1 @ X11))),
% 0.60/0.82      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.60/0.82  thf(t170_relat_1, axiom,
% 0.60/0.82    (![A:$i,B:$i]:
% 0.60/0.82     ( ( v1_relat_1 @ B ) =>
% 0.60/0.82       ( r1_tarski @
% 0.60/0.82         ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ B @ ( k2_relat_1 @ B ) ) ) ))).
% 0.60/0.82  thf('7', plain,
% 0.60/0.82      (![X12 : $i, X13 : $i]:
% 0.60/0.82         ((r1_tarski @ (k10_relat_1 @ X12 @ X13) @ 
% 0.60/0.82           (k10_relat_1 @ X12 @ (k2_relat_1 @ X12)))
% 0.60/0.82          | ~ (v1_relat_1 @ X12))),
% 0.60/0.82      inference('cnf', [status(esa)], [t170_relat_1])).
% 0.60/0.82  thf('8', plain,
% 0.60/0.82      (![X0 : $i, X1 : $i]:
% 0.60/0.82         ((r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.60/0.82          | ~ (v1_relat_1 @ X0)
% 0.60/0.82          | ~ (v1_relat_1 @ X0))),
% 0.60/0.82      inference('sup+', [status(thm)], ['6', '7'])).
% 0.60/0.82  thf('9', plain,
% 0.60/0.82      (![X0 : $i, X1 : $i]:
% 0.60/0.82         (~ (v1_relat_1 @ X0)
% 0.60/0.82          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0)))),
% 0.60/0.82      inference('simplify', [status(thm)], ['8'])).
% 0.60/0.82  thf(t91_relat_1, axiom,
% 0.60/0.82    (![A:$i,B:$i]:
% 0.60/0.82     ( ( v1_relat_1 @ B ) =>
% 0.60/0.82       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.60/0.82         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.60/0.82  thf('10', plain,
% 0.60/0.82      (![X21 : $i, X22 : $i]:
% 0.60/0.82         (~ (r1_tarski @ X21 @ (k1_relat_1 @ X22))
% 0.60/0.82          | ((k1_relat_1 @ (k7_relat_1 @ X22 @ X21)) = (X21))
% 0.60/0.82          | ~ (v1_relat_1 @ X22))),
% 0.60/0.82      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.60/0.82  thf('11', plain,
% 0.60/0.82      (![X0 : $i, X1 : $i]:
% 0.60/0.82         (~ (v1_relat_1 @ X0)
% 0.60/0.82          | ~ (v1_relat_1 @ X0)
% 0.60/0.82          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1)))
% 0.60/0.82              = (k10_relat_1 @ X0 @ X1)))),
% 0.60/0.82      inference('sup-', [status(thm)], ['9', '10'])).
% 0.60/0.82  thf('12', plain,
% 0.60/0.82      (![X0 : $i, X1 : $i]:
% 0.60/0.82         (((k1_relat_1 @ (k7_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1)))
% 0.60/0.82            = (k10_relat_1 @ X0 @ X1))
% 0.60/0.82          | ~ (v1_relat_1 @ X0))),
% 0.60/0.82      inference('simplify', [status(thm)], ['11'])).
% 0.60/0.82  thf('13', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf(t103_relat_1, axiom,
% 0.60/0.82    (![A:$i,B:$i,C:$i]:
% 0.60/0.82     ( ( v1_relat_1 @ C ) =>
% 0.60/0.82       ( ( r1_tarski @ A @ B ) =>
% 0.60/0.82         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k7_relat_1 @ C @ A ) ) ) ))).
% 0.60/0.82  thf('14', plain,
% 0.60/0.82      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.60/0.82         (~ (r1_tarski @ X5 @ X6)
% 0.60/0.82          | ~ (v1_relat_1 @ X7)
% 0.60/0.82          | ((k7_relat_1 @ (k7_relat_1 @ X7 @ X6) @ X5)
% 0.60/0.82              = (k7_relat_1 @ X7 @ X5)))),
% 0.60/0.82      inference('cnf', [status(esa)], [t103_relat_1])).
% 0.60/0.82  thf('15', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         (((k7_relat_1 @ (k7_relat_1 @ X0 @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C))
% 0.60/0.82            = (k7_relat_1 @ X0 @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.60/0.82          | ~ (v1_relat_1 @ X0))),
% 0.60/0.82      inference('sup-', [status(thm)], ['13', '14'])).
% 0.60/0.82  thf(t89_relat_1, axiom,
% 0.60/0.82    (![A:$i,B:$i]:
% 0.60/0.82     ( ( v1_relat_1 @ B ) =>
% 0.60/0.82       ( r1_tarski @
% 0.60/0.82         ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ))).
% 0.60/0.82  thf('16', plain,
% 0.60/0.82      (![X19 : $i, X20 : $i]:
% 0.60/0.82         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X19 @ X20)) @ 
% 0.60/0.82           (k1_relat_1 @ X19))
% 0.60/0.82          | ~ (v1_relat_1 @ X19))),
% 0.60/0.82      inference('cnf', [status(esa)], [t89_relat_1])).
% 0.60/0.82  thf('17', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         ((r1_tarski @ 
% 0.60/0.82           (k1_relat_1 @ (k7_relat_1 @ X0 @ (k10_relat_1 @ sk_A @ sk_C))) @ 
% 0.60/0.82           (k1_relat_1 @ (k7_relat_1 @ X0 @ sk_B)))
% 0.60/0.82          | ~ (v1_relat_1 @ X0)
% 0.60/0.82          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ sk_B)))),
% 0.60/0.82      inference('sup+', [status(thm)], ['15', '16'])).
% 0.60/0.82  thf('18', plain,
% 0.60/0.82      (![X3 : $i, X4 : $i]:
% 0.60/0.82         (~ (v1_relat_1 @ X3) | (v1_relat_1 @ (k7_relat_1 @ X3 @ X4)))),
% 0.60/0.82      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.60/0.82  thf('19', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         (~ (v1_relat_1 @ X0)
% 0.60/0.82          | (r1_tarski @ 
% 0.60/0.82             (k1_relat_1 @ (k7_relat_1 @ X0 @ (k10_relat_1 @ sk_A @ sk_C))) @ 
% 0.60/0.82             (k1_relat_1 @ (k7_relat_1 @ X0 @ sk_B))))),
% 0.60/0.82      inference('clc', [status(thm)], ['17', '18'])).
% 0.60/0.82  thf('20', plain,
% 0.60/0.82      (((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ 
% 0.60/0.82         (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_B)))
% 0.60/0.82        | ~ (v1_relat_1 @ sk_A)
% 0.60/0.82        | ~ (v1_relat_1 @ sk_A))),
% 0.60/0.82      inference('sup+', [status(thm)], ['12', '19'])).
% 0.60/0.82  thf('21', plain, ((v1_relat_1 @ sk_A)),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf('22', plain, ((v1_relat_1 @ sk_A)),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf('23', plain,
% 0.60/0.82      ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ 
% 0.60/0.82        (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_B)))),
% 0.60/0.82      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.60/0.82  thf(t163_funct_1, axiom,
% 0.60/0.82    (![A:$i,B:$i,C:$i]:
% 0.60/0.82     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.60/0.82       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.60/0.82           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.60/0.82         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.60/0.82  thf('24', plain,
% 0.60/0.82      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.60/0.82         (~ (r1_tarski @ X27 @ (k1_relat_1 @ X28))
% 0.60/0.82          | ~ (r1_tarski @ (k9_relat_1 @ X28 @ X27) @ X29)
% 0.60/0.82          | (r1_tarski @ X27 @ (k10_relat_1 @ X28 @ X29))
% 0.60/0.82          | ~ (v1_funct_1 @ X28)
% 0.60/0.82          | ~ (v1_relat_1 @ X28))),
% 0.60/0.82      inference('cnf', [status(esa)], [t163_funct_1])).
% 0.60/0.82  thf('25', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         (~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_B))
% 0.60/0.82          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_B))
% 0.60/0.82          | (r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ 
% 0.60/0.82             (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ X0))
% 0.60/0.82          | ~ (r1_tarski @ 
% 0.60/0.82               (k9_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ 
% 0.60/0.82                (k10_relat_1 @ sk_A @ sk_C)) @ 
% 0.60/0.82               X0))),
% 0.60/0.82      inference('sup-', [status(thm)], ['23', '24'])).
% 0.60/0.82  thf('26', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         (~ (v1_relat_1 @ sk_A)
% 0.60/0.82          | ~ (r1_tarski @ 
% 0.60/0.82               (k9_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ 
% 0.60/0.82                (k10_relat_1 @ sk_A @ sk_C)) @ 
% 0.60/0.82               X0)
% 0.60/0.82          | (r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ 
% 0.60/0.82             (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ X0))
% 0.60/0.82          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_B)))),
% 0.60/0.82      inference('sup-', [status(thm)], ['5', '25'])).
% 0.60/0.82  thf('27', plain, ((v1_relat_1 @ sk_A)),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf('28', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         (~ (r1_tarski @ 
% 0.60/0.82             (k9_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ 
% 0.60/0.82              (k10_relat_1 @ sk_A @ sk_C)) @ 
% 0.60/0.82             X0)
% 0.60/0.82          | (r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ 
% 0.60/0.82             (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ X0))
% 0.60/0.82          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_B)))),
% 0.60/0.82      inference('demod', [status(thm)], ['26', '27'])).
% 0.60/0.82  thf('29', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         (~ (v1_relat_1 @ sk_A)
% 0.60/0.82          | ~ (v1_funct_1 @ sk_A)
% 0.60/0.82          | (r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ 
% 0.60/0.82             (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ X0))
% 0.60/0.82          | ~ (r1_tarski @ 
% 0.60/0.82               (k9_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ 
% 0.60/0.82                (k10_relat_1 @ sk_A @ sk_C)) @ 
% 0.60/0.82               X0))),
% 0.60/0.82      inference('sup-', [status(thm)], ['4', '28'])).
% 0.60/0.82  thf('30', plain, ((v1_relat_1 @ sk_A)),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf('31', plain, ((v1_funct_1 @ sk_A)),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf('32', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ 
% 0.60/0.82           (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ X0))
% 0.60/0.82          | ~ (r1_tarski @ 
% 0.60/0.82               (k9_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ 
% 0.60/0.82                (k10_relat_1 @ sk_A @ sk_C)) @ 
% 0.60/0.82               X0))),
% 0.60/0.82      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.60/0.82  thf('33', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         (~ (r1_tarski @ (k9_relat_1 @ sk_A @ (k10_relat_1 @ sk_A @ sk_C)) @ X0)
% 0.60/0.82          | ~ (v1_relat_1 @ sk_A)
% 0.60/0.82          | (r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ 
% 0.60/0.82             (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ X0)))),
% 0.60/0.82      inference('sup-', [status(thm)], ['3', '32'])).
% 0.60/0.82  thf('34', plain, ((v1_relat_1 @ sk_A)),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf('35', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         (~ (r1_tarski @ (k9_relat_1 @ sk_A @ (k10_relat_1 @ sk_A @ sk_C)) @ X0)
% 0.60/0.82          | (r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ 
% 0.60/0.82             (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ X0)))),
% 0.60/0.82      inference('demod', [status(thm)], ['33', '34'])).
% 0.60/0.82  thf('36', plain,
% 0.60/0.82      ((~ (v1_relat_1 @ sk_A)
% 0.60/0.82        | ~ (v1_funct_1 @ sk_A)
% 0.60/0.82        | (r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ 
% 0.60/0.82           (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C)))),
% 0.60/0.82      inference('sup-', [status(thm)], ['0', '35'])).
% 0.60/0.82  thf('37', plain, ((v1_relat_1 @ sk_A)),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf('38', plain, ((v1_funct_1 @ sk_A)),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf('39', plain,
% 0.60/0.82      ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ 
% 0.60/0.82        (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.60/0.82      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.60/0.82  thf(d10_xboole_0, axiom,
% 0.60/0.82    (![A:$i,B:$i]:
% 0.60/0.82     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.60/0.82  thf('40', plain,
% 0.60/0.82      (![X0 : $i, X2 : $i]:
% 0.60/0.82         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.60/0.82      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.60/0.82  thf('41', plain,
% 0.60/0.82      ((~ (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C) @ 
% 0.60/0.82           (k10_relat_1 @ sk_A @ sk_C))
% 0.60/0.82        | ((k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C)
% 0.60/0.82            = (k10_relat_1 @ sk_A @ sk_C)))),
% 0.60/0.82      inference('sup-', [status(thm)], ['39', '40'])).
% 0.60/0.82  thf(t88_relat_1, axiom,
% 0.60/0.82    (![A:$i,B:$i]:
% 0.60/0.82     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.60/0.82  thf('42', plain,
% 0.60/0.82      (![X17 : $i, X18 : $i]:
% 0.60/0.82         ((r1_tarski @ (k7_relat_1 @ X17 @ X18) @ X17) | ~ (v1_relat_1 @ X17))),
% 0.60/0.82      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.60/0.82  thf(t179_relat_1, axiom,
% 0.60/0.82    (![A:$i,B:$i]:
% 0.60/0.82     ( ( v1_relat_1 @ B ) =>
% 0.60/0.82       ( ![C:$i]:
% 0.60/0.82         ( ( v1_relat_1 @ C ) =>
% 0.60/0.82           ( ( r1_tarski @ B @ C ) =>
% 0.60/0.82             ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.60/0.82  thf('43', plain,
% 0.60/0.82      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.60/0.82         (~ (v1_relat_1 @ X14)
% 0.60/0.82          | (r1_tarski @ (k10_relat_1 @ X15 @ X16) @ (k10_relat_1 @ X14 @ X16))
% 0.60/0.82          | ~ (r1_tarski @ X15 @ X14)
% 0.60/0.82          | ~ (v1_relat_1 @ X15))),
% 0.60/0.82      inference('cnf', [status(esa)], [t179_relat_1])).
% 0.60/0.82  thf('44', plain,
% 0.60/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.82         (~ (v1_relat_1 @ X0)
% 0.60/0.82          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.60/0.82          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X2) @ 
% 0.60/0.82             (k10_relat_1 @ X0 @ X2))
% 0.60/0.82          | ~ (v1_relat_1 @ X0))),
% 0.60/0.82      inference('sup-', [status(thm)], ['42', '43'])).
% 0.60/0.82  thf('45', plain,
% 0.60/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.82         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X2) @ 
% 0.60/0.82           (k10_relat_1 @ X0 @ X2))
% 0.60/0.82          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.60/0.82          | ~ (v1_relat_1 @ X0))),
% 0.60/0.82      inference('simplify', [status(thm)], ['44'])).
% 0.60/0.82  thf('46', plain,
% 0.60/0.82      (![X3 : $i, X4 : $i]:
% 0.60/0.82         (~ (v1_relat_1 @ X3) | (v1_relat_1 @ (k7_relat_1 @ X3 @ X4)))),
% 0.60/0.82      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.60/0.82  thf('47', plain,
% 0.60/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.82         (~ (v1_relat_1 @ X0)
% 0.60/0.82          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X2) @ 
% 0.60/0.82             (k10_relat_1 @ X0 @ X2)))),
% 0.60/0.82      inference('clc', [status(thm)], ['45', '46'])).
% 0.60/0.82  thf('48', plain,
% 0.60/0.82      (![X3 : $i, X4 : $i]:
% 0.60/0.82         (~ (v1_relat_1 @ X3) | (v1_relat_1 @ (k7_relat_1 @ X3 @ X4)))),
% 0.60/0.82      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.60/0.82  thf('49', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         (((k7_relat_1 @ (k7_relat_1 @ X0 @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C))
% 0.60/0.82            = (k7_relat_1 @ X0 @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.60/0.82          | ~ (v1_relat_1 @ X0))),
% 0.60/0.82      inference('sup-', [status(thm)], ['13', '14'])).
% 0.60/0.82  thf('50', plain,
% 0.60/0.82      (![X3 : $i, X4 : $i]:
% 0.60/0.82         (~ (v1_relat_1 @ X3) | (v1_relat_1 @ (k7_relat_1 @ X3 @ X4)))),
% 0.60/0.82      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.60/0.82  thf('51', plain,
% 0.60/0.82      ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ 
% 0.60/0.82        (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_B)))),
% 0.60/0.82      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.60/0.82  thf('52', plain,
% 0.60/0.82      (![X21 : $i, X22 : $i]:
% 0.60/0.82         (~ (r1_tarski @ X21 @ (k1_relat_1 @ X22))
% 0.60/0.82          | ((k1_relat_1 @ (k7_relat_1 @ X22 @ X21)) = (X21))
% 0.60/0.82          | ~ (v1_relat_1 @ X22))),
% 0.60/0.82      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.60/0.82  thf('53', plain,
% 0.60/0.82      ((~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_B))
% 0.60/0.82        | ((k1_relat_1 @ 
% 0.60/0.82            (k7_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ 
% 0.60/0.82             (k10_relat_1 @ sk_A @ sk_C)))
% 0.60/0.82            = (k10_relat_1 @ sk_A @ sk_C)))),
% 0.60/0.82      inference('sup-', [status(thm)], ['51', '52'])).
% 0.60/0.82  thf('54', plain,
% 0.60/0.82      ((~ (v1_relat_1 @ sk_A)
% 0.60/0.82        | ((k1_relat_1 @ 
% 0.60/0.82            (k7_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ 
% 0.60/0.82             (k10_relat_1 @ sk_A @ sk_C)))
% 0.60/0.82            = (k10_relat_1 @ sk_A @ sk_C)))),
% 0.60/0.82      inference('sup-', [status(thm)], ['50', '53'])).
% 0.60/0.82  thf('55', plain, ((v1_relat_1 @ sk_A)),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf('56', plain,
% 0.60/0.82      (((k1_relat_1 @ 
% 0.60/0.82         (k7_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.60/0.82         = (k10_relat_1 @ sk_A @ sk_C))),
% 0.60/0.82      inference('demod', [status(thm)], ['54', '55'])).
% 0.60/0.82  thf('57', plain,
% 0.60/0.82      ((((k1_relat_1 @ (k7_relat_1 @ sk_A @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.60/0.82          = (k10_relat_1 @ sk_A @ sk_C))
% 0.60/0.82        | ~ (v1_relat_1 @ sk_A))),
% 0.60/0.82      inference('sup+', [status(thm)], ['49', '56'])).
% 0.60/0.82  thf('58', plain, ((v1_relat_1 @ sk_A)),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf('59', plain,
% 0.60/0.82      (((k1_relat_1 @ (k7_relat_1 @ sk_A @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.60/0.82         = (k10_relat_1 @ sk_A @ sk_C))),
% 0.60/0.82      inference('demod', [status(thm)], ['57', '58'])).
% 0.60/0.82  thf('60', plain,
% 0.60/0.82      (![X21 : $i, X22 : $i]:
% 0.60/0.82         (~ (r1_tarski @ X21 @ (k1_relat_1 @ X22))
% 0.60/0.82          | ((k1_relat_1 @ (k7_relat_1 @ X22 @ X21)) = (X21))
% 0.60/0.82          | ~ (v1_relat_1 @ X22))),
% 0.60/0.82      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.60/0.82  thf('61', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         (~ (r1_tarski @ X0 @ (k10_relat_1 @ sk_A @ sk_C))
% 0.60/0.82          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.60/0.82          | ((k1_relat_1 @ 
% 0.60/0.82              (k7_relat_1 @ 
% 0.60/0.82               (k7_relat_1 @ sk_A @ (k10_relat_1 @ sk_A @ sk_C)) @ X0))
% 0.60/0.82              = (X0)))),
% 0.60/0.82      inference('sup-', [status(thm)], ['59', '60'])).
% 0.60/0.82  thf('62', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         (~ (v1_relat_1 @ sk_A)
% 0.60/0.82          | ((k1_relat_1 @ 
% 0.60/0.82              (k7_relat_1 @ 
% 0.60/0.82               (k7_relat_1 @ sk_A @ (k10_relat_1 @ sk_A @ sk_C)) @ X0))
% 0.60/0.82              = (X0))
% 0.60/0.82          | ~ (r1_tarski @ X0 @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.60/0.82      inference('sup-', [status(thm)], ['48', '61'])).
% 0.60/0.82  thf('63', plain, ((v1_relat_1 @ sk_A)),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf('64', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         (((k1_relat_1 @ 
% 0.60/0.82            (k7_relat_1 @ (k7_relat_1 @ sk_A @ (k10_relat_1 @ sk_A @ sk_C)) @ 
% 0.60/0.82             X0))
% 0.60/0.82            = (X0))
% 0.60/0.82          | ~ (r1_tarski @ X0 @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.60/0.82      inference('demod', [status(thm)], ['62', '63'])).
% 0.60/0.82  thf('65', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         (~ (v1_relat_1 @ sk_A)
% 0.60/0.82          | ((k1_relat_1 @ 
% 0.60/0.82              (k7_relat_1 @ 
% 0.60/0.82               (k7_relat_1 @ sk_A @ (k10_relat_1 @ sk_A @ sk_C)) @ 
% 0.60/0.82               (k10_relat_1 @ (k7_relat_1 @ sk_A @ X0) @ sk_C)))
% 0.60/0.82              = (k10_relat_1 @ (k7_relat_1 @ sk_A @ X0) @ sk_C)))),
% 0.60/0.82      inference('sup-', [status(thm)], ['47', '64'])).
% 0.60/0.82  thf('66', plain, ((v1_relat_1 @ sk_A)),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf('67', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         ((k1_relat_1 @ 
% 0.60/0.82           (k7_relat_1 @ (k7_relat_1 @ sk_A @ (k10_relat_1 @ sk_A @ sk_C)) @ 
% 0.60/0.82            (k10_relat_1 @ (k7_relat_1 @ sk_A @ X0) @ sk_C)))
% 0.60/0.82           = (k10_relat_1 @ (k7_relat_1 @ sk_A @ X0) @ sk_C))),
% 0.60/0.82      inference('demod', [status(thm)], ['65', '66'])).
% 0.60/0.82  thf('68', plain,
% 0.60/0.82      (![X3 : $i, X4 : $i]:
% 0.60/0.82         (~ (v1_relat_1 @ X3) | (v1_relat_1 @ (k7_relat_1 @ X3 @ X4)))),
% 0.60/0.82      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.60/0.82  thf('69', plain,
% 0.60/0.82      (((k1_relat_1 @ (k7_relat_1 @ sk_A @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.60/0.82         = (k10_relat_1 @ sk_A @ sk_C))),
% 0.60/0.82      inference('demod', [status(thm)], ['57', '58'])).
% 0.60/0.82  thf('70', plain,
% 0.60/0.82      (![X19 : $i, X20 : $i]:
% 0.60/0.82         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X19 @ X20)) @ 
% 0.60/0.82           (k1_relat_1 @ X19))
% 0.60/0.82          | ~ (v1_relat_1 @ X19))),
% 0.60/0.82      inference('cnf', [status(esa)], [t89_relat_1])).
% 0.60/0.82  thf('71', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         ((r1_tarski @ 
% 0.60/0.82           (k1_relat_1 @ 
% 0.60/0.82            (k7_relat_1 @ (k7_relat_1 @ sk_A @ (k10_relat_1 @ sk_A @ sk_C)) @ 
% 0.60/0.82             X0)) @ 
% 0.60/0.82           (k10_relat_1 @ sk_A @ sk_C))
% 0.60/0.82          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ (k10_relat_1 @ sk_A @ sk_C))))),
% 0.60/0.82      inference('sup+', [status(thm)], ['69', '70'])).
% 0.60/0.82  thf('72', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         (~ (v1_relat_1 @ sk_A)
% 0.60/0.82          | (r1_tarski @ 
% 0.60/0.82             (k1_relat_1 @ 
% 0.60/0.82              (k7_relat_1 @ 
% 0.60/0.82               (k7_relat_1 @ sk_A @ (k10_relat_1 @ sk_A @ sk_C)) @ X0)) @ 
% 0.60/0.82             (k10_relat_1 @ sk_A @ sk_C)))),
% 0.60/0.82      inference('sup-', [status(thm)], ['68', '71'])).
% 0.60/0.82  thf('73', plain, ((v1_relat_1 @ sk_A)),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf('74', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         (r1_tarski @ 
% 0.60/0.82          (k1_relat_1 @ 
% 0.60/0.82           (k7_relat_1 @ (k7_relat_1 @ sk_A @ (k10_relat_1 @ sk_A @ sk_C)) @ X0)) @ 
% 0.60/0.82          (k10_relat_1 @ sk_A @ sk_C))),
% 0.60/0.82      inference('demod', [status(thm)], ['72', '73'])).
% 0.60/0.82  thf('75', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_A @ X0) @ sk_C) @ 
% 0.60/0.82          (k10_relat_1 @ sk_A @ sk_C))),
% 0.60/0.82      inference('sup+', [status(thm)], ['67', '74'])).
% 0.60/0.82  thf('76', plain,
% 0.60/0.82      (((k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C)
% 0.60/0.82         = (k10_relat_1 @ sk_A @ sk_C))),
% 0.60/0.82      inference('demod', [status(thm)], ['41', '75'])).
% 0.60/0.82  thf('77', plain,
% 0.60/0.82      (((k10_relat_1 @ sk_A @ sk_C)
% 0.60/0.82         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf('78', plain, ($false),
% 0.60/0.82      inference('simplify_reflect-', [status(thm)], ['76', '77'])).
% 0.60/0.82  
% 0.60/0.82  % SZS output end Refutation
% 0.60/0.82  
% 0.60/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
