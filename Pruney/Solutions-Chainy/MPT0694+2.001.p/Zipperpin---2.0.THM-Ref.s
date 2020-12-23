%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0OdOBr9c9J

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:32 EST 2020

% Result     : Theorem 1.15s
% Output     : Refutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :   63 (  76 expanded)
%              Number of leaves         :   24 (  31 expanded)
%              Depth                    :   13
%              Number of atoms          :  568 ( 703 expanded)
%              Number of equality atoms :   15 (  23 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_tarski @ X9 @ X8 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t162_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf('6',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X27 @ X28 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X29 @ X28 ) @ X27 )
        = ( k9_relat_1 @ X29 @ X27 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t162_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
        = ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc8_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('8',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('10',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X33 @ X32 ) @ X34 )
        = ( k3_xboole_0 @ X32 @ ( k10_relat_1 @ X33 @ X34 ) ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('11',plain,(
    ! [X35: $i,X36: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X35 @ ( k10_relat_1 @ X35 @ X36 ) ) @ X36 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) ) @ X2 )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) ) @ X2 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t158_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ! [D: $i] :
          ( ( v1_relat_1 @ D )
         => ( ( ( r1_tarski @ C @ D )
              & ( r1_tarski @ A @ B ) )
           => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ D @ B ) ) ) ) ) )).

thf('22',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( r1_tarski @ ( k9_relat_1 @ X24 @ X25 ) @ ( k9_relat_1 @ X23 @ X26 ) )
      | ~ ( r1_tarski @ X24 @ X23 )
      | ~ ( r1_tarski @ X25 @ X26 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t158_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X2 ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ X2 ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k9_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('26',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ( r1_tarski @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) ) @ ( k3_xboole_0 @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','29'])).

thf(t149_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t149_funct_1])).

thf('31',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('33',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ) ) @ ( k3_xboole_0 @ sk_B @ ( k9_relat_1 @ sk_C @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['34','35','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0OdOBr9c9J
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:04:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.15/1.34  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.15/1.34  % Solved by: fo/fo7.sh
% 1.15/1.34  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.15/1.34  % done 872 iterations in 0.862s
% 1.15/1.34  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.15/1.34  % SZS output start Refutation
% 1.15/1.34  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.15/1.34  thf(sk_C_type, type, sk_C: $i).
% 1.15/1.34  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.15/1.34  thf(sk_B_type, type, sk_B: $i).
% 1.15/1.34  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.15/1.34  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.15/1.34  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.15/1.34  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.15/1.34  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.15/1.34  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.15/1.34  thf(sk_A_type, type, sk_A: $i).
% 1.15/1.34  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.15/1.34  thf(commutativity_k2_tarski, axiom,
% 1.15/1.34    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.15/1.34  thf('0', plain,
% 1.15/1.34      (![X8 : $i, X9 : $i]: ((k2_tarski @ X9 @ X8) = (k2_tarski @ X8 @ X9))),
% 1.15/1.34      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.15/1.34  thf(t12_setfam_1, axiom,
% 1.15/1.34    (![A:$i,B:$i]:
% 1.15/1.34     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.15/1.34  thf('1', plain,
% 1.15/1.34      (![X19 : $i, X20 : $i]:
% 1.15/1.34         ((k1_setfam_1 @ (k2_tarski @ X19 @ X20)) = (k3_xboole_0 @ X19 @ X20))),
% 1.15/1.34      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.15/1.34  thf('2', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 1.15/1.34      inference('sup+', [status(thm)], ['0', '1'])).
% 1.15/1.34  thf('3', plain,
% 1.15/1.34      (![X19 : $i, X20 : $i]:
% 1.15/1.34         ((k1_setfam_1 @ (k2_tarski @ X19 @ X20)) = (k3_xboole_0 @ X19 @ X20))),
% 1.15/1.34      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.15/1.34  thf('4', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.15/1.34      inference('sup+', [status(thm)], ['2', '3'])).
% 1.15/1.34  thf(t17_xboole_1, axiom,
% 1.15/1.34    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.15/1.34  thf('5', plain,
% 1.15/1.34      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 1.15/1.34      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.15/1.34  thf(t162_relat_1, axiom,
% 1.15/1.34    (![A:$i]:
% 1.15/1.34     ( ( v1_relat_1 @ A ) =>
% 1.15/1.34       ( ![B:$i,C:$i]:
% 1.15/1.34         ( ( r1_tarski @ B @ C ) =>
% 1.15/1.34           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 1.15/1.34             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 1.15/1.34  thf('6', plain,
% 1.15/1.34      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.15/1.34         (~ (r1_tarski @ X27 @ X28)
% 1.15/1.34          | ((k9_relat_1 @ (k7_relat_1 @ X29 @ X28) @ X27)
% 1.15/1.34              = (k9_relat_1 @ X29 @ X27))
% 1.15/1.34          | ~ (v1_relat_1 @ X29))),
% 1.15/1.34      inference('cnf', [status(esa)], [t162_relat_1])).
% 1.15/1.34  thf('7', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.34         (~ (v1_relat_1 @ X2)
% 1.15/1.34          | ((k9_relat_1 @ (k7_relat_1 @ X2 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 1.15/1.34              = (k9_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1))))),
% 1.15/1.34      inference('sup-', [status(thm)], ['5', '6'])).
% 1.15/1.34  thf(fc8_funct_1, axiom,
% 1.15/1.34    (![A:$i,B:$i]:
% 1.15/1.34     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.15/1.34       ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) & 
% 1.15/1.34         ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 1.15/1.34  thf('8', plain,
% 1.15/1.34      (![X30 : $i, X31 : $i]:
% 1.15/1.34         (~ (v1_funct_1 @ X30)
% 1.15/1.34          | ~ (v1_relat_1 @ X30)
% 1.15/1.34          | (v1_funct_1 @ (k7_relat_1 @ X30 @ X31)))),
% 1.15/1.34      inference('cnf', [status(esa)], [fc8_funct_1])).
% 1.15/1.34  thf(dt_k7_relat_1, axiom,
% 1.15/1.34    (![A:$i,B:$i]:
% 1.15/1.34     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 1.15/1.34  thf('9', plain,
% 1.15/1.34      (![X21 : $i, X22 : $i]:
% 1.15/1.34         (~ (v1_relat_1 @ X21) | (v1_relat_1 @ (k7_relat_1 @ X21 @ X22)))),
% 1.15/1.34      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.15/1.34  thf(t139_funct_1, axiom,
% 1.15/1.34    (![A:$i,B:$i,C:$i]:
% 1.15/1.34     ( ( v1_relat_1 @ C ) =>
% 1.15/1.34       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 1.15/1.34         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 1.15/1.34  thf('10', plain,
% 1.15/1.34      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.15/1.34         (((k10_relat_1 @ (k7_relat_1 @ X33 @ X32) @ X34)
% 1.15/1.34            = (k3_xboole_0 @ X32 @ (k10_relat_1 @ X33 @ X34)))
% 1.15/1.34          | ~ (v1_relat_1 @ X33))),
% 1.15/1.34      inference('cnf', [status(esa)], [t139_funct_1])).
% 1.15/1.34  thf(t145_funct_1, axiom,
% 1.15/1.34    (![A:$i,B:$i]:
% 1.15/1.34     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.15/1.34       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 1.15/1.34  thf('11', plain,
% 1.15/1.34      (![X35 : $i, X36 : $i]:
% 1.15/1.34         ((r1_tarski @ (k9_relat_1 @ X35 @ (k10_relat_1 @ X35 @ X36)) @ X36)
% 1.15/1.34          | ~ (v1_funct_1 @ X35)
% 1.15/1.34          | ~ (v1_relat_1 @ X35))),
% 1.15/1.34      inference('cnf', [status(esa)], [t145_funct_1])).
% 1.15/1.34  thf('12', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.34         ((r1_tarski @ 
% 1.15/1.34           (k9_relat_1 @ (k7_relat_1 @ X1 @ X2) @ 
% 1.15/1.34            (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 1.15/1.34           X0)
% 1.15/1.34          | ~ (v1_relat_1 @ X1)
% 1.15/1.34          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2))
% 1.15/1.34          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X2)))),
% 1.15/1.34      inference('sup+', [status(thm)], ['10', '11'])).
% 1.15/1.34  thf('13', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.34         (~ (v1_relat_1 @ X1)
% 1.15/1.34          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 1.15/1.34          | ~ (v1_relat_1 @ X1)
% 1.15/1.34          | (r1_tarski @ 
% 1.15/1.34             (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 1.15/1.34              (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2))) @ 
% 1.15/1.34             X2))),
% 1.15/1.34      inference('sup-', [status(thm)], ['9', '12'])).
% 1.15/1.34  thf('14', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.34         ((r1_tarski @ 
% 1.15/1.34           (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 1.15/1.34            (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2))) @ 
% 1.15/1.34           X2)
% 1.15/1.34          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 1.15/1.34          | ~ (v1_relat_1 @ X1))),
% 1.15/1.34      inference('simplify', [status(thm)], ['13'])).
% 1.15/1.34  thf('15', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.34         (~ (v1_relat_1 @ X1)
% 1.15/1.34          | ~ (v1_funct_1 @ X1)
% 1.15/1.34          | ~ (v1_relat_1 @ X1)
% 1.15/1.34          | (r1_tarski @ 
% 1.15/1.34             (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 1.15/1.34              (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2))) @ 
% 1.15/1.34             X2))),
% 1.15/1.34      inference('sup-', [status(thm)], ['8', '14'])).
% 1.15/1.34  thf('16', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.34         ((r1_tarski @ 
% 1.15/1.34           (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 1.15/1.34            (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2))) @ 
% 1.15/1.34           X2)
% 1.15/1.34          | ~ (v1_funct_1 @ X1)
% 1.15/1.34          | ~ (v1_relat_1 @ X1))),
% 1.15/1.34      inference('simplify', [status(thm)], ['15'])).
% 1.15/1.34  thf('17', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.34         ((r1_tarski @ 
% 1.15/1.34           (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 1.15/1.34           X0)
% 1.15/1.34          | ~ (v1_relat_1 @ X1)
% 1.15/1.34          | ~ (v1_relat_1 @ X1)
% 1.15/1.34          | ~ (v1_funct_1 @ X1))),
% 1.15/1.34      inference('sup+', [status(thm)], ['7', '16'])).
% 1.15/1.34  thf('18', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.34         (~ (v1_funct_1 @ X1)
% 1.15/1.34          | ~ (v1_relat_1 @ X1)
% 1.15/1.34          | (r1_tarski @ 
% 1.15/1.34             (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 1.15/1.34             X0))),
% 1.15/1.34      inference('simplify', [status(thm)], ['17'])).
% 1.15/1.34  thf('19', plain,
% 1.15/1.34      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 1.15/1.34      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.15/1.34  thf(d10_xboole_0, axiom,
% 1.15/1.34    (![A:$i,B:$i]:
% 1.15/1.34     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.15/1.34  thf('20', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.15/1.34      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.15/1.34  thf('21', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.15/1.34      inference('simplify', [status(thm)], ['20'])).
% 1.15/1.34  thf(t158_relat_1, axiom,
% 1.15/1.34    (![A:$i,B:$i,C:$i]:
% 1.15/1.34     ( ( v1_relat_1 @ C ) =>
% 1.15/1.34       ( ![D:$i]:
% 1.15/1.34         ( ( v1_relat_1 @ D ) =>
% 1.15/1.34           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 1.15/1.34             ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ D @ B ) ) ) ) ) ))).
% 1.15/1.34  thf('22', plain,
% 1.15/1.34      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.15/1.34         (~ (v1_relat_1 @ X23)
% 1.15/1.34          | (r1_tarski @ (k9_relat_1 @ X24 @ X25) @ (k9_relat_1 @ X23 @ X26))
% 1.15/1.34          | ~ (r1_tarski @ X24 @ X23)
% 1.15/1.34          | ~ (r1_tarski @ X25 @ X26)
% 1.15/1.34          | ~ (v1_relat_1 @ X24))),
% 1.15/1.34      inference('cnf', [status(esa)], [t158_relat_1])).
% 1.15/1.34  thf('23', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.34         (~ (v1_relat_1 @ X0)
% 1.15/1.34          | ~ (r1_tarski @ X2 @ X1)
% 1.15/1.34          | (r1_tarski @ (k9_relat_1 @ X0 @ X2) @ (k9_relat_1 @ X0 @ X1))
% 1.15/1.34          | ~ (v1_relat_1 @ X0))),
% 1.15/1.34      inference('sup-', [status(thm)], ['21', '22'])).
% 1.15/1.34  thf('24', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.34         ((r1_tarski @ (k9_relat_1 @ X0 @ X2) @ (k9_relat_1 @ X0 @ X1))
% 1.15/1.34          | ~ (r1_tarski @ X2 @ X1)
% 1.15/1.34          | ~ (v1_relat_1 @ X0))),
% 1.15/1.34      inference('simplify', [status(thm)], ['23'])).
% 1.15/1.34  thf('25', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.34         (~ (v1_relat_1 @ X2)
% 1.15/1.34          | (r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 1.15/1.34             (k9_relat_1 @ X2 @ X0)))),
% 1.15/1.34      inference('sup-', [status(thm)], ['19', '24'])).
% 1.15/1.34  thf(t19_xboole_1, axiom,
% 1.15/1.34    (![A:$i,B:$i,C:$i]:
% 1.15/1.34     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 1.15/1.34       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.15/1.34  thf('26', plain,
% 1.15/1.34      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.15/1.34         (~ (r1_tarski @ X5 @ X6)
% 1.15/1.34          | ~ (r1_tarski @ X5 @ X7)
% 1.15/1.34          | (r1_tarski @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 1.15/1.34      inference('cnf', [status(esa)], [t19_xboole_1])).
% 1.15/1.34  thf('27', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.15/1.34         (~ (v1_relat_1 @ X1)
% 1.15/1.34          | (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 1.15/1.34             (k3_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ X3))
% 1.15/1.34          | ~ (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ X3))),
% 1.15/1.34      inference('sup-', [status(thm)], ['25', '26'])).
% 1.15/1.34  thf('28', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.34         (~ (v1_relat_1 @ X1)
% 1.15/1.34          | ~ (v1_funct_1 @ X1)
% 1.15/1.34          | (r1_tarski @ 
% 1.15/1.34             (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 1.15/1.34             (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ X0))
% 1.15/1.34          | ~ (v1_relat_1 @ X1))),
% 1.15/1.34      inference('sup-', [status(thm)], ['18', '27'])).
% 1.15/1.34  thf('29', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.34         ((r1_tarski @ 
% 1.15/1.34           (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 1.15/1.34           (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ X0))
% 1.15/1.34          | ~ (v1_funct_1 @ X1)
% 1.15/1.34          | ~ (v1_relat_1 @ X1))),
% 1.15/1.34      inference('simplify', [status(thm)], ['28'])).
% 1.15/1.34  thf('30', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.34         ((r1_tarski @ 
% 1.15/1.34           (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2))) @ 
% 1.15/1.34           (k3_xboole_0 @ X2 @ (k9_relat_1 @ X1 @ X0)))
% 1.15/1.34          | ~ (v1_relat_1 @ X1)
% 1.15/1.34          | ~ (v1_funct_1 @ X1))),
% 1.15/1.34      inference('sup+', [status(thm)], ['4', '29'])).
% 1.15/1.34  thf(t149_funct_1, conjecture,
% 1.15/1.34    (![A:$i,B:$i,C:$i]:
% 1.15/1.34     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.15/1.34       ( r1_tarski @
% 1.15/1.34         ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) @ 
% 1.15/1.34         ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ))).
% 1.15/1.34  thf(zf_stmt_0, negated_conjecture,
% 1.15/1.34    (~( ![A:$i,B:$i,C:$i]:
% 1.15/1.34        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.15/1.34          ( r1_tarski @
% 1.15/1.34            ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) @ 
% 1.15/1.34            ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) )),
% 1.15/1.34    inference('cnf.neg', [status(esa)], [t149_funct_1])).
% 1.15/1.34  thf('31', plain,
% 1.15/1.34      (~ (r1_tarski @ 
% 1.15/1.34          (k9_relat_1 @ sk_C @ 
% 1.15/1.34           (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C @ sk_B))) @ 
% 1.15/1.34          (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ sk_B))),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf('32', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.15/1.34      inference('sup+', [status(thm)], ['2', '3'])).
% 1.15/1.34  thf('33', plain,
% 1.15/1.34      (~ (r1_tarski @ 
% 1.15/1.34          (k9_relat_1 @ sk_C @ 
% 1.15/1.34           (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C @ sk_B))) @ 
% 1.15/1.34          (k3_xboole_0 @ sk_B @ (k9_relat_1 @ sk_C @ sk_A)))),
% 1.15/1.34      inference('demod', [status(thm)], ['31', '32'])).
% 1.15/1.34  thf('34', plain, ((~ (v1_funct_1 @ sk_C) | ~ (v1_relat_1 @ sk_C))),
% 1.15/1.34      inference('sup-', [status(thm)], ['30', '33'])).
% 1.15/1.34  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf('36', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf('37', plain, ($false),
% 1.15/1.34      inference('demod', [status(thm)], ['34', '35', '36'])).
% 1.15/1.34  
% 1.15/1.34  % SZS output end Refutation
% 1.15/1.34  
% 1.15/1.35  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
