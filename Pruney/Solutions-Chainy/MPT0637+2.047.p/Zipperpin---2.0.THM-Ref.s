%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.S0C5hTw6Un

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:02 EST 2020

% Result     : Theorem 8.77s
% Output     : Refutation 8.77s
% Verified   : 
% Statistics : Number of formulae       :  225 (5750 expanded)
%              Number of leaves         :   27 (2029 expanded)
%              Depth                    :   20
%              Number of atoms          : 2194 (54850 expanded)
%              Number of equality atoms :  151 (4025 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k7_relat_1 @ X34 @ X33 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t43_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_funct_1])).

thf('1',plain,(
    ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
     != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('4',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('7',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X30 ) @ X31 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X31 ) @ X30 )
        = X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('10',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('11',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X30 ) @ X31 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X31 ) @ X30 )
        = X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X24 @ X23 ) @ X25 )
        = ( k5_relat_1 @ X24 @ ( k5_relat_1 @ X23 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('17',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X28 @ ( k6_relat_1 @ X29 ) ) @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('18',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ( X0
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k5_relat_1 @ X2 @ X1 ) @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ X2 @ X1 )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k5_relat_1 @ X2 @ X1 ) @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ X2 @ X1 )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) )
      | ( ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf('24',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) )
      | ( ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) @ ( k6_relat_1 @ X1 ) ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) @ ( k6_relat_1 @ X1 ) ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','25'])).

thf('27',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('28',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k7_relat_1 @ X34 @ X33 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t192_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('29',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k7_relat_1 @ X21 @ X22 )
        = ( k7_relat_1 @ X21 @ ( k3_xboole_0 @ ( k1_relat_1 @ X21 ) @ X22 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('30',plain,(
    ! [X27: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('31',plain,(
    ! [X32: $i] :
      ( ( ( k5_relat_1 @ X32 @ ( k6_relat_1 @ ( k2_relat_1 @ X32 ) ) )
        = X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k7_relat_1 @ X34 @ X33 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('36',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X24 @ X23 ) @ X25 )
        = ( k5_relat_1 @ X24 @ ( k5_relat_1 @ X23 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','40'])).

thf('42',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('43',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) ) @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['29','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('47',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('48',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['45','46','47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['28','49'])).

thf('51',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('52',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k7_relat_1 @ X21 @ X22 )
        = ( k7_relat_1 @ X21 @ ( k3_xboole_0 @ ( k1_relat_1 @ X21 ) @ X22 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['50','55','56'])).

thf('58',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k7_relat_1 @ X34 @ X33 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['50','55','56'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('61',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X24 @ X23 ) @ X25 )
        = ( k5_relat_1 @ X24 @ ( k5_relat_1 @ X23 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['59','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['50','55','56'])).

thf('68',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('69',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('70',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['66','67','68','69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','71'])).

thf('73',plain,(
    ! [X32: $i] :
      ( ( ( k5_relat_1 @ X32 @ ( k6_relat_1 @ ( k2_relat_1 @ X32 ) ) )
        = X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('74',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k7_relat_1 @ X34 @ X33 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X27: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('77',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('78',plain,(
    ! [X27: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('79',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['75','76','77','78','79'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('81',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) @ X20 )
        = ( k7_relat_1 @ X18 @ ( k3_xboole_0 @ X19 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('82',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k7_relat_1 @ X34 @ X33 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('83',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['81','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['80','89'])).

thf('91',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['72','92'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('94',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) )
      = ( k4_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('95',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) @ X20 )
        = ( k7_relat_1 @ X18 @ ( k3_xboole_0 @ X19 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) @ X20 )
        = ( k7_relat_1 @ X18 @ ( k3_xboole_0 @ X19 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X1 ) @ X0 )
        = ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X1 ) @ X0 )
        = ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['93','104'])).

thf('106',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['75','76','77','78','79'])).

thf('109',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k7_relat_1 @ X21 @ X22 )
        = ( k7_relat_1 @ X21 @ ( k3_xboole_0 @ ( k1_relat_1 @ X21 ) @ X22 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('110',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k7_relat_1 @ X34 @ X33 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('111',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X28 @ ( k6_relat_1 @ X29 ) ) @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('114',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['109','115'])).

thf('117',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('118',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('121',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('122',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('123',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['50','55','56'])).

thf('125',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['75','76','77','78','79'])).

thf('127',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['50','55','56'])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['75','76','77','78','79'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['50','55','56'])).

thf('132',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('133',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('135',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('136',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['133','134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['50','55','56'])).

thf('138',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('139',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k7_relat_1 @ X34 @ X33 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('140',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['137','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('143',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('144',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['50','55','56'])).

thf('146',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['133','134','135'])).

thf('147',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['141','142','143','144','145','146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['136','147'])).

thf('149',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k7_relat_1 @ X34 @ X33 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['75','76','77','78','79'])).

thf('156',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) @ X20 )
        = ( k7_relat_1 @ X18 @ ( k3_xboole_0 @ X19 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) @ X0 )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) @ X20 )
        = ( k7_relat_1 @ X18 @ ( k3_xboole_0 @ X19 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('164',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('166',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X2 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['161','166'])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['154','167'])).

thf('169',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['154','167'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('173',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['50','55','56'])).

thf('181',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['75','76','77','78','79'])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('184',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['26','27','57','107','108','119','120','121','122','123','124','125','126','127','128','129','130','148','153','178','179','180','181','182','183'])).

thf('185',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k7_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['4','184'])).

thf('186',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('188',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('189',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['186','189'])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['26','27','57','107','108','119','120','121','122','123','124','125','126','127','128','129','130','148','153','178','179','180','181','182','183'])).

thf('192',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('193',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['26','27','57','107','108','119','120','121','122','123','124','125','126','127','128','129','130','148','153','178','179','180','181','182','183'])).

thf('194',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['190','191','192','193'])).

thf('195',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['185','194'])).

thf('196',plain,(
    $false ),
    inference(simplify,[status(thm)],['195'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.S0C5hTw6Un
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:18:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 8.77/8.99  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 8.77/8.99  % Solved by: fo/fo7.sh
% 8.77/8.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.77/8.99  % done 6351 iterations in 8.542s
% 8.77/8.99  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 8.77/8.99  % SZS output start Refutation
% 8.77/8.99  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 8.77/8.99  thf(sk_B_type, type, sk_B: $i).
% 8.77/8.99  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 8.77/8.99  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 8.77/8.99  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 8.77/8.99  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 8.77/8.99  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 8.77/8.99  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 8.77/8.99  thf(sk_A_type, type, sk_A: $i).
% 8.77/8.99  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 8.77/8.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.77/8.99  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 8.77/8.99  thf(t94_relat_1, axiom,
% 8.77/8.99    (![A:$i,B:$i]:
% 8.77/8.99     ( ( v1_relat_1 @ B ) =>
% 8.77/8.99       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 8.77/8.99  thf('0', plain,
% 8.77/8.99      (![X33 : $i, X34 : $i]:
% 8.77/8.99         (((k7_relat_1 @ X34 @ X33) = (k5_relat_1 @ (k6_relat_1 @ X33) @ X34))
% 8.77/8.99          | ~ (v1_relat_1 @ X34))),
% 8.77/8.99      inference('cnf', [status(esa)], [t94_relat_1])).
% 8.77/8.99  thf(t43_funct_1, conjecture,
% 8.77/8.99    (![A:$i,B:$i]:
% 8.77/8.99     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 8.77/8.99       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 8.77/8.99  thf(zf_stmt_0, negated_conjecture,
% 8.77/8.99    (~( ![A:$i,B:$i]:
% 8.77/8.99        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 8.77/8.99          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 8.77/8.99    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 8.77/8.99  thf('1', plain,
% 8.77/8.99      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 8.77/8.99         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 8.77/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.77/8.99  thf('2', plain,
% 8.77/8.99      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 8.77/8.99          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 8.77/8.99        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 8.77/8.99      inference('sup-', [status(thm)], ['0', '1'])).
% 8.77/8.99  thf(fc3_funct_1, axiom,
% 8.77/8.99    (![A:$i]:
% 8.77/8.99     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 8.77/8.99       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 8.77/8.99  thf('3', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.77/8.99      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.77/8.99  thf('4', plain,
% 8.77/8.99      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 8.77/8.99         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 8.77/8.99      inference('demod', [status(thm)], ['2', '3'])).
% 8.77/8.99  thf(d10_xboole_0, axiom,
% 8.77/8.99    (![A:$i,B:$i]:
% 8.77/8.99     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 8.77/8.99  thf('5', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 8.77/8.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.77/8.99  thf('6', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 8.77/8.99      inference('simplify', [status(thm)], ['5'])).
% 8.77/8.99  thf(t77_relat_1, axiom,
% 8.77/8.99    (![A:$i,B:$i]:
% 8.77/8.99     ( ( v1_relat_1 @ B ) =>
% 8.77/8.99       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 8.77/8.99         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 8.77/8.99  thf('7', plain,
% 8.77/8.99      (![X30 : $i, X31 : $i]:
% 8.77/8.99         (~ (r1_tarski @ (k1_relat_1 @ X30) @ X31)
% 8.77/8.99          | ((k5_relat_1 @ (k6_relat_1 @ X31) @ X30) = (X30))
% 8.77/8.99          | ~ (v1_relat_1 @ X30))),
% 8.77/8.99      inference('cnf', [status(esa)], [t77_relat_1])).
% 8.77/8.99  thf('8', plain,
% 8.77/8.99      (![X0 : $i]:
% 8.77/8.99         (~ (v1_relat_1 @ X0)
% 8.77/8.99          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 8.77/8.99      inference('sup-', [status(thm)], ['6', '7'])).
% 8.77/8.99  thf(t17_xboole_1, axiom,
% 8.77/8.99    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 8.77/8.99  thf('9', plain,
% 8.77/8.99      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 8.77/8.99      inference('cnf', [status(esa)], [t17_xboole_1])).
% 8.77/8.99  thf(t71_relat_1, axiom,
% 8.77/8.99    (![A:$i]:
% 8.77/8.99     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 8.77/8.99       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 8.77/8.99  thf('10', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 8.77/8.99      inference('cnf', [status(esa)], [t71_relat_1])).
% 8.77/8.99  thf('11', plain,
% 8.77/8.99      (![X30 : $i, X31 : $i]:
% 8.77/8.99         (~ (r1_tarski @ (k1_relat_1 @ X30) @ X31)
% 8.77/8.99          | ((k5_relat_1 @ (k6_relat_1 @ X31) @ X30) = (X30))
% 8.77/8.99          | ~ (v1_relat_1 @ X30))),
% 8.77/8.99      inference('cnf', [status(esa)], [t77_relat_1])).
% 8.77/8.99  thf('12', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         (~ (r1_tarski @ X0 @ X1)
% 8.77/8.99          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 8.77/8.99          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 8.77/8.99              = (k6_relat_1 @ X0)))),
% 8.77/8.99      inference('sup-', [status(thm)], ['10', '11'])).
% 8.77/8.99  thf('13', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.77/8.99      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.77/8.99  thf('14', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         (~ (r1_tarski @ X0 @ X1)
% 8.77/8.99          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 8.77/8.99              = (k6_relat_1 @ X0)))),
% 8.77/8.99      inference('demod', [status(thm)], ['12', '13'])).
% 8.77/8.99  thf('15', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         ((k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 8.77/8.99           (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 8.77/8.99           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 8.77/8.99      inference('sup-', [status(thm)], ['9', '14'])).
% 8.77/8.99  thf(t55_relat_1, axiom,
% 8.77/8.99    (![A:$i]:
% 8.77/8.99     ( ( v1_relat_1 @ A ) =>
% 8.77/8.99       ( ![B:$i]:
% 8.77/8.99         ( ( v1_relat_1 @ B ) =>
% 8.77/8.99           ( ![C:$i]:
% 8.77/8.99             ( ( v1_relat_1 @ C ) =>
% 8.77/8.99               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 8.77/8.99                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 8.77/8.99  thf('16', plain,
% 8.77/8.99      (![X23 : $i, X24 : $i, X25 : $i]:
% 8.77/8.99         (~ (v1_relat_1 @ X23)
% 8.77/8.99          | ((k5_relat_1 @ (k5_relat_1 @ X24 @ X23) @ X25)
% 8.77/8.99              = (k5_relat_1 @ X24 @ (k5_relat_1 @ X23 @ X25)))
% 8.77/8.99          | ~ (v1_relat_1 @ X25)
% 8.77/8.99          | ~ (v1_relat_1 @ X24))),
% 8.77/8.99      inference('cnf', [status(esa)], [t55_relat_1])).
% 8.77/8.99  thf(t76_relat_1, axiom,
% 8.77/8.99    (![A:$i,B:$i]:
% 8.77/8.99     ( ( v1_relat_1 @ B ) =>
% 8.77/8.99       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 8.77/8.99         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 8.77/8.99  thf('17', plain,
% 8.77/8.99      (![X28 : $i, X29 : $i]:
% 8.77/8.99         ((r1_tarski @ (k5_relat_1 @ X28 @ (k6_relat_1 @ X29)) @ X28)
% 8.77/8.99          | ~ (v1_relat_1 @ X28))),
% 8.77/8.99      inference('cnf', [status(esa)], [t76_relat_1])).
% 8.77/8.99  thf('18', plain,
% 8.77/8.99      (![X0 : $i, X2 : $i]:
% 8.77/8.99         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 8.77/8.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.77/8.99  thf('19', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         (~ (v1_relat_1 @ X0)
% 8.77/8.99          | ~ (r1_tarski @ X0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 8.77/8.99          | ((X0) = (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 8.77/8.99      inference('sup-', [status(thm)], ['17', '18'])).
% 8.77/8.99  thf('20', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.77/8.99         (~ (r1_tarski @ (k5_relat_1 @ X2 @ X1) @ 
% 8.77/8.99             (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 8.77/8.99          | ~ (v1_relat_1 @ X2)
% 8.77/8.99          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 8.77/8.99          | ~ (v1_relat_1 @ X1)
% 8.77/8.99          | ((k5_relat_1 @ X2 @ X1)
% 8.77/8.99              = (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ (k6_relat_1 @ X0)))
% 8.77/8.99          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1)))),
% 8.77/8.99      inference('sup-', [status(thm)], ['16', '19'])).
% 8.77/8.99  thf('21', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.77/8.99      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.77/8.99  thf('22', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.77/8.99         (~ (r1_tarski @ (k5_relat_1 @ X2 @ X1) @ 
% 8.77/8.99             (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 8.77/8.99          | ~ (v1_relat_1 @ X2)
% 8.77/8.99          | ~ (v1_relat_1 @ X1)
% 8.77/8.99          | ((k5_relat_1 @ X2 @ X1)
% 8.77/8.99              = (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ (k6_relat_1 @ X0)))
% 8.77/8.99          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1)))),
% 8.77/8.99      inference('demod', [status(thm)], ['20', '21'])).
% 8.77/8.99  thf('23', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.77/8.99         (~ (r1_tarski @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ 
% 8.77/8.99             (k5_relat_1 @ X2 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))
% 8.77/8.99          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X1)))
% 8.77/8.99          | ((k5_relat_1 @ X2 @ (k6_relat_1 @ X1))
% 8.77/8.99              = (k5_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ 
% 8.77/8.99                 (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))
% 8.77/8.99          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 8.77/8.99          | ~ (v1_relat_1 @ X2))),
% 8.77/8.99      inference('sup-', [status(thm)], ['15', '22'])).
% 8.77/8.99  thf('24', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.77/8.99      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.77/8.99  thf('25', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.77/8.99         (~ (r1_tarski @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ 
% 8.77/8.99             (k5_relat_1 @ X2 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))
% 8.77/8.99          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X1)))
% 8.77/8.99          | ((k5_relat_1 @ X2 @ (k6_relat_1 @ X1))
% 8.77/8.99              = (k5_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ 
% 8.77/8.99                 (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))
% 8.77/8.99          | ~ (v1_relat_1 @ X2))),
% 8.77/8.99      inference('demod', [status(thm)], ['23', '24'])).
% 8.77/8.99  thf('26', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         (~ (r1_tarski @ 
% 8.77/8.99             (k5_relat_1 @ 
% 8.77/8.99              (k6_relat_1 @ 
% 8.77/8.99               (k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))) @ 
% 8.77/8.99              (k6_relat_1 @ X1)) @ 
% 8.77/8.99             (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 8.77/8.99          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 8.77/8.99          | ~ (v1_relat_1 @ 
% 8.77/8.99               (k6_relat_1 @ 
% 8.77/8.99                (k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))))
% 8.77/8.99          | ((k5_relat_1 @ 
% 8.77/8.99              (k6_relat_1 @ 
% 8.77/8.99               (k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))) @ 
% 8.77/8.99              (k6_relat_1 @ X1))
% 8.77/8.99              = (k5_relat_1 @ 
% 8.77/8.99                 (k5_relat_1 @ 
% 8.77/8.99                  (k6_relat_1 @ 
% 8.77/8.99                   (k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))) @ 
% 8.77/8.99                  (k6_relat_1 @ X1)) @ 
% 8.77/8.99                 (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))
% 8.77/8.99          | ~ (v1_relat_1 @ 
% 8.77/8.99               (k5_relat_1 @ 
% 8.77/8.99                (k6_relat_1 @ 
% 8.77/8.99                 (k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))) @ 
% 8.77/8.99                (k6_relat_1 @ X1))))),
% 8.77/8.99      inference('sup-', [status(thm)], ['8', '25'])).
% 8.77/8.99  thf('27', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 8.77/8.99      inference('cnf', [status(esa)], [t71_relat_1])).
% 8.77/8.99  thf('28', plain,
% 8.77/8.99      (![X33 : $i, X34 : $i]:
% 8.77/8.99         (((k7_relat_1 @ X34 @ X33) = (k5_relat_1 @ (k6_relat_1 @ X33) @ X34))
% 8.77/8.99          | ~ (v1_relat_1 @ X34))),
% 8.77/8.99      inference('cnf', [status(esa)], [t94_relat_1])).
% 8.77/8.99  thf(t192_relat_1, axiom,
% 8.77/8.99    (![A:$i,B:$i]:
% 8.77/8.99     ( ( v1_relat_1 @ B ) =>
% 8.77/8.99       ( ( k7_relat_1 @ B @ A ) =
% 8.77/8.99         ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 8.77/8.99  thf('29', plain,
% 8.77/8.99      (![X21 : $i, X22 : $i]:
% 8.77/8.99         (((k7_relat_1 @ X21 @ X22)
% 8.77/8.99            = (k7_relat_1 @ X21 @ (k3_xboole_0 @ (k1_relat_1 @ X21) @ X22)))
% 8.77/8.99          | ~ (v1_relat_1 @ X21))),
% 8.77/8.99      inference('cnf', [status(esa)], [t192_relat_1])).
% 8.77/8.99  thf('30', plain, (![X27 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 8.77/8.99      inference('cnf', [status(esa)], [t71_relat_1])).
% 8.77/8.99  thf(t80_relat_1, axiom,
% 8.77/8.99    (![A:$i]:
% 8.77/8.99     ( ( v1_relat_1 @ A ) =>
% 8.77/8.99       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 8.77/8.99  thf('31', plain,
% 8.77/8.99      (![X32 : $i]:
% 8.77/8.99         (((k5_relat_1 @ X32 @ (k6_relat_1 @ (k2_relat_1 @ X32))) = (X32))
% 8.77/8.99          | ~ (v1_relat_1 @ X32))),
% 8.77/8.99      inference('cnf', [status(esa)], [t80_relat_1])).
% 8.77/8.99  thf('32', plain,
% 8.77/8.99      (![X0 : $i]:
% 8.77/8.99         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 8.77/8.99            = (k6_relat_1 @ X0))
% 8.77/8.99          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 8.77/8.99      inference('sup+', [status(thm)], ['30', '31'])).
% 8.77/8.99  thf('33', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.77/8.99      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.77/8.99  thf('34', plain,
% 8.77/8.99      (![X0 : $i]:
% 8.77/8.99         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 8.77/8.99           = (k6_relat_1 @ X0))),
% 8.77/8.99      inference('demod', [status(thm)], ['32', '33'])).
% 8.77/8.99  thf('35', plain,
% 8.77/8.99      (![X33 : $i, X34 : $i]:
% 8.77/8.99         (((k7_relat_1 @ X34 @ X33) = (k5_relat_1 @ (k6_relat_1 @ X33) @ X34))
% 8.77/8.99          | ~ (v1_relat_1 @ X34))),
% 8.77/8.99      inference('cnf', [status(esa)], [t94_relat_1])).
% 8.77/8.99  thf('36', plain,
% 8.77/8.99      (![X23 : $i, X24 : $i, X25 : $i]:
% 8.77/8.99         (~ (v1_relat_1 @ X23)
% 8.77/8.99          | ((k5_relat_1 @ (k5_relat_1 @ X24 @ X23) @ X25)
% 8.77/8.99              = (k5_relat_1 @ X24 @ (k5_relat_1 @ X23 @ X25)))
% 8.77/8.99          | ~ (v1_relat_1 @ X25)
% 8.77/8.99          | ~ (v1_relat_1 @ X24))),
% 8.77/8.99      inference('cnf', [status(esa)], [t55_relat_1])).
% 8.77/8.99  thf('37', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.77/8.99         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 8.77/8.99            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 8.77/8.99          | ~ (v1_relat_1 @ X1)
% 8.77/8.99          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 8.77/8.99          | ~ (v1_relat_1 @ X2)
% 8.77/8.99          | ~ (v1_relat_1 @ X1))),
% 8.77/8.99      inference('sup+', [status(thm)], ['35', '36'])).
% 8.77/8.99  thf('38', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.77/8.99      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.77/8.99  thf('39', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.77/8.99         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 8.77/8.99            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 8.77/8.99          | ~ (v1_relat_1 @ X1)
% 8.77/8.99          | ~ (v1_relat_1 @ X2)
% 8.77/8.99          | ~ (v1_relat_1 @ X1))),
% 8.77/8.99      inference('demod', [status(thm)], ['37', '38'])).
% 8.77/8.99  thf('40', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.77/8.99         (~ (v1_relat_1 @ X2)
% 8.77/8.99          | ~ (v1_relat_1 @ X1)
% 8.77/8.99          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 8.77/8.99              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 8.77/8.99      inference('simplify', [status(thm)], ['39'])).
% 8.77/8.99  thf('41', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         (((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 8.77/8.99            (k6_relat_1 @ X0))
% 8.77/8.99            = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 8.77/8.99          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 8.77/8.99          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 8.77/8.99      inference('sup+', [status(thm)], ['34', '40'])).
% 8.77/8.99  thf('42', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.77/8.99      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.77/8.99  thf('43', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.77/8.99      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.77/8.99  thf('44', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 8.77/8.99           (k6_relat_1 @ X0))
% 8.77/8.99           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 8.77/8.99      inference('demod', [status(thm)], ['41', '42', '43'])).
% 8.77/8.99  thf('45', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         (((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 8.77/8.99            (k6_relat_1 @ X1))
% 8.77/8.99            = (k5_relat_1 @ 
% 8.77/8.99               (k6_relat_1 @ 
% 8.77/8.99                (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0)) @ 
% 8.77/8.99               (k6_relat_1 @ X1)))
% 8.77/8.99          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 8.77/8.99      inference('sup+', [status(thm)], ['29', '44'])).
% 8.77/8.99  thf('46', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 8.77/8.99           (k6_relat_1 @ X0))
% 8.77/8.99           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 8.77/8.99      inference('demod', [status(thm)], ['41', '42', '43'])).
% 8.77/8.99  thf('47', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 8.77/8.99      inference('cnf', [status(esa)], [t71_relat_1])).
% 8.77/8.99  thf('48', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.77/8.99      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.77/8.99  thf('49', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 8.77/8.99           = (k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 8.77/8.99              (k6_relat_1 @ X1)))),
% 8.77/8.99      inference('demod', [status(thm)], ['45', '46', '47', '48'])).
% 8.77/8.99  thf('50', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 8.77/8.99            = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0)))
% 8.77/8.99          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 8.77/8.99      inference('sup+', [status(thm)], ['28', '49'])).
% 8.77/8.99  thf('51', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 8.77/8.99      inference('cnf', [status(esa)], [t71_relat_1])).
% 8.77/8.99  thf('52', plain,
% 8.77/8.99      (![X21 : $i, X22 : $i]:
% 8.77/8.99         (((k7_relat_1 @ X21 @ X22)
% 8.77/8.99            = (k7_relat_1 @ X21 @ (k3_xboole_0 @ (k1_relat_1 @ X21) @ X22)))
% 8.77/8.99          | ~ (v1_relat_1 @ X21))),
% 8.77/8.99      inference('cnf', [status(esa)], [t192_relat_1])).
% 8.77/8.99  thf('53', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 8.77/8.99            = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 8.77/8.99          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 8.77/8.99      inference('sup+', [status(thm)], ['51', '52'])).
% 8.77/8.99  thf('54', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.77/8.99      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.77/8.99  thf('55', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 8.77/8.99           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 8.77/8.99      inference('demod', [status(thm)], ['53', '54'])).
% 8.77/8.99  thf('56', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.77/8.99      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.77/8.99  thf('57', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 8.77/8.99           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 8.77/8.99      inference('demod', [status(thm)], ['50', '55', '56'])).
% 8.77/8.99  thf('58', plain,
% 8.77/8.99      (![X33 : $i, X34 : $i]:
% 8.77/8.99         (((k7_relat_1 @ X34 @ X33) = (k5_relat_1 @ (k6_relat_1 @ X33) @ X34))
% 8.77/8.99          | ~ (v1_relat_1 @ X34))),
% 8.77/8.99      inference('cnf', [status(esa)], [t94_relat_1])).
% 8.77/8.99  thf('59', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 8.77/8.99           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 8.77/8.99      inference('demod', [status(thm)], ['50', '55', '56'])).
% 8.77/8.99  thf('60', plain,
% 8.77/8.99      (![X0 : $i]:
% 8.77/8.99         (~ (v1_relat_1 @ X0)
% 8.77/8.99          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 8.77/8.99      inference('sup-', [status(thm)], ['6', '7'])).
% 8.77/8.99  thf('61', plain,
% 8.77/8.99      (![X23 : $i, X24 : $i, X25 : $i]:
% 8.77/8.99         (~ (v1_relat_1 @ X23)
% 8.77/8.99          | ((k5_relat_1 @ (k5_relat_1 @ X24 @ X23) @ X25)
% 8.77/8.99              = (k5_relat_1 @ X24 @ (k5_relat_1 @ X23 @ X25)))
% 8.77/8.99          | ~ (v1_relat_1 @ X25)
% 8.77/8.99          | ~ (v1_relat_1 @ X24))),
% 8.77/8.99      inference('cnf', [status(esa)], [t55_relat_1])).
% 8.77/8.99  thf('62', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         (((k5_relat_1 @ X0 @ X1)
% 8.77/8.99            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 8.77/8.99               (k5_relat_1 @ X0 @ X1)))
% 8.77/8.99          | ~ (v1_relat_1 @ X0)
% 8.77/8.99          | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 8.77/8.99          | ~ (v1_relat_1 @ X1)
% 8.77/8.99          | ~ (v1_relat_1 @ X0))),
% 8.77/8.99      inference('sup+', [status(thm)], ['60', '61'])).
% 8.77/8.99  thf('63', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.77/8.99      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.77/8.99  thf('64', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         (((k5_relat_1 @ X0 @ X1)
% 8.77/8.99            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 8.77/8.99               (k5_relat_1 @ X0 @ X1)))
% 8.77/8.99          | ~ (v1_relat_1 @ X0)
% 8.77/8.99          | ~ (v1_relat_1 @ X1)
% 8.77/8.99          | ~ (v1_relat_1 @ X0))),
% 8.77/8.99      inference('demod', [status(thm)], ['62', '63'])).
% 8.77/8.99  thf('65', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         (~ (v1_relat_1 @ X1)
% 8.77/8.99          | ~ (v1_relat_1 @ X0)
% 8.77/8.99          | ((k5_relat_1 @ X0 @ X1)
% 8.77/8.99              = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 8.77/8.99                 (k5_relat_1 @ X0 @ X1))))),
% 8.77/8.99      inference('simplify', [status(thm)], ['64'])).
% 8.77/8.99  thf('66', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 8.77/8.99            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ (k6_relat_1 @ X0))) @ 
% 8.77/8.99               (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 8.77/8.99          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 8.77/8.99          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 8.77/8.99      inference('sup+', [status(thm)], ['59', '65'])).
% 8.77/8.99  thf('67', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 8.77/8.99           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 8.77/8.99      inference('demod', [status(thm)], ['50', '55', '56'])).
% 8.77/8.99  thf('68', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 8.77/8.99      inference('cnf', [status(esa)], [t71_relat_1])).
% 8.77/8.99  thf('69', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.77/8.99      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.77/8.99  thf('70', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.77/8.99      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.77/8.99  thf('71', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 8.77/8.99           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 8.77/8.99              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 8.77/8.99      inference('demod', [status(thm)], ['66', '67', '68', '69', '70'])).
% 8.77/8.99  thf('72', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 8.77/8.99            = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0))
% 8.77/8.99          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 8.77/8.99      inference('sup+', [status(thm)], ['58', '71'])).
% 8.77/8.99  thf('73', plain,
% 8.77/8.99      (![X32 : $i]:
% 8.77/8.99         (((k5_relat_1 @ X32 @ (k6_relat_1 @ (k2_relat_1 @ X32))) = (X32))
% 8.77/8.99          | ~ (v1_relat_1 @ X32))),
% 8.77/8.99      inference('cnf', [status(esa)], [t80_relat_1])).
% 8.77/8.99  thf('74', plain,
% 8.77/8.99      (![X33 : $i, X34 : $i]:
% 8.77/8.99         (((k7_relat_1 @ X34 @ X33) = (k5_relat_1 @ (k6_relat_1 @ X33) @ X34))
% 8.77/8.99          | ~ (v1_relat_1 @ X34))),
% 8.77/8.99      inference('cnf', [status(esa)], [t94_relat_1])).
% 8.77/8.99  thf('75', plain,
% 8.77/8.99      (![X0 : $i]:
% 8.77/8.99         (((k7_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0))) @ X0)
% 8.77/8.99            = (k6_relat_1 @ X0))
% 8.77/8.99          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 8.77/8.99          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0)))))),
% 8.77/8.99      inference('sup+', [status(thm)], ['73', '74'])).
% 8.77/8.99  thf('76', plain, (![X27 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 8.77/8.99      inference('cnf', [status(esa)], [t71_relat_1])).
% 8.77/8.99  thf('77', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.77/8.99      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.77/8.99  thf('78', plain, (![X27 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 8.77/8.99      inference('cnf', [status(esa)], [t71_relat_1])).
% 8.77/8.99  thf('79', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.77/8.99      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.77/8.99  thf('80', plain,
% 8.77/8.99      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 8.77/8.99      inference('demod', [status(thm)], ['75', '76', '77', '78', '79'])).
% 8.77/8.99  thf(t100_relat_1, axiom,
% 8.77/8.99    (![A:$i,B:$i,C:$i]:
% 8.77/8.99     ( ( v1_relat_1 @ C ) =>
% 8.77/8.99       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 8.77/8.99         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 8.77/8.99  thf('81', plain,
% 8.77/8.99      (![X18 : $i, X19 : $i, X20 : $i]:
% 8.77/8.99         (((k7_relat_1 @ (k7_relat_1 @ X18 @ X19) @ X20)
% 8.77/8.99            = (k7_relat_1 @ X18 @ (k3_xboole_0 @ X19 @ X20)))
% 8.77/8.99          | ~ (v1_relat_1 @ X18))),
% 8.77/8.99      inference('cnf', [status(esa)], [t100_relat_1])).
% 8.77/8.99  thf('82', plain,
% 8.77/8.99      (![X33 : $i, X34 : $i]:
% 8.77/8.99         (((k7_relat_1 @ X34 @ X33) = (k5_relat_1 @ (k6_relat_1 @ X33) @ X34))
% 8.77/8.99          | ~ (v1_relat_1 @ X34))),
% 8.77/8.99      inference('cnf', [status(esa)], [t94_relat_1])).
% 8.77/8.99  thf(dt_k5_relat_1, axiom,
% 8.77/8.99    (![A:$i,B:$i]:
% 8.77/8.99     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 8.77/8.99       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 8.77/8.99  thf('83', plain,
% 8.77/8.99      (![X16 : $i, X17 : $i]:
% 8.77/8.99         (~ (v1_relat_1 @ X16)
% 8.77/8.99          | ~ (v1_relat_1 @ X17)
% 8.77/8.99          | (v1_relat_1 @ (k5_relat_1 @ X16 @ X17)))),
% 8.77/8.99      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 8.77/8.99  thf('84', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 8.77/8.99          | ~ (v1_relat_1 @ X1)
% 8.77/8.99          | ~ (v1_relat_1 @ X1)
% 8.77/8.99          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 8.77/8.99      inference('sup+', [status(thm)], ['82', '83'])).
% 8.77/8.99  thf('85', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.77/8.99      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.77/8.99  thf('86', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 8.77/8.99          | ~ (v1_relat_1 @ X1)
% 8.77/8.99          | ~ (v1_relat_1 @ X1))),
% 8.77/8.99      inference('demod', [status(thm)], ['84', '85'])).
% 8.77/8.99  thf('87', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 8.77/8.99      inference('simplify', [status(thm)], ['86'])).
% 8.77/8.99  thf('88', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.77/8.99         ((v1_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 8.77/8.99          | ~ (v1_relat_1 @ X2)
% 8.77/8.99          | ~ (v1_relat_1 @ X2))),
% 8.77/8.99      inference('sup+', [status(thm)], ['81', '87'])).
% 8.77/8.99  thf('89', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.77/8.99         (~ (v1_relat_1 @ X2)
% 8.77/8.99          | (v1_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))),
% 8.77/8.99      inference('simplify', [status(thm)], ['88'])).
% 8.77/8.99  thf('90', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         ((v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 8.77/8.99          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 8.77/8.99      inference('sup+', [status(thm)], ['80', '89'])).
% 8.77/8.99  thf('91', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.77/8.99      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.77/8.99  thf('92', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 8.77/8.99      inference('demod', [status(thm)], ['90', '91'])).
% 8.77/8.99  thf('93', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 8.77/8.99           = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0))),
% 8.77/8.99      inference('demod', [status(thm)], ['72', '92'])).
% 8.77/8.99  thf(t47_xboole_1, axiom,
% 8.77/8.99    (![A:$i,B:$i]:
% 8.77/8.99     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 8.77/8.99  thf('94', plain,
% 8.77/8.99      (![X5 : $i, X6 : $i]:
% 8.77/8.99         ((k4_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6))
% 8.77/8.99           = (k4_xboole_0 @ X5 @ X6))),
% 8.77/8.99      inference('cnf', [status(esa)], [t47_xboole_1])).
% 8.77/8.99  thf(t48_xboole_1, axiom,
% 8.77/8.99    (![A:$i,B:$i]:
% 8.77/8.99     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 8.77/8.99  thf('95', plain,
% 8.77/8.99      (![X7 : $i, X8 : $i]:
% 8.77/8.99         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 8.77/8.99           = (k3_xboole_0 @ X7 @ X8))),
% 8.77/8.99      inference('cnf', [status(esa)], [t48_xboole_1])).
% 8.77/8.99  thf('96', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 8.77/8.99           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 8.77/8.99      inference('sup+', [status(thm)], ['94', '95'])).
% 8.77/8.99  thf('97', plain,
% 8.77/8.99      (![X7 : $i, X8 : $i]:
% 8.77/8.99         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 8.77/8.99           = (k3_xboole_0 @ X7 @ X8))),
% 8.77/8.99      inference('cnf', [status(esa)], [t48_xboole_1])).
% 8.77/8.99  thf('98', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         ((k3_xboole_0 @ X1 @ X0)
% 8.77/8.99           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 8.77/8.99      inference('demod', [status(thm)], ['96', '97'])).
% 8.77/8.99  thf('99', plain,
% 8.77/8.99      (![X18 : $i, X19 : $i, X20 : $i]:
% 8.77/8.99         (((k7_relat_1 @ (k7_relat_1 @ X18 @ X19) @ X20)
% 8.77/8.99            = (k7_relat_1 @ X18 @ (k3_xboole_0 @ X19 @ X20)))
% 8.77/8.99          | ~ (v1_relat_1 @ X18))),
% 8.77/8.99      inference('cnf', [status(esa)], [t100_relat_1])).
% 8.77/8.99  thf('100', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.77/8.99         (((k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 8.77/8.99            = (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 8.77/8.99          | ~ (v1_relat_1 @ X2))),
% 8.77/8.99      inference('sup+', [status(thm)], ['98', '99'])).
% 8.77/8.99  thf('101', plain,
% 8.77/8.99      (![X18 : $i, X19 : $i, X20 : $i]:
% 8.77/8.99         (((k7_relat_1 @ (k7_relat_1 @ X18 @ X19) @ X20)
% 8.77/8.99            = (k7_relat_1 @ X18 @ (k3_xboole_0 @ X19 @ X20)))
% 8.77/8.99          | ~ (v1_relat_1 @ X18))),
% 8.77/8.99      inference('cnf', [status(esa)], [t100_relat_1])).
% 8.77/8.99  thf('102', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.77/8.99         (((k7_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X1) @ X0)
% 8.77/8.99            = (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 8.77/8.99          | ~ (v1_relat_1 @ X2)
% 8.77/8.99          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X1)))),
% 8.77/8.99      inference('sup+', [status(thm)], ['100', '101'])).
% 8.77/8.99  thf('103', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 8.77/8.99      inference('simplify', [status(thm)], ['86'])).
% 8.77/8.99  thf('104', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.77/8.99         (~ (v1_relat_1 @ X2)
% 8.77/8.99          | ((k7_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X1) @ X0)
% 8.77/8.99              = (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 8.77/8.99      inference('clc', [status(thm)], ['102', '103'])).
% 8.77/8.99  thf('105', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.77/8.99         (((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 8.77/8.99            = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X0 @ X2)))
% 8.77/8.99          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 8.77/8.99      inference('sup+', [status(thm)], ['93', '104'])).
% 8.77/8.99  thf('106', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.77/8.99      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.77/8.99  thf('107', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.77/8.99         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 8.77/8.99           = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X0 @ X2)))),
% 8.77/8.99      inference('demod', [status(thm)], ['105', '106'])).
% 8.77/8.99  thf('108', plain,
% 8.77/8.99      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 8.77/8.99      inference('demod', [status(thm)], ['75', '76', '77', '78', '79'])).
% 8.77/8.99  thf('109', plain,
% 8.77/8.99      (![X21 : $i, X22 : $i]:
% 8.77/8.99         (((k7_relat_1 @ X21 @ X22)
% 8.77/8.99            = (k7_relat_1 @ X21 @ (k3_xboole_0 @ (k1_relat_1 @ X21) @ X22)))
% 8.77/8.99          | ~ (v1_relat_1 @ X21))),
% 8.77/8.99      inference('cnf', [status(esa)], [t192_relat_1])).
% 8.77/8.99  thf('110', plain,
% 8.77/8.99      (![X33 : $i, X34 : $i]:
% 8.77/8.99         (((k7_relat_1 @ X34 @ X33) = (k5_relat_1 @ (k6_relat_1 @ X33) @ X34))
% 8.77/8.99          | ~ (v1_relat_1 @ X34))),
% 8.77/8.99      inference('cnf', [status(esa)], [t94_relat_1])).
% 8.77/8.99  thf('111', plain,
% 8.77/8.99      (![X28 : $i, X29 : $i]:
% 8.77/8.99         ((r1_tarski @ (k5_relat_1 @ X28 @ (k6_relat_1 @ X29)) @ X28)
% 8.77/8.99          | ~ (v1_relat_1 @ X28))),
% 8.77/8.99      inference('cnf', [status(esa)], [t76_relat_1])).
% 8.77/8.99  thf('112', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         ((r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 8.77/8.99           (k6_relat_1 @ X0))
% 8.77/8.99          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 8.77/8.99          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 8.77/8.99      inference('sup+', [status(thm)], ['110', '111'])).
% 8.77/8.99  thf('113', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.77/8.99      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.77/8.99  thf('114', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.77/8.99      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.77/8.99  thf('115', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ (k6_relat_1 @ X0))),
% 8.77/8.99      inference('demod', [status(thm)], ['112', '113', '114'])).
% 8.77/8.99  thf('116', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         ((r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 8.77/8.99           (k6_relat_1 @ (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0)))
% 8.77/8.99          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 8.77/8.99      inference('sup+', [status(thm)], ['109', '115'])).
% 8.77/8.99  thf('117', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 8.77/8.99      inference('cnf', [status(esa)], [t71_relat_1])).
% 8.77/8.99  thf('118', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.77/8.99      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.77/8.99  thf('119', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 8.77/8.99          (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 8.77/8.99      inference('demod', [status(thm)], ['116', '117', '118'])).
% 8.77/8.99  thf('120', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.77/8.99      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.77/8.99  thf('121', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 8.77/8.99      inference('cnf', [status(esa)], [t71_relat_1])).
% 8.77/8.99  thf('122', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.77/8.99      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.77/8.99  thf('123', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 8.77/8.99      inference('cnf', [status(esa)], [t71_relat_1])).
% 8.77/8.99  thf('124', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 8.77/8.99           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 8.77/8.99      inference('demod', [status(thm)], ['50', '55', '56'])).
% 8.77/8.99  thf('125', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.77/8.99         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 8.77/8.99           = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X0 @ X2)))),
% 8.77/8.99      inference('demod', [status(thm)], ['105', '106'])).
% 8.77/8.99  thf('126', plain,
% 8.77/8.99      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 8.77/8.99      inference('demod', [status(thm)], ['75', '76', '77', '78', '79'])).
% 8.77/8.99  thf('127', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 8.77/8.99      inference('cnf', [status(esa)], [t71_relat_1])).
% 8.77/8.99  thf('128', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 8.77/8.99           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 8.77/8.99      inference('demod', [status(thm)], ['50', '55', '56'])).
% 8.77/8.99  thf('129', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.77/8.99         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 8.77/8.99           = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X0 @ X2)))),
% 8.77/8.99      inference('demod', [status(thm)], ['105', '106'])).
% 8.77/8.99  thf('130', plain,
% 8.77/8.99      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 8.77/8.99      inference('demod', [status(thm)], ['75', '76', '77', '78', '79'])).
% 8.77/8.99  thf('131', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 8.77/8.99           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 8.77/8.99      inference('demod', [status(thm)], ['50', '55', '56'])).
% 8.77/8.99  thf('132', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.77/8.99         (~ (v1_relat_1 @ X2)
% 8.77/8.99          | ~ (v1_relat_1 @ X1)
% 8.77/8.99          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 8.77/8.99              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 8.77/8.99      inference('simplify', [status(thm)], ['39'])).
% 8.77/8.99  thf('133', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.77/8.99         (((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 8.77/8.99            (k6_relat_1 @ X1))
% 8.77/8.99            = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 8.77/8.99               (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 8.77/8.99          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 8.77/8.99          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 8.77/8.99      inference('sup+', [status(thm)], ['131', '132'])).
% 8.77/8.99  thf('134', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.77/8.99      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.77/8.99  thf('135', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.77/8.99      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.77/8.99  thf('136', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.77/8.99         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 8.77/8.99           (k6_relat_1 @ X1))
% 8.77/8.99           = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 8.77/8.99              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 8.77/8.99      inference('demod', [status(thm)], ['133', '134', '135'])).
% 8.77/8.99  thf('137', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 8.77/8.99           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 8.77/8.99      inference('demod', [status(thm)], ['50', '55', '56'])).
% 8.77/8.99  thf('138', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.77/8.99         (~ (v1_relat_1 @ X2)
% 8.77/8.99          | ~ (v1_relat_1 @ X1)
% 8.77/8.99          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 8.77/8.99              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 8.77/8.99      inference('simplify', [status(thm)], ['39'])).
% 8.77/8.99  thf('139', plain,
% 8.77/8.99      (![X33 : $i, X34 : $i]:
% 8.77/8.99         (((k7_relat_1 @ X34 @ X33) = (k5_relat_1 @ (k6_relat_1 @ X33) @ X34))
% 8.77/8.99          | ~ (v1_relat_1 @ X34))),
% 8.77/8.99      inference('cnf', [status(esa)], [t94_relat_1])).
% 8.77/8.99  thf('140', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.77/8.99         (((k7_relat_1 @ (k5_relat_1 @ X2 @ X0) @ X1)
% 8.77/8.99            = (k5_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 8.77/8.99          | ~ (v1_relat_1 @ X2)
% 8.77/8.99          | ~ (v1_relat_1 @ X0)
% 8.77/8.99          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X0)))),
% 8.77/8.99      inference('sup+', [status(thm)], ['138', '139'])).
% 8.77/8.99  thf('141', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.77/8.99         (~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 8.77/8.99          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 8.77/8.99          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 8.77/8.99          | ((k7_relat_1 @ 
% 8.77/8.99              (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)) @ X2)
% 8.77/8.99              = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 8.77/8.99                 (k6_relat_1 @ X1))))),
% 8.77/8.99      inference('sup-', [status(thm)], ['137', '140'])).
% 8.77/8.99  thf('142', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 8.77/8.99      inference('demod', [status(thm)], ['90', '91'])).
% 8.77/8.99  thf('143', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.77/8.99      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.77/8.99  thf('144', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.77/8.99      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.77/8.99  thf('145', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 8.77/8.99           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 8.77/8.99      inference('demod', [status(thm)], ['50', '55', '56'])).
% 8.77/8.99  thf('146', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.77/8.99         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 8.77/8.99           (k6_relat_1 @ X1))
% 8.77/8.99           = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 8.77/8.99              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 8.77/8.99      inference('demod', [status(thm)], ['133', '134', '135'])).
% 8.77/8.99  thf('147', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.77/8.99         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 8.77/8.99           = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 8.77/8.99              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 8.77/8.99      inference('demod', [status(thm)],
% 8.77/8.99                ['141', '142', '143', '144', '145', '146'])).
% 8.77/8.99  thf('148', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.77/8.99         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 8.77/8.99           (k6_relat_1 @ X1))
% 8.77/8.99           = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2))),
% 8.77/8.99      inference('demod', [status(thm)], ['136', '147'])).
% 8.77/8.99  thf('149', plain,
% 8.77/8.99      (![X33 : $i, X34 : $i]:
% 8.77/8.99         (((k7_relat_1 @ X34 @ X33) = (k5_relat_1 @ (k6_relat_1 @ X33) @ X34))
% 8.77/8.99          | ~ (v1_relat_1 @ X34))),
% 8.77/8.99      inference('cnf', [status(esa)], [t94_relat_1])).
% 8.77/8.99  thf('150', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         ((k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 8.77/8.99           (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 8.77/8.99           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 8.77/8.99      inference('sup-', [status(thm)], ['9', '14'])).
% 8.77/8.99  thf('151', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         (((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X0)
% 8.77/8.99            = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 8.77/8.99          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 8.77/8.99      inference('sup+', [status(thm)], ['149', '150'])).
% 8.77/8.99  thf('152', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.77/8.99      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.77/8.99  thf('153', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         ((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X0)
% 8.77/8.99           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 8.77/8.99      inference('demod', [status(thm)], ['151', '152'])).
% 8.77/8.99  thf('154', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         ((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X0)
% 8.77/8.99           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 8.77/8.99      inference('demod', [status(thm)], ['151', '152'])).
% 8.77/8.99  thf('155', plain,
% 8.77/8.99      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 8.77/8.99      inference('demod', [status(thm)], ['75', '76', '77', '78', '79'])).
% 8.77/8.99  thf('156', plain,
% 8.77/8.99      (![X18 : $i, X19 : $i, X20 : $i]:
% 8.77/8.99         (((k7_relat_1 @ (k7_relat_1 @ X18 @ X19) @ X20)
% 8.77/8.99            = (k7_relat_1 @ X18 @ (k3_xboole_0 @ X19 @ X20)))
% 8.77/8.99          | ~ (v1_relat_1 @ X18))),
% 8.77/8.99      inference('cnf', [status(esa)], [t100_relat_1])).
% 8.77/8.99  thf('157', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         (((k7_relat_1 @ 
% 8.77/8.99            (k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X1) @ X0)
% 8.77/8.99            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 8.77/8.99          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 8.77/8.99      inference('sup+', [status(thm)], ['155', '156'])).
% 8.77/8.99  thf('158', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.77/8.99      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.77/8.99  thf('159', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         ((k7_relat_1 @ 
% 8.77/8.99           (k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X1) @ X0)
% 8.77/8.99           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 8.77/8.99      inference('demod', [status(thm)], ['157', '158'])).
% 8.77/8.99  thf('160', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         ((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X0)
% 8.77/8.99           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 8.77/8.99      inference('demod', [status(thm)], ['151', '152'])).
% 8.77/8.99  thf('161', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         ((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X0)
% 8.77/8.99           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 8.77/8.99      inference('demod', [status(thm)], ['159', '160'])).
% 8.77/8.99  thf('162', plain,
% 8.77/8.99      (![X18 : $i, X19 : $i, X20 : $i]:
% 8.77/8.99         (((k7_relat_1 @ (k7_relat_1 @ X18 @ X19) @ X20)
% 8.77/8.99            = (k7_relat_1 @ X18 @ (k3_xboole_0 @ X19 @ X20)))
% 8.77/8.99          | ~ (v1_relat_1 @ X18))),
% 8.77/8.99      inference('cnf', [status(esa)], [t100_relat_1])).
% 8.77/8.99  thf('163', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ (k6_relat_1 @ X0))),
% 8.77/8.99      inference('demod', [status(thm)], ['112', '113', '114'])).
% 8.77/8.99  thf('164', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.77/8.99         ((r1_tarski @ 
% 8.77/8.99           (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0) @ 
% 8.77/8.99           (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 8.77/8.99          | ~ (v1_relat_1 @ (k6_relat_1 @ X2)))),
% 8.77/8.99      inference('sup+', [status(thm)], ['162', '163'])).
% 8.77/8.99  thf('165', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 8.77/8.99      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.77/8.99  thf('166', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.77/8.99         (r1_tarski @ 
% 8.77/8.99          (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0) @ 
% 8.77/8.99          (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 8.77/8.99      inference('demod', [status(thm)], ['164', '165'])).
% 8.77/8.99  thf('167', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.77/8.99         (r1_tarski @ 
% 8.77/8.99          (k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X2) @ 
% 8.77/8.99          (k6_relat_1 @ (k3_xboole_0 @ X0 @ X2)))),
% 8.77/8.99      inference('sup+', [status(thm)], ['161', '166'])).
% 8.77/8.99  thf('168', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         (r1_tarski @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 8.77/8.99          (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 8.77/8.99      inference('sup+', [status(thm)], ['154', '167'])).
% 8.77/8.99  thf('169', plain,
% 8.77/8.99      (![X0 : $i, X2 : $i]:
% 8.77/8.99         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 8.77/8.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.77/8.99  thf('170', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         (~ (r1_tarski @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 8.77/8.99             (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 8.77/8.99          | ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 8.77/8.99              = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 8.77/8.99      inference('sup-', [status(thm)], ['168', '169'])).
% 8.77/8.99  thf('171', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         (r1_tarski @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 8.77/8.99          (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 8.77/8.99      inference('sup+', [status(thm)], ['154', '167'])).
% 8.77/8.99  thf('172', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 8.77/8.99           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 8.77/8.99      inference('demod', [status(thm)], ['170', '171'])).
% 8.77/8.99  thf('173', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 8.77/8.99      inference('cnf', [status(esa)], [t71_relat_1])).
% 8.77/8.99  thf('174', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         ((k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 8.77/8.99           = (k3_xboole_0 @ X0 @ X1))),
% 8.77/8.99      inference('sup+', [status(thm)], ['172', '173'])).
% 8.77/8.99  thf('175', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 8.77/8.99      inference('cnf', [status(esa)], [t71_relat_1])).
% 8.77/8.99  thf('176', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 8.77/8.99      inference('demod', [status(thm)], ['174', '175'])).
% 8.77/8.99  thf('177', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         ((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X0)
% 8.77/8.99           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 8.77/8.99      inference('demod', [status(thm)], ['151', '152'])).
% 8.77/8.99  thf('178', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         ((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X0)
% 8.77/8.99           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 8.77/8.99      inference('sup+', [status(thm)], ['176', '177'])).
% 8.77/8.99  thf('179', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 8.77/8.99      inference('cnf', [status(esa)], [t71_relat_1])).
% 8.77/8.99  thf('180', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 8.77/8.99           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 8.77/8.99      inference('demod', [status(thm)], ['50', '55', '56'])).
% 8.77/8.99  thf('181', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.77/8.99         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 8.77/8.99           = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X0 @ X2)))),
% 8.77/8.99      inference('demod', [status(thm)], ['105', '106'])).
% 8.77/8.99  thf('182', plain,
% 8.77/8.99      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 8.77/8.99      inference('demod', [status(thm)], ['75', '76', '77', '78', '79'])).
% 8.77/8.99  thf('183', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 8.77/8.99      inference('demod', [status(thm)], ['90', '91'])).
% 8.77/8.99  thf('184', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 8.77/8.99           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 8.77/8.99      inference('demod', [status(thm)],
% 8.77/8.99                ['26', '27', '57', '107', '108', '119', '120', '121', '122', 
% 8.77/8.99                 '123', '124', '125', '126', '127', '128', '129', '130', 
% 8.77/8.99                 '148', '153', '178', '179', '180', '181', '182', '183'])).
% 8.77/8.99  thf('185', plain,
% 8.77/8.99      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 8.77/8.99         != (k7_relat_1 @ (k6_relat_1 @ sk_B) @ sk_A))),
% 8.77/8.99      inference('demod', [status(thm)], ['4', '184'])).
% 8.77/8.99  thf('186', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 8.77/8.99      inference('demod', [status(thm)], ['174', '175'])).
% 8.77/8.99  thf('187', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 8.77/8.99          (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 8.77/8.99      inference('demod', [status(thm)], ['116', '117', '118'])).
% 8.77/8.99  thf('188', plain,
% 8.77/8.99      (![X0 : $i, X2 : $i]:
% 8.77/8.99         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 8.77/8.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.77/8.99  thf('189', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         (~ (r1_tarski @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 8.77/8.99             (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 8.77/8.99          | ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 8.77/8.99              = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 8.77/8.99      inference('sup-', [status(thm)], ['187', '188'])).
% 8.77/8.99  thf('190', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         (~ (r1_tarski @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 8.77/8.99             (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 8.77/8.99          | ((k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 8.77/8.99              = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 8.77/8.99      inference('sup-', [status(thm)], ['186', '189'])).
% 8.77/8.99  thf('191', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 8.77/8.99           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 8.77/8.99      inference('demod', [status(thm)],
% 8.77/8.99                ['26', '27', '57', '107', '108', '119', '120', '121', '122', 
% 8.77/8.99                 '123', '124', '125', '126', '127', '128', '129', '130', 
% 8.77/8.99                 '148', '153', '178', '179', '180', '181', '182', '183'])).
% 8.77/8.99  thf('192', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 8.77/8.99      inference('simplify', [status(thm)], ['5'])).
% 8.77/8.99  thf('193', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 8.77/8.99           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 8.77/8.99      inference('demod', [status(thm)],
% 8.77/8.99                ['26', '27', '57', '107', '108', '119', '120', '121', '122', 
% 8.77/8.99                 '123', '124', '125', '126', '127', '128', '129', '130', 
% 8.77/8.99                 '148', '153', '178', '179', '180', '181', '182', '183'])).
% 8.77/8.99  thf('194', plain,
% 8.77/8.99      (![X0 : $i, X1 : $i]:
% 8.77/8.99         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 8.77/8.99           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 8.77/8.99      inference('demod', [status(thm)], ['190', '191', '192', '193'])).
% 8.77/8.99  thf('195', plain,
% 8.77/8.99      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 8.77/8.99         != (k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 8.77/8.99      inference('demod', [status(thm)], ['185', '194'])).
% 8.77/8.99  thf('196', plain, ($false), inference('simplify', [status(thm)], ['195'])).
% 8.77/8.99  
% 8.77/8.99  % SZS output end Refutation
% 8.77/8.99  
% 8.77/9.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
