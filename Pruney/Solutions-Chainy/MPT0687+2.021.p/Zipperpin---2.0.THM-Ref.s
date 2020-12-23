%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uIED5bx4cY

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:13 EST 2020

% Result     : Theorem 2.41s
% Output     : Refutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 395 expanded)
%              Number of leaves         :   31 ( 124 expanded)
%              Depth                    :   21
%              Number of atoms          :  827 (3361 expanded)
%              Number of equality atoms :   88 ( 330 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t171_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X31: $i] :
      ( ( ( k10_relat_1 @ X31 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t171_relat_1])).

thf(t142_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
      <=> ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
        <=> ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t142_funct_1])).

thf('1',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['1'])).

thf('4',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['1'])).

thf(t52_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X21 @ ( k1_tarski @ X20 ) )
        = ( k1_tarski @ X20 ) )
      | ~ ( r2_hidden @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t52_zfmisc_1])).

thf('8',plain,
    ( ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('10',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t174_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
          & ( ( k10_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf('11',plain,(
    ! [X32: $i,X33: $i] :
      ( ( X32 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X33 )
      | ~ ( r1_tarski @ X32 @ ( k2_relat_1 @ X33 ) )
      | ( ( k10_relat_1 @ X33 @ X32 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t174_relat_1])).

thf('12',plain,
    ( ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
       != k1_xboole_0 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
      & ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','14'])).

thf('16',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
      & ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X11: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X13 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','26','27'])).

thf(t51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) )
        = ( k1_tarski @ B ) )
     => ( r2_hidden @ B @ A ) ) )).

thf('29',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r2_hidden @ X18 @ X19 )
      | ( ( k3_xboole_0 @ X19 @ ( k1_tarski @ X18 ) )
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t51_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
       != ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
      & ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','30'])).

thf(t111_relat_1,axiom,(
    ! [A: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('32',plain,(
    ! [X28: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X28 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t111_relat_1])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('33',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X34 @ X35 ) ) @ X35 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('35',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('36',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t110_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('37',plain,(
    ! [X27: $i] :
      ( ( ( k7_relat_1 @ X27 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('38',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['34','35','41'])).

thf('43',plain,(
    ! [X11: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X13 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
      & ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('46',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
      & ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('47',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ sk_A @ k1_xboole_0 ) )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
      & ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['31','44','45','46'])).

thf('48',plain,
    ( ( r2_hidden @ sk_A @ k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
      & ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('50',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ( ( k4_xboole_0 @ X23 @ ( k1_tarski @ X22 ) )
       != X23 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','52'])).

thf('54',plain,(
    ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['3','53'])).

thf('55',plain,(
    ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['2','54'])).

thf('56',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k4_xboole_0 @ X23 @ ( k1_tarski @ X24 ) )
        = X23 )
      | ( r2_hidden @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('57',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf(t168_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k10_relat_1 @ B @ A )
        = ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ) )).

thf('59',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k10_relat_1 @ X29 @ X30 )
        = ( k10_relat_1 @ X29 @ ( k3_xboole_0 @ ( k2_relat_1 @ X29 ) @ X30 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k1_tarski @ X1 ) )
        = ( k10_relat_1 @ X0 @ ( k4_xboole_0 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['34','35','41'])).

thf('62',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k1_tarski @ X1 ) )
        = ( k10_relat_1 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['60','67'])).

thf('69',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf('70',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('71',plain,(
    ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['3','53','70'])).

thf('72',plain,(
    ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['69','71'])).

thf('73',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k10_relat_1 @ sk_B @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['68','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k10_relat_1 @ sk_B @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ( k10_relat_1 @ sk_B @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['55','75'])).

thf('77',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    $false ),
    inference(simplify,[status(thm)],['79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uIED5bx4cY
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:00:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.41/2.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.41/2.65  % Solved by: fo/fo7.sh
% 2.41/2.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.41/2.65  % done 1387 iterations in 2.197s
% 2.41/2.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.41/2.65  % SZS output start Refutation
% 2.41/2.65  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.41/2.65  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.41/2.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.41/2.65  thf(sk_A_type, type, sk_A: $i).
% 2.41/2.65  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.41/2.65  thf(sk_B_type, type, sk_B: $i).
% 2.41/2.65  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.41/2.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.41/2.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.41/2.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.41/2.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.41/2.65  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.41/2.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.41/2.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.41/2.65  thf(t171_relat_1, axiom,
% 2.41/2.65    (![A:$i]:
% 2.41/2.65     ( ( v1_relat_1 @ A ) =>
% 2.41/2.65       ( ( k10_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 2.41/2.65  thf('0', plain,
% 2.41/2.65      (![X31 : $i]:
% 2.41/2.65         (((k10_relat_1 @ X31 @ k1_xboole_0) = (k1_xboole_0))
% 2.41/2.65          | ~ (v1_relat_1 @ X31))),
% 2.41/2.65      inference('cnf', [status(esa)], [t171_relat_1])).
% 2.41/2.65  thf(t142_funct_1, conjecture,
% 2.41/2.65    (![A:$i,B:$i]:
% 2.41/2.65     ( ( v1_relat_1 @ B ) =>
% 2.41/2.65       ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) <=>
% 2.41/2.65         ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) ) != ( k1_xboole_0 ) ) ) ))).
% 2.41/2.65  thf(zf_stmt_0, negated_conjecture,
% 2.41/2.65    (~( ![A:$i,B:$i]:
% 2.41/2.65        ( ( v1_relat_1 @ B ) =>
% 2.41/2.65          ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) <=>
% 2.41/2.65            ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) ) != ( k1_xboole_0 ) ) ) ) )),
% 2.41/2.65    inference('cnf.neg', [status(esa)], [t142_funct_1])).
% 2.41/2.65  thf('1', plain,
% 2.41/2.65      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) != (k1_xboole_0))
% 2.41/2.65        | (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 2.41/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.65  thf('2', plain,
% 2.41/2.65      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) != (k1_xboole_0)))
% 2.41/2.65         <= (~ (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 2.41/2.65      inference('split', [status(esa)], ['1'])).
% 2.41/2.65  thf('3', plain,
% 2.41/2.65      (~ (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))) | 
% 2.41/2.65       ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 2.41/2.65      inference('split', [status(esa)], ['1'])).
% 2.41/2.65  thf('4', plain,
% 2.41/2.65      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))
% 2.41/2.65        | ~ (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 2.41/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.65  thf('5', plain,
% 2.41/2.65      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))
% 2.41/2.65         <= ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 2.41/2.65      inference('split', [status(esa)], ['4'])).
% 2.41/2.65  thf('6', plain,
% 2.41/2.65      (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))
% 2.41/2.65         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 2.41/2.65      inference('split', [status(esa)], ['1'])).
% 2.41/2.65  thf(t52_zfmisc_1, axiom,
% 2.41/2.65    (![A:$i,B:$i]:
% 2.41/2.65     ( ( r2_hidden @ A @ B ) =>
% 2.41/2.65       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 2.41/2.65  thf('7', plain,
% 2.41/2.65      (![X20 : $i, X21 : $i]:
% 2.41/2.65         (((k3_xboole_0 @ X21 @ (k1_tarski @ X20)) = (k1_tarski @ X20))
% 2.41/2.65          | ~ (r2_hidden @ X20 @ X21))),
% 2.41/2.65      inference('cnf', [status(esa)], [t52_zfmisc_1])).
% 2.41/2.65  thf('8', plain,
% 2.41/2.65      ((((k3_xboole_0 @ (k2_relat_1 @ sk_B) @ (k1_tarski @ sk_A))
% 2.41/2.65          = (k1_tarski @ sk_A)))
% 2.41/2.65         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 2.41/2.65      inference('sup-', [status(thm)], ['6', '7'])).
% 2.41/2.65  thf(t17_xboole_1, axiom,
% 2.41/2.65    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 2.41/2.65  thf('9', plain,
% 2.41/2.65      (![X9 : $i, X10 : $i]: (r1_tarski @ (k3_xboole_0 @ X9 @ X10) @ X9)),
% 2.41/2.65      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.41/2.65  thf('10', plain,
% 2.41/2.65      (((r1_tarski @ (k1_tarski @ sk_A) @ (k2_relat_1 @ sk_B)))
% 2.41/2.65         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 2.41/2.65      inference('sup+', [status(thm)], ['8', '9'])).
% 2.41/2.65  thf(t174_relat_1, axiom,
% 2.41/2.65    (![A:$i,B:$i]:
% 2.41/2.65     ( ( v1_relat_1 @ B ) =>
% 2.41/2.65       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 2.41/2.65            ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) & 
% 2.41/2.65            ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 2.41/2.65  thf('11', plain,
% 2.41/2.65      (![X32 : $i, X33 : $i]:
% 2.41/2.65         (((X32) = (k1_xboole_0))
% 2.41/2.65          | ~ (v1_relat_1 @ X33)
% 2.41/2.65          | ~ (r1_tarski @ X32 @ (k2_relat_1 @ X33))
% 2.41/2.65          | ((k10_relat_1 @ X33 @ X32) != (k1_xboole_0)))),
% 2.41/2.65      inference('cnf', [status(esa)], [t174_relat_1])).
% 2.41/2.65  thf('12', plain,
% 2.41/2.65      (((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) != (k1_xboole_0))
% 2.41/2.65         | ~ (v1_relat_1 @ sk_B)
% 2.41/2.65         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 2.41/2.65         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 2.41/2.65      inference('sup-', [status(thm)], ['10', '11'])).
% 2.41/2.65  thf('13', plain, ((v1_relat_1 @ sk_B)),
% 2.41/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.65  thf('14', plain,
% 2.41/2.65      (((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) != (k1_xboole_0))
% 2.41/2.65         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 2.41/2.65         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 2.41/2.65      inference('demod', [status(thm)], ['12', '13'])).
% 2.41/2.65  thf('15', plain,
% 2.41/2.65      (((((k1_xboole_0) != (k1_xboole_0))
% 2.41/2.65         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 2.41/2.65         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) & 
% 2.41/2.65             (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 2.41/2.65      inference('sup-', [status(thm)], ['5', '14'])).
% 2.41/2.65  thf('16', plain,
% 2.41/2.65      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 2.41/2.65         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) & 
% 2.41/2.65             (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 2.41/2.65      inference('simplify', [status(thm)], ['15'])).
% 2.41/2.65  thf('17', plain,
% 2.41/2.65      (![X9 : $i, X10 : $i]: (r1_tarski @ (k3_xboole_0 @ X9 @ X10) @ X9)),
% 2.41/2.65      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.41/2.65  thf(t37_xboole_1, axiom,
% 2.41/2.65    (![A:$i,B:$i]:
% 2.41/2.65     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.41/2.65  thf('18', plain,
% 2.41/2.65      (![X11 : $i, X13 : $i]:
% 2.41/2.65         (((k4_xboole_0 @ X11 @ X13) = (k1_xboole_0))
% 2.41/2.65          | ~ (r1_tarski @ X11 @ X13))),
% 2.41/2.65      inference('cnf', [status(esa)], [t37_xboole_1])).
% 2.41/2.65  thf('19', plain,
% 2.41/2.65      (![X0 : $i, X1 : $i]:
% 2.41/2.65         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 2.41/2.65      inference('sup-', [status(thm)], ['17', '18'])).
% 2.41/2.65  thf(t40_xboole_1, axiom,
% 2.41/2.65    (![A:$i,B:$i]:
% 2.41/2.65     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 2.41/2.65  thf('20', plain,
% 2.41/2.65      (![X14 : $i, X15 : $i]:
% 2.41/2.65         ((k4_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X15)
% 2.41/2.65           = (k4_xboole_0 @ X14 @ X15))),
% 2.41/2.65      inference('cnf', [status(esa)], [t40_xboole_1])).
% 2.41/2.65  thf(t48_xboole_1, axiom,
% 2.41/2.65    (![A:$i,B:$i]:
% 2.41/2.65     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.41/2.65  thf('21', plain,
% 2.41/2.65      (![X16 : $i, X17 : $i]:
% 2.41/2.65         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 2.41/2.65           = (k3_xboole_0 @ X16 @ X17))),
% 2.41/2.65      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.41/2.65  thf('22', plain,
% 2.41/2.65      (![X0 : $i, X1 : $i]:
% 2.41/2.65         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 2.41/2.65           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 2.41/2.65      inference('sup+', [status(thm)], ['20', '21'])).
% 2.41/2.65  thf('23', plain,
% 2.41/2.65      (![X0 : $i, X1 : $i]:
% 2.41/2.65         ((k4_xboole_0 @ (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) @ 
% 2.41/2.65           k1_xboole_0)
% 2.41/2.65           = (k3_xboole_0 @ (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) @ X0))),
% 2.41/2.65      inference('sup+', [status(thm)], ['19', '22'])).
% 2.41/2.65  thf('24', plain,
% 2.41/2.65      (![X9 : $i, X10 : $i]: (r1_tarski @ (k3_xboole_0 @ X9 @ X10) @ X9)),
% 2.41/2.65      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.41/2.65  thf(t12_xboole_1, axiom,
% 2.41/2.65    (![A:$i,B:$i]:
% 2.41/2.65     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 2.41/2.65  thf('25', plain,
% 2.41/2.65      (![X7 : $i, X8 : $i]:
% 2.41/2.65         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 2.41/2.65      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.41/2.65  thf('26', plain,
% 2.41/2.65      (![X0 : $i, X1 : $i]:
% 2.41/2.65         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 2.41/2.65      inference('sup-', [status(thm)], ['24', '25'])).
% 2.41/2.65  thf('27', plain,
% 2.41/2.65      (![X0 : $i, X1 : $i]:
% 2.41/2.65         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 2.41/2.65      inference('sup-', [status(thm)], ['24', '25'])).
% 2.41/2.65  thf('28', plain,
% 2.41/2.65      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 2.41/2.65      inference('demod', [status(thm)], ['23', '26', '27'])).
% 2.41/2.65  thf(t51_zfmisc_1, axiom,
% 2.41/2.65    (![A:$i,B:$i]:
% 2.41/2.65     ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_tarski @ B ) ) =>
% 2.41/2.65       ( r2_hidden @ B @ A ) ))).
% 2.41/2.65  thf('29', plain,
% 2.41/2.65      (![X18 : $i, X19 : $i]:
% 2.41/2.65         ((r2_hidden @ X18 @ X19)
% 2.41/2.65          | ((k3_xboole_0 @ X19 @ (k1_tarski @ X18)) != (k1_tarski @ X18)))),
% 2.41/2.65      inference('cnf', [status(esa)], [t51_zfmisc_1])).
% 2.41/2.65  thf('30', plain,
% 2.41/2.65      (![X0 : $i]:
% 2.41/2.65         (((k4_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0) != (k1_tarski @ X0))
% 2.41/2.65          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 2.41/2.65      inference('sup-', [status(thm)], ['28', '29'])).
% 2.41/2.65  thf('31', plain,
% 2.41/2.65      (((((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_tarski @ sk_A))
% 2.41/2.65         | (r2_hidden @ sk_A @ (k1_tarski @ sk_A))))
% 2.41/2.65         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) & 
% 2.41/2.65             (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 2.41/2.65      inference('sup-', [status(thm)], ['16', '30'])).
% 2.41/2.65  thf(t111_relat_1, axiom,
% 2.41/2.65    (![A:$i]: ( ( k7_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 2.41/2.65  thf('32', plain,
% 2.41/2.65      (![X28 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X28) = (k1_xboole_0))),
% 2.41/2.65      inference('cnf', [status(esa)], [t111_relat_1])).
% 2.41/2.65  thf(t87_relat_1, axiom,
% 2.41/2.65    (![A:$i,B:$i]:
% 2.41/2.65     ( ( v1_relat_1 @ B ) =>
% 2.41/2.65       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 2.41/2.65  thf('33', plain,
% 2.41/2.65      (![X34 : $i, X35 : $i]:
% 2.41/2.65         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X34 @ X35)) @ X35)
% 2.41/2.65          | ~ (v1_relat_1 @ X34))),
% 2.41/2.65      inference('cnf', [status(esa)], [t87_relat_1])).
% 2.41/2.65  thf('34', plain,
% 2.41/2.65      (![X0 : $i]:
% 2.41/2.65         ((r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)
% 2.41/2.65          | ~ (v1_relat_1 @ k1_xboole_0))),
% 2.41/2.65      inference('sup+', [status(thm)], ['32', '33'])).
% 2.41/2.65  thf(t60_relat_1, axiom,
% 2.41/2.65    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 2.41/2.65     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 2.41/2.65  thf('35', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.41/2.65      inference('cnf', [status(esa)], [t60_relat_1])).
% 2.41/2.65  thf('36', plain, ((v1_relat_1 @ sk_B)),
% 2.41/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.65  thf(t110_relat_1, axiom,
% 2.41/2.65    (![A:$i]:
% 2.41/2.65     ( ( v1_relat_1 @ A ) =>
% 2.41/2.65       ( ( k7_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 2.41/2.65  thf('37', plain,
% 2.41/2.65      (![X27 : $i]:
% 2.41/2.65         (((k7_relat_1 @ X27 @ k1_xboole_0) = (k1_xboole_0))
% 2.41/2.65          | ~ (v1_relat_1 @ X27))),
% 2.41/2.65      inference('cnf', [status(esa)], [t110_relat_1])).
% 2.41/2.65  thf(dt_k7_relat_1, axiom,
% 2.41/2.65    (![A:$i,B:$i]:
% 2.41/2.65     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 2.41/2.65  thf('38', plain,
% 2.41/2.65      (![X25 : $i, X26 : $i]:
% 2.41/2.65         (~ (v1_relat_1 @ X25) | (v1_relat_1 @ (k7_relat_1 @ X25 @ X26)))),
% 2.41/2.65      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 2.41/2.65  thf('39', plain,
% 2.41/2.65      (![X0 : $i]:
% 2.41/2.65         ((v1_relat_1 @ k1_xboole_0)
% 2.41/2.65          | ~ (v1_relat_1 @ X0)
% 2.41/2.65          | ~ (v1_relat_1 @ X0))),
% 2.41/2.65      inference('sup+', [status(thm)], ['37', '38'])).
% 2.41/2.65  thf('40', plain,
% 2.41/2.65      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 2.41/2.65      inference('simplify', [status(thm)], ['39'])).
% 2.41/2.65  thf('41', plain, ((v1_relat_1 @ k1_xboole_0)),
% 2.41/2.65      inference('sup-', [status(thm)], ['36', '40'])).
% 2.41/2.65  thf('42', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 2.41/2.65      inference('demod', [status(thm)], ['34', '35', '41'])).
% 2.41/2.65  thf('43', plain,
% 2.41/2.65      (![X11 : $i, X13 : $i]:
% 2.41/2.65         (((k4_xboole_0 @ X11 @ X13) = (k1_xboole_0))
% 2.41/2.65          | ~ (r1_tarski @ X11 @ X13))),
% 2.41/2.65      inference('cnf', [status(esa)], [t37_xboole_1])).
% 2.41/2.65  thf('44', plain,
% 2.41/2.65      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.41/2.65      inference('sup-', [status(thm)], ['42', '43'])).
% 2.41/2.65  thf('45', plain,
% 2.41/2.65      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 2.41/2.65         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) & 
% 2.41/2.65             (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 2.41/2.65      inference('simplify', [status(thm)], ['15'])).
% 2.41/2.65  thf('46', plain,
% 2.41/2.65      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 2.41/2.65         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) & 
% 2.41/2.65             (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 2.41/2.65      inference('simplify', [status(thm)], ['15'])).
% 2.41/2.65  thf('47', plain,
% 2.41/2.65      (((((k1_xboole_0) != (k1_xboole_0)) | (r2_hidden @ sk_A @ k1_xboole_0)))
% 2.41/2.65         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) & 
% 2.41/2.65             (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 2.41/2.65      inference('demod', [status(thm)], ['31', '44', '45', '46'])).
% 2.41/2.65  thf('48', plain,
% 2.41/2.65      (((r2_hidden @ sk_A @ k1_xboole_0))
% 2.41/2.65         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) & 
% 2.41/2.65             (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 2.41/2.65      inference('simplify', [status(thm)], ['47'])).
% 2.41/2.65  thf('49', plain,
% 2.41/2.65      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.41/2.65      inference('sup-', [status(thm)], ['42', '43'])).
% 2.41/2.65  thf(t65_zfmisc_1, axiom,
% 2.41/2.65    (![A:$i,B:$i]:
% 2.41/2.65     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 2.41/2.65       ( ~( r2_hidden @ B @ A ) ) ))).
% 2.41/2.65  thf('50', plain,
% 2.41/2.65      (![X22 : $i, X23 : $i]:
% 2.41/2.65         (~ (r2_hidden @ X22 @ X23)
% 2.41/2.65          | ((k4_xboole_0 @ X23 @ (k1_tarski @ X22)) != (X23)))),
% 2.41/2.65      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 2.41/2.65  thf('51', plain,
% 2.41/2.65      (![X0 : $i]:
% 2.41/2.65         (((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 2.41/2.65      inference('sup-', [status(thm)], ['49', '50'])).
% 2.41/2.65  thf('52', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 2.41/2.65      inference('simplify', [status(thm)], ['51'])).
% 2.41/2.65  thf('53', plain,
% 2.41/2.65      (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) | 
% 2.41/2.65       ~ (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))),
% 2.41/2.65      inference('sup-', [status(thm)], ['48', '52'])).
% 2.41/2.65  thf('54', plain,
% 2.41/2.65      (~ (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))),
% 2.41/2.65      inference('sat_resolution*', [status(thm)], ['3', '53'])).
% 2.41/2.65  thf('55', plain,
% 2.41/2.65      (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) != (k1_xboole_0))),
% 2.41/2.65      inference('simpl_trail', [status(thm)], ['2', '54'])).
% 2.41/2.65  thf('56', plain,
% 2.41/2.65      (![X23 : $i, X24 : $i]:
% 2.41/2.65         (((k4_xboole_0 @ X23 @ (k1_tarski @ X24)) = (X23))
% 2.41/2.65          | (r2_hidden @ X24 @ X23))),
% 2.41/2.65      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 2.41/2.65  thf('57', plain,
% 2.41/2.65      (![X16 : $i, X17 : $i]:
% 2.41/2.65         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 2.41/2.65           = (k3_xboole_0 @ X16 @ X17))),
% 2.41/2.65      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.41/2.65  thf('58', plain,
% 2.41/2.65      (![X0 : $i, X1 : $i]:
% 2.41/2.65         (((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 2.41/2.65          | (r2_hidden @ X1 @ X0))),
% 2.41/2.65      inference('sup+', [status(thm)], ['56', '57'])).
% 2.41/2.65  thf(t168_relat_1, axiom,
% 2.41/2.65    (![A:$i,B:$i]:
% 2.41/2.65     ( ( v1_relat_1 @ B ) =>
% 2.41/2.65       ( ( k10_relat_1 @ B @ A ) =
% 2.41/2.65         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 2.41/2.65  thf('59', plain,
% 2.41/2.65      (![X29 : $i, X30 : $i]:
% 2.41/2.65         (((k10_relat_1 @ X29 @ X30)
% 2.41/2.65            = (k10_relat_1 @ X29 @ (k3_xboole_0 @ (k2_relat_1 @ X29) @ X30)))
% 2.41/2.65          | ~ (v1_relat_1 @ X29))),
% 2.41/2.65      inference('cnf', [status(esa)], [t168_relat_1])).
% 2.41/2.65  thf('60', plain,
% 2.41/2.65      (![X0 : $i, X1 : $i]:
% 2.41/2.65         (((k10_relat_1 @ X0 @ (k1_tarski @ X1))
% 2.41/2.65            = (k10_relat_1 @ X0 @ 
% 2.41/2.65               (k4_xboole_0 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 2.41/2.65          | (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 2.41/2.65          | ~ (v1_relat_1 @ X0))),
% 2.41/2.65      inference('sup+', [status(thm)], ['58', '59'])).
% 2.41/2.65  thf('61', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 2.41/2.65      inference('demod', [status(thm)], ['34', '35', '41'])).
% 2.41/2.65  thf('62', plain,
% 2.41/2.65      (![X7 : $i, X8 : $i]:
% 2.41/2.65         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 2.41/2.65      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.41/2.65  thf('63', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.41/2.65      inference('sup-', [status(thm)], ['61', '62'])).
% 2.41/2.65  thf('64', plain,
% 2.41/2.65      (![X14 : $i, X15 : $i]:
% 2.41/2.65         ((k4_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X15)
% 2.41/2.65           = (k4_xboole_0 @ X14 @ X15))),
% 2.41/2.65      inference('cnf', [status(esa)], [t40_xboole_1])).
% 2.41/2.65  thf('65', plain,
% 2.41/2.65      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 2.41/2.65      inference('sup+', [status(thm)], ['63', '64'])).
% 2.41/2.65  thf('66', plain,
% 2.41/2.65      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.41/2.65      inference('sup-', [status(thm)], ['42', '43'])).
% 2.41/2.65  thf('67', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.41/2.65      inference('demod', [status(thm)], ['65', '66'])).
% 2.41/2.65  thf('68', plain,
% 2.41/2.65      (![X0 : $i, X1 : $i]:
% 2.41/2.65         (((k10_relat_1 @ X0 @ (k1_tarski @ X1))
% 2.41/2.65            = (k10_relat_1 @ X0 @ k1_xboole_0))
% 2.41/2.65          | (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 2.41/2.65          | ~ (v1_relat_1 @ X0))),
% 2.41/2.65      inference('demod', [status(thm)], ['60', '67'])).
% 2.41/2.65  thf('69', plain,
% 2.41/2.65      ((~ (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))
% 2.41/2.65         <= (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 2.41/2.65      inference('split', [status(esa)], ['4'])).
% 2.41/2.65  thf('70', plain,
% 2.41/2.65      (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) | 
% 2.41/2.65       (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))),
% 2.41/2.65      inference('split', [status(esa)], ['4'])).
% 2.41/2.65  thf('71', plain, (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 2.41/2.65      inference('sat_resolution*', [status(thm)], ['3', '53', '70'])).
% 2.41/2.65  thf('72', plain, (~ (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 2.41/2.65      inference('simpl_trail', [status(thm)], ['69', '71'])).
% 2.41/2.65  thf('73', plain,
% 2.41/2.65      ((~ (v1_relat_1 @ sk_B)
% 2.41/2.65        | ((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A))
% 2.41/2.65            = (k10_relat_1 @ sk_B @ k1_xboole_0)))),
% 2.41/2.65      inference('sup-', [status(thm)], ['68', '72'])).
% 2.41/2.65  thf('74', plain, ((v1_relat_1 @ sk_B)),
% 2.41/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.65  thf('75', plain,
% 2.41/2.65      (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A))
% 2.41/2.65         = (k10_relat_1 @ sk_B @ k1_xboole_0))),
% 2.41/2.65      inference('demod', [status(thm)], ['73', '74'])).
% 2.41/2.65  thf('76', plain, (((k10_relat_1 @ sk_B @ k1_xboole_0) != (k1_xboole_0))),
% 2.41/2.65      inference('demod', [status(thm)], ['55', '75'])).
% 2.41/2.65  thf('77', plain,
% 2.41/2.65      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_B))),
% 2.41/2.65      inference('sup-', [status(thm)], ['0', '76'])).
% 2.41/2.65  thf('78', plain, ((v1_relat_1 @ sk_B)),
% 2.41/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.65  thf('79', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 2.41/2.65      inference('demod', [status(thm)], ['77', '78'])).
% 2.41/2.65  thf('80', plain, ($false), inference('simplify', [status(thm)], ['79'])).
% 2.41/2.65  
% 2.41/2.65  % SZS output end Refutation
% 2.41/2.65  
% 2.41/2.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
