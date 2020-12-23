%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AD6ym0bWaU

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:41 EST 2020

% Result     : Theorem 45.01s
% Output     : Refutation 45.01s
% Verified   : 
% Statistics : Number of formulae       :  316 ( 786 expanded)
%              Number of leaves         :   37 ( 248 expanded)
%              Depth                    :   37
%              Number of atoms          : 2405 (6160 expanded)
%              Number of equality atoms :  226 ( 657 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('0',plain,(
    ! [X69: $i] :
      ( ( k1_ordinal1 @ X69 )
      = ( k2_xboole_0 @ X69 @ ( k1_tarski @ X69 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('1',plain,(
    ! [X32: $i,X33: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X32 @ X33 ) @ X32 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X27: $i,X29: $i] :
      ( ( ( k4_xboole_0 @ X27 @ X29 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X34 @ X35 ) @ X36 )
      = ( k4_xboole_0 @ X34 @ ( k2_xboole_0 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_ordinal1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ X27 @ X28 )
      | ( ( k4_xboole_0 @ X27 @ X28 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t12_ordinal1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k1_ordinal1 @ A )
        = ( k1_ordinal1 @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k1_ordinal1 @ A )
          = ( k1_ordinal1 @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_ordinal1])).

thf('10',plain,
    ( ( k1_ordinal1 @ sk_A )
    = ( k1_ordinal1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X69: $i] :
      ( ( k1_ordinal1 @ X69 )
      = ( k2_xboole_0 @ X69 @ ( k1_tarski @ X69 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('12',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X37 @ X38 ) @ X39 )
      | ~ ( r1_tarski @ X37 @ ( k2_xboole_0 @ X38 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_ordinal1 @ sk_A ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_B ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X32: $i,X33: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X32 @ X33 ) @ X32 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('17',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k2_xboole_0 @ X31 @ X30 )
        = X30 )
      | ~ ( r1_tarski @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t44_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf('19',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ( X61 = k1_xboole_0 )
      | ( X62 = k1_xboole_0 )
      | ( X61 = X62 )
      | ( ( k1_tarski @ X63 )
       != ( k2_xboole_0 @ X61 @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[t44_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X2 )
       != X0 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
        = X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X2 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X2 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X2 ) @ X1 )
        = ( k1_tarski @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ X24 @ X25 )
      | ( X24 != X25 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('23',plain,(
    ! [X25: $i] :
      ( r1_tarski @ X25 @ X25 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X27: $i,X29: $i] :
      ( ( ( k4_xboole_0 @ X27 @ X29 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('26',plain,(
    ! [X64: $i,X65: $i] :
      ( ~ ( r2_hidden @ X64 @ X65 )
      | ( ( k4_xboole_0 @ X65 @ ( k1_tarski @ X64 ) )
       != X65 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('28',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( X45 != X44 )
      | ( r2_hidden @ X45 @ X46 )
      | ( X46
       != ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('29',plain,(
    ! [X44: $i] :
      ( r2_hidden @ X44 @ ( k1_tarski @ X44 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X2 ) @ X1 )
        = ( k1_tarski @ X2 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X2 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['21','30'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k4_xboole_0 @ X40 @ ( k4_xboole_0 @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k1_ordinal1 @ sk_A )
    = ( k1_ordinal1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X69: $i] :
      ( ( k1_ordinal1 @ X69 )
      = ( k2_xboole_0 @ X69 @ ( k1_tarski @ X69 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('38',plain,(
    ! [X42: $i,X43: $i] :
      ( r1_tarski @ X42 @ ( k2_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('42',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k2_xboole_0 @ X31 @ X30 )
        = X30 )
      | ~ ( r1_tarski @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('44',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X42: $i,X43: $i] :
      ( r1_tarski @ X42 @ ( k2_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('46',plain,(
    ! [X27: $i,X29: $i] :
      ( ( ( k4_xboole_0 @ X27 @ X29 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k4_xboole_0 @ X40 @ ( k4_xboole_0 @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('51',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k4_xboole_0 @ X40 @ ( k4_xboole_0 @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('53',plain,(
    ! [X49: $i] :
      ( ( k2_tarski @ X49 @ X49 )
      = ( k1_tarski @ X49 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('54',plain,(
    ! [X67: $i,X68: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X67 @ X68 ) )
      = ( k3_xboole_0 @ X67 @ X68 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('59',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X34 @ X35 ) @ X36 )
      = ( k4_xboole_0 @ X34 @ ( k2_xboole_0 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ X27 @ X28 )
      | ( ( k4_xboole_0 @ X27 @ X28 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k4_xboole_0 @ X40 @ ( k4_xboole_0 @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('71',plain,(
    ! [X32: $i,X33: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X32 @ X33 ) @ X32 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X24: $i,X26: $i] :
      ( ( X24 = X26 )
      | ~ ( r1_tarski @ X26 @ X24 )
      | ~ ( r1_tarski @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['57','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['56','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['49','77'])).

thf('79',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['44','78'])).

thf('80',plain,(
    ! [X65: $i,X66: $i] :
      ( ( ( k4_xboole_0 @ X65 @ ( k1_tarski @ X66 ) )
        = X65 )
      | ( r2_hidden @ X66 @ X65 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('81',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k4_xboole_0 @ X40 @ ( k4_xboole_0 @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ sk_B @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['79','84'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('86',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('87',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ sk_B @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['85','87'])).

thf('89',plain,(
    ! [X69: $i] :
      ( ( k1_ordinal1 @ X69 )
      = ( k2_xboole_0 @ X69 @ ( k1_tarski @ X69 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('90',plain,
    ( ( k1_ordinal1 @ sk_A )
    = ( k1_ordinal1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('91',plain,(
    ! [X70: $i] :
      ( r2_hidden @ X70 @ ( k1_ordinal1 @ X70 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('92',plain,(
    r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('94',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ ( k1_ordinal1 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['92','94'])).

thf('96',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ X1 )
      | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( k1_ordinal1 @ sk_A ) @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X34 @ X35 ) @ X36 )
      = ( k4_xboole_0 @ X34 @ ( k2_xboole_0 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ X1 )
      | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ ( k1_ordinal1 @ sk_A ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ ( k4_xboole_0 @ ( k1_ordinal1 @ sk_A ) @ ( k1_ordinal1 @ X0 ) ) )
      | ( r2_hidden @ sk_B @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['89','99'])).

thf('101',plain,
    ( ( k1_ordinal1 @ sk_A )
    = ( k1_ordinal1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X69: $i] :
      ( ( k1_ordinal1 @ X69 )
      = ( k2_xboole_0 @ X69 @ ( k1_tarski @ X69 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('103',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X34 @ X35 ) @ X36 )
      = ( k4_xboole_0 @ X34 @ ( k2_xboole_0 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('104',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('105',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X34 @ X35 ) @ X36 )
      = ( k4_xboole_0 @ X34 @ ( k2_xboole_0 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('106',plain,(
    ! [X64: $i,X65: $i] :
      ( ~ ( r2_hidden @ X64 @ X65 )
      | ( ( k4_xboole_0 @ X65 @ ( k1_tarski @ X64 ) )
       != X65 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
       != ( k4_xboole_0 @ X2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
       != ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['104','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['103','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['102','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_B @ ( k4_xboole_0 @ X0 @ ( k1_ordinal1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['101','111'])).

thf('113',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['100','112'])).

thf('114',plain,(
    ! [X44: $i,X46: $i,X47: $i] :
      ( ~ ( r2_hidden @ X47 @ X46 )
      | ( X47 = X44 )
      | ( X46
       != ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('115',plain,(
    ! [X44: $i,X47: $i] :
      ( ( X47 = X44 )
      | ~ ( r2_hidden @ X47 @ ( k1_tarski @ X44 ) ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['113','115'])).

thf('117',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['116','117'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('120',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['88','120'])).

thf('122',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ X27 @ X28 )
      | ( ( k4_xboole_0 @ X27 @ X28 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('123',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k2_xboole_0 @ X31 @ X30 )
        = X30 )
      | ~ ( r1_tarski @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('126',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('128',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X34 @ X35 ) @ X36 )
      = ( k4_xboole_0 @ X34 @ ( k2_xboole_0 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('131',plain,(
    ! [X32: $i,X33: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X32 @ X33 ) @ X32 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('132',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X27: $i,X29: $i] :
      ( ( ( k4_xboole_0 @ X27 @ X29 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['129','134'])).

thf('136',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X34 @ X35 ) @ X36 )
      = ( k4_xboole_0 @ X34 @ ( k2_xboole_0 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('137',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X34 @ X35 ) @ X36 )
      = ( k4_xboole_0 @ X34 @ ( k2_xboole_0 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('138',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ X0 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X34 @ X35 ) @ X36 )
      = ( k4_xboole_0 @ X34 @ ( k2_xboole_0 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('140',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X34 @ X35 ) @ X36 )
      = ( k4_xboole_0 @ X34 @ ( k2_xboole_0 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('141',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X3 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['138','139','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['135','141'])).

thf('143',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k4_xboole_0 @ X40 @ ( k4_xboole_0 @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['56','76'])).

thf('146',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( sk_B
      = ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['126','146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('149',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ X27 @ X28 )
      | ( ( k4_xboole_0 @ X27 @ X28 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k2_xboole_0 @ X31 @ X30 )
        = X30 )
      | ~ ( r1_tarski @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X34 @ X35 ) @ X36 )
      = ( k4_xboole_0 @ X34 @ ( k2_xboole_0 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('156',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['153','156'])).

thf('158',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k4_xboole_0 @ X40 @ ( k4_xboole_0 @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('159',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X34 @ X35 ) @ X36 )
      = ( k4_xboole_0 @ X34 @ ( k2_xboole_0 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('160',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['157','160'])).

thf('162',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ X27 @ X28 )
      | ( ( k4_xboole_0 @ X27 @ X28 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k2_xboole_0 @ X31 @ X30 )
        = X30 )
      | ~ ( r1_tarski @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ sk_A ) )
      = ( k2_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['147','166'])).

thf('168',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['154','155'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['158','159'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ X27 @ X28 )
      | ( ( k4_xboole_0 @ X27 @ X28 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_A ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k4_xboole_0 @ X40 @ ( k4_xboole_0 @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('176',plain,(
    ! [X44: $i] :
      ( r2_hidden @ X44 @ ( k1_tarski @ X44 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('177',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('179',plain,(
    ! [X71: $i,X72: $i] :
      ( ~ ( r2_hidden @ X71 @ X72 )
      | ~ ( r1_tarski @ X72 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) @ X1 )
      | ( r2_hidden @ X1 @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['175','180'])).

thf('182',plain,(
    r2_hidden @ sk_A @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['174','181'])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('184',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
       != ( k4_xboole_0 @ X2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
       != ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    k1_xboole_0
 != ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['182','185'])).

thf('187',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( k1_xboole_0
      = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','186'])).

thf('188',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(simplify,[status(thm)],['187'])).

thf('189',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k4_xboole_0 @ X40 @ ( k4_xboole_0 @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('190',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ X27 @ X28 )
      | ( ( k4_xboole_0 @ X27 @ X28 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['188','191'])).

thf('193',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(simplify,[status(thm)],['192'])).

thf('194',plain,(
    ! [X32: $i,X33: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X32 @ X33 ) @ X32 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('195',plain,(
    ! [X24: $i,X26: $i] :
      ( ( X24 = X26 )
      | ~ ( r1_tarski @ X26 @ X24 )
      | ~ ( r1_tarski @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,
    ( ( k1_tarski @ sk_A )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['193','196'])).

thf('198',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['15','197'])).

thf('199',plain,(
    ! [X27: $i,X29: $i] :
      ( ( ( k4_xboole_0 @ X27 @ X29 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('200',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X34 @ X35 ) @ X36 )
      = ( k4_xboole_0 @ X34 @ ( k2_xboole_0 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('202',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('203',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['201','202'])).

thf('204',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('205',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( r2_hidden @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['203','204'])).

thf('206',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('207',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('208',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['207'])).

thf('209',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['206','208'])).

thf('210',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['209'])).

thf('211',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['205','210'])).

thf('212',plain,(
    ! [X71: $i,X72: $i] :
      ( ~ ( r2_hidden @ X71 @ X72 )
      | ~ ( r1_tarski @ X72 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('213',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) @ X1 ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    ~ ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['200','213'])).

thf('215',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['56','76'])).

thf('216',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X34 @ X35 ) @ X36 )
      = ( k4_xboole_0 @ X34 @ ( k2_xboole_0 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('217',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['215','216'])).

thf('218',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('219',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['217','218'])).

thf('220',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ X27 @ X28 )
      | ( ( k4_xboole_0 @ X27 @ X28 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('221',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['219','220'])).

thf('222',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['221'])).

thf('223',plain,(
    ! [X42: $i,X43: $i] :
      ( r1_tarski @ X42 @ ( k2_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('224',plain,(
    ! [X24: $i,X26: $i] :
      ( ( X24 = X26 )
      | ~ ( r1_tarski @ X26 @ X24 )
      | ~ ( r1_tarski @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('225',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['223','224'])).

thf('226',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['222','225'])).

thf('227',plain,(
    ! [X44: $i] :
      ( r2_hidden @ X44 @ ( k1_tarski @ X44 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('228',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X2 ) @ X1 )
        = ( k1_tarski @ X2 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X2 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['21','30'])).

thf('229',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['116','117'])).

thf('230',plain,(
    ! [X70: $i] :
      ( r2_hidden @ X70 @ ( k1_ordinal1 @ X70 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('231',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('232',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_ordinal1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['230','231'])).

thf('233',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X34 @ X35 ) @ X36 )
      = ( k4_xboole_0 @ X34 @ ( k2_xboole_0 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('234',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['207'])).

thf('235',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['233','234'])).

thf('236',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['232','235'])).

thf('237',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_B @ ( k2_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['229','236'])).

thf('238',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('239',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ X27 @ X28 )
      | ( ( k4_xboole_0 @ X27 @ X28 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('240',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      | ( r1_tarski @ ( k1_tarski @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['238','239'])).

thf('241',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X1 ) @ X0 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['240'])).

thf('242',plain,(
    ! [X44: $i] :
      ( r2_hidden @ X44 @ ( k1_tarski @ X44 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('243',plain,(
    ! [X71: $i,X72: $i] :
      ( ~ ( r2_hidden @ X71 @ X72 )
      | ~ ( r1_tarski @ X72 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('244',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['242','243'])).

thf('245',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['241','244'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('246',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C @ X12 @ X11 ) @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('247',plain,(
    ! [X71: $i,X72: $i] :
      ( ~ ( r2_hidden @ X71 @ X72 )
      | ~ ( r1_tarski @ X72 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('248',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( sk_C @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['246','247'])).

thf('249',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( sk_C @ X0 @ ( k1_tarski @ X0 ) ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['245','248'])).

thf('250',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf('251',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['249','250'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('252',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('253',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['251','252'])).

thf('254',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('255',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['209'])).

thf('256',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['254','255'])).

thf('257',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('258',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['256','257'])).

thf('259',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k3_xboole_0 @ X11 @ X14 ) )
      | ~ ( r1_xboole_0 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('260',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['258','259'])).

thf('261',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['253','260'])).

thf('262',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('263',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['261','262'])).

thf('264',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['263'])).

thf('265',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('266',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['264','265'])).

thf('267',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X34 @ X35 ) @ X36 )
      = ( k4_xboole_0 @ X34 @ ( k2_xboole_0 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('268',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['266','267'])).

thf('269',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['207'])).

thf('270',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['268','269'])).

thf('271',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_B @ ( k4_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['237','270'])).

thf('272',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B @ ( k1_tarski @ X0 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['228','271'])).

thf('273',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['227','272'])).

thf('274',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ X27 @ X28 )
      | ( ( k4_xboole_0 @ X27 @ X28 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('275',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['273','274'])).

thf('276',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference(simplify,[status(thm)],['275'])).

thf('277',plain,(
    $false ),
    inference(demod,[status(thm)],['214','226','276'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AD6ym0bWaU
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:15:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 45.01/45.26  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 45.01/45.26  % Solved by: fo/fo7.sh
% 45.01/45.26  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 45.01/45.26  % done 40630 iterations in 44.789s
% 45.01/45.26  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 45.01/45.26  % SZS output start Refutation
% 45.01/45.26  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 45.01/45.26  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 45.01/45.26  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 45.01/45.26  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 45.01/45.26  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 45.01/45.26  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 45.01/45.26  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 45.01/45.26  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 45.01/45.26  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 45.01/45.26  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 45.01/45.26  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 45.01/45.26  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 45.01/45.26  thf(sk_B_type, type, sk_B: $i).
% 45.01/45.26  thf(sk_A_type, type, sk_A: $i).
% 45.01/45.26  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 45.01/45.26  thf(d1_ordinal1, axiom,
% 45.01/45.26    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 45.01/45.26  thf('0', plain,
% 45.01/45.26      (![X69 : $i]:
% 45.01/45.26         ((k1_ordinal1 @ X69) = (k2_xboole_0 @ X69 @ (k1_tarski @ X69)))),
% 45.01/45.26      inference('cnf', [status(esa)], [d1_ordinal1])).
% 45.01/45.26  thf(t36_xboole_1, axiom,
% 45.01/45.26    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 45.01/45.26  thf('1', plain,
% 45.01/45.26      (![X32 : $i, X33 : $i]: (r1_tarski @ (k4_xboole_0 @ X32 @ X33) @ X32)),
% 45.01/45.26      inference('cnf', [status(esa)], [t36_xboole_1])).
% 45.01/45.26  thf(l32_xboole_1, axiom,
% 45.01/45.26    (![A:$i,B:$i]:
% 45.01/45.26     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 45.01/45.26  thf('2', plain,
% 45.01/45.26      (![X27 : $i, X29 : $i]:
% 45.01/45.26         (((k4_xboole_0 @ X27 @ X29) = (k1_xboole_0))
% 45.01/45.26          | ~ (r1_tarski @ X27 @ X29))),
% 45.01/45.26      inference('cnf', [status(esa)], [l32_xboole_1])).
% 45.01/45.26  thf('3', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 45.01/45.26      inference('sup-', [status(thm)], ['1', '2'])).
% 45.01/45.26  thf(t41_xboole_1, axiom,
% 45.01/45.26    (![A:$i,B:$i,C:$i]:
% 45.01/45.26     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 45.01/45.26       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 45.01/45.26  thf('4', plain,
% 45.01/45.26      (![X34 : $i, X35 : $i, X36 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ (k4_xboole_0 @ X34 @ X35) @ X36)
% 45.01/45.26           = (k4_xboole_0 @ X34 @ (k2_xboole_0 @ X35 @ X36)))),
% 45.01/45.26      inference('cnf', [status(esa)], [t41_xboole_1])).
% 45.01/45.26  thf('5', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 45.01/45.26      inference('demod', [status(thm)], ['3', '4'])).
% 45.01/45.26  thf('6', plain,
% 45.01/45.26      (![X0 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_ordinal1 @ X0)) = (k1_xboole_0))),
% 45.01/45.26      inference('sup+', [status(thm)], ['0', '5'])).
% 45.01/45.26  thf('7', plain,
% 45.01/45.26      (![X27 : $i, X28 : $i]:
% 45.01/45.26         ((r1_tarski @ X27 @ X28)
% 45.01/45.26          | ((k4_xboole_0 @ X27 @ X28) != (k1_xboole_0)))),
% 45.01/45.26      inference('cnf', [status(esa)], [l32_xboole_1])).
% 45.01/45.26  thf('8', plain,
% 45.01/45.26      (![X0 : $i]:
% 45.01/45.26         (((k1_xboole_0) != (k1_xboole_0))
% 45.01/45.26          | (r1_tarski @ (k1_tarski @ X0) @ (k1_ordinal1 @ X0)))),
% 45.01/45.26      inference('sup-', [status(thm)], ['6', '7'])).
% 45.01/45.26  thf('9', plain,
% 45.01/45.26      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_ordinal1 @ X0))),
% 45.01/45.26      inference('simplify', [status(thm)], ['8'])).
% 45.01/45.26  thf(t12_ordinal1, conjecture,
% 45.01/45.26    (![A:$i,B:$i]:
% 45.01/45.26     ( ( ( k1_ordinal1 @ A ) = ( k1_ordinal1 @ B ) ) => ( ( A ) = ( B ) ) ))).
% 45.01/45.26  thf(zf_stmt_0, negated_conjecture,
% 45.01/45.26    (~( ![A:$i,B:$i]:
% 45.01/45.26        ( ( ( k1_ordinal1 @ A ) = ( k1_ordinal1 @ B ) ) => ( ( A ) = ( B ) ) ) )),
% 45.01/45.26    inference('cnf.neg', [status(esa)], [t12_ordinal1])).
% 45.01/45.26  thf('10', plain, (((k1_ordinal1 @ sk_A) = (k1_ordinal1 @ sk_B))),
% 45.01/45.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.01/45.26  thf('11', plain,
% 45.01/45.26      (![X69 : $i]:
% 45.01/45.26         ((k1_ordinal1 @ X69) = (k2_xboole_0 @ X69 @ (k1_tarski @ X69)))),
% 45.01/45.26      inference('cnf', [status(esa)], [d1_ordinal1])).
% 45.01/45.26  thf(t43_xboole_1, axiom,
% 45.01/45.26    (![A:$i,B:$i,C:$i]:
% 45.01/45.26     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 45.01/45.26       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 45.01/45.26  thf('12', plain,
% 45.01/45.26      (![X37 : $i, X38 : $i, X39 : $i]:
% 45.01/45.26         ((r1_tarski @ (k4_xboole_0 @ X37 @ X38) @ X39)
% 45.01/45.26          | ~ (r1_tarski @ X37 @ (k2_xboole_0 @ X38 @ X39)))),
% 45.01/45.26      inference('cnf', [status(esa)], [t43_xboole_1])).
% 45.01/45.26  thf('13', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         (~ (r1_tarski @ X1 @ (k1_ordinal1 @ X0))
% 45.01/45.26          | (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k1_tarski @ X0)))),
% 45.01/45.26      inference('sup-', [status(thm)], ['11', '12'])).
% 45.01/45.26  thf('14', plain,
% 45.01/45.26      (![X0 : $i]:
% 45.01/45.26         (~ (r1_tarski @ X0 @ (k1_ordinal1 @ sk_A))
% 45.01/45.26          | (r1_tarski @ (k4_xboole_0 @ X0 @ sk_B) @ (k1_tarski @ sk_B)))),
% 45.01/45.26      inference('sup-', [status(thm)], ['10', '13'])).
% 45.01/45.26  thf('15', plain,
% 45.01/45.26      ((r1_tarski @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 45.01/45.26        (k1_tarski @ sk_B))),
% 45.01/45.26      inference('sup-', [status(thm)], ['9', '14'])).
% 45.01/45.26  thf('16', plain,
% 45.01/45.26      (![X32 : $i, X33 : $i]: (r1_tarski @ (k4_xboole_0 @ X32 @ X33) @ X32)),
% 45.01/45.26      inference('cnf', [status(esa)], [t36_xboole_1])).
% 45.01/45.26  thf(t12_xboole_1, axiom,
% 45.01/45.26    (![A:$i,B:$i]:
% 45.01/45.26     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 45.01/45.26  thf('17', plain,
% 45.01/45.26      (![X30 : $i, X31 : $i]:
% 45.01/45.26         (((k2_xboole_0 @ X31 @ X30) = (X30)) | ~ (r1_tarski @ X31 @ X30))),
% 45.01/45.26      inference('cnf', [status(esa)], [t12_xboole_1])).
% 45.01/45.26  thf('18', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 45.01/45.26      inference('sup-', [status(thm)], ['16', '17'])).
% 45.01/45.26  thf(t44_zfmisc_1, axiom,
% 45.01/45.26    (![A:$i,B:$i,C:$i]:
% 45.01/45.26     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 45.01/45.26          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 45.01/45.26          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 45.01/45.26  thf('19', plain,
% 45.01/45.26      (![X61 : $i, X62 : $i, X63 : $i]:
% 45.01/45.26         (((X61) = (k1_xboole_0))
% 45.01/45.26          | ((X62) = (k1_xboole_0))
% 45.01/45.26          | ((X61) = (X62))
% 45.01/45.26          | ((k1_tarski @ X63) != (k2_xboole_0 @ X61 @ X62)))),
% 45.01/45.26      inference('cnf', [status(esa)], [t44_zfmisc_1])).
% 45.01/45.26  thf('20', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.01/45.26         (((k1_tarski @ X2) != (X0))
% 45.01/45.26          | ((k4_xboole_0 @ X0 @ X1) = (X0))
% 45.01/45.26          | ((X0) = (k1_xboole_0))
% 45.01/45.26          | ((k4_xboole_0 @ X0 @ X1) = (k1_xboole_0)))),
% 45.01/45.26      inference('sup-', [status(thm)], ['18', '19'])).
% 45.01/45.26  thf('21', plain,
% 45.01/45.26      (![X1 : $i, X2 : $i]:
% 45.01/45.26         (((k4_xboole_0 @ (k1_tarski @ X2) @ X1) = (k1_xboole_0))
% 45.01/45.26          | ((k1_tarski @ X2) = (k1_xboole_0))
% 45.01/45.26          | ((k4_xboole_0 @ (k1_tarski @ X2) @ X1) = (k1_tarski @ X2)))),
% 45.01/45.26      inference('simplify', [status(thm)], ['20'])).
% 45.01/45.26  thf(d10_xboole_0, axiom,
% 45.01/45.26    (![A:$i,B:$i]:
% 45.01/45.26     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 45.01/45.26  thf('22', plain,
% 45.01/45.26      (![X24 : $i, X25 : $i]: ((r1_tarski @ X24 @ X25) | ((X24) != (X25)))),
% 45.01/45.26      inference('cnf', [status(esa)], [d10_xboole_0])).
% 45.01/45.26  thf('23', plain, (![X25 : $i]: (r1_tarski @ X25 @ X25)),
% 45.01/45.26      inference('simplify', [status(thm)], ['22'])).
% 45.01/45.26  thf('24', plain,
% 45.01/45.26      (![X27 : $i, X29 : $i]:
% 45.01/45.26         (((k4_xboole_0 @ X27 @ X29) = (k1_xboole_0))
% 45.01/45.26          | ~ (r1_tarski @ X27 @ X29))),
% 45.01/45.26      inference('cnf', [status(esa)], [l32_xboole_1])).
% 45.01/45.26  thf('25', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 45.01/45.26      inference('sup-', [status(thm)], ['23', '24'])).
% 45.01/45.26  thf(t65_zfmisc_1, axiom,
% 45.01/45.26    (![A:$i,B:$i]:
% 45.01/45.26     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 45.01/45.26       ( ~( r2_hidden @ B @ A ) ) ))).
% 45.01/45.26  thf('26', plain,
% 45.01/45.26      (![X64 : $i, X65 : $i]:
% 45.01/45.26         (~ (r2_hidden @ X64 @ X65)
% 45.01/45.26          | ((k4_xboole_0 @ X65 @ (k1_tarski @ X64)) != (X65)))),
% 45.01/45.26      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 45.01/45.26  thf('27', plain,
% 45.01/45.26      (![X0 : $i]:
% 45.01/45.26         (((k1_xboole_0) != (k1_tarski @ X0))
% 45.01/45.26          | ~ (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 45.01/45.26      inference('sup-', [status(thm)], ['25', '26'])).
% 45.01/45.26  thf(d1_tarski, axiom,
% 45.01/45.26    (![A:$i,B:$i]:
% 45.01/45.26     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 45.01/45.26       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 45.01/45.26  thf('28', plain,
% 45.01/45.26      (![X44 : $i, X45 : $i, X46 : $i]:
% 45.01/45.26         (((X45) != (X44))
% 45.01/45.26          | (r2_hidden @ X45 @ X46)
% 45.01/45.26          | ((X46) != (k1_tarski @ X44)))),
% 45.01/45.26      inference('cnf', [status(esa)], [d1_tarski])).
% 45.01/45.26  thf('29', plain, (![X44 : $i]: (r2_hidden @ X44 @ (k1_tarski @ X44))),
% 45.01/45.26      inference('simplify', [status(thm)], ['28'])).
% 45.01/45.26  thf('30', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 45.01/45.26      inference('demod', [status(thm)], ['27', '29'])).
% 45.01/45.26  thf('31', plain,
% 45.01/45.26      (![X1 : $i, X2 : $i]:
% 45.01/45.26         (((k4_xboole_0 @ (k1_tarski @ X2) @ X1) = (k1_tarski @ X2))
% 45.01/45.26          | ((k4_xboole_0 @ (k1_tarski @ X2) @ X1) = (k1_xboole_0)))),
% 45.01/45.26      inference('clc', [status(thm)], ['21', '30'])).
% 45.01/45.26  thf(t48_xboole_1, axiom,
% 45.01/45.26    (![A:$i,B:$i]:
% 45.01/45.26     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 45.01/45.26  thf('32', plain,
% 45.01/45.26      (![X40 : $i, X41 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ X40 @ (k4_xboole_0 @ X40 @ X41))
% 45.01/45.26           = (k3_xboole_0 @ X40 @ X41))),
% 45.01/45.26      inference('cnf', [status(esa)], [t48_xboole_1])).
% 45.01/45.26  thf('33', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         (((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 45.01/45.26            = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 45.01/45.26          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 45.01/45.26      inference('sup+', [status(thm)], ['31', '32'])).
% 45.01/45.26  thf('34', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 45.01/45.26      inference('sup-', [status(thm)], ['23', '24'])).
% 45.01/45.26  thf('35', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         (((k1_xboole_0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 45.01/45.26          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 45.01/45.26      inference('demod', [status(thm)], ['33', '34'])).
% 45.01/45.26  thf('36', plain, (((k1_ordinal1 @ sk_A) = (k1_ordinal1 @ sk_B))),
% 45.01/45.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.01/45.26  thf('37', plain,
% 45.01/45.26      (![X69 : $i]:
% 45.01/45.26         ((k1_ordinal1 @ X69) = (k2_xboole_0 @ X69 @ (k1_tarski @ X69)))),
% 45.01/45.26      inference('cnf', [status(esa)], [d1_ordinal1])).
% 45.01/45.26  thf(t7_xboole_1, axiom,
% 45.01/45.26    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 45.01/45.26  thf('38', plain,
% 45.01/45.26      (![X42 : $i, X43 : $i]: (r1_tarski @ X42 @ (k2_xboole_0 @ X42 @ X43))),
% 45.01/45.26      inference('cnf', [status(esa)], [t7_xboole_1])).
% 45.01/45.26  thf('39', plain, (![X0 : $i]: (r1_tarski @ X0 @ (k1_ordinal1 @ X0))),
% 45.01/45.26      inference('sup+', [status(thm)], ['37', '38'])).
% 45.01/45.26  thf('40', plain, ((r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A))),
% 45.01/45.26      inference('sup+', [status(thm)], ['36', '39'])).
% 45.01/45.26  thf('41', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         (~ (r1_tarski @ X1 @ (k1_ordinal1 @ X0))
% 45.01/45.26          | (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k1_tarski @ X0)))),
% 45.01/45.26      inference('sup-', [status(thm)], ['11', '12'])).
% 45.01/45.26  thf('42', plain,
% 45.01/45.26      ((r1_tarski @ (k4_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_A))),
% 45.01/45.26      inference('sup-', [status(thm)], ['40', '41'])).
% 45.01/45.26  thf('43', plain,
% 45.01/45.26      (![X30 : $i, X31 : $i]:
% 45.01/45.26         (((k2_xboole_0 @ X31 @ X30) = (X30)) | ~ (r1_tarski @ X31 @ X30))),
% 45.01/45.26      inference('cnf', [status(esa)], [t12_xboole_1])).
% 45.01/45.26  thf('44', plain,
% 45.01/45.26      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_A))
% 45.01/45.26         = (k1_tarski @ sk_A))),
% 45.01/45.26      inference('sup-', [status(thm)], ['42', '43'])).
% 45.01/45.26  thf('45', plain,
% 45.01/45.26      (![X42 : $i, X43 : $i]: (r1_tarski @ X42 @ (k2_xboole_0 @ X42 @ X43))),
% 45.01/45.26      inference('cnf', [status(esa)], [t7_xboole_1])).
% 45.01/45.26  thf('46', plain,
% 45.01/45.26      (![X27 : $i, X29 : $i]:
% 45.01/45.26         (((k4_xboole_0 @ X27 @ X29) = (k1_xboole_0))
% 45.01/45.26          | ~ (r1_tarski @ X27 @ X29))),
% 45.01/45.26      inference('cnf', [status(esa)], [l32_xboole_1])).
% 45.01/45.26  thf('47', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 45.01/45.26      inference('sup-', [status(thm)], ['45', '46'])).
% 45.01/45.26  thf('48', plain,
% 45.01/45.26      (![X40 : $i, X41 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ X40 @ (k4_xboole_0 @ X40 @ X41))
% 45.01/45.26           = (k3_xboole_0 @ X40 @ X41))),
% 45.01/45.26      inference('cnf', [status(esa)], [t48_xboole_1])).
% 45.01/45.26  thf('49', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 45.01/45.26           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 45.01/45.26      inference('sup+', [status(thm)], ['47', '48'])).
% 45.01/45.26  thf('50', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 45.01/45.26      inference('sup-', [status(thm)], ['23', '24'])).
% 45.01/45.26  thf('51', plain,
% 45.01/45.26      (![X40 : $i, X41 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ X40 @ (k4_xboole_0 @ X40 @ X41))
% 45.01/45.26           = (k3_xboole_0 @ X40 @ X41))),
% 45.01/45.26      inference('cnf', [status(esa)], [t48_xboole_1])).
% 45.01/45.26  thf('52', plain,
% 45.01/45.26      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 45.01/45.26      inference('sup+', [status(thm)], ['50', '51'])).
% 45.01/45.26  thf(t69_enumset1, axiom,
% 45.01/45.26    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 45.01/45.26  thf('53', plain,
% 45.01/45.26      (![X49 : $i]: ((k2_tarski @ X49 @ X49) = (k1_tarski @ X49))),
% 45.01/45.26      inference('cnf', [status(esa)], [t69_enumset1])).
% 45.01/45.26  thf(t12_setfam_1, axiom,
% 45.01/45.26    (![A:$i,B:$i]:
% 45.01/45.26     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 45.01/45.26  thf('54', plain,
% 45.01/45.26      (![X67 : $i, X68 : $i]:
% 45.01/45.26         ((k1_setfam_1 @ (k2_tarski @ X67 @ X68)) = (k3_xboole_0 @ X67 @ X68))),
% 45.01/45.26      inference('cnf', [status(esa)], [t12_setfam_1])).
% 45.01/45.26  thf('55', plain,
% 45.01/45.26      (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 45.01/45.26      inference('sup+', [status(thm)], ['53', '54'])).
% 45.01/45.26  thf('56', plain,
% 45.01/45.26      (![X0 : $i]:
% 45.01/45.26         ((k1_setfam_1 @ (k1_tarski @ X0)) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 45.01/45.26      inference('sup+', [status(thm)], ['52', '55'])).
% 45.01/45.26  thf('57', plain,
% 45.01/45.26      (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 45.01/45.26      inference('sup+', [status(thm)], ['53', '54'])).
% 45.01/45.26  thf('58', plain,
% 45.01/45.26      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 45.01/45.26      inference('sup+', [status(thm)], ['50', '51'])).
% 45.01/45.26  thf('59', plain,
% 45.01/45.26      (![X34 : $i, X35 : $i, X36 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ (k4_xboole_0 @ X34 @ X35) @ X36)
% 45.01/45.26           = (k4_xboole_0 @ X34 @ (k2_xboole_0 @ X35 @ X36)))),
% 45.01/45.26      inference('cnf', [status(esa)], [t41_xboole_1])).
% 45.01/45.26  thf('60', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ X1)
% 45.01/45.26           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X1)))),
% 45.01/45.26      inference('sup+', [status(thm)], ['58', '59'])).
% 45.01/45.26  thf('61', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 45.01/45.26      inference('sup-', [status(thm)], ['23', '24'])).
% 45.01/45.26  thf('62', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 45.01/45.26      inference('sup-', [status(thm)], ['16', '17'])).
% 45.01/45.26  thf('63', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 45.01/45.26      inference('sup+', [status(thm)], ['61', '62'])).
% 45.01/45.26  thf('64', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ X1)
% 45.01/45.26           = (k4_xboole_0 @ X0 @ X1))),
% 45.01/45.26      inference('demod', [status(thm)], ['60', '63'])).
% 45.01/45.26  thf('65', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 45.01/45.26      inference('sup-', [status(thm)], ['23', '24'])).
% 45.01/45.26  thf('66', plain,
% 45.01/45.26      (![X0 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 45.01/45.26      inference('sup+', [status(thm)], ['64', '65'])).
% 45.01/45.26  thf('67', plain,
% 45.01/45.26      (![X27 : $i, X28 : $i]:
% 45.01/45.26         ((r1_tarski @ X27 @ X28)
% 45.01/45.26          | ((k4_xboole_0 @ X27 @ X28) != (k1_xboole_0)))),
% 45.01/45.26      inference('cnf', [status(esa)], [l32_xboole_1])).
% 45.01/45.26  thf('68', plain,
% 45.01/45.26      (![X0 : $i]:
% 45.01/45.26         (((k1_xboole_0) != (k1_xboole_0))
% 45.01/45.26          | (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X0)))),
% 45.01/45.26      inference('sup-', [status(thm)], ['66', '67'])).
% 45.01/45.26  thf('69', plain, (![X0 : $i]: (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X0))),
% 45.01/45.26      inference('simplify', [status(thm)], ['68'])).
% 45.01/45.26  thf('70', plain,
% 45.01/45.26      (![X40 : $i, X41 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ X40 @ (k4_xboole_0 @ X40 @ X41))
% 45.01/45.26           = (k3_xboole_0 @ X40 @ X41))),
% 45.01/45.26      inference('cnf', [status(esa)], [t48_xboole_1])).
% 45.01/45.26  thf('71', plain,
% 45.01/45.26      (![X32 : $i, X33 : $i]: (r1_tarski @ (k4_xboole_0 @ X32 @ X33) @ X32)),
% 45.01/45.26      inference('cnf', [status(esa)], [t36_xboole_1])).
% 45.01/45.26  thf('72', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 45.01/45.26      inference('sup+', [status(thm)], ['70', '71'])).
% 45.01/45.26  thf('73', plain,
% 45.01/45.26      (![X24 : $i, X26 : $i]:
% 45.01/45.26         (((X24) = (X26))
% 45.01/45.26          | ~ (r1_tarski @ X26 @ X24)
% 45.01/45.26          | ~ (r1_tarski @ X24 @ X26))),
% 45.01/45.26      inference('cnf', [status(esa)], [d10_xboole_0])).
% 45.01/45.26  thf('74', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 45.01/45.26          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 45.01/45.26      inference('sup-', [status(thm)], ['72', '73'])).
% 45.01/45.26  thf('75', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 45.01/45.26      inference('sup-', [status(thm)], ['69', '74'])).
% 45.01/45.26  thf('76', plain, (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (X0))),
% 45.01/45.26      inference('demod', [status(thm)], ['57', '75'])).
% 45.01/45.26  thf('77', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 45.01/45.26      inference('demod', [status(thm)], ['56', '76'])).
% 45.01/45.26  thf('78', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 45.01/45.26      inference('demod', [status(thm)], ['49', '77'])).
% 45.01/45.26  thf('79', plain,
% 45.01/45.26      (((k4_xboole_0 @ sk_B @ sk_A)
% 45.01/45.26         = (k3_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_A)))),
% 45.01/45.26      inference('sup+', [status(thm)], ['44', '78'])).
% 45.01/45.26  thf('80', plain,
% 45.01/45.26      (![X65 : $i, X66 : $i]:
% 45.01/45.26         (((k4_xboole_0 @ X65 @ (k1_tarski @ X66)) = (X65))
% 45.01/45.26          | (r2_hidden @ X66 @ X65))),
% 45.01/45.26      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 45.01/45.26  thf('81', plain,
% 45.01/45.26      (![X40 : $i, X41 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ X40 @ (k4_xboole_0 @ X40 @ X41))
% 45.01/45.26           = (k3_xboole_0 @ X40 @ X41))),
% 45.01/45.26      inference('cnf', [status(esa)], [t48_xboole_1])).
% 45.01/45.26  thf('82', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         (((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 45.01/45.26          | (r2_hidden @ X1 @ X0))),
% 45.01/45.26      inference('sup+', [status(thm)], ['80', '81'])).
% 45.01/45.26  thf('83', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 45.01/45.26      inference('sup-', [status(thm)], ['23', '24'])).
% 45.01/45.26  thf('84', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         (((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 45.01/45.26          | (r2_hidden @ X1 @ X0))),
% 45.01/45.26      inference('demod', [status(thm)], ['82', '83'])).
% 45.01/45.26  thf('85', plain,
% 45.01/45.26      ((((k1_xboole_0) = (k4_xboole_0 @ sk_B @ sk_A))
% 45.01/45.26        | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A)))),
% 45.01/45.26      inference('sup+', [status(thm)], ['79', '84'])).
% 45.01/45.26  thf(d5_xboole_0, axiom,
% 45.01/45.26    (![A:$i,B:$i,C:$i]:
% 45.01/45.26     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 45.01/45.26       ( ![D:$i]:
% 45.01/45.26         ( ( r2_hidden @ D @ C ) <=>
% 45.01/45.26           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 45.01/45.26  thf('86', plain,
% 45.01/45.26      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 45.01/45.26         (~ (r2_hidden @ X6 @ X5)
% 45.01/45.26          | (r2_hidden @ X6 @ X3)
% 45.01/45.26          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 45.01/45.26      inference('cnf', [status(esa)], [d5_xboole_0])).
% 45.01/45.26  thf('87', plain,
% 45.01/45.26      (![X3 : $i, X4 : $i, X6 : $i]:
% 45.01/45.26         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 45.01/45.26      inference('simplify', [status(thm)], ['86'])).
% 45.01/45.26  thf('88', plain,
% 45.01/45.26      ((((k1_xboole_0) = (k4_xboole_0 @ sk_B @ sk_A))
% 45.01/45.26        | (r2_hidden @ sk_A @ sk_B))),
% 45.01/45.26      inference('sup-', [status(thm)], ['85', '87'])).
% 45.01/45.26  thf('89', plain,
% 45.01/45.26      (![X69 : $i]:
% 45.01/45.26         ((k1_ordinal1 @ X69) = (k2_xboole_0 @ X69 @ (k1_tarski @ X69)))),
% 45.01/45.26      inference('cnf', [status(esa)], [d1_ordinal1])).
% 45.01/45.26  thf('90', plain, (((k1_ordinal1 @ sk_A) = (k1_ordinal1 @ sk_B))),
% 45.01/45.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.01/45.26  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 45.01/45.26  thf('91', plain, (![X70 : $i]: (r2_hidden @ X70 @ (k1_ordinal1 @ X70))),
% 45.01/45.26      inference('cnf', [status(esa)], [t10_ordinal1])).
% 45.01/45.26  thf('92', plain, ((r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))),
% 45.01/45.26      inference('sup+', [status(thm)], ['90', '91'])).
% 45.01/45.26  thf('93', plain,
% 45.01/45.26      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 45.01/45.26         (~ (r2_hidden @ X2 @ X3)
% 45.01/45.26          | (r2_hidden @ X2 @ X4)
% 45.01/45.26          | (r2_hidden @ X2 @ X5)
% 45.01/45.26          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 45.01/45.26      inference('cnf', [status(esa)], [d5_xboole_0])).
% 45.01/45.26  thf('94', plain,
% 45.01/45.26      (![X2 : $i, X3 : $i, X4 : $i]:
% 45.01/45.26         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 45.01/45.26          | (r2_hidden @ X2 @ X4)
% 45.01/45.26          | ~ (r2_hidden @ X2 @ X3))),
% 45.01/45.26      inference('simplify', [status(thm)], ['93'])).
% 45.01/45.26  thf('95', plain,
% 45.01/45.26      (![X0 : $i]:
% 45.01/45.26         ((r2_hidden @ sk_B @ X0)
% 45.01/45.26          | (r2_hidden @ sk_B @ (k4_xboole_0 @ (k1_ordinal1 @ sk_A) @ X0)))),
% 45.01/45.26      inference('sup-', [status(thm)], ['92', '94'])).
% 45.01/45.26  thf('96', plain,
% 45.01/45.26      (![X2 : $i, X3 : $i, X4 : $i]:
% 45.01/45.26         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 45.01/45.26          | (r2_hidden @ X2 @ X4)
% 45.01/45.26          | ~ (r2_hidden @ X2 @ X3))),
% 45.01/45.26      inference('simplify', [status(thm)], ['93'])).
% 45.01/45.26  thf('97', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         ((r2_hidden @ sk_B @ X0)
% 45.01/45.26          | (r2_hidden @ sk_B @ X1)
% 45.01/45.26          | (r2_hidden @ sk_B @ 
% 45.01/45.26             (k4_xboole_0 @ (k4_xboole_0 @ (k1_ordinal1 @ sk_A) @ X0) @ X1)))),
% 45.01/45.26      inference('sup-', [status(thm)], ['95', '96'])).
% 45.01/45.26  thf('98', plain,
% 45.01/45.26      (![X34 : $i, X35 : $i, X36 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ (k4_xboole_0 @ X34 @ X35) @ X36)
% 45.01/45.26           = (k4_xboole_0 @ X34 @ (k2_xboole_0 @ X35 @ X36)))),
% 45.01/45.26      inference('cnf', [status(esa)], [t41_xboole_1])).
% 45.01/45.26  thf('99', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         ((r2_hidden @ sk_B @ X0)
% 45.01/45.26          | (r2_hidden @ sk_B @ X1)
% 45.01/45.26          | (r2_hidden @ sk_B @ 
% 45.01/45.26             (k4_xboole_0 @ (k1_ordinal1 @ sk_A) @ (k2_xboole_0 @ X0 @ X1))))),
% 45.01/45.26      inference('demod', [status(thm)], ['97', '98'])).
% 45.01/45.26  thf('100', plain,
% 45.01/45.26      (![X0 : $i]:
% 45.01/45.26         ((r2_hidden @ sk_B @ 
% 45.01/45.26           (k4_xboole_0 @ (k1_ordinal1 @ sk_A) @ (k1_ordinal1 @ X0)))
% 45.01/45.26          | (r2_hidden @ sk_B @ (k1_tarski @ X0))
% 45.01/45.26          | (r2_hidden @ sk_B @ X0))),
% 45.01/45.26      inference('sup+', [status(thm)], ['89', '99'])).
% 45.01/45.26  thf('101', plain, (((k1_ordinal1 @ sk_A) = (k1_ordinal1 @ sk_B))),
% 45.01/45.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.01/45.26  thf('102', plain,
% 45.01/45.26      (![X69 : $i]:
% 45.01/45.26         ((k1_ordinal1 @ X69) = (k2_xboole_0 @ X69 @ (k1_tarski @ X69)))),
% 45.01/45.26      inference('cnf', [status(esa)], [d1_ordinal1])).
% 45.01/45.26  thf('103', plain,
% 45.01/45.26      (![X34 : $i, X35 : $i, X36 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ (k4_xboole_0 @ X34 @ X35) @ X36)
% 45.01/45.26           = (k4_xboole_0 @ X34 @ (k2_xboole_0 @ X35 @ X36)))),
% 45.01/45.26      inference('cnf', [status(esa)], [t41_xboole_1])).
% 45.01/45.26  thf(idempotence_k2_xboole_0, axiom,
% 45.01/45.26    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 45.01/45.26  thf('104', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ X8) = (X8))),
% 45.01/45.26      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 45.01/45.26  thf('105', plain,
% 45.01/45.26      (![X34 : $i, X35 : $i, X36 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ (k4_xboole_0 @ X34 @ X35) @ X36)
% 45.01/45.26           = (k4_xboole_0 @ X34 @ (k2_xboole_0 @ X35 @ X36)))),
% 45.01/45.26      inference('cnf', [status(esa)], [t41_xboole_1])).
% 45.01/45.26  thf('106', plain,
% 45.01/45.26      (![X64 : $i, X65 : $i]:
% 45.01/45.26         (~ (r2_hidden @ X64 @ X65)
% 45.01/45.26          | ((k4_xboole_0 @ X65 @ (k1_tarski @ X64)) != (X65)))),
% 45.01/45.26      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 45.01/45.26  thf('107', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.01/45.26         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 45.01/45.26            != (k4_xboole_0 @ X2 @ X1))
% 45.01/45.26          | ~ (r2_hidden @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 45.01/45.26      inference('sup-', [status(thm)], ['105', '106'])).
% 45.01/45.26  thf('108', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0))
% 45.01/45.26            != (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 45.01/45.26          | ~ (r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 45.01/45.26      inference('sup-', [status(thm)], ['104', '107'])).
% 45.01/45.26  thf('109', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 45.01/45.26      inference('simplify', [status(thm)], ['108'])).
% 45.01/45.26  thf('110', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.01/45.26         ~ (r2_hidden @ X0 @ 
% 45.01/45.26            (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 45.01/45.26      inference('sup-', [status(thm)], ['103', '109'])).
% 45.01/45.26  thf('111', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ (k1_ordinal1 @ X0)))),
% 45.01/45.26      inference('sup-', [status(thm)], ['102', '110'])).
% 45.01/45.26  thf('112', plain,
% 45.01/45.26      (![X0 : $i]:
% 45.01/45.26         ~ (r2_hidden @ sk_B @ (k4_xboole_0 @ X0 @ (k1_ordinal1 @ sk_A)))),
% 45.01/45.26      inference('sup-', [status(thm)], ['101', '111'])).
% 45.01/45.26  thf('113', plain,
% 45.01/45.26      (((r2_hidden @ sk_B @ sk_A) | (r2_hidden @ sk_B @ (k1_tarski @ sk_A)))),
% 45.01/45.26      inference('sup-', [status(thm)], ['100', '112'])).
% 45.01/45.26  thf('114', plain,
% 45.01/45.26      (![X44 : $i, X46 : $i, X47 : $i]:
% 45.01/45.26         (~ (r2_hidden @ X47 @ X46)
% 45.01/45.26          | ((X47) = (X44))
% 45.01/45.26          | ((X46) != (k1_tarski @ X44)))),
% 45.01/45.26      inference('cnf', [status(esa)], [d1_tarski])).
% 45.01/45.26  thf('115', plain,
% 45.01/45.26      (![X44 : $i, X47 : $i]:
% 45.01/45.26         (((X47) = (X44)) | ~ (r2_hidden @ X47 @ (k1_tarski @ X44)))),
% 45.01/45.26      inference('simplify', [status(thm)], ['114'])).
% 45.01/45.26  thf('116', plain, (((r2_hidden @ sk_B @ sk_A) | ((sk_B) = (sk_A)))),
% 45.01/45.26      inference('sup-', [status(thm)], ['113', '115'])).
% 45.01/45.26  thf('117', plain, (((sk_A) != (sk_B))),
% 45.01/45.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.01/45.26  thf('118', plain, ((r2_hidden @ sk_B @ sk_A)),
% 45.01/45.26      inference('simplify_reflect-', [status(thm)], ['116', '117'])).
% 45.01/45.26  thf(antisymmetry_r2_hidden, axiom,
% 45.01/45.26    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 45.01/45.26  thf('119', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 45.01/45.26      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 45.01/45.26  thf('120', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 45.01/45.26      inference('sup-', [status(thm)], ['118', '119'])).
% 45.01/45.26  thf('121', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_B @ sk_A))),
% 45.01/45.26      inference('clc', [status(thm)], ['88', '120'])).
% 45.01/45.26  thf('122', plain,
% 45.01/45.26      (![X27 : $i, X28 : $i]:
% 45.01/45.26         ((r1_tarski @ X27 @ X28)
% 45.01/45.26          | ((k4_xboole_0 @ X27 @ X28) != (k1_xboole_0)))),
% 45.01/45.26      inference('cnf', [status(esa)], [l32_xboole_1])).
% 45.01/45.26  thf('123', plain,
% 45.01/45.26      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_B @ sk_A))),
% 45.01/45.26      inference('sup-', [status(thm)], ['121', '122'])).
% 45.01/45.26  thf('124', plain, ((r1_tarski @ sk_B @ sk_A)),
% 45.01/45.26      inference('simplify', [status(thm)], ['123'])).
% 45.01/45.26  thf('125', plain,
% 45.01/45.26      (![X30 : $i, X31 : $i]:
% 45.01/45.26         (((k2_xboole_0 @ X31 @ X30) = (X30)) | ~ (r1_tarski @ X31 @ X30))),
% 45.01/45.26      inference('cnf', [status(esa)], [t12_xboole_1])).
% 45.01/45.26  thf('126', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 45.01/45.26      inference('sup-', [status(thm)], ['124', '125'])).
% 45.01/45.26  thf('127', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 45.01/45.26      inference('demod', [status(thm)], ['3', '4'])).
% 45.01/45.26  thf('128', plain,
% 45.01/45.26      (![X34 : $i, X35 : $i, X36 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ (k4_xboole_0 @ X34 @ X35) @ X36)
% 45.01/45.26           = (k4_xboole_0 @ X34 @ (k2_xboole_0 @ X35 @ X36)))),
% 45.01/45.26      inference('cnf', [status(esa)], [t41_xboole_1])).
% 45.01/45.26  thf('129', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 45.01/45.26           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)))),
% 45.01/45.26      inference('sup+', [status(thm)], ['127', '128'])).
% 45.01/45.26  thf('130', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 45.01/45.26      inference('sup-', [status(thm)], ['23', '24'])).
% 45.01/45.26  thf('131', plain,
% 45.01/45.26      (![X32 : $i, X33 : $i]: (r1_tarski @ (k4_xboole_0 @ X32 @ X33) @ X32)),
% 45.01/45.26      inference('cnf', [status(esa)], [t36_xboole_1])).
% 45.01/45.26  thf('132', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 45.01/45.26      inference('sup+', [status(thm)], ['130', '131'])).
% 45.01/45.26  thf('133', plain,
% 45.01/45.26      (![X27 : $i, X29 : $i]:
% 45.01/45.26         (((k4_xboole_0 @ X27 @ X29) = (k1_xboole_0))
% 45.01/45.26          | ~ (r1_tarski @ X27 @ X29))),
% 45.01/45.26      inference('cnf', [status(esa)], [l32_xboole_1])).
% 45.01/45.26  thf('134', plain,
% 45.01/45.26      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 45.01/45.26      inference('sup-', [status(thm)], ['132', '133'])).
% 45.01/45.26  thf('135', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.01/45.26         ((k1_xboole_0)
% 45.01/45.26           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)))),
% 45.01/45.26      inference('demod', [status(thm)], ['129', '134'])).
% 45.01/45.26  thf('136', plain,
% 45.01/45.26      (![X34 : $i, X35 : $i, X36 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ (k4_xboole_0 @ X34 @ X35) @ X36)
% 45.01/45.26           = (k4_xboole_0 @ X34 @ (k2_xboole_0 @ X35 @ X36)))),
% 45.01/45.26      inference('cnf', [status(esa)], [t41_xboole_1])).
% 45.01/45.26  thf('137', plain,
% 45.01/45.26      (![X34 : $i, X35 : $i, X36 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ (k4_xboole_0 @ X34 @ X35) @ X36)
% 45.01/45.26           = (k4_xboole_0 @ X34 @ (k2_xboole_0 @ X35 @ X36)))),
% 45.01/45.26      inference('cnf', [status(esa)], [t41_xboole_1])).
% 45.01/45.26  thf('138', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3)
% 45.01/45.26           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k2_xboole_0 @ X0 @ X3)))),
% 45.01/45.26      inference('sup+', [status(thm)], ['136', '137'])).
% 45.01/45.26  thf('139', plain,
% 45.01/45.26      (![X34 : $i, X35 : $i, X36 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ (k4_xboole_0 @ X34 @ X35) @ X36)
% 45.01/45.26           = (k4_xboole_0 @ X34 @ (k2_xboole_0 @ X35 @ X36)))),
% 45.01/45.26      inference('cnf', [status(esa)], [t41_xboole_1])).
% 45.01/45.26  thf('140', plain,
% 45.01/45.26      (![X34 : $i, X35 : $i, X36 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ (k4_xboole_0 @ X34 @ X35) @ X36)
% 45.01/45.26           = (k4_xboole_0 @ X34 @ (k2_xboole_0 @ X35 @ X36)))),
% 45.01/45.26      inference('cnf', [status(esa)], [t41_xboole_1])).
% 45.01/45.26  thf('141', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X3))
% 45.01/45.26           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X3))))),
% 45.01/45.26      inference('demod', [status(thm)], ['138', '139', '140'])).
% 45.01/45.26  thf('142', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.01/45.26         ((k1_xboole_0)
% 45.01/45.26           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 45.01/45.26      inference('demod', [status(thm)], ['135', '141'])).
% 45.01/45.26  thf('143', plain,
% 45.01/45.26      (![X40 : $i, X41 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ X40 @ (k4_xboole_0 @ X40 @ X41))
% 45.01/45.26           = (k3_xboole_0 @ X40 @ X41))),
% 45.01/45.26      inference('cnf', [status(esa)], [t48_xboole_1])).
% 45.01/45.26  thf('144', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 45.01/45.26           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 45.01/45.26      inference('sup+', [status(thm)], ['142', '143'])).
% 45.01/45.26  thf('145', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 45.01/45.26      inference('demod', [status(thm)], ['56', '76'])).
% 45.01/45.26  thf('146', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.01/45.26         ((X1)
% 45.01/45.26           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 45.01/45.26      inference('demod', [status(thm)], ['144', '145'])).
% 45.01/45.26  thf('147', plain,
% 45.01/45.26      (![X0 : $i]: ((sk_B) = (k3_xboole_0 @ sk_B @ (k2_xboole_0 @ X0 @ sk_A)))),
% 45.01/45.26      inference('sup+', [status(thm)], ['126', '146'])).
% 45.01/45.26  thf('148', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 45.01/45.26      inference('demod', [status(thm)], ['3', '4'])).
% 45.01/45.26  thf('149', plain,
% 45.01/45.26      (![X27 : $i, X28 : $i]:
% 45.01/45.26         ((r1_tarski @ X27 @ X28)
% 45.01/45.26          | ((k4_xboole_0 @ X27 @ X28) != (k1_xboole_0)))),
% 45.01/45.26      inference('cnf', [status(esa)], [l32_xboole_1])).
% 45.01/45.26  thf('150', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         (((k1_xboole_0) != (k1_xboole_0))
% 45.01/45.26          | (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 45.01/45.26      inference('sup-', [status(thm)], ['148', '149'])).
% 45.01/45.26  thf('151', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 45.01/45.26      inference('simplify', [status(thm)], ['150'])).
% 45.01/45.26  thf('152', plain,
% 45.01/45.26      (![X30 : $i, X31 : $i]:
% 45.01/45.26         (((k2_xboole_0 @ X31 @ X30) = (X30)) | ~ (r1_tarski @ X31 @ X30))),
% 45.01/45.26      inference('cnf', [status(esa)], [t12_xboole_1])).
% 45.01/45.26  thf('153', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 45.01/45.26           = (k2_xboole_0 @ X1 @ X0))),
% 45.01/45.26      inference('sup-', [status(thm)], ['151', '152'])).
% 45.01/45.26  thf('154', plain,
% 45.01/45.26      (![X34 : $i, X35 : $i, X36 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ (k4_xboole_0 @ X34 @ X35) @ X36)
% 45.01/45.26           = (k4_xboole_0 @ X34 @ (k2_xboole_0 @ X35 @ X36)))),
% 45.01/45.26      inference('cnf', [status(esa)], [t41_xboole_1])).
% 45.01/45.26  thf('155', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 45.01/45.26      inference('sup-', [status(thm)], ['45', '46'])).
% 45.01/45.26  thf('156', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ X2 @ 
% 45.01/45.26           (k2_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))
% 45.01/45.26           = (k1_xboole_0))),
% 45.01/45.26      inference('sup+', [status(thm)], ['154', '155'])).
% 45.01/45.26  thf('157', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))
% 45.01/45.26           = (k1_xboole_0))),
% 45.01/45.26      inference('sup+', [status(thm)], ['153', '156'])).
% 45.01/45.26  thf('158', plain,
% 45.01/45.26      (![X40 : $i, X41 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ X40 @ (k4_xboole_0 @ X40 @ X41))
% 45.01/45.26           = (k3_xboole_0 @ X40 @ X41))),
% 45.01/45.26      inference('cnf', [status(esa)], [t48_xboole_1])).
% 45.01/45.26  thf('159', plain,
% 45.01/45.26      (![X34 : $i, X35 : $i, X36 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ (k4_xboole_0 @ X34 @ X35) @ X36)
% 45.01/45.26           = (k4_xboole_0 @ X34 @ (k2_xboole_0 @ X35 @ X36)))),
% 45.01/45.26      inference('cnf', [status(esa)], [t41_xboole_1])).
% 45.01/45.26  thf('160', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 45.01/45.26           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 45.01/45.26      inference('sup+', [status(thm)], ['158', '159'])).
% 45.01/45.26  thf('161', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 45.01/45.26      inference('demod', [status(thm)], ['157', '160'])).
% 45.01/45.26  thf('162', plain,
% 45.01/45.26      (![X27 : $i, X28 : $i]:
% 45.01/45.26         ((r1_tarski @ X27 @ X28)
% 45.01/45.26          | ((k4_xboole_0 @ X27 @ X28) != (k1_xboole_0)))),
% 45.01/45.26      inference('cnf', [status(esa)], [l32_xboole_1])).
% 45.01/45.26  thf('163', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         (((k1_xboole_0) != (k1_xboole_0))
% 45.01/45.26          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 45.01/45.26      inference('sup-', [status(thm)], ['161', '162'])).
% 45.01/45.26  thf('164', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 45.01/45.26      inference('simplify', [status(thm)], ['163'])).
% 45.01/45.26  thf('165', plain,
% 45.01/45.26      (![X30 : $i, X31 : $i]:
% 45.01/45.26         (((k2_xboole_0 @ X31 @ X30) = (X30)) | ~ (r1_tarski @ X31 @ X30))),
% 45.01/45.26      inference('cnf', [status(esa)], [t12_xboole_1])).
% 45.01/45.26  thf('166', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 45.01/45.26      inference('sup-', [status(thm)], ['164', '165'])).
% 45.01/45.26  thf('167', plain,
% 45.01/45.26      (![X0 : $i]:
% 45.01/45.26         ((k2_xboole_0 @ sk_B @ (k2_xboole_0 @ X0 @ sk_A))
% 45.01/45.26           = (k2_xboole_0 @ X0 @ sk_A))),
% 45.01/45.26      inference('sup+', [status(thm)], ['147', '166'])).
% 45.01/45.26  thf('168', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ X2 @ 
% 45.01/45.26           (k2_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))
% 45.01/45.26           = (k1_xboole_0))),
% 45.01/45.26      inference('sup+', [status(thm)], ['154', '155'])).
% 45.01/45.26  thf('169', plain,
% 45.01/45.26      (![X0 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A))
% 45.01/45.26           = (k1_xboole_0))),
% 45.01/45.26      inference('sup+', [status(thm)], ['167', '168'])).
% 45.01/45.26  thf('170', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 45.01/45.26           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 45.01/45.26      inference('sup+', [status(thm)], ['158', '159'])).
% 45.01/45.26  thf('171', plain,
% 45.01/45.26      (![X0 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ sk_B) @ sk_A) = (k1_xboole_0))),
% 45.01/45.26      inference('demod', [status(thm)], ['169', '170'])).
% 45.01/45.26  thf('172', plain,
% 45.01/45.26      (![X27 : $i, X28 : $i]:
% 45.01/45.26         ((r1_tarski @ X27 @ X28)
% 45.01/45.26          | ((k4_xboole_0 @ X27 @ X28) != (k1_xboole_0)))),
% 45.01/45.26      inference('cnf', [status(esa)], [l32_xboole_1])).
% 45.01/45.26  thf('173', plain,
% 45.01/45.26      (![X0 : $i]:
% 45.01/45.26         (((k1_xboole_0) != (k1_xboole_0))
% 45.01/45.26          | (r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ sk_A))),
% 45.01/45.26      inference('sup-', [status(thm)], ['171', '172'])).
% 45.01/45.26  thf('174', plain,
% 45.01/45.26      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ sk_A)),
% 45.01/45.26      inference('simplify', [status(thm)], ['173'])).
% 45.01/45.26  thf('175', plain,
% 45.01/45.26      (![X40 : $i, X41 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ X40 @ (k4_xboole_0 @ X40 @ X41))
% 45.01/45.26           = (k3_xboole_0 @ X40 @ X41))),
% 45.01/45.26      inference('cnf', [status(esa)], [t48_xboole_1])).
% 45.01/45.26  thf('176', plain, (![X44 : $i]: (r2_hidden @ X44 @ (k1_tarski @ X44))),
% 45.01/45.26      inference('simplify', [status(thm)], ['28'])).
% 45.01/45.26  thf('177', plain,
% 45.01/45.26      (![X2 : $i, X3 : $i, X4 : $i]:
% 45.01/45.26         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 45.01/45.26          | (r2_hidden @ X2 @ X4)
% 45.01/45.26          | ~ (r2_hidden @ X2 @ X3))),
% 45.01/45.26      inference('simplify', [status(thm)], ['93'])).
% 45.01/45.26  thf('178', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         ((r2_hidden @ X0 @ X1)
% 45.01/45.26          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 45.01/45.26      inference('sup-', [status(thm)], ['176', '177'])).
% 45.01/45.26  thf(t7_ordinal1, axiom,
% 45.01/45.26    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 45.01/45.26  thf('179', plain,
% 45.01/45.26      (![X71 : $i, X72 : $i]:
% 45.01/45.26         (~ (r2_hidden @ X71 @ X72) | ~ (r1_tarski @ X72 @ X71))),
% 45.01/45.26      inference('cnf', [status(esa)], [t7_ordinal1])).
% 45.01/45.26  thf('180', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         ((r2_hidden @ X1 @ X0)
% 45.01/45.26          | ~ (r1_tarski @ (k4_xboole_0 @ (k1_tarski @ X1) @ X0) @ X1))),
% 45.01/45.26      inference('sup-', [status(thm)], ['178', '179'])).
% 45.01/45.26  thf('181', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         (~ (r1_tarski @ (k3_xboole_0 @ (k1_tarski @ X1) @ X0) @ X1)
% 45.01/45.26          | (r2_hidden @ X1 @ (k4_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 45.01/45.26      inference('sup-', [status(thm)], ['175', '180'])).
% 45.01/45.26  thf('182', plain,
% 45.01/45.26      ((r2_hidden @ sk_A @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 45.01/45.26      inference('sup-', [status(thm)], ['174', '181'])).
% 45.01/45.26  thf('183', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 45.01/45.26      inference('demod', [status(thm)], ['3', '4'])).
% 45.01/45.26  thf('184', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.01/45.26         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 45.01/45.26            != (k4_xboole_0 @ X2 @ X1))
% 45.01/45.26          | ~ (r2_hidden @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 45.01/45.26      inference('sup-', [status(thm)], ['105', '106'])).
% 45.01/45.26  thf('185', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         (((k1_xboole_0) != (k4_xboole_0 @ (k1_tarski @ X1) @ X0))
% 45.01/45.26          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 45.01/45.26      inference('sup-', [status(thm)], ['183', '184'])).
% 45.01/45.26  thf('186', plain,
% 45.01/45.26      (((k1_xboole_0) != (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 45.01/45.26      inference('sup-', [status(thm)], ['182', '185'])).
% 45.01/45.26  thf('187', plain,
% 45.01/45.26      ((((k1_xboole_0) != (k1_xboole_0))
% 45.01/45.26        | ((k1_xboole_0) = (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 45.01/45.26      inference('sup-', [status(thm)], ['35', '186'])).
% 45.01/45.26  thf('188', plain,
% 45.01/45.26      (((k1_xboole_0) = (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 45.01/45.26      inference('simplify', [status(thm)], ['187'])).
% 45.01/45.26  thf('189', plain,
% 45.01/45.26      (![X40 : $i, X41 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ X40 @ (k4_xboole_0 @ X40 @ X41))
% 45.01/45.26           = (k3_xboole_0 @ X40 @ X41))),
% 45.01/45.26      inference('cnf', [status(esa)], [t48_xboole_1])).
% 45.01/45.26  thf('190', plain,
% 45.01/45.26      (![X27 : $i, X28 : $i]:
% 45.01/45.26         ((r1_tarski @ X27 @ X28)
% 45.01/45.26          | ((k4_xboole_0 @ X27 @ X28) != (k1_xboole_0)))),
% 45.01/45.26      inference('cnf', [status(esa)], [l32_xboole_1])).
% 45.01/45.26  thf('191', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 45.01/45.26          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 45.01/45.26      inference('sup-', [status(thm)], ['189', '190'])).
% 45.01/45.26  thf('192', plain,
% 45.01/45.26      ((((k1_xboole_0) != (k1_xboole_0))
% 45.01/45.26        | (r1_tarski @ (k1_tarski @ sk_A) @ 
% 45.01/45.26           (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 45.01/45.26      inference('sup-', [status(thm)], ['188', '191'])).
% 45.01/45.26  thf('193', plain,
% 45.01/45.26      ((r1_tarski @ (k1_tarski @ sk_A) @ 
% 45.01/45.26        (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 45.01/45.26      inference('simplify', [status(thm)], ['192'])).
% 45.01/45.26  thf('194', plain,
% 45.01/45.26      (![X32 : $i, X33 : $i]: (r1_tarski @ (k4_xboole_0 @ X32 @ X33) @ X32)),
% 45.01/45.26      inference('cnf', [status(esa)], [t36_xboole_1])).
% 45.01/45.26  thf('195', plain,
% 45.01/45.26      (![X24 : $i, X26 : $i]:
% 45.01/45.26         (((X24) = (X26))
% 45.01/45.26          | ~ (r1_tarski @ X26 @ X24)
% 45.01/45.26          | ~ (r1_tarski @ X24 @ X26))),
% 45.01/45.26      inference('cnf', [status(esa)], [d10_xboole_0])).
% 45.01/45.26  thf('196', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 45.01/45.26          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 45.01/45.26      inference('sup-', [status(thm)], ['194', '195'])).
% 45.01/45.26  thf('197', plain,
% 45.01/45.26      (((k1_tarski @ sk_A) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 45.01/45.26      inference('sup-', [status(thm)], ['193', '196'])).
% 45.01/45.26  thf('198', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))),
% 45.01/45.26      inference('demod', [status(thm)], ['15', '197'])).
% 45.01/45.26  thf('199', plain,
% 45.01/45.26      (![X27 : $i, X29 : $i]:
% 45.01/45.26         (((k4_xboole_0 @ X27 @ X29) = (k1_xboole_0))
% 45.01/45.26          | ~ (r1_tarski @ X27 @ X29))),
% 45.01/45.26      inference('cnf', [status(esa)], [l32_xboole_1])).
% 45.01/45.26  thf('200', plain,
% 45.01/45.26      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 45.01/45.26      inference('sup-', [status(thm)], ['198', '199'])).
% 45.01/45.26  thf('201', plain,
% 45.01/45.26      (![X34 : $i, X35 : $i, X36 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ (k4_xboole_0 @ X34 @ X35) @ X36)
% 45.01/45.26           = (k4_xboole_0 @ X34 @ (k2_xboole_0 @ X35 @ X36)))),
% 45.01/45.26      inference('cnf', [status(esa)], [t41_xboole_1])).
% 45.01/45.26  thf('202', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 45.01/45.26      inference('sup-', [status(thm)], ['23', '24'])).
% 45.01/45.26  thf('203', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 45.01/45.26           = (k1_xboole_0))),
% 45.01/45.26      inference('sup+', [status(thm)], ['201', '202'])).
% 45.01/45.26  thf('204', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         ((r2_hidden @ X0 @ X1)
% 45.01/45.26          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 45.01/45.26      inference('sup-', [status(thm)], ['176', '177'])).
% 45.01/45.26  thf('205', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         ((r2_hidden @ X1 @ k1_xboole_0)
% 45.01/45.26          | (r2_hidden @ X1 @ 
% 45.01/45.26             (k2_xboole_0 @ X0 @ (k4_xboole_0 @ (k1_tarski @ X1) @ X0))))),
% 45.01/45.26      inference('sup+', [status(thm)], ['203', '204'])).
% 45.01/45.26  thf('206', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 45.01/45.26      inference('sup-', [status(thm)], ['23', '24'])).
% 45.01/45.26  thf('207', plain,
% 45.01/45.26      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 45.01/45.26         (~ (r2_hidden @ X6 @ X5)
% 45.01/45.26          | ~ (r2_hidden @ X6 @ X4)
% 45.01/45.26          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 45.01/45.26      inference('cnf', [status(esa)], [d5_xboole_0])).
% 45.01/45.26  thf('208', plain,
% 45.01/45.26      (![X3 : $i, X4 : $i, X6 : $i]:
% 45.01/45.26         (~ (r2_hidden @ X6 @ X4)
% 45.01/45.26          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 45.01/45.26      inference('simplify', [status(thm)], ['207'])).
% 45.01/45.26  thf('209', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 45.01/45.26      inference('sup-', [status(thm)], ['206', '208'])).
% 45.01/45.26  thf('210', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 45.01/45.26      inference('condensation', [status(thm)], ['209'])).
% 45.01/45.26  thf('211', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         (r2_hidden @ X1 @ 
% 45.01/45.26          (k2_xboole_0 @ X0 @ (k4_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 45.01/45.26      inference('clc', [status(thm)], ['205', '210'])).
% 45.01/45.26  thf('212', plain,
% 45.01/45.26      (![X71 : $i, X72 : $i]:
% 45.01/45.26         (~ (r2_hidden @ X71 @ X72) | ~ (r1_tarski @ X72 @ X71))),
% 45.01/45.26      inference('cnf', [status(esa)], [t7_ordinal1])).
% 45.01/45.26  thf('213', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         ~ (r1_tarski @ 
% 45.01/45.26            (k2_xboole_0 @ X0 @ (k4_xboole_0 @ (k1_tarski @ X1) @ X0)) @ X1)),
% 45.01/45.26      inference('sup-', [status(thm)], ['211', '212'])).
% 45.01/45.26  thf('214', plain,
% 45.01/45.26      (~ (r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0) @ sk_A)),
% 45.01/45.26      inference('sup-', [status(thm)], ['200', '213'])).
% 45.01/45.26  thf('215', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 45.01/45.26      inference('demod', [status(thm)], ['56', '76'])).
% 45.01/45.26  thf('216', plain,
% 45.01/45.26      (![X34 : $i, X35 : $i, X36 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ (k4_xboole_0 @ X34 @ X35) @ X36)
% 45.01/45.26           = (k4_xboole_0 @ X34 @ (k2_xboole_0 @ X35 @ X36)))),
% 45.01/45.26      inference('cnf', [status(esa)], [t41_xboole_1])).
% 45.01/45.26  thf('217', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ X1 @ X0)
% 45.01/45.26           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 45.01/45.26      inference('sup+', [status(thm)], ['215', '216'])).
% 45.01/45.26  thf('218', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 45.01/45.26      inference('sup-', [status(thm)], ['23', '24'])).
% 45.01/45.26  thf('219', plain,
% 45.01/45.26      (![X0 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0) = (k1_xboole_0))),
% 45.01/45.26      inference('sup+', [status(thm)], ['217', '218'])).
% 45.01/45.26  thf('220', plain,
% 45.01/45.26      (![X27 : $i, X28 : $i]:
% 45.01/45.26         ((r1_tarski @ X27 @ X28)
% 45.01/45.26          | ((k4_xboole_0 @ X27 @ X28) != (k1_xboole_0)))),
% 45.01/45.26      inference('cnf', [status(esa)], [l32_xboole_1])).
% 45.01/45.26  thf('221', plain,
% 45.01/45.26      (![X0 : $i]:
% 45.01/45.26         (((k1_xboole_0) != (k1_xboole_0))
% 45.01/45.26          | (r1_tarski @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0))),
% 45.01/45.26      inference('sup-', [status(thm)], ['219', '220'])).
% 45.01/45.26  thf('222', plain,
% 45.01/45.26      (![X0 : $i]: (r1_tarski @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0)),
% 45.01/45.26      inference('simplify', [status(thm)], ['221'])).
% 45.01/45.26  thf('223', plain,
% 45.01/45.26      (![X42 : $i, X43 : $i]: (r1_tarski @ X42 @ (k2_xboole_0 @ X42 @ X43))),
% 45.01/45.26      inference('cnf', [status(esa)], [t7_xboole_1])).
% 45.01/45.26  thf('224', plain,
% 45.01/45.26      (![X24 : $i, X26 : $i]:
% 45.01/45.26         (((X24) = (X26))
% 45.01/45.26          | ~ (r1_tarski @ X26 @ X24)
% 45.01/45.26          | ~ (r1_tarski @ X24 @ X26))),
% 45.01/45.26      inference('cnf', [status(esa)], [d10_xboole_0])).
% 45.01/45.26  thf('225', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 45.01/45.26          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 45.01/45.26      inference('sup-', [status(thm)], ['223', '224'])).
% 45.01/45.26  thf('226', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 45.01/45.26      inference('sup-', [status(thm)], ['222', '225'])).
% 45.01/45.26  thf('227', plain, (![X44 : $i]: (r2_hidden @ X44 @ (k1_tarski @ X44))),
% 45.01/45.26      inference('simplify', [status(thm)], ['28'])).
% 45.01/45.26  thf('228', plain,
% 45.01/45.26      (![X1 : $i, X2 : $i]:
% 45.01/45.26         (((k4_xboole_0 @ (k1_tarski @ X2) @ X1) = (k1_tarski @ X2))
% 45.01/45.26          | ((k4_xboole_0 @ (k1_tarski @ X2) @ X1) = (k1_xboole_0)))),
% 45.01/45.26      inference('clc', [status(thm)], ['21', '30'])).
% 45.01/45.26  thf('229', plain, ((r2_hidden @ sk_B @ sk_A)),
% 45.01/45.26      inference('simplify_reflect-', [status(thm)], ['116', '117'])).
% 45.01/45.26  thf('230', plain, (![X70 : $i]: (r2_hidden @ X70 @ (k1_ordinal1 @ X70))),
% 45.01/45.26      inference('cnf', [status(esa)], [t10_ordinal1])).
% 45.01/45.26  thf('231', plain,
% 45.01/45.26      (![X2 : $i, X3 : $i, X4 : $i]:
% 45.01/45.26         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 45.01/45.26          | (r2_hidden @ X2 @ X4)
% 45.01/45.26          | ~ (r2_hidden @ X2 @ X3))),
% 45.01/45.26      inference('simplify', [status(thm)], ['93'])).
% 45.01/45.26  thf('232', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         ((r2_hidden @ X0 @ X1)
% 45.01/45.26          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_ordinal1 @ X0) @ X1)))),
% 45.01/45.26      inference('sup-', [status(thm)], ['230', '231'])).
% 45.01/45.26  thf('233', plain,
% 45.01/45.26      (![X34 : $i, X35 : $i, X36 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ (k4_xboole_0 @ X34 @ X35) @ X36)
% 45.01/45.26           = (k4_xboole_0 @ X34 @ (k2_xboole_0 @ X35 @ X36)))),
% 45.01/45.26      inference('cnf', [status(esa)], [t41_xboole_1])).
% 45.01/45.26  thf('234', plain,
% 45.01/45.26      (![X3 : $i, X4 : $i, X6 : $i]:
% 45.01/45.26         (~ (r2_hidden @ X6 @ X4)
% 45.01/45.26          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 45.01/45.26      inference('simplify', [status(thm)], ['207'])).
% 45.01/45.26  thf('235', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 45.01/45.26         (~ (r2_hidden @ X3 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 45.01/45.26          | ~ (r2_hidden @ X3 @ X0))),
% 45.01/45.26      inference('sup-', [status(thm)], ['233', '234'])).
% 45.01/45.26  thf('236', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.01/45.26         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X0))),
% 45.01/45.26      inference('sup-', [status(thm)], ['232', '235'])).
% 45.01/45.26  thf('237', plain,
% 45.01/45.26      (![X0 : $i]: (r2_hidden @ sk_B @ (k2_xboole_0 @ X0 @ sk_A))),
% 45.01/45.26      inference('sup-', [status(thm)], ['229', '236'])).
% 45.01/45.26  thf('238', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         (((k1_xboole_0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 45.01/45.26          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 45.01/45.26      inference('demod', [status(thm)], ['33', '34'])).
% 45.01/45.26  thf('239', plain,
% 45.01/45.26      (![X27 : $i, X28 : $i]:
% 45.01/45.26         ((r1_tarski @ X27 @ X28)
% 45.01/45.26          | ((k4_xboole_0 @ X27 @ X28) != (k1_xboole_0)))),
% 45.01/45.26      inference('cnf', [status(esa)], [l32_xboole_1])).
% 45.01/45.26  thf('240', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         (((k1_xboole_0) != (k1_xboole_0))
% 45.01/45.26          | ((k1_xboole_0) = (k3_xboole_0 @ (k1_tarski @ X1) @ X0))
% 45.01/45.26          | (r1_tarski @ (k1_tarski @ X1) @ X0))),
% 45.01/45.26      inference('sup-', [status(thm)], ['238', '239'])).
% 45.01/45.26  thf('241', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         ((r1_tarski @ (k1_tarski @ X1) @ X0)
% 45.01/45.26          | ((k1_xboole_0) = (k3_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 45.01/45.26      inference('simplify', [status(thm)], ['240'])).
% 45.01/45.26  thf('242', plain, (![X44 : $i]: (r2_hidden @ X44 @ (k1_tarski @ X44))),
% 45.01/45.26      inference('simplify', [status(thm)], ['28'])).
% 45.01/45.26  thf('243', plain,
% 45.01/45.26      (![X71 : $i, X72 : $i]:
% 45.01/45.26         (~ (r2_hidden @ X71 @ X72) | ~ (r1_tarski @ X72 @ X71))),
% 45.01/45.26      inference('cnf', [status(esa)], [t7_ordinal1])).
% 45.01/45.26  thf('244', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ X0)),
% 45.01/45.26      inference('sup-', [status(thm)], ['242', '243'])).
% 45.01/45.26  thf('245', plain,
% 45.01/45.26      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X0))),
% 45.01/45.26      inference('sup-', [status(thm)], ['241', '244'])).
% 45.01/45.26  thf(t4_xboole_0, axiom,
% 45.01/45.26    (![A:$i,B:$i]:
% 45.01/45.26     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 45.01/45.26            ( r1_xboole_0 @ A @ B ) ) ) & 
% 45.01/45.26       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 45.01/45.26            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 45.01/45.26  thf('246', plain,
% 45.01/45.26      (![X11 : $i, X12 : $i]:
% 45.01/45.26         ((r1_xboole_0 @ X11 @ X12)
% 45.01/45.26          | (r2_hidden @ (sk_C @ X12 @ X11) @ (k3_xboole_0 @ X11 @ X12)))),
% 45.01/45.26      inference('cnf', [status(esa)], [t4_xboole_0])).
% 45.01/45.26  thf('247', plain,
% 45.01/45.26      (![X71 : $i, X72 : $i]:
% 45.01/45.26         (~ (r2_hidden @ X71 @ X72) | ~ (r1_tarski @ X72 @ X71))),
% 45.01/45.26      inference('cnf', [status(esa)], [t7_ordinal1])).
% 45.01/45.26  thf('248', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         ((r1_xboole_0 @ X1 @ X0)
% 45.01/45.26          | ~ (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ (sk_C @ X0 @ X1)))),
% 45.01/45.26      inference('sup-', [status(thm)], ['246', '247'])).
% 45.01/45.26  thf('249', plain,
% 45.01/45.26      (![X0 : $i]:
% 45.01/45.26         (~ (r1_tarski @ k1_xboole_0 @ (sk_C @ X0 @ (k1_tarski @ X0)))
% 45.01/45.26          | (r1_xboole_0 @ (k1_tarski @ X0) @ X0))),
% 45.01/45.26      inference('sup-', [status(thm)], ['245', '248'])).
% 45.01/45.26  thf('250', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 45.01/45.26      inference('sup+', [status(thm)], ['130', '131'])).
% 45.01/45.26  thf('251', plain, (![X0 : $i]: (r1_xboole_0 @ (k1_tarski @ X0) @ X0)),
% 45.01/45.26      inference('demod', [status(thm)], ['249', '250'])).
% 45.01/45.26  thf(symmetry_r1_xboole_0, axiom,
% 45.01/45.26    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 45.01/45.26  thf('252', plain,
% 45.01/45.26      (![X9 : $i, X10 : $i]:
% 45.01/45.26         ((r1_xboole_0 @ X9 @ X10) | ~ (r1_xboole_0 @ X10 @ X9))),
% 45.01/45.26      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 45.01/45.26  thf('253', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ (k1_tarski @ X0))),
% 45.01/45.26      inference('sup-', [status(thm)], ['251', '252'])).
% 45.01/45.26  thf('254', plain,
% 45.01/45.26      (![X3 : $i, X4 : $i, X7 : $i]:
% 45.01/45.26         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 45.01/45.26          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 45.01/45.26          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 45.01/45.26      inference('cnf', [status(esa)], [d5_xboole_0])).
% 45.01/45.26  thf('255', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 45.01/45.26      inference('condensation', [status(thm)], ['209'])).
% 45.01/45.26  thf('256', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 45.01/45.26          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 45.01/45.26      inference('sup-', [status(thm)], ['254', '255'])).
% 45.01/45.26  thf('257', plain,
% 45.01/45.26      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 45.01/45.26      inference('sup-', [status(thm)], ['132', '133'])).
% 45.01/45.26  thf('258', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 45.01/45.26          | ((X1) = (k1_xboole_0)))),
% 45.01/45.26      inference('demod', [status(thm)], ['256', '257'])).
% 45.01/45.26  thf('259', plain,
% 45.01/45.26      (![X11 : $i, X13 : $i, X14 : $i]:
% 45.01/45.26         (~ (r2_hidden @ X13 @ (k3_xboole_0 @ X11 @ X14))
% 45.01/45.26          | ~ (r1_xboole_0 @ X11 @ X14))),
% 45.01/45.26      inference('cnf', [status(esa)], [t4_xboole_0])).
% 45.01/45.26  thf('260', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 45.01/45.26      inference('sup-', [status(thm)], ['258', '259'])).
% 45.01/45.26  thf('261', plain,
% 45.01/45.26      (![X0 : $i]: ((k3_xboole_0 @ X0 @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 45.01/45.26      inference('sup-', [status(thm)], ['253', '260'])).
% 45.01/45.26  thf('262', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 45.01/45.26          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 45.01/45.26      inference('sup-', [status(thm)], ['189', '190'])).
% 45.01/45.26  thf('263', plain,
% 45.01/45.26      (![X0 : $i]:
% 45.01/45.26         (((k1_xboole_0) != (k1_xboole_0))
% 45.01/45.26          | (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ (k1_tarski @ X0))))),
% 45.01/45.26      inference('sup-', [status(thm)], ['261', '262'])).
% 45.01/45.26  thf('264', plain,
% 45.01/45.26      (![X0 : $i]: (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ (k1_tarski @ X0)))),
% 45.01/45.26      inference('simplify', [status(thm)], ['263'])).
% 45.01/45.26  thf('265', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 45.01/45.26          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 45.01/45.26      inference('sup-', [status(thm)], ['194', '195'])).
% 45.01/45.26  thf('266', plain,
% 45.01/45.26      (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ (k1_tarski @ X0)))),
% 45.01/45.26      inference('sup-', [status(thm)], ['264', '265'])).
% 45.01/45.26  thf('267', plain,
% 45.01/45.26      (![X34 : $i, X35 : $i, X36 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ (k4_xboole_0 @ X34 @ X35) @ X36)
% 45.01/45.26           = (k4_xboole_0 @ X34 @ (k2_xboole_0 @ X35 @ X36)))),
% 45.01/45.26      inference('cnf', [status(esa)], [t41_xboole_1])).
% 45.01/45.26  thf('268', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i]:
% 45.01/45.26         ((k4_xboole_0 @ X0 @ X1)
% 45.01/45.26           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 45.01/45.26      inference('sup+', [status(thm)], ['266', '267'])).
% 45.01/45.26  thf('269', plain,
% 45.01/45.26      (![X3 : $i, X4 : $i, X6 : $i]:
% 45.01/45.26         (~ (r2_hidden @ X6 @ X4)
% 45.01/45.26          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 45.01/45.26      inference('simplify', [status(thm)], ['207'])).
% 45.01/45.26  thf('270', plain,
% 45.01/45.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.01/45.26         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 45.01/45.26          | ~ (r2_hidden @ X2 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 45.01/45.26      inference('sup-', [status(thm)], ['268', '269'])).
% 45.01/45.26  thf('271', plain,
% 45.01/45.26      (![X0 : $i]: ~ (r2_hidden @ sk_B @ (k4_xboole_0 @ X0 @ sk_A))),
% 45.01/45.26      inference('sup-', [status(thm)], ['237', '270'])).
% 45.01/45.26  thf('272', plain,
% 45.01/45.26      (![X0 : $i]:
% 45.01/45.26         (~ (r2_hidden @ sk_B @ (k1_tarski @ X0))
% 45.01/45.26          | ((k4_xboole_0 @ (k1_tarski @ X0) @ sk_A) = (k1_xboole_0)))),
% 45.01/45.26      inference('sup-', [status(thm)], ['228', '271'])).
% 45.01/45.26  thf('273', plain,
% 45.01/45.26      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))),
% 45.01/45.26      inference('sup-', [status(thm)], ['227', '272'])).
% 45.01/45.26  thf('274', plain,
% 45.01/45.26      (![X27 : $i, X28 : $i]:
% 45.01/45.26         ((r1_tarski @ X27 @ X28)
% 45.01/45.26          | ((k4_xboole_0 @ X27 @ X28) != (k1_xboole_0)))),
% 45.01/45.26      inference('cnf', [status(esa)], [l32_xboole_1])).
% 45.01/45.26  thf('275', plain,
% 45.01/45.26      ((((k1_xboole_0) != (k1_xboole_0))
% 45.01/45.26        | (r1_tarski @ (k1_tarski @ sk_B) @ sk_A))),
% 45.01/45.26      inference('sup-', [status(thm)], ['273', '274'])).
% 45.01/45.26  thf('276', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ sk_A)),
% 45.01/45.26      inference('simplify', [status(thm)], ['275'])).
% 45.01/45.26  thf('277', plain, ($false),
% 45.01/45.26      inference('demod', [status(thm)], ['214', '226', '276'])).
% 45.01/45.26  
% 45.01/45.26  % SZS output end Refutation
% 45.01/45.26  
% 45.01/45.27  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
