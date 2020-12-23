%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wCp6yHfKTz

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:25 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 837 expanded)
%              Number of leaves         :   33 ( 271 expanded)
%              Depth                    :   21
%              Number of atoms          :  858 (6484 expanded)
%              Number of equality atoms :   88 ( 582 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('0',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t187_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) )
         => ( ( k7_relat_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) )
           => ( ( k7_relat_1 @ A @ B )
              = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t187_relat_1])).

thf('1',plain,(
    r1_xboole_0 @ sk_B @ ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t87_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_xboole_0 @ X23 @ X24 )
      | ( ( k2_xboole_0 @ ( k4_xboole_0 @ X25 @ X23 ) @ X24 )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ X25 @ X24 ) @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t87_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ ( k1_relat_1 @ sk_A ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ ( k1_relat_1 @ sk_A ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k1_relat_1 @ sk_A ) )
    = ( k4_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ ( k1_relat_1 @ sk_A ) ) @ sk_B ) ),
    inference('sup+',[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ( ( k4_xboole_0 @ X12 @ X13 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t45_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( B
        = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ) )).

thf('9',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X18
        = ( k2_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t55_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X21 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t55_xboole_1])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('14',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('16',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('17',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X12: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X14 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('25',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X18
        = ( k2_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['17','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','28'])).

thf('31',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['4','29','30'])).

thf('32',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('33',plain,
    ( ( k5_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_B )
    = ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t9_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('35',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X27 @ X28 )
      | ( r1_tarski @ ( k2_xboole_0 @ X27 @ X29 ) @ ( k2_xboole_0 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t9_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','28'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X18
        = ( k2_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('41',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k5_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','42'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('44',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('45',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t107_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )).

thf('47',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t107_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    r1_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_B ) ) @ sk_B ),
    inference('sup+',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ ( k1_relat_1 @ sk_A ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ ( k1_relat_1 @ sk_A ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('52',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k1_relat_1 @ sk_A ) )
    = ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k1_relat_1 @ sk_A ) ) @ sk_B ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','28'])).

thf('54',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k1_relat_1 @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k5_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','42'])).

thf('56',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k4_xboole_0 @ ( k5_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('58',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_B ) )
    = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_B ) ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['4','29','30'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('61',plain,
    ( ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k5_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','42'])).

thf('63',plain,
    ( ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('65',plain,(
    ! [X12: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X14 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','28'])).

thf('69',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_B ) )
    = ( k1_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['58','67','68'])).

thf('70',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['49','69'])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('71',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X55 ) @ X56 )
      | ( ( k9_relat_1 @ X55 @ X56 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('72',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k9_relat_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( k9_relat_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['72','73'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('75',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( v1_relat_1 @ X51 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X51 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('76',plain,(
    ! [X53: $i,X54: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X53 @ X54 ) )
        = ( k9_relat_1 @ X53 @ X54 ) )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('77',plain,(
    ! [X57: $i] :
      ( ( ( k2_relat_1 @ X57 )
       != k1_xboole_0 )
      | ( X57 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ( ( k7_relat_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k7_relat_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k7_relat_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ( k7_relat_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['84','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wCp6yHfKTz
% 0.14/0.37  % Computer   : n019.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 12:50:53 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.55/0.75  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.55/0.75  % Solved by: fo/fo7.sh
% 0.55/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.75  % done 710 iterations in 0.266s
% 0.55/0.75  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.55/0.75  % SZS output start Refutation
% 0.55/0.75  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.55/0.75  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.55/0.75  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.55/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.55/0.75  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.55/0.75  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.55/0.75  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.55/0.75  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.55/0.75  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.55/0.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.55/0.75  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.75  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.55/0.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.75  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.55/0.75  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.55/0.75  thf(t4_boole, axiom,
% 0.55/0.75    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.55/0.75  thf('0', plain,
% 0.55/0.75      (![X19 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X19) = (k1_xboole_0))),
% 0.55/0.75      inference('cnf', [status(esa)], [t4_boole])).
% 0.55/0.75  thf(t187_relat_1, conjecture,
% 0.55/0.75    (![A:$i]:
% 0.55/0.75     ( ( v1_relat_1 @ A ) =>
% 0.55/0.75       ( ![B:$i]:
% 0.55/0.75         ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) ) =>
% 0.55/0.75           ( ( k7_relat_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.55/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.75    (~( ![A:$i]:
% 0.55/0.75        ( ( v1_relat_1 @ A ) =>
% 0.55/0.75          ( ![B:$i]:
% 0.55/0.75            ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) ) =>
% 0.55/0.75              ( ( k7_relat_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.55/0.75    inference('cnf.neg', [status(esa)], [t187_relat_1])).
% 0.55/0.75  thf('1', plain, ((r1_xboole_0 @ sk_B @ (k1_relat_1 @ sk_A))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf(t87_xboole_1, axiom,
% 0.55/0.75    (![A:$i,B:$i,C:$i]:
% 0.55/0.75     ( ( r1_xboole_0 @ A @ B ) =>
% 0.55/0.75       ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B ) =
% 0.55/0.75         ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ))).
% 0.55/0.75  thf('2', plain,
% 0.55/0.75      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.55/0.75         (~ (r1_xboole_0 @ X23 @ X24)
% 0.55/0.75          | ((k2_xboole_0 @ (k4_xboole_0 @ X25 @ X23) @ X24)
% 0.55/0.75              = (k4_xboole_0 @ (k2_xboole_0 @ X25 @ X24) @ X23)))),
% 0.55/0.75      inference('cnf', [status(esa)], [t87_xboole_1])).
% 0.55/0.75  thf('3', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ (k1_relat_1 @ sk_A))
% 0.55/0.75           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ (k1_relat_1 @ sk_A)) @ sk_B))),
% 0.55/0.75      inference('sup-', [status(thm)], ['1', '2'])).
% 0.55/0.75  thf('4', plain,
% 0.55/0.75      (((k2_xboole_0 @ k1_xboole_0 @ (k1_relat_1 @ sk_A))
% 0.55/0.75         = (k4_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ (k1_relat_1 @ sk_A)) @ 
% 0.55/0.75            sk_B))),
% 0.55/0.75      inference('sup+', [status(thm)], ['0', '3'])).
% 0.55/0.75  thf('5', plain,
% 0.55/0.75      (![X19 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X19) = (k1_xboole_0))),
% 0.55/0.75      inference('cnf', [status(esa)], [t4_boole])).
% 0.55/0.75  thf(t37_xboole_1, axiom,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.55/0.75  thf('6', plain,
% 0.55/0.75      (![X12 : $i, X13 : $i]:
% 0.55/0.75         ((r1_tarski @ X12 @ X13)
% 0.55/0.75          | ((k4_xboole_0 @ X12 @ X13) != (k1_xboole_0)))),
% 0.55/0.75      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.55/0.75  thf('7', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.55/0.75      inference('sup-', [status(thm)], ['5', '6'])).
% 0.55/0.75  thf('8', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.55/0.75      inference('simplify', [status(thm)], ['7'])).
% 0.55/0.75  thf(t45_xboole_1, axiom,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( r1_tarski @ A @ B ) =>
% 0.55/0.75       ( ( B ) = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ))).
% 0.55/0.75  thf('9', plain,
% 0.55/0.75      (![X17 : $i, X18 : $i]:
% 0.55/0.75         (((X18) = (k2_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))
% 0.55/0.75          | ~ (r1_tarski @ X17 @ X18))),
% 0.55/0.75      inference('cnf', [status(esa)], [t45_xboole_1])).
% 0.55/0.75  thf('10', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         ((X0) = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['8', '9'])).
% 0.55/0.75  thf('11', plain,
% 0.55/0.75      (![X19 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X19) = (k1_xboole_0))),
% 0.55/0.75      inference('cnf', [status(esa)], [t4_boole])).
% 0.55/0.75  thf(t55_xboole_1, axiom,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) =
% 0.55/0.75       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.55/0.75  thf('12', plain,
% 0.55/0.75      (![X20 : $i, X21 : $i]:
% 0.55/0.75         ((k4_xboole_0 @ (k2_xboole_0 @ X20 @ X21) @ (k3_xboole_0 @ X20 @ X21))
% 0.55/0.75           = (k2_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ 
% 0.55/0.75              (k4_xboole_0 @ X21 @ X20)))),
% 0.55/0.75      inference('cnf', [status(esa)], [t55_xboole_1])).
% 0.55/0.75  thf(l98_xboole_1, axiom,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( k5_xboole_0 @ A @ B ) =
% 0.55/0.75       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.55/0.75  thf('13', plain,
% 0.55/0.75      (![X4 : $i, X5 : $i]:
% 0.55/0.75         ((k5_xboole_0 @ X4 @ X5)
% 0.55/0.75           = (k4_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ (k3_xboole_0 @ X4 @ X5)))),
% 0.55/0.75      inference('cnf', [status(esa)], [l98_xboole_1])).
% 0.55/0.75  thf('14', plain,
% 0.55/0.75      (![X20 : $i, X21 : $i]:
% 0.55/0.75         ((k5_xboole_0 @ X20 @ X21)
% 0.55/0.75           = (k2_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ 
% 0.55/0.75              (k4_xboole_0 @ X21 @ X20)))),
% 0.55/0.75      inference('demod', [status(thm)], ['12', '13'])).
% 0.55/0.75  thf('15', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         ((k5_xboole_0 @ X0 @ k1_xboole_0)
% 0.55/0.75           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.55/0.75      inference('sup+', [status(thm)], ['11', '14'])).
% 0.55/0.75  thf(t5_boole, axiom,
% 0.55/0.75    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.55/0.75  thf('16', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.55/0.75      inference('cnf', [status(esa)], [t5_boole])).
% 0.55/0.75  thf('17', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         ((X0) = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.55/0.75      inference('demod', [status(thm)], ['15', '16'])).
% 0.55/0.75  thf(d3_tarski, axiom,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( r1_tarski @ A @ B ) <=>
% 0.55/0.75       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.55/0.75  thf('18', plain,
% 0.55/0.75      (![X1 : $i, X3 : $i]:
% 0.55/0.75         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.55/0.75      inference('cnf', [status(esa)], [d3_tarski])).
% 0.55/0.75  thf('19', plain,
% 0.55/0.75      (![X1 : $i, X3 : $i]:
% 0.55/0.75         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.55/0.75      inference('cnf', [status(esa)], [d3_tarski])).
% 0.55/0.75  thf('20', plain,
% 0.55/0.75      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.55/0.75      inference('sup-', [status(thm)], ['18', '19'])).
% 0.55/0.75  thf('21', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.55/0.75      inference('simplify', [status(thm)], ['20'])).
% 0.55/0.75  thf('22', plain,
% 0.55/0.75      (![X12 : $i, X14 : $i]:
% 0.55/0.75         (((k4_xboole_0 @ X12 @ X14) = (k1_xboole_0))
% 0.55/0.75          | ~ (r1_tarski @ X12 @ X14))),
% 0.55/0.75      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.55/0.75  thf('23', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.55/0.75      inference('sup-', [status(thm)], ['21', '22'])).
% 0.55/0.75  thf('24', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.55/0.75      inference('simplify', [status(thm)], ['20'])).
% 0.55/0.75  thf('25', plain,
% 0.55/0.75      (![X17 : $i, X18 : $i]:
% 0.55/0.75         (((X18) = (k2_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))
% 0.55/0.75          | ~ (r1_tarski @ X17 @ X18))),
% 0.55/0.75      inference('cnf', [status(esa)], [t45_xboole_1])).
% 0.55/0.75  thf('26', plain,
% 0.55/0.75      (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['24', '25'])).
% 0.55/0.75  thf('27', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.55/0.75      inference('sup+', [status(thm)], ['23', '26'])).
% 0.55/0.75  thf('28', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.55/0.75      inference('demod', [status(thm)], ['17', '27'])).
% 0.55/0.75  thf('29', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.55/0.75      inference('demod', [status(thm)], ['10', '28'])).
% 0.55/0.75  thf('30', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.55/0.75      inference('demod', [status(thm)], ['10', '28'])).
% 0.55/0.75  thf('31', plain,
% 0.55/0.75      (((k1_relat_1 @ sk_A) = (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_B))),
% 0.55/0.75      inference('demod', [status(thm)], ['4', '29', '30'])).
% 0.55/0.75  thf('32', plain,
% 0.55/0.75      (![X20 : $i, X21 : $i]:
% 0.55/0.75         ((k5_xboole_0 @ X20 @ X21)
% 0.55/0.75           = (k2_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ 
% 0.55/0.75              (k4_xboole_0 @ X21 @ X20)))),
% 0.55/0.75      inference('demod', [status(thm)], ['12', '13'])).
% 0.55/0.75  thf('33', plain,
% 0.55/0.75      (((k5_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_B)
% 0.55/0.75         = (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ 
% 0.55/0.75            (k4_xboole_0 @ sk_B @ (k1_relat_1 @ sk_A))))),
% 0.55/0.75      inference('sup+', [status(thm)], ['31', '32'])).
% 0.55/0.75  thf('34', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.55/0.75      inference('simplify', [status(thm)], ['7'])).
% 0.55/0.75  thf(t9_xboole_1, axiom,
% 0.55/0.75    (![A:$i,B:$i,C:$i]:
% 0.55/0.75     ( ( r1_tarski @ A @ B ) =>
% 0.55/0.75       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.55/0.75  thf('35', plain,
% 0.55/0.75      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.55/0.75         (~ (r1_tarski @ X27 @ X28)
% 0.55/0.75          | (r1_tarski @ (k2_xboole_0 @ X27 @ X29) @ (k2_xboole_0 @ X28 @ X29)))),
% 0.55/0.75      inference('cnf', [status(esa)], [t9_xboole_1])).
% 0.55/0.75  thf('36', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         (r1_tarski @ (k2_xboole_0 @ k1_xboole_0 @ X1) @ 
% 0.55/0.75          (k2_xboole_0 @ X0 @ X1))),
% 0.55/0.75      inference('sup-', [status(thm)], ['34', '35'])).
% 0.55/0.75  thf('37', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.55/0.75      inference('demod', [status(thm)], ['10', '28'])).
% 0.55/0.75  thf('38', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ X1))),
% 0.55/0.75      inference('demod', [status(thm)], ['36', '37'])).
% 0.55/0.75  thf('39', plain,
% 0.55/0.75      (![X17 : $i, X18 : $i]:
% 0.55/0.75         (((X18) = (k2_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))
% 0.55/0.75          | ~ (r1_tarski @ X17 @ X18))),
% 0.55/0.75      inference('cnf', [status(esa)], [t45_xboole_1])).
% 0.55/0.75  thf('40', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         ((k2_xboole_0 @ X1 @ X0)
% 0.55/0.75           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['38', '39'])).
% 0.55/0.75  thf(t40_xboole_1, axiom,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.55/0.75  thf('41', plain,
% 0.55/0.75      (![X15 : $i, X16 : $i]:
% 0.55/0.75         ((k4_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ X16)
% 0.55/0.75           = (k4_xboole_0 @ X15 @ X16))),
% 0.55/0.75      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.55/0.75  thf('42', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         ((k2_xboole_0 @ X1 @ X0)
% 0.55/0.75           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.55/0.75      inference('demod', [status(thm)], ['40', '41'])).
% 0.55/0.75  thf('43', plain,
% 0.55/0.75      (((k5_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_B)
% 0.55/0.75         = (k2_xboole_0 @ sk_B @ (k1_relat_1 @ sk_A)))),
% 0.55/0.75      inference('demod', [status(thm)], ['33', '42'])).
% 0.55/0.75  thf(t21_xboole_1, axiom,
% 0.55/0.75    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.55/0.75  thf('44', plain,
% 0.55/0.75      (![X10 : $i, X11 : $i]:
% 0.55/0.75         ((k3_xboole_0 @ X10 @ (k2_xboole_0 @ X10 @ X11)) = (X10))),
% 0.55/0.75      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.55/0.75  thf('45', plain,
% 0.55/0.75      (((k3_xboole_0 @ sk_B @ (k5_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_B))
% 0.55/0.75         = (sk_B))),
% 0.55/0.75      inference('sup+', [status(thm)], ['43', '44'])).
% 0.55/0.75  thf('46', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.55/0.75      inference('simplify', [status(thm)], ['20'])).
% 0.55/0.75  thf(t107_xboole_1, axiom,
% 0.55/0.75    (![A:$i,B:$i,C:$i]:
% 0.55/0.75     ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.55/0.75       ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 0.55/0.75         ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.55/0.75  thf('47', plain,
% 0.55/0.75      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.55/0.75         ((r1_xboole_0 @ X6 @ (k3_xboole_0 @ X7 @ X8))
% 0.55/0.75          | ~ (r1_tarski @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.55/0.75      inference('cnf', [status(esa)], [t107_xboole_1])).
% 0.55/0.75  thf('48', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         (r1_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))),
% 0.55/0.75      inference('sup-', [status(thm)], ['46', '47'])).
% 0.55/0.75  thf('49', plain,
% 0.55/0.75      ((r1_xboole_0 @ 
% 0.55/0.75        (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_B)) @ 
% 0.55/0.75        sk_B)),
% 0.55/0.75      inference('sup+', [status(thm)], ['45', '48'])).
% 0.55/0.75  thf('50', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.55/0.75      inference('sup-', [status(thm)], ['21', '22'])).
% 0.55/0.75  thf('51', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ (k1_relat_1 @ sk_A))
% 0.55/0.75           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ (k1_relat_1 @ sk_A)) @ sk_B))),
% 0.55/0.75      inference('sup-', [status(thm)], ['1', '2'])).
% 0.55/0.75  thf('52', plain,
% 0.55/0.75      (((k2_xboole_0 @ k1_xboole_0 @ (k1_relat_1 @ sk_A))
% 0.55/0.75         = (k4_xboole_0 @ (k2_xboole_0 @ sk_B @ (k1_relat_1 @ sk_A)) @ sk_B))),
% 0.55/0.75      inference('sup+', [status(thm)], ['50', '51'])).
% 0.55/0.75  thf('53', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.55/0.75      inference('demod', [status(thm)], ['10', '28'])).
% 0.55/0.75  thf('54', plain,
% 0.55/0.75      (((k1_relat_1 @ sk_A)
% 0.55/0.75         = (k4_xboole_0 @ (k2_xboole_0 @ sk_B @ (k1_relat_1 @ sk_A)) @ sk_B))),
% 0.55/0.75      inference('demod', [status(thm)], ['52', '53'])).
% 0.55/0.75  thf('55', plain,
% 0.55/0.75      (((k5_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_B)
% 0.55/0.75         = (k2_xboole_0 @ sk_B @ (k1_relat_1 @ sk_A)))),
% 0.55/0.75      inference('demod', [status(thm)], ['33', '42'])).
% 0.55/0.75  thf('56', plain,
% 0.55/0.75      (((k1_relat_1 @ sk_A)
% 0.55/0.75         = (k4_xboole_0 @ (k5_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_B) @ sk_B))),
% 0.55/0.75      inference('demod', [status(thm)], ['54', '55'])).
% 0.55/0.75  thf('57', plain,
% 0.55/0.75      (![X20 : $i, X21 : $i]:
% 0.55/0.75         ((k5_xboole_0 @ X20 @ X21)
% 0.55/0.75           = (k2_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ 
% 0.55/0.75              (k4_xboole_0 @ X21 @ X20)))),
% 0.55/0.75      inference('demod', [status(thm)], ['12', '13'])).
% 0.55/0.75  thf('58', plain,
% 0.55/0.75      (((k5_xboole_0 @ sk_B @ (k5_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_B))
% 0.55/0.75         = (k2_xboole_0 @ 
% 0.55/0.75            (k4_xboole_0 @ sk_B @ (k5_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_B)) @ 
% 0.55/0.75            (k1_relat_1 @ sk_A)))),
% 0.55/0.75      inference('sup+', [status(thm)], ['56', '57'])).
% 0.55/0.75  thf('59', plain,
% 0.55/0.75      (((k1_relat_1 @ sk_A) = (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_B))),
% 0.55/0.75      inference('demod', [status(thm)], ['4', '29', '30'])).
% 0.55/0.75  thf('60', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         ((k2_xboole_0 @ X1 @ X0)
% 0.55/0.75           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.55/0.75      inference('demod', [status(thm)], ['40', '41'])).
% 0.55/0.75  thf('61', plain,
% 0.55/0.75      (((k2_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_B)
% 0.55/0.75         = (k2_xboole_0 @ sk_B @ (k1_relat_1 @ sk_A)))),
% 0.55/0.75      inference('sup+', [status(thm)], ['59', '60'])).
% 0.55/0.75  thf('62', plain,
% 0.55/0.75      (((k5_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_B)
% 0.55/0.75         = (k2_xboole_0 @ sk_B @ (k1_relat_1 @ sk_A)))),
% 0.55/0.75      inference('demod', [status(thm)], ['33', '42'])).
% 0.55/0.75  thf('63', plain,
% 0.55/0.75      (((k2_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_B)
% 0.55/0.75         = (k5_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_B))),
% 0.55/0.75      inference('demod', [status(thm)], ['61', '62'])).
% 0.55/0.75  thf('64', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ X1))),
% 0.55/0.75      inference('demod', [status(thm)], ['36', '37'])).
% 0.55/0.75  thf('65', plain,
% 0.55/0.75      (![X12 : $i, X14 : $i]:
% 0.55/0.75         (((k4_xboole_0 @ X12 @ X14) = (k1_xboole_0))
% 0.55/0.75          | ~ (r1_tarski @ X12 @ X14))),
% 0.55/0.75      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.55/0.75  thf('66', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.55/0.75      inference('sup-', [status(thm)], ['64', '65'])).
% 0.55/0.75  thf('67', plain,
% 0.55/0.75      (((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_B))
% 0.55/0.75         = (k1_xboole_0))),
% 0.55/0.75      inference('sup+', [status(thm)], ['63', '66'])).
% 0.55/0.75  thf('68', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.55/0.75      inference('demod', [status(thm)], ['10', '28'])).
% 0.55/0.75  thf('69', plain,
% 0.55/0.75      (((k5_xboole_0 @ sk_B @ (k5_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_B))
% 0.55/0.75         = (k1_relat_1 @ sk_A))),
% 0.55/0.75      inference('demod', [status(thm)], ['58', '67', '68'])).
% 0.55/0.75  thf('70', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_B)),
% 0.55/0.75      inference('demod', [status(thm)], ['49', '69'])).
% 0.55/0.75  thf(t151_relat_1, axiom,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( v1_relat_1 @ B ) =>
% 0.55/0.75       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.55/0.75         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.55/0.75  thf('71', plain,
% 0.55/0.75      (![X55 : $i, X56 : $i]:
% 0.55/0.75         (~ (r1_xboole_0 @ (k1_relat_1 @ X55) @ X56)
% 0.55/0.75          | ((k9_relat_1 @ X55 @ X56) = (k1_xboole_0))
% 0.55/0.75          | ~ (v1_relat_1 @ X55))),
% 0.55/0.75      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.55/0.75  thf('72', plain,
% 0.55/0.75      ((~ (v1_relat_1 @ sk_A) | ((k9_relat_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['70', '71'])).
% 0.55/0.75  thf('73', plain, ((v1_relat_1 @ sk_A)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('74', plain, (((k9_relat_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.55/0.75      inference('demod', [status(thm)], ['72', '73'])).
% 0.55/0.75  thf(dt_k7_relat_1, axiom,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.55/0.75  thf('75', plain,
% 0.55/0.75      (![X51 : $i, X52 : $i]:
% 0.55/0.75         (~ (v1_relat_1 @ X51) | (v1_relat_1 @ (k7_relat_1 @ X51 @ X52)))),
% 0.55/0.75      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.55/0.75  thf(t148_relat_1, axiom,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( v1_relat_1 @ B ) =>
% 0.55/0.75       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.55/0.75  thf('76', plain,
% 0.55/0.75      (![X53 : $i, X54 : $i]:
% 0.55/0.75         (((k2_relat_1 @ (k7_relat_1 @ X53 @ X54)) = (k9_relat_1 @ X53 @ X54))
% 0.55/0.75          | ~ (v1_relat_1 @ X53))),
% 0.55/0.75      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.55/0.75  thf(t64_relat_1, axiom,
% 0.55/0.75    (![A:$i]:
% 0.55/0.75     ( ( v1_relat_1 @ A ) =>
% 0.55/0.75       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.55/0.75           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.55/0.75         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.55/0.75  thf('77', plain,
% 0.55/0.75      (![X57 : $i]:
% 0.55/0.75         (((k2_relat_1 @ X57) != (k1_xboole_0))
% 0.55/0.75          | ((X57) = (k1_xboole_0))
% 0.55/0.75          | ~ (v1_relat_1 @ X57))),
% 0.55/0.75      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.55/0.75  thf('78', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         (((k9_relat_1 @ X1 @ X0) != (k1_xboole_0))
% 0.55/0.75          | ~ (v1_relat_1 @ X1)
% 0.55/0.75          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.55/0.75          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['76', '77'])).
% 0.55/0.75  thf('79', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         (~ (v1_relat_1 @ X1)
% 0.55/0.75          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.55/0.75          | ~ (v1_relat_1 @ X1)
% 0.55/0.75          | ((k9_relat_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['75', '78'])).
% 0.55/0.75  thf('80', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         (((k9_relat_1 @ X1 @ X0) != (k1_xboole_0))
% 0.55/0.75          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.55/0.75          | ~ (v1_relat_1 @ X1))),
% 0.55/0.75      inference('simplify', [status(thm)], ['79'])).
% 0.55/0.75  thf('81', plain,
% 0.55/0.75      ((((k1_xboole_0) != (k1_xboole_0))
% 0.55/0.75        | ~ (v1_relat_1 @ sk_A)
% 0.55/0.75        | ((k7_relat_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['74', '80'])).
% 0.55/0.75  thf('82', plain, ((v1_relat_1 @ sk_A)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('83', plain,
% 0.55/0.75      ((((k1_xboole_0) != (k1_xboole_0))
% 0.55/0.75        | ((k7_relat_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.55/0.75      inference('demod', [status(thm)], ['81', '82'])).
% 0.55/0.75  thf('84', plain, (((k7_relat_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.55/0.75      inference('simplify', [status(thm)], ['83'])).
% 0.55/0.75  thf('85', plain, (((k7_relat_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('86', plain, ($false),
% 0.55/0.75      inference('simplify_reflect-', [status(thm)], ['84', '85'])).
% 0.55/0.75  
% 0.55/0.75  % SZS output end Refutation
% 0.55/0.75  
% 0.55/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
