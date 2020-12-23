%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.04PreVFA2h

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:09 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 670 expanded)
%              Number of leaves         :   23 ( 218 expanded)
%              Depth                    :   27
%              Number of atoms          : 1002 (5536 expanded)
%              Number of equality atoms :   55 ( 285 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t95_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( ( k7_relat_1 @ B @ A )
            = k1_xboole_0 )
        <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t95_relat_1])).

thf('0',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('4',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('7',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t86_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('9',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X26 @ ( k1_relat_1 @ ( k7_relat_1 @ X28 @ X27 ) ) )
      | ( r2_hidden @ X26 @ ( k1_relat_1 @ X28 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('12',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r1_xboole_0 @ X2 @ ( k1_relat_1 @ X0 ) )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ ( k1_relat_1 @ X0 ) )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_B )
        | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ sk_A ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['7','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ sk_A )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('20',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X26 @ ( k1_relat_1 @ ( k7_relat_1 @ X28 @ X27 ) ) )
      | ( r2_hidden @ X26 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ X1 )
        | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ sk_A ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf('26',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('27',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('28',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_B )
        | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) @ X0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) @ X0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) @ X0 )
        = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('37',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('38',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('39',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('44',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','46'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('53',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('65',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','68'])).

thf('70',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('73',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['36','73'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('75',plain,(
    ! [X25: $i] :
      ( ( ( k1_relat_1 @ X25 )
       != k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('76',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      | ( ( k7_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( ( k7_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( ( k7_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['3','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('82',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k7_relat_1 @ sk_B @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','83'])).

thf('85',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','84'])).

thf('86',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('87',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('88',plain,
    ( ( k7_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','83','87'])).

thf('89',plain,
    ( ( k7_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['86','88'])).

thf('90',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('91',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('92',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X26 @ X27 )
      | ~ ( r2_hidden @ X26 @ ( k1_relat_1 @ X28 ) )
      | ( r2_hidden @ X26 @ ( k1_relat_1 @ ( k7_relat_1 @ X28 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X2 ) ) )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ X1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ X1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['89','98'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('100',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('102',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['99','100','101','102'])).

thf('104',plain,(
    $false ),
    inference(demod,[status(thm)],['85','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.04PreVFA2h
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:20:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.69/0.87  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.69/0.87  % Solved by: fo/fo7.sh
% 0.69/0.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.87  % done 1330 iterations in 0.409s
% 0.69/0.87  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.69/0.87  % SZS output start Refutation
% 0.69/0.87  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.69/0.87  thf(sk_B_type, type, sk_B: $i).
% 0.69/0.87  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.69/0.87  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.69/0.87  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.87  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.69/0.87  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.69/0.87  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.69/0.87  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.69/0.87  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.69/0.87  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.69/0.87  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.69/0.87  thf(t95_relat_1, conjecture,
% 0.69/0.87    (![A:$i,B:$i]:
% 0.69/0.87     ( ( v1_relat_1 @ B ) =>
% 0.69/0.87       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.69/0.87         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.69/0.87  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.87    (~( ![A:$i,B:$i]:
% 0.69/0.87        ( ( v1_relat_1 @ B ) =>
% 0.69/0.87          ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.69/0.87            ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 0.69/0.87    inference('cnf.neg', [status(esa)], [t95_relat_1])).
% 0.69/0.87  thf('0', plain,
% 0.69/0.87      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.69/0.87        | ((k7_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('1', plain,
% 0.69/0.87      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.69/0.87         <= (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.69/0.87      inference('split', [status(esa)], ['0'])).
% 0.69/0.87  thf('2', plain,
% 0.69/0.87      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.69/0.87       ~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.69/0.87      inference('split', [status(esa)], ['0'])).
% 0.69/0.87  thf(dt_k7_relat_1, axiom,
% 0.69/0.87    (![A:$i,B:$i]:
% 0.69/0.87     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.69/0.87  thf('3', plain,
% 0.69/0.87      (![X23 : $i, X24 : $i]:
% 0.69/0.87         (~ (v1_relat_1 @ X23) | (v1_relat_1 @ (k7_relat_1 @ X23 @ X24)))),
% 0.69/0.87      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.69/0.87  thf('4', plain,
% 0.69/0.87      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.69/0.87        | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('5', plain,
% 0.69/0.87      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.69/0.87         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.69/0.87      inference('split', [status(esa)], ['4'])).
% 0.69/0.87  thf(symmetry_r1_xboole_0, axiom,
% 0.69/0.87    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.69/0.87  thf('6', plain,
% 0.69/0.87      (![X3 : $i, X4 : $i]:
% 0.69/0.87         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.69/0.87      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.69/0.87  thf('7', plain,
% 0.69/0.87      (((r1_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.69/0.87         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['5', '6'])).
% 0.69/0.87  thf(t3_xboole_0, axiom,
% 0.69/0.87    (![A:$i,B:$i]:
% 0.69/0.87     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.69/0.87            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.69/0.87       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.69/0.87            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.69/0.87  thf('8', plain,
% 0.69/0.87      (![X5 : $i, X6 : $i]:
% 0.69/0.87         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X5))),
% 0.69/0.87      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.69/0.87  thf(t86_relat_1, axiom,
% 0.69/0.87    (![A:$i,B:$i,C:$i]:
% 0.69/0.87     ( ( v1_relat_1 @ C ) =>
% 0.69/0.87       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 0.69/0.87         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 0.69/0.87  thf('9', plain,
% 0.69/0.87      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.69/0.87         (~ (r2_hidden @ X26 @ (k1_relat_1 @ (k7_relat_1 @ X28 @ X27)))
% 0.69/0.87          | (r2_hidden @ X26 @ (k1_relat_1 @ X28))
% 0.69/0.87          | ~ (v1_relat_1 @ X28))),
% 0.69/0.87      inference('cnf', [status(esa)], [t86_relat_1])).
% 0.69/0.87  thf('10', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.87         ((r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2)
% 0.69/0.87          | ~ (v1_relat_1 @ X1)
% 0.69/0.87          | (r2_hidden @ (sk_C @ X2 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))) @ 
% 0.69/0.87             (k1_relat_1 @ X1)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['8', '9'])).
% 0.69/0.87  thf('11', plain,
% 0.69/0.87      (![X5 : $i, X6 : $i]:
% 0.69/0.87         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X6))),
% 0.69/0.87      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.69/0.87  thf('12', plain,
% 0.69/0.87      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.69/0.87         (~ (r2_hidden @ X7 @ X5)
% 0.69/0.87          | ~ (r2_hidden @ X7 @ X8)
% 0.69/0.87          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.69/0.87      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.69/0.87  thf('13', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.87         ((r1_xboole_0 @ X1 @ X0)
% 0.69/0.87          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.69/0.87          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.69/0.87      inference('sup-', [status(thm)], ['11', '12'])).
% 0.69/0.87  thf('14', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.87         (~ (v1_relat_1 @ X0)
% 0.69/0.87          | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ X2)
% 0.69/0.87          | ~ (r1_xboole_0 @ X2 @ (k1_relat_1 @ X0))
% 0.69/0.87          | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ X2))),
% 0.69/0.87      inference('sup-', [status(thm)], ['10', '13'])).
% 0.69/0.87  thf('15', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.87         (~ (r1_xboole_0 @ X2 @ (k1_relat_1 @ X0))
% 0.69/0.87          | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ X2)
% 0.69/0.87          | ~ (v1_relat_1 @ X0))),
% 0.69/0.87      inference('simplify', [status(thm)], ['14'])).
% 0.69/0.87  thf('16', plain,
% 0.69/0.87      ((![X0 : $i]:
% 0.69/0.87          (~ (v1_relat_1 @ sk_B)
% 0.69/0.87           | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ sk_A)))
% 0.69/0.87         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['7', '15'])).
% 0.69/0.87  thf('17', plain, ((v1_relat_1 @ sk_B)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('18', plain,
% 0.69/0.87      ((![X0 : $i]:
% 0.69/0.87          (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ sk_A))
% 0.69/0.87         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.69/0.87      inference('demod', [status(thm)], ['16', '17'])).
% 0.69/0.87  thf('19', plain,
% 0.69/0.87      (![X5 : $i, X6 : $i]:
% 0.69/0.87         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X5))),
% 0.69/0.87      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.69/0.87  thf('20', plain,
% 0.69/0.87      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.69/0.87         (~ (r2_hidden @ X26 @ (k1_relat_1 @ (k7_relat_1 @ X28 @ X27)))
% 0.69/0.87          | (r2_hidden @ X26 @ X27)
% 0.69/0.87          | ~ (v1_relat_1 @ X28))),
% 0.69/0.87      inference('cnf', [status(esa)], [t86_relat_1])).
% 0.69/0.87  thf('21', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.87         ((r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2)
% 0.69/0.87          | ~ (v1_relat_1 @ X1)
% 0.69/0.87          | (r2_hidden @ (sk_C @ X2 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))) @ 
% 0.69/0.87             X0))),
% 0.69/0.87      inference('sup-', [status(thm)], ['19', '20'])).
% 0.69/0.87  thf('22', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.87         ((r1_xboole_0 @ X1 @ X0)
% 0.69/0.87          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.69/0.87          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.69/0.87      inference('sup-', [status(thm)], ['11', '12'])).
% 0.69/0.87  thf('23', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.87         (~ (v1_relat_1 @ X1)
% 0.69/0.87          | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2)
% 0.69/0.87          | ~ (r1_xboole_0 @ X2 @ X0)
% 0.69/0.87          | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2))),
% 0.69/0.87      inference('sup-', [status(thm)], ['21', '22'])).
% 0.69/0.87  thf('24', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.87         (~ (r1_xboole_0 @ X2 @ X0)
% 0.69/0.87          | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2)
% 0.69/0.87          | ~ (v1_relat_1 @ X1))),
% 0.69/0.87      inference('simplify', [status(thm)], ['23'])).
% 0.69/0.87  thf('25', plain,
% 0.69/0.87      ((![X0 : $i, X1 : $i]:
% 0.69/0.87          (~ (v1_relat_1 @ X1)
% 0.69/0.87           | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ sk_A)) @ 
% 0.69/0.87              (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))))
% 0.69/0.87         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['18', '24'])).
% 0.69/0.87  thf('26', plain,
% 0.69/0.87      (![X5 : $i, X6 : $i]:
% 0.69/0.87         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X5))),
% 0.69/0.87      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.69/0.87  thf('27', plain,
% 0.69/0.87      (![X5 : $i, X6 : $i]:
% 0.69/0.87         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X5))),
% 0.69/0.87      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.69/0.87  thf('28', plain,
% 0.69/0.87      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.69/0.87         (~ (r2_hidden @ X7 @ X5)
% 0.69/0.87          | ~ (r2_hidden @ X7 @ X8)
% 0.69/0.87          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.69/0.87      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.69/0.87  thf('29', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.87         ((r1_xboole_0 @ X0 @ X1)
% 0.69/0.87          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.69/0.87          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.69/0.87      inference('sup-', [status(thm)], ['27', '28'])).
% 0.69/0.87  thf('30', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i]:
% 0.69/0.87         ((r1_xboole_0 @ X0 @ X1)
% 0.69/0.87          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.69/0.87          | (r1_xboole_0 @ X0 @ X1))),
% 0.69/0.87      inference('sup-', [status(thm)], ['26', '29'])).
% 0.69/0.87  thf('31', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i]:
% 0.69/0.87         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.69/0.87      inference('simplify', [status(thm)], ['30'])).
% 0.69/0.87  thf('32', plain,
% 0.69/0.87      ((![X0 : $i]:
% 0.69/0.87          (~ (v1_relat_1 @ sk_B)
% 0.69/0.87           | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) @ X0)))
% 0.69/0.87         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['25', '31'])).
% 0.69/0.87  thf('33', plain, ((v1_relat_1 @ sk_B)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('34', plain,
% 0.69/0.87      ((![X0 : $i]:
% 0.69/0.87          (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) @ X0))
% 0.69/0.87         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.69/0.87      inference('demod', [status(thm)], ['32', '33'])).
% 0.69/0.87  thf(d7_xboole_0, axiom,
% 0.69/0.87    (![A:$i,B:$i]:
% 0.69/0.87     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.69/0.87       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.69/0.87  thf('35', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i]:
% 0.69/0.87         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.69/0.87      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.69/0.87  thf('36', plain,
% 0.69/0.87      ((![X0 : $i]:
% 0.69/0.87          ((k3_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) @ X0)
% 0.69/0.87            = (k1_xboole_0)))
% 0.69/0.87         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['34', '35'])).
% 0.69/0.87  thf(t48_xboole_1, axiom,
% 0.69/0.87    (![A:$i,B:$i]:
% 0.69/0.87     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.69/0.87  thf('37', plain,
% 0.69/0.87      (![X9 : $i, X10 : $i]:
% 0.69/0.87         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.69/0.87           = (k3_xboole_0 @ X9 @ X10))),
% 0.69/0.87      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.69/0.87  thf(t79_xboole_1, axiom,
% 0.69/0.87    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.69/0.87  thf('38', plain,
% 0.69/0.87      (![X11 : $i, X12 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X12)),
% 0.69/0.87      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.69/0.87  thf('39', plain,
% 0.69/0.87      (![X3 : $i, X4 : $i]:
% 0.69/0.87         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.69/0.87      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.69/0.87  thf('40', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.69/0.87      inference('sup-', [status(thm)], ['38', '39'])).
% 0.69/0.87  thf('41', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i]:
% 0.69/0.87         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.69/0.87      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.69/0.87  thf('42', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i]:
% 0.69/0.87         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.69/0.87      inference('sup-', [status(thm)], ['40', '41'])).
% 0.69/0.87  thf('43', plain,
% 0.69/0.87      (![X9 : $i, X10 : $i]:
% 0.69/0.87         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.69/0.87           = (k3_xboole_0 @ X9 @ X10))),
% 0.69/0.87      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.69/0.87  thf('44', plain,
% 0.69/0.87      (![X11 : $i, X12 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X12)),
% 0.69/0.87      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.69/0.87  thf('45', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i]:
% 0.69/0.87         (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))),
% 0.69/0.87      inference('sup+', [status(thm)], ['43', '44'])).
% 0.69/0.87  thf('46', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i]:
% 0.69/0.87         (r1_xboole_0 @ k1_xboole_0 @ 
% 0.69/0.87          (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.69/0.87      inference('sup+', [status(thm)], ['42', '45'])).
% 0.69/0.87  thf('47', plain,
% 0.69/0.87      (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X0 @ X0))),
% 0.69/0.87      inference('sup+', [status(thm)], ['37', '46'])).
% 0.69/0.87  thf('48', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i]:
% 0.69/0.87         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.69/0.87      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.69/0.87  thf('49', plain,
% 0.69/0.87      (![X0 : $i]:
% 0.69/0.87         ((k3_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.69/0.87      inference('sup-', [status(thm)], ['47', '48'])).
% 0.69/0.87  thf('50', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i]:
% 0.69/0.87         (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))),
% 0.69/0.87      inference('sup+', [status(thm)], ['43', '44'])).
% 0.69/0.87  thf('51', plain,
% 0.69/0.87      (![X0 : $i]:
% 0.69/0.87         (r1_xboole_0 @ k1_xboole_0 @ 
% 0.69/0.87          (k4_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X0 @ X0)))),
% 0.69/0.87      inference('sup+', [status(thm)], ['49', '50'])).
% 0.69/0.87  thf('52', plain,
% 0.69/0.87      (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X0 @ X0))),
% 0.69/0.87      inference('sup+', [status(thm)], ['37', '46'])).
% 0.69/0.87  thf(t83_xboole_1, axiom,
% 0.69/0.87    (![A:$i,B:$i]:
% 0.69/0.87     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.69/0.87  thf('53', plain,
% 0.69/0.87      (![X13 : $i, X14 : $i]:
% 0.69/0.87         (((k4_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_xboole_0 @ X13 @ X14))),
% 0.69/0.87      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.69/0.87  thf('54', plain,
% 0.69/0.87      (![X0 : $i]:
% 0.69/0.87         ((k4_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.69/0.87      inference('sup-', [status(thm)], ['52', '53'])).
% 0.69/0.87  thf('55', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.69/0.87      inference('demod', [status(thm)], ['51', '54'])).
% 0.69/0.87  thf('56', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i]:
% 0.69/0.87         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.69/0.87      inference('simplify', [status(thm)], ['30'])).
% 0.69/0.87  thf('57', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.69/0.87      inference('sup-', [status(thm)], ['55', '56'])).
% 0.69/0.87  thf('58', plain,
% 0.69/0.87      (![X3 : $i, X4 : $i]:
% 0.69/0.87         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.69/0.87      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.69/0.87  thf('59', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.69/0.87      inference('sup-', [status(thm)], ['57', '58'])).
% 0.69/0.87  thf('60', plain,
% 0.69/0.87      (![X13 : $i, X14 : $i]:
% 0.69/0.87         (((k4_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_xboole_0 @ X13 @ X14))),
% 0.69/0.87      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.69/0.87  thf('61', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.69/0.87      inference('sup-', [status(thm)], ['59', '60'])).
% 0.69/0.87  thf('62', plain,
% 0.69/0.87      (![X9 : $i, X10 : $i]:
% 0.69/0.87         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.69/0.87           = (k3_xboole_0 @ X9 @ X10))),
% 0.69/0.87      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.69/0.87  thf('63', plain,
% 0.69/0.87      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.69/0.87      inference('sup+', [status(thm)], ['61', '62'])).
% 0.69/0.87  thf('64', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.69/0.87      inference('sup-', [status(thm)], ['55', '56'])).
% 0.69/0.87  thf('65', plain,
% 0.69/0.87      (![X13 : $i, X14 : $i]:
% 0.69/0.87         (((k4_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_xboole_0 @ X13 @ X14))),
% 0.69/0.87      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.69/0.87  thf('66', plain,
% 0.69/0.87      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.69/0.87      inference('sup-', [status(thm)], ['64', '65'])).
% 0.69/0.87  thf('67', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i]:
% 0.69/0.87         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.69/0.87      inference('sup-', [status(thm)], ['40', '41'])).
% 0.69/0.87  thf('68', plain,
% 0.69/0.87      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.69/0.87      inference('sup+', [status(thm)], ['66', '67'])).
% 0.69/0.87  thf('69', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.69/0.87      inference('demod', [status(thm)], ['63', '68'])).
% 0.69/0.87  thf('70', plain,
% 0.69/0.87      (![X9 : $i, X10 : $i]:
% 0.69/0.87         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.69/0.87           = (k3_xboole_0 @ X9 @ X10))),
% 0.69/0.87      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.69/0.87  thf('71', plain,
% 0.69/0.87      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.69/0.87      inference('sup+', [status(thm)], ['69', '70'])).
% 0.69/0.87  thf('72', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.69/0.87      inference('sup-', [status(thm)], ['59', '60'])).
% 0.69/0.87  thf('73', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.69/0.87      inference('demod', [status(thm)], ['71', '72'])).
% 0.69/0.87  thf('74', plain,
% 0.69/0.87      ((((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (k1_xboole_0)))
% 0.69/0.87         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.69/0.87      inference('sup+', [status(thm)], ['36', '73'])).
% 0.69/0.87  thf(t64_relat_1, axiom,
% 0.69/0.87    (![A:$i]:
% 0.69/0.87     ( ( v1_relat_1 @ A ) =>
% 0.69/0.87       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.69/0.87           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.69/0.87         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.69/0.87  thf('75', plain,
% 0.69/0.87      (![X25 : $i]:
% 0.69/0.87         (((k1_relat_1 @ X25) != (k1_xboole_0))
% 0.69/0.87          | ((X25) = (k1_xboole_0))
% 0.69/0.87          | ~ (v1_relat_1 @ X25))),
% 0.69/0.87      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.69/0.87  thf('76', plain,
% 0.69/0.87      (((((k1_xboole_0) != (k1_xboole_0))
% 0.69/0.87         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.69/0.87         | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))
% 0.69/0.87         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['74', '75'])).
% 0.69/0.87  thf('77', plain,
% 0.69/0.87      (((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))
% 0.69/0.87         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.69/0.87         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.69/0.87      inference('simplify', [status(thm)], ['76'])).
% 0.69/0.87  thf('78', plain,
% 0.69/0.87      (((~ (v1_relat_1 @ sk_B) | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))
% 0.69/0.87         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['3', '77'])).
% 0.69/0.87  thf('79', plain, ((v1_relat_1 @ sk_B)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('80', plain,
% 0.69/0.87      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.69/0.87         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.69/0.87      inference('demod', [status(thm)], ['78', '79'])).
% 0.69/0.87  thf('81', plain,
% 0.69/0.87      ((((k7_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 0.69/0.87         <= (~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.69/0.87      inference('split', [status(esa)], ['0'])).
% 0.69/0.87  thf('82', plain,
% 0.69/0.87      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.69/0.87         <= (~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) & 
% 0.69/0.87             ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['80', '81'])).
% 0.69/0.87  thf('83', plain,
% 0.69/0.87      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.69/0.87       ~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.69/0.87      inference('simplify', [status(thm)], ['82'])).
% 0.69/0.87  thf('84', plain, (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.69/0.87      inference('sat_resolution*', [status(thm)], ['2', '83'])).
% 0.69/0.87  thf('85', plain, (~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.69/0.87      inference('simpl_trail', [status(thm)], ['1', '84'])).
% 0.69/0.87  thf('86', plain,
% 0.69/0.87      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.69/0.87         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.69/0.87      inference('split', [status(esa)], ['4'])).
% 0.69/0.87  thf('87', plain,
% 0.69/0.87      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.69/0.87       ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.69/0.87      inference('split', [status(esa)], ['4'])).
% 0.69/0.87  thf('88', plain, ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.69/0.87      inference('sat_resolution*', [status(thm)], ['2', '83', '87'])).
% 0.69/0.87  thf('89', plain, (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.69/0.87      inference('simpl_trail', [status(thm)], ['86', '88'])).
% 0.69/0.87  thf('90', plain,
% 0.69/0.87      (![X5 : $i, X6 : $i]:
% 0.69/0.87         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X6))),
% 0.69/0.87      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.69/0.87  thf('91', plain,
% 0.69/0.87      (![X5 : $i, X6 : $i]:
% 0.69/0.87         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X5))),
% 0.69/0.87      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.69/0.87  thf('92', plain,
% 0.69/0.87      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.69/0.87         (~ (r2_hidden @ X26 @ X27)
% 0.69/0.87          | ~ (r2_hidden @ X26 @ (k1_relat_1 @ X28))
% 0.69/0.87          | (r2_hidden @ X26 @ (k1_relat_1 @ (k7_relat_1 @ X28 @ X27)))
% 0.69/0.87          | ~ (v1_relat_1 @ X28))),
% 0.69/0.87      inference('cnf', [status(esa)], [t86_relat_1])).
% 0.69/0.87  thf('93', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.87         ((r1_xboole_0 @ (k1_relat_1 @ X0) @ X1)
% 0.69/0.87          | ~ (v1_relat_1 @ X0)
% 0.69/0.87          | (r2_hidden @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ 
% 0.69/0.87             (k1_relat_1 @ (k7_relat_1 @ X0 @ X2)))
% 0.69/0.87          | ~ (r2_hidden @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ X2))),
% 0.69/0.87      inference('sup-', [status(thm)], ['91', '92'])).
% 0.69/0.87  thf('94', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i]:
% 0.69/0.87         ((r1_xboole_0 @ (k1_relat_1 @ X1) @ X0)
% 0.69/0.87          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ X1)) @ 
% 0.69/0.87             (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.69/0.87          | ~ (v1_relat_1 @ X1)
% 0.69/0.87          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ X0))),
% 0.69/0.87      inference('sup-', [status(thm)], ['90', '93'])).
% 0.69/0.87  thf('95', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i]:
% 0.69/0.87         (~ (v1_relat_1 @ X1)
% 0.69/0.87          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ X1)) @ 
% 0.69/0.87             (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.69/0.87          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ X0))),
% 0.69/0.87      inference('simplify', [status(thm)], ['94'])).
% 0.69/0.87  thf('96', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.87         ((r1_xboole_0 @ X1 @ X0)
% 0.69/0.87          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.69/0.87          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.69/0.87      inference('sup-', [status(thm)], ['11', '12'])).
% 0.69/0.87  thf('97', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i]:
% 0.69/0.87         ((r1_xboole_0 @ (k1_relat_1 @ X1) @ X0)
% 0.69/0.87          | ~ (v1_relat_1 @ X1)
% 0.69/0.87          | ~ (r1_xboole_0 @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.69/0.87          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ X0))),
% 0.69/0.87      inference('sup-', [status(thm)], ['95', '96'])).
% 0.69/0.87  thf('98', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i]:
% 0.69/0.87         (~ (r1_xboole_0 @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.69/0.87          | ~ (v1_relat_1 @ X1)
% 0.69/0.87          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ X0))),
% 0.69/0.87      inference('simplify', [status(thm)], ['97'])).
% 0.69/0.87  thf('99', plain,
% 0.69/0.87      ((~ (r1_xboole_0 @ sk_A @ (k1_relat_1 @ k1_xboole_0))
% 0.69/0.87        | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.69/0.87        | ~ (v1_relat_1 @ sk_B))),
% 0.69/0.87      inference('sup-', [status(thm)], ['89', '98'])).
% 0.69/0.87  thf(t60_relat_1, axiom,
% 0.69/0.87    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.69/0.87     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.69/0.87  thf('100', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.69/0.87      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.69/0.87  thf('101', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.69/0.87      inference('sup-', [status(thm)], ['57', '58'])).
% 0.69/0.87  thf('102', plain, ((v1_relat_1 @ sk_B)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('103', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.69/0.87      inference('demod', [status(thm)], ['99', '100', '101', '102'])).
% 0.69/0.87  thf('104', plain, ($false), inference('demod', [status(thm)], ['85', '103'])).
% 0.69/0.87  
% 0.69/0.87  % SZS output end Refutation
% 0.69/0.87  
% 0.69/0.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
