%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ugn6rEkGc3

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:07 EST 2020

% Result     : Theorem 4.97s
% Output     : Refutation 5.02s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 208 expanded)
%              Number of leaves         :   26 (  68 expanded)
%              Depth                    :   20
%              Number of atoms          :  744 (1880 expanded)
%              Number of equality atoms :   35 (  97 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

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
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
   <= ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('4',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('7',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
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
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t86_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('9',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ ( k7_relat_1 @ X17 @ X16 ) ) )
      | ( r2_hidden @ X15 @ ( k1_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('12',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
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
        ( ~ ( v1_relat_1 @ sk_B_1 )
        | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) ) @ sk_A ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['7','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) ) @ sk_A )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('19',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('20',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ ( k7_relat_1 @ X17 @ X16 ) ) )
      | ( r2_hidden @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_B @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('23',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ sk_A ) ) ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['18','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ sk_A ) ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('30',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('31',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ sk_A ) )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(fc16_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_xboole_0 @ B ) )
     => ( ( v1_xboole_0 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('32',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_xboole_0 @ X13 )
      | ( v1_xboole_0 @ ( k7_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[fc16_relat_1])).

thf('33',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('35',plain,(
    ! [X14: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X14 ) ) @ X14 )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('36',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k7_relat_1 @ X19 @ X18 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X18 ) @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ sk_A ) ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['31','40'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('43',plain,
    ( ( ( k1_xboole_0
        = ( k7_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ sk_A ) ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ sk_B_1 @ sk_A ) ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['3','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k1_xboole_0
      = ( k7_relat_1 @ sk_B_1 @ sk_A ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k7_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k7_relat_1 @ sk_B_1 @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','49'])).

thf('51',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','50'])).

thf('52',plain,
    ( ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('53',plain,
    ( ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('54',plain,
    ( ( k7_relat_1 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','49','53'])).

thf('55',plain,
    ( ( k7_relat_1 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['52','54'])).

thf('56',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('57',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('58',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X17 ) )
      | ( r2_hidden @ X15 @ ( k1_relat_1 @ ( k7_relat_1 @ X17 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X2 ) ) )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ X1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ X1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['55','63'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('65',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('66',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('67',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['64','65','66','67'])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['51','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ugn6rEkGc3
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:36:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 4.97/5.20  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.97/5.20  % Solved by: fo/fo7.sh
% 4.97/5.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.97/5.20  % done 3458 iterations in 4.745s
% 4.97/5.20  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.97/5.20  % SZS output start Refutation
% 4.97/5.20  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 4.97/5.20  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 4.97/5.20  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.97/5.20  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.97/5.20  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.97/5.20  thf(sk_B_1_type, type, sk_B_1: $i).
% 4.97/5.20  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.97/5.20  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.97/5.20  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.97/5.20  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 4.97/5.20  thf(sk_A_type, type, sk_A: $i).
% 4.97/5.20  thf(sk_B_type, type, sk_B: $i > $i).
% 4.97/5.20  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.97/5.20  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 4.97/5.20  thf(t95_relat_1, conjecture,
% 4.97/5.20    (![A:$i,B:$i]:
% 4.97/5.20     ( ( v1_relat_1 @ B ) =>
% 4.97/5.20       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 4.97/5.20         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 4.97/5.20  thf(zf_stmt_0, negated_conjecture,
% 4.97/5.20    (~( ![A:$i,B:$i]:
% 4.97/5.20        ( ( v1_relat_1 @ B ) =>
% 4.97/5.20          ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 4.97/5.20            ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 4.97/5.20    inference('cnf.neg', [status(esa)], [t95_relat_1])).
% 4.97/5.20  thf('0', plain,
% 4.97/5.20      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 4.97/5.20        | ((k7_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))),
% 4.97/5.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.20  thf('1', plain,
% 4.97/5.20      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 4.97/5.20         <= (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 4.97/5.20      inference('split', [status(esa)], ['0'])).
% 4.97/5.20  thf('2', plain,
% 4.97/5.20      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)) | 
% 4.97/5.20       ~ (((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 4.97/5.20      inference('split', [status(esa)], ['0'])).
% 4.97/5.20  thf(dt_k7_relat_1, axiom,
% 4.97/5.20    (![A:$i,B:$i]:
% 4.97/5.20     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 4.97/5.20  thf('3', plain,
% 4.97/5.20      (![X10 : $i, X11 : $i]:
% 4.97/5.20         (~ (v1_relat_1 @ X10) | (v1_relat_1 @ (k7_relat_1 @ X10 @ X11)))),
% 4.97/5.20      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 4.97/5.20  thf('4', plain,
% 4.97/5.20      (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 4.97/5.20        | ((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 4.97/5.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.20  thf('5', plain,
% 4.97/5.20      (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 4.97/5.20         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 4.97/5.20      inference('split', [status(esa)], ['4'])).
% 4.97/5.20  thf(symmetry_r1_xboole_0, axiom,
% 4.97/5.20    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 4.97/5.20  thf('6', plain,
% 4.97/5.20      (![X4 : $i, X5 : $i]:
% 4.97/5.20         ((r1_xboole_0 @ X4 @ X5) | ~ (r1_xboole_0 @ X5 @ X4))),
% 4.97/5.20      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 4.97/5.20  thf('7', plain,
% 4.97/5.20      (((r1_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 4.97/5.20         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 4.97/5.20      inference('sup-', [status(thm)], ['5', '6'])).
% 4.97/5.20  thf(t3_xboole_0, axiom,
% 4.97/5.20    (![A:$i,B:$i]:
% 4.97/5.20     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 4.97/5.20            ( r1_xboole_0 @ A @ B ) ) ) & 
% 4.97/5.20       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 4.97/5.20            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 4.97/5.20  thf('8', plain,
% 4.97/5.20      (![X6 : $i, X7 : $i]:
% 4.97/5.20         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 4.97/5.20      inference('cnf', [status(esa)], [t3_xboole_0])).
% 4.97/5.20  thf(t86_relat_1, axiom,
% 4.97/5.20    (![A:$i,B:$i,C:$i]:
% 4.97/5.20     ( ( v1_relat_1 @ C ) =>
% 4.97/5.20       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 4.97/5.20         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 4.97/5.20  thf('9', plain,
% 4.97/5.20      (![X15 : $i, X16 : $i, X17 : $i]:
% 4.97/5.20         (~ (r2_hidden @ X15 @ (k1_relat_1 @ (k7_relat_1 @ X17 @ X16)))
% 4.97/5.20          | (r2_hidden @ X15 @ (k1_relat_1 @ X17))
% 4.97/5.20          | ~ (v1_relat_1 @ X17))),
% 4.97/5.20      inference('cnf', [status(esa)], [t86_relat_1])).
% 4.97/5.20  thf('10', plain,
% 4.97/5.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.97/5.20         ((r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2)
% 4.97/5.20          | ~ (v1_relat_1 @ X1)
% 4.97/5.20          | (r2_hidden @ (sk_C @ X2 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))) @ 
% 4.97/5.20             (k1_relat_1 @ X1)))),
% 4.97/5.20      inference('sup-', [status(thm)], ['8', '9'])).
% 4.97/5.20  thf('11', plain,
% 4.97/5.20      (![X6 : $i, X7 : $i]:
% 4.97/5.20         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 4.97/5.20      inference('cnf', [status(esa)], [t3_xboole_0])).
% 4.97/5.20  thf('12', plain,
% 4.97/5.20      (![X6 : $i, X8 : $i, X9 : $i]:
% 4.97/5.20         (~ (r2_hidden @ X8 @ X6)
% 4.97/5.20          | ~ (r2_hidden @ X8 @ X9)
% 4.97/5.20          | ~ (r1_xboole_0 @ X6 @ X9))),
% 4.97/5.20      inference('cnf', [status(esa)], [t3_xboole_0])).
% 4.97/5.20  thf('13', plain,
% 4.97/5.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.97/5.20         ((r1_xboole_0 @ X1 @ X0)
% 4.97/5.20          | ~ (r1_xboole_0 @ X0 @ X2)
% 4.97/5.20          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 4.97/5.20      inference('sup-', [status(thm)], ['11', '12'])).
% 4.97/5.20  thf('14', plain,
% 4.97/5.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.97/5.20         (~ (v1_relat_1 @ X0)
% 4.97/5.20          | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ X2)
% 4.97/5.20          | ~ (r1_xboole_0 @ X2 @ (k1_relat_1 @ X0))
% 4.97/5.20          | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ X2))),
% 4.97/5.20      inference('sup-', [status(thm)], ['10', '13'])).
% 4.97/5.20  thf('15', plain,
% 4.97/5.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.97/5.20         (~ (r1_xboole_0 @ X2 @ (k1_relat_1 @ X0))
% 4.97/5.20          | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ X2)
% 4.97/5.20          | ~ (v1_relat_1 @ X0))),
% 4.97/5.20      inference('simplify', [status(thm)], ['14'])).
% 4.97/5.20  thf('16', plain,
% 4.97/5.20      ((![X0 : $i]:
% 4.97/5.20          (~ (v1_relat_1 @ sk_B_1)
% 4.97/5.20           | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0)) @ sk_A)))
% 4.97/5.20         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 4.97/5.20      inference('sup-', [status(thm)], ['7', '15'])).
% 4.97/5.20  thf('17', plain, ((v1_relat_1 @ sk_B_1)),
% 4.97/5.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.20  thf('18', plain,
% 4.97/5.20      ((![X0 : $i]:
% 4.97/5.20          (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0)) @ sk_A))
% 4.97/5.20         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 4.97/5.20      inference('demod', [status(thm)], ['16', '17'])).
% 4.97/5.20  thf(d1_xboole_0, axiom,
% 4.97/5.20    (![A:$i]:
% 4.97/5.20     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 4.97/5.20  thf('19', plain,
% 4.97/5.20      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 4.97/5.20      inference('cnf', [status(esa)], [d1_xboole_0])).
% 4.97/5.20  thf('20', plain,
% 4.97/5.20      (![X15 : $i, X16 : $i, X17 : $i]:
% 4.97/5.20         (~ (r2_hidden @ X15 @ (k1_relat_1 @ (k7_relat_1 @ X17 @ X16)))
% 4.97/5.20          | (r2_hidden @ X15 @ X16)
% 4.97/5.20          | ~ (v1_relat_1 @ X17))),
% 4.97/5.20      inference('cnf', [status(esa)], [t86_relat_1])).
% 4.97/5.20  thf('21', plain,
% 4.97/5.20      (![X0 : $i, X1 : $i]:
% 4.97/5.20         ((v1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 4.97/5.20          | ~ (v1_relat_1 @ X1)
% 4.97/5.20          | (r2_hidden @ (sk_B @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))) @ X0))),
% 4.97/5.20      inference('sup-', [status(thm)], ['19', '20'])).
% 4.97/5.20  thf('22', plain,
% 4.97/5.20      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 4.97/5.20      inference('cnf', [status(esa)], [d1_xboole_0])).
% 4.97/5.20  thf('23', plain,
% 4.97/5.20      (![X6 : $i, X8 : $i, X9 : $i]:
% 4.97/5.20         (~ (r2_hidden @ X8 @ X6)
% 4.97/5.20          | ~ (r2_hidden @ X8 @ X9)
% 4.97/5.20          | ~ (r1_xboole_0 @ X6 @ X9))),
% 4.97/5.20      inference('cnf', [status(esa)], [t3_xboole_0])).
% 4.97/5.20  thf('24', plain,
% 4.97/5.20      (![X0 : $i, X1 : $i]:
% 4.97/5.20         ((v1_xboole_0 @ X0)
% 4.97/5.20          | ~ (r1_xboole_0 @ X0 @ X1)
% 4.97/5.20          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 4.97/5.20      inference('sup-', [status(thm)], ['22', '23'])).
% 4.97/5.20  thf('25', plain,
% 4.97/5.20      (![X0 : $i, X1 : $i]:
% 4.97/5.20         (~ (v1_relat_1 @ X1)
% 4.97/5.20          | (v1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 4.97/5.20          | ~ (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0)
% 4.97/5.20          | (v1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 4.97/5.20      inference('sup-', [status(thm)], ['21', '24'])).
% 4.97/5.20  thf('26', plain,
% 4.97/5.20      (![X0 : $i, X1 : $i]:
% 4.97/5.20         (~ (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0)
% 4.97/5.20          | (v1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 4.97/5.20          | ~ (v1_relat_1 @ X1))),
% 4.97/5.20      inference('simplify', [status(thm)], ['25'])).
% 4.97/5.20  thf('27', plain,
% 4.97/5.20      (((~ (v1_relat_1 @ sk_B_1)
% 4.97/5.20         | (v1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ sk_A)))))
% 4.97/5.20         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 4.97/5.20      inference('sup-', [status(thm)], ['18', '26'])).
% 4.97/5.20  thf('28', plain, ((v1_relat_1 @ sk_B_1)),
% 4.97/5.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.20  thf('29', plain,
% 4.97/5.20      (((v1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ sk_A))))
% 4.97/5.20         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 4.97/5.20      inference('demod', [status(thm)], ['27', '28'])).
% 4.97/5.20  thf(l13_xboole_0, axiom,
% 4.97/5.20    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 4.97/5.20  thf('30', plain,
% 4.97/5.20      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 4.97/5.20      inference('cnf', [status(esa)], [l13_xboole_0])).
% 4.97/5.20  thf('31', plain,
% 4.97/5.20      ((((k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ sk_A)) = (k1_xboole_0)))
% 4.97/5.20         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 4.97/5.20      inference('sup-', [status(thm)], ['29', '30'])).
% 4.97/5.20  thf(fc16_relat_1, axiom,
% 4.97/5.20    (![A:$i,B:$i]:
% 4.97/5.20     ( ( ( v1_relat_1 @ A ) & ( v1_xboole_0 @ B ) ) =>
% 4.97/5.20       ( ( v1_xboole_0 @ ( k7_relat_1 @ A @ B ) ) & 
% 4.97/5.20         ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 4.97/5.20  thf('32', plain,
% 4.97/5.20      (![X12 : $i, X13 : $i]:
% 4.97/5.20         (~ (v1_relat_1 @ X12)
% 4.97/5.20          | ~ (v1_xboole_0 @ X13)
% 4.97/5.20          | (v1_xboole_0 @ (k7_relat_1 @ X12 @ X13)))),
% 4.97/5.20      inference('cnf', [status(esa)], [fc16_relat_1])).
% 4.97/5.20  thf('33', plain,
% 4.97/5.20      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 4.97/5.20      inference('cnf', [status(esa)], [l13_xboole_0])).
% 4.97/5.20  thf('34', plain,
% 4.97/5.20      (![X0 : $i, X1 : $i]:
% 4.97/5.20         (~ (v1_xboole_0 @ X0)
% 4.97/5.20          | ~ (v1_relat_1 @ X1)
% 4.97/5.20          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 4.97/5.20      inference('sup-', [status(thm)], ['32', '33'])).
% 4.97/5.20  thf(t78_relat_1, axiom,
% 4.97/5.20    (![A:$i]:
% 4.97/5.20     ( ( v1_relat_1 @ A ) =>
% 4.97/5.20       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 4.97/5.20  thf('35', plain,
% 4.97/5.20      (![X14 : $i]:
% 4.97/5.20         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X14)) @ X14) = (X14))
% 4.97/5.20          | ~ (v1_relat_1 @ X14))),
% 4.97/5.20      inference('cnf', [status(esa)], [t78_relat_1])).
% 4.97/5.20  thf(t94_relat_1, axiom,
% 4.97/5.20    (![A:$i,B:$i]:
% 4.97/5.20     ( ( v1_relat_1 @ B ) =>
% 4.97/5.20       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 4.97/5.20  thf('36', plain,
% 4.97/5.20      (![X18 : $i, X19 : $i]:
% 4.97/5.20         (((k7_relat_1 @ X19 @ X18) = (k5_relat_1 @ (k6_relat_1 @ X18) @ X19))
% 4.97/5.20          | ~ (v1_relat_1 @ X19))),
% 4.97/5.20      inference('cnf', [status(esa)], [t94_relat_1])).
% 4.97/5.20  thf('37', plain,
% 4.97/5.20      (![X0 : $i]:
% 4.97/5.20         (((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0))
% 4.97/5.20          | ~ (v1_relat_1 @ X0)
% 4.97/5.20          | ~ (v1_relat_1 @ X0))),
% 4.97/5.20      inference('sup+', [status(thm)], ['35', '36'])).
% 4.97/5.20  thf('38', plain,
% 4.97/5.20      (![X0 : $i]:
% 4.97/5.20         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 4.97/5.20      inference('simplify', [status(thm)], ['37'])).
% 4.97/5.20  thf('39', plain,
% 4.97/5.20      (![X0 : $i]:
% 4.97/5.20         (((k1_xboole_0) = (X0))
% 4.97/5.20          | ~ (v1_relat_1 @ X0)
% 4.97/5.20          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 4.97/5.20          | ~ (v1_relat_1 @ X0))),
% 4.97/5.20      inference('sup+', [status(thm)], ['34', '38'])).
% 4.97/5.20  thf('40', plain,
% 4.97/5.20      (![X0 : $i]:
% 4.97/5.20         (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 4.97/5.20          | ~ (v1_relat_1 @ X0)
% 4.97/5.20          | ((k1_xboole_0) = (X0)))),
% 4.97/5.20      inference('simplify', [status(thm)], ['39'])).
% 4.97/5.20  thf('41', plain,
% 4.97/5.20      (((~ (v1_xboole_0 @ k1_xboole_0)
% 4.97/5.20         | ((k1_xboole_0) = (k7_relat_1 @ sk_B_1 @ sk_A))
% 4.97/5.20         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B_1 @ sk_A))))
% 4.97/5.20         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 4.97/5.20      inference('sup-', [status(thm)], ['31', '40'])).
% 4.97/5.20  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 4.97/5.20  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.97/5.20      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.97/5.20  thf('43', plain,
% 4.97/5.20      (((((k1_xboole_0) = (k7_relat_1 @ sk_B_1 @ sk_A))
% 4.97/5.20         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B_1 @ sk_A))))
% 4.97/5.20         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 4.97/5.20      inference('demod', [status(thm)], ['41', '42'])).
% 4.97/5.20  thf('44', plain,
% 4.97/5.20      (((~ (v1_relat_1 @ sk_B_1)
% 4.97/5.20         | ((k1_xboole_0) = (k7_relat_1 @ sk_B_1 @ sk_A))))
% 4.97/5.20         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 4.97/5.20      inference('sup-', [status(thm)], ['3', '43'])).
% 4.97/5.20  thf('45', plain, ((v1_relat_1 @ sk_B_1)),
% 4.97/5.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.20  thf('46', plain,
% 4.97/5.20      ((((k1_xboole_0) = (k7_relat_1 @ sk_B_1 @ sk_A)))
% 4.97/5.20         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 4.97/5.20      inference('demod', [status(thm)], ['44', '45'])).
% 4.97/5.20  thf('47', plain,
% 4.97/5.20      ((((k7_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))
% 4.97/5.20         <= (~ (((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 4.97/5.20      inference('split', [status(esa)], ['0'])).
% 4.97/5.20  thf('48', plain,
% 4.97/5.20      ((((k1_xboole_0) != (k1_xboole_0)))
% 4.97/5.20         <= (~ (((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) & 
% 4.97/5.20             ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 4.97/5.20      inference('sup-', [status(thm)], ['46', '47'])).
% 4.97/5.20  thf('49', plain,
% 4.97/5.20      ((((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 4.97/5.20       ~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 4.97/5.20      inference('simplify', [status(thm)], ['48'])).
% 4.97/5.20  thf('50', plain, (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 4.97/5.20      inference('sat_resolution*', [status(thm)], ['2', '49'])).
% 4.97/5.20  thf('51', plain, (~ (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 4.97/5.20      inference('simpl_trail', [status(thm)], ['1', '50'])).
% 4.97/5.20  thf('52', plain,
% 4.97/5.20      ((((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 4.97/5.20         <= ((((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 4.97/5.20      inference('split', [status(esa)], ['4'])).
% 4.97/5.20  thf('53', plain,
% 4.97/5.20      ((((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 4.97/5.20       ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 4.97/5.20      inference('split', [status(esa)], ['4'])).
% 4.97/5.20  thf('54', plain, ((((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 4.97/5.20      inference('sat_resolution*', [status(thm)], ['2', '49', '53'])).
% 4.97/5.20  thf('55', plain, (((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 4.97/5.20      inference('simpl_trail', [status(thm)], ['52', '54'])).
% 4.97/5.20  thf('56', plain,
% 4.97/5.20      (![X6 : $i, X7 : $i]:
% 4.97/5.20         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 4.97/5.20      inference('cnf', [status(esa)], [t3_xboole_0])).
% 4.97/5.20  thf('57', plain,
% 4.97/5.20      (![X6 : $i, X7 : $i]:
% 4.97/5.20         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 4.97/5.20      inference('cnf', [status(esa)], [t3_xboole_0])).
% 4.97/5.20  thf('58', plain,
% 4.97/5.20      (![X15 : $i, X16 : $i, X17 : $i]:
% 4.97/5.20         (~ (r2_hidden @ X15 @ X16)
% 4.97/5.20          | ~ (r2_hidden @ X15 @ (k1_relat_1 @ X17))
% 4.97/5.20          | (r2_hidden @ X15 @ (k1_relat_1 @ (k7_relat_1 @ X17 @ X16)))
% 4.97/5.21          | ~ (v1_relat_1 @ X17))),
% 4.97/5.21      inference('cnf', [status(esa)], [t86_relat_1])).
% 4.97/5.21  thf('59', plain,
% 4.97/5.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.97/5.21         ((r1_xboole_0 @ (k1_relat_1 @ X0) @ X1)
% 4.97/5.21          | ~ (v1_relat_1 @ X0)
% 4.97/5.21          | (r2_hidden @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ 
% 4.97/5.21             (k1_relat_1 @ (k7_relat_1 @ X0 @ X2)))
% 4.97/5.21          | ~ (r2_hidden @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ X2))),
% 4.97/5.21      inference('sup-', [status(thm)], ['57', '58'])).
% 4.97/5.21  thf('60', plain,
% 4.97/5.21      (![X0 : $i, X1 : $i]:
% 4.97/5.21         ((r1_xboole_0 @ (k1_relat_1 @ X1) @ X0)
% 4.97/5.21          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ X1)) @ 
% 4.97/5.21             (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 4.97/5.21          | ~ (v1_relat_1 @ X1)
% 4.97/5.21          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ X0))),
% 4.97/5.21      inference('sup-', [status(thm)], ['56', '59'])).
% 4.97/5.21  thf('61', plain,
% 4.97/5.21      (![X0 : $i, X1 : $i]:
% 4.97/5.21         (~ (v1_relat_1 @ X1)
% 4.97/5.21          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ X1)) @ 
% 4.97/5.21             (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 4.97/5.21          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ X0))),
% 5.02/5.21      inference('simplify', [status(thm)], ['60'])).
% 5.02/5.21  thf('62', plain,
% 5.02/5.21      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 5.02/5.21      inference('cnf', [status(esa)], [d1_xboole_0])).
% 5.02/5.21  thf('63', plain,
% 5.02/5.21      (![X0 : $i, X1 : $i]:
% 5.02/5.21         ((r1_xboole_0 @ (k1_relat_1 @ X1) @ X0)
% 5.02/5.21          | ~ (v1_relat_1 @ X1)
% 5.02/5.21          | ~ (v1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 5.02/5.21      inference('sup-', [status(thm)], ['61', '62'])).
% 5.02/5.21  thf('64', plain,
% 5.02/5.21      ((~ (v1_xboole_0 @ (k1_relat_1 @ k1_xboole_0))
% 5.02/5.21        | ~ (v1_relat_1 @ sk_B_1)
% 5.02/5.21        | (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 5.02/5.21      inference('sup-', [status(thm)], ['55', '63'])).
% 5.02/5.21  thf(t60_relat_1, axiom,
% 5.02/5.21    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 5.02/5.21     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 5.02/5.21  thf('65', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 5.02/5.21      inference('cnf', [status(esa)], [t60_relat_1])).
% 5.02/5.21  thf('66', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.02/5.21      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 5.02/5.21  thf('67', plain, ((v1_relat_1 @ sk_B_1)),
% 5.02/5.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.21  thf('68', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 5.02/5.21      inference('demod', [status(thm)], ['64', '65', '66', '67'])).
% 5.02/5.21  thf('69', plain, ($false), inference('demod', [status(thm)], ['51', '68'])).
% 5.02/5.21  
% 5.02/5.21  % SZS output end Refutation
% 5.02/5.21  
% 5.02/5.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
