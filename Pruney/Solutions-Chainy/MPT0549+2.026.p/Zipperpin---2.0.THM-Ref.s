%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GMWCTUxgYD

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 132 expanded)
%              Number of leaves         :   22 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :  672 (1220 expanded)
%              Number of equality atoms :   62 ( 106 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t151_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( ( k9_relat_1 @ B @ A )
            = k1_xboole_0 )
        <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t151_relat_1])).

thf('0',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ( ( k9_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ( ( k9_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ( ( k9_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k9_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k9_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('6',plain,(
    ! [X13: $i] :
      ( ( ( k2_relat_1 @ X13 )
       != k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ( ( k7_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) )
   <= ( ( k9_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k7_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) )
   <= ( ( k9_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k9_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t95_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k7_relat_1 @ X14 @ X15 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('15',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) )
   <= ( ( k9_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) )
   <= ( ( k9_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
   <= ( ( k9_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
   <= ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ( ( k9_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ( ( k9_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('22',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

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

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('30',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('31',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k9_relat_1 @ X10 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X10 @ X8 @ X9 ) @ ( k1_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('34',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k9_relat_1 @ X10 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X10 @ X8 @ X9 ) @ X8 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) )
      | ( ( k9_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) )
      | ( ( k9_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ( ( k9_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['29','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('43',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X14 ) @ X15 )
      | ( ( k7_relat_1 @ X14 @ X15 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('44',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ( ( k7_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('48',plain,
    ( ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B_1 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = ( k9_relat_1 @ sk_B_1 @ sk_A ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['40','41','50'])).

thf('52',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = ( k9_relat_1 @ sk_B_1 @ sk_A ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('53',plain,
    ( ( ( k9_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k9_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('54',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( ( k9_relat_1 @ sk_B_1 @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k9_relat_1 @ sk_B_1 @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ( ( k9_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','20','21','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GMWCTUxgYD
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:12:53 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 58 iterations in 0.046s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.52  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.52  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.52  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.22/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.52  thf(t151_relat_1, conjecture,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ B ) =>
% 0.22/0.52       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.52         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i,B:$i]:
% 0.22/0.52        ( ( v1_relat_1 @ B ) =>
% 0.22/0.52          ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.52            ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t151_relat_1])).
% 0.22/0.52  thf('0', plain,
% 0.22/0.52      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.22/0.52        | ((k9_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)) | 
% 0.22/0.52       ~ (((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.22/0.52      inference('split', [status(esa)], ['0'])).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.22/0.52        | ((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      ((((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.22/0.52         <= ((((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.52      inference('split', [status(esa)], ['2'])).
% 0.22/0.52  thf(dt_k7_relat_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      (![X5 : $i, X6 : $i]:
% 0.22/0.52         (~ (v1_relat_1 @ X5) | (v1_relat_1 @ (k7_relat_1 @ X5 @ X6)))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.22/0.52  thf(t148_relat_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ B ) =>
% 0.22/0.52       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      (![X11 : $i, X12 : $i]:
% 0.22/0.52         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 0.22/0.52          | ~ (v1_relat_1 @ X11))),
% 0.22/0.52      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.22/0.52  thf(t64_relat_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ A ) =>
% 0.22/0.52       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.22/0.52           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.22/0.52         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.52  thf('6', plain,
% 0.22/0.52      (![X13 : $i]:
% 0.22/0.52         (((k2_relat_1 @ X13) != (k1_xboole_0))
% 0.22/0.52          | ((X13) = (k1_xboole_0))
% 0.22/0.52          | ~ (v1_relat_1 @ X13))),
% 0.22/0.52      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (((k9_relat_1 @ X1 @ X0) != (k1_xboole_0))
% 0.22/0.52          | ~ (v1_relat_1 @ X1)
% 0.22/0.52          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.22/0.52          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (v1_relat_1 @ X1)
% 0.22/0.52          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.22/0.52          | ~ (v1_relat_1 @ X1)
% 0.22/0.52          | ((k9_relat_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['4', '7'])).
% 0.22/0.52  thf('9', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (((k9_relat_1 @ X1 @ X0) != (k1_xboole_0))
% 0.22/0.52          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.22/0.52          | ~ (v1_relat_1 @ X1))),
% 0.22/0.52      inference('simplify', [status(thm)], ['8'])).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      (((((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.52         | ~ (v1_relat_1 @ sk_B_1)
% 0.22/0.52         | ((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))
% 0.22/0.52         <= ((((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['3', '9'])).
% 0.22/0.52  thf('11', plain, ((v1_relat_1 @ sk_B_1)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      (((((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.52         | ((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))
% 0.22/0.52         <= ((((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.52      inference('demod', [status(thm)], ['10', '11'])).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      ((((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.22/0.52         <= ((((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.52      inference('simplify', [status(thm)], ['12'])).
% 0.22/0.52  thf(t95_relat_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ B ) =>
% 0.22/0.52       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.52         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      (![X14 : $i, X15 : $i]:
% 0.22/0.52         (((k7_relat_1 @ X14 @ X15) != (k1_xboole_0))
% 0.22/0.52          | (r1_xboole_0 @ (k1_relat_1 @ X14) @ X15)
% 0.22/0.52          | ~ (v1_relat_1 @ X14))),
% 0.22/0.52      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      (((((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.52         | ~ (v1_relat_1 @ sk_B_1)
% 0.22/0.52         | (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))
% 0.22/0.52         <= ((((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.52  thf('16', plain, ((v1_relat_1 @ sk_B_1)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('17', plain,
% 0.22/0.52      (((((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.52         | (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))
% 0.22/0.52         <= ((((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.52      inference('demod', [status(thm)], ['15', '16'])).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 0.22/0.52         <= ((((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.52      inference('simplify', [status(thm)], ['17'])).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 0.22/0.52         <= (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.22/0.52      inference('split', [status(esa)], ['0'])).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)) | 
% 0.22/0.52       ~ (((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)) | 
% 0.22/0.52       (((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.22/0.52      inference('split', [status(esa)], ['2'])).
% 0.22/0.52  thf('22', plain,
% 0.22/0.52      (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 0.22/0.52         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.22/0.52      inference('split', [status(esa)], ['2'])).
% 0.22/0.52  thf(t3_xboole_0, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.22/0.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.52            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.22/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X2 @ X0)
% 0.22/0.52          | ~ (r2_hidden @ X2 @ X3)
% 0.22/0.52          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.22/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ X1 @ X0)
% 0.22/0.52          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.22/0.52          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.22/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.52  thf('27', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ X0 @ X1)
% 0.22/0.52          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.22/0.52          | (r1_xboole_0 @ X0 @ X1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['23', '26'])).
% 0.22/0.52  thf('28', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.22/0.52      inference('simplify', [status(thm)], ['27'])).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      (((r1_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.22/0.52         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['22', '28'])).
% 0.22/0.52  thf(t7_xboole_0, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.52          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.22/0.52  thf('30', plain,
% 0.22/0.52      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.22/0.52      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.22/0.52  thf(t143_relat_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ C ) =>
% 0.22/0.52       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.22/0.52         ( ?[D:$i]:
% 0.22/0.52           ( ( r2_hidden @ D @ B ) & 
% 0.22/0.52             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.22/0.52             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.22/0.52  thf('31', plain,
% 0.22/0.52      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X9 @ (k9_relat_1 @ X10 @ X8))
% 0.22/0.52          | (r2_hidden @ (sk_D @ X10 @ X8 @ X9) @ (k1_relat_1 @ X10))
% 0.22/0.52          | ~ (v1_relat_1 @ X10))),
% 0.22/0.52      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.22/0.52  thf('32', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (((k9_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.22/0.52          | ~ (v1_relat_1 @ X1)
% 0.22/0.52          | (r2_hidden @ (sk_D @ X1 @ X0 @ (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.22/0.52             (k1_relat_1 @ X1)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.52  thf('33', plain,
% 0.22/0.52      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.22/0.52      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.22/0.52  thf('34', plain,
% 0.22/0.52      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X9 @ (k9_relat_1 @ X10 @ X8))
% 0.22/0.52          | (r2_hidden @ (sk_D @ X10 @ X8 @ X9) @ X8)
% 0.22/0.52          | ~ (v1_relat_1 @ X10))),
% 0.22/0.52      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.22/0.52  thf('35', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (((k9_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.22/0.52          | ~ (v1_relat_1 @ X1)
% 0.22/0.52          | (r2_hidden @ (sk_D @ X1 @ X0 @ (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.22/0.52             X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.52  thf('36', plain,
% 0.22/0.52      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X2 @ X0)
% 0.22/0.52          | ~ (r2_hidden @ X2 @ X3)
% 0.22/0.52          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.22/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.52  thf('37', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.52         (~ (v1_relat_1 @ X1)
% 0.22/0.52          | ((k9_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.22/0.52          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.22/0.52          | ~ (r2_hidden @ 
% 0.22/0.52               (sk_D @ X1 @ X0 @ (sk_B @ (k9_relat_1 @ X1 @ X0))) @ X2))),
% 0.22/0.52      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.52  thf('38', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (v1_relat_1 @ X0)
% 0.22/0.52          | ((k9_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.22/0.52          | ~ (r1_xboole_0 @ X1 @ (k1_relat_1 @ X0))
% 0.22/0.52          | ((k9_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.22/0.52          | ~ (v1_relat_1 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['32', '37'])).
% 0.22/0.52  thf('39', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (r1_xboole_0 @ X1 @ (k1_relat_1 @ X0))
% 0.22/0.52          | ((k9_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.22/0.52          | ~ (v1_relat_1 @ X0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['38'])).
% 0.22/0.52  thf('40', plain,
% 0.22/0.52      (((~ (v1_relat_1 @ sk_B_1)
% 0.22/0.52         | ((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))
% 0.22/0.52         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['29', '39'])).
% 0.22/0.52  thf('41', plain, ((v1_relat_1 @ sk_B_1)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('42', plain,
% 0.22/0.52      (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 0.22/0.52         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.22/0.52      inference('split', [status(esa)], ['2'])).
% 0.22/0.52  thf('43', plain,
% 0.22/0.52      (![X14 : $i, X15 : $i]:
% 0.22/0.52         (~ (r1_xboole_0 @ (k1_relat_1 @ X14) @ X15)
% 0.22/0.52          | ((k7_relat_1 @ X14 @ X15) = (k1_xboole_0))
% 0.22/0.52          | ~ (v1_relat_1 @ X14))),
% 0.22/0.52      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.22/0.52  thf('44', plain,
% 0.22/0.52      (((~ (v1_relat_1 @ sk_B_1)
% 0.22/0.52         | ((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))
% 0.22/0.52         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['42', '43'])).
% 0.22/0.52  thf('45', plain, ((v1_relat_1 @ sk_B_1)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('46', plain,
% 0.22/0.52      ((((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.22/0.52         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.22/0.52      inference('demod', [status(thm)], ['44', '45'])).
% 0.22/0.52  thf('47', plain,
% 0.22/0.52      (![X11 : $i, X12 : $i]:
% 0.22/0.52         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 0.22/0.52          | ~ (v1_relat_1 @ X11))),
% 0.22/0.52      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.22/0.52  thf('48', plain,
% 0.22/0.52      (((((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ sk_B_1 @ sk_A))
% 0.22/0.52         | ~ (v1_relat_1 @ sk_B_1)))
% 0.22/0.52         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['46', '47'])).
% 0.22/0.52  thf('49', plain, ((v1_relat_1 @ sk_B_1)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('50', plain,
% 0.22/0.52      ((((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ sk_B_1 @ sk_A)))
% 0.22/0.52         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.22/0.52      inference('demod', [status(thm)], ['48', '49'])).
% 0.22/0.52  thf('51', plain,
% 0.22/0.52      ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 0.22/0.52         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.22/0.52      inference('demod', [status(thm)], ['40', '41', '50'])).
% 0.22/0.52  thf('52', plain,
% 0.22/0.52      ((((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ sk_B_1 @ sk_A)))
% 0.22/0.52         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.22/0.52      inference('demod', [status(thm)], ['48', '49'])).
% 0.22/0.52  thf('53', plain,
% 0.22/0.52      ((((k9_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))
% 0.22/0.52         <= (~ (((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.52      inference('split', [status(esa)], ['0'])).
% 0.22/0.52  thf('54', plain,
% 0.22/0.52      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.22/0.52         <= (~ (((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) & 
% 0.22/0.52             ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['52', '53'])).
% 0.22/0.52  thf('55', plain,
% 0.22/0.52      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.22/0.52         <= (~ (((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) & 
% 0.22/0.52             ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['51', '54'])).
% 0.22/0.52  thf('56', plain,
% 0.22/0.52      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)) | 
% 0.22/0.52       (((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['55'])).
% 0.22/0.52  thf('57', plain, ($false),
% 0.22/0.52      inference('sat_resolution*', [status(thm)], ['1', '20', '21', '56'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
