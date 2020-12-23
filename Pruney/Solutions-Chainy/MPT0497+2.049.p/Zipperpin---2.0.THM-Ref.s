%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NiBYrykTN1

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:12 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 170 expanded)
%              Number of leaves         :   22 (  55 expanded)
%              Depth                    :   19
%              Number of atoms          :  663 (1658 expanded)
%              Number of equality atoms :   40 ( 105 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) ) ) ),
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

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t86_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ ( k7_relat_1 @ X22 @ X21 ) ) )
      | ( r2_hidden @ X20 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('10',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) ) @ ( k1_relat_1 @ sk_B_1 ) ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['5','13'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('15',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('16',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ ( k7_relat_1 @ X22 @ X21 ) ) )
      | ( r2_hidden @ X20 @ ( k1_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_B @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('19',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ sk_A ) )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['14','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ sk_A ) )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('27',plain,(
    ! [X19: $i] :
      ( ( ( k1_relat_1 @ X19 )
       != k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('28',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ sk_A ) )
      | ( ( k7_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( ( k7_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ sk_A ) ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ( ( k7_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['3','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k7_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k7_relat_1 @ sk_B_1 @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','35'])).

thf('37',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','36'])).

thf('38',plain,
    ( ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('39',plain,
    ( ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('40',plain,
    ( ( k7_relat_1 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','35','39'])).

thf('41',plain,
    ( ( k7_relat_1 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['38','40'])).

thf('42',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('43',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('44',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ X22 ) )
      | ( r2_hidden @ X20 @ ( k1_relat_1 @ ( k7_relat_1 @ X22 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X2 ) ) )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ X1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ X1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( r2_hidden @ ( sk_C @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['41','47'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('49',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('50',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( r2_hidden @ ( sk_C @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) @ k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('52',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('53',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('55',plain,(
    ! [X12: $i] :
      ( r1_xboole_0 @ X12 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('56',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['51','56'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['37','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NiBYrykTN1
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:36:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.91/1.11  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.91/1.11  % Solved by: fo/fo7.sh
% 0.91/1.11  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.11  % done 1378 iterations in 0.656s
% 0.91/1.11  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.91/1.11  % SZS output start Refutation
% 0.91/1.11  thf(sk_B_type, type, sk_B: $i > $i).
% 0.91/1.11  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.11  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.91/1.11  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.91/1.11  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.91/1.11  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.91/1.11  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.91/1.11  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.91/1.11  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.91/1.11  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.91/1.11  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.91/1.11  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.91/1.11  thf(t95_relat_1, conjecture,
% 0.91/1.11    (![A:$i,B:$i]:
% 0.91/1.11     ( ( v1_relat_1 @ B ) =>
% 0.91/1.11       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.91/1.11         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.91/1.11  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.11    (~( ![A:$i,B:$i]:
% 0.91/1.11        ( ( v1_relat_1 @ B ) =>
% 0.91/1.11          ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.91/1.11            ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 0.91/1.11    inference('cnf.neg', [status(esa)], [t95_relat_1])).
% 0.91/1.11  thf('0', plain,
% 0.91/1.11      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.91/1.11        | ((k7_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('1', plain,
% 0.91/1.11      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 0.91/1.11         <= (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.91/1.11      inference('split', [status(esa)], ['0'])).
% 0.91/1.11  thf('2', plain,
% 0.91/1.11      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)) | 
% 0.91/1.11       ~ (((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.91/1.11      inference('split', [status(esa)], ['0'])).
% 0.91/1.11  thf(dt_k7_relat_1, axiom,
% 0.91/1.11    (![A:$i,B:$i]:
% 0.91/1.11     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.91/1.11  thf('3', plain,
% 0.91/1.11      (![X17 : $i, X18 : $i]:
% 0.91/1.11         (~ (v1_relat_1 @ X17) | (v1_relat_1 @ (k7_relat_1 @ X17 @ X18)))),
% 0.91/1.11      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.91/1.11  thf('4', plain,
% 0.91/1.11      (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.91/1.11        | ((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('5', plain,
% 0.91/1.11      (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 0.91/1.11         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.91/1.11      inference('split', [status(esa)], ['4'])).
% 0.91/1.11  thf(t3_xboole_0, axiom,
% 0.91/1.11    (![A:$i,B:$i]:
% 0.91/1.11     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.91/1.11            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.91/1.11       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.91/1.11            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.91/1.11  thf('6', plain,
% 0.91/1.11      (![X2 : $i, X3 : $i]:
% 0.91/1.11         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C @ X3 @ X2) @ X2))),
% 0.91/1.11      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.91/1.11  thf(t86_relat_1, axiom,
% 0.91/1.11    (![A:$i,B:$i,C:$i]:
% 0.91/1.11     ( ( v1_relat_1 @ C ) =>
% 0.91/1.11       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 0.91/1.11         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 0.91/1.11  thf('7', plain,
% 0.91/1.11      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.91/1.11         (~ (r2_hidden @ X20 @ (k1_relat_1 @ (k7_relat_1 @ X22 @ X21)))
% 0.91/1.11          | (r2_hidden @ X20 @ X21)
% 0.91/1.11          | ~ (v1_relat_1 @ X22))),
% 0.91/1.11      inference('cnf', [status(esa)], [t86_relat_1])).
% 0.91/1.11  thf('8', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.11         ((r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2)
% 0.91/1.11          | ~ (v1_relat_1 @ X1)
% 0.91/1.11          | (r2_hidden @ (sk_C @ X2 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))) @ 
% 0.91/1.11             X0))),
% 0.91/1.11      inference('sup-', [status(thm)], ['6', '7'])).
% 0.91/1.11  thf('9', plain,
% 0.91/1.11      (![X2 : $i, X3 : $i]:
% 0.91/1.11         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C @ X3 @ X2) @ X3))),
% 0.91/1.11      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.91/1.11  thf('10', plain,
% 0.91/1.11      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.91/1.11         (~ (r2_hidden @ X4 @ X2)
% 0.91/1.11          | ~ (r2_hidden @ X4 @ X5)
% 0.91/1.11          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.91/1.11      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.91/1.11  thf('11', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.11         ((r1_xboole_0 @ X1 @ X0)
% 0.91/1.11          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.91/1.11          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.91/1.11      inference('sup-', [status(thm)], ['9', '10'])).
% 0.91/1.11  thf('12', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.11         (~ (v1_relat_1 @ X1)
% 0.91/1.11          | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2)
% 0.91/1.11          | ~ (r1_xboole_0 @ X2 @ X0)
% 0.91/1.11          | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2))),
% 0.91/1.11      inference('sup-', [status(thm)], ['8', '11'])).
% 0.91/1.11  thf('13', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.11         (~ (r1_xboole_0 @ X2 @ X0)
% 0.91/1.11          | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2)
% 0.91/1.11          | ~ (v1_relat_1 @ X1))),
% 0.91/1.11      inference('simplify', [status(thm)], ['12'])).
% 0.91/1.11  thf('14', plain,
% 0.91/1.11      ((![X0 : $i]:
% 0.91/1.11          (~ (v1_relat_1 @ X0)
% 0.91/1.11           | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X0 @ sk_A)) @ 
% 0.91/1.11              (k1_relat_1 @ sk_B_1))))
% 0.91/1.11         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.91/1.11      inference('sup-', [status(thm)], ['5', '13'])).
% 0.91/1.11  thf(t7_xboole_0, axiom,
% 0.91/1.11    (![A:$i]:
% 0.91/1.11     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.91/1.11          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.91/1.11  thf('15', plain,
% 0.91/1.11      (![X10 : $i]:
% 0.91/1.11         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.91/1.11      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.91/1.11  thf('16', plain,
% 0.91/1.11      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.91/1.11         (~ (r2_hidden @ X20 @ (k1_relat_1 @ (k7_relat_1 @ X22 @ X21)))
% 0.91/1.11          | (r2_hidden @ X20 @ (k1_relat_1 @ X22))
% 0.91/1.11          | ~ (v1_relat_1 @ X22))),
% 0.91/1.11      inference('cnf', [status(esa)], [t86_relat_1])).
% 0.91/1.11  thf('17', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i]:
% 0.91/1.11         (((k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) = (k1_xboole_0))
% 0.91/1.11          | ~ (v1_relat_1 @ X1)
% 0.91/1.11          | (r2_hidden @ (sk_B @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))) @ 
% 0.91/1.11             (k1_relat_1 @ X1)))),
% 0.91/1.11      inference('sup-', [status(thm)], ['15', '16'])).
% 0.91/1.11  thf('18', plain,
% 0.91/1.11      (![X10 : $i]:
% 0.91/1.11         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.91/1.11      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.91/1.11  thf('19', plain,
% 0.91/1.11      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.91/1.11         (~ (r2_hidden @ X4 @ X2)
% 0.91/1.11          | ~ (r2_hidden @ X4 @ X5)
% 0.91/1.11          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.91/1.11      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.91/1.11  thf('20', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i]:
% 0.91/1.11         (((X0) = (k1_xboole_0))
% 0.91/1.11          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.91/1.11          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 0.91/1.11      inference('sup-', [status(thm)], ['18', '19'])).
% 0.91/1.11  thf('21', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i]:
% 0.91/1.11         (~ (v1_relat_1 @ X0)
% 0.91/1.11          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ X1)) = (k1_xboole_0))
% 0.91/1.11          | ~ (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 0.91/1.11               (k1_relat_1 @ X0))
% 0.91/1.11          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ X1)) = (k1_xboole_0)))),
% 0.91/1.11      inference('sup-', [status(thm)], ['17', '20'])).
% 0.91/1.11  thf('22', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i]:
% 0.91/1.11         (~ (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 0.91/1.11             (k1_relat_1 @ X0))
% 0.91/1.11          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ X1)) = (k1_xboole_0))
% 0.91/1.11          | ~ (v1_relat_1 @ X0))),
% 0.91/1.11      inference('simplify', [status(thm)], ['21'])).
% 0.91/1.11  thf('23', plain,
% 0.91/1.11      (((~ (v1_relat_1 @ sk_B_1)
% 0.91/1.11         | ~ (v1_relat_1 @ sk_B_1)
% 0.91/1.11         | ((k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ sk_A)) = (k1_xboole_0))))
% 0.91/1.11         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.91/1.11      inference('sup-', [status(thm)], ['14', '22'])).
% 0.91/1.11  thf('24', plain, ((v1_relat_1 @ sk_B_1)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('25', plain, ((v1_relat_1 @ sk_B_1)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('26', plain,
% 0.91/1.11      ((((k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ sk_A)) = (k1_xboole_0)))
% 0.91/1.11         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.91/1.11      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.91/1.11  thf(t64_relat_1, axiom,
% 0.91/1.11    (![A:$i]:
% 0.91/1.11     ( ( v1_relat_1 @ A ) =>
% 0.91/1.11       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.91/1.11           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.91/1.11         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.91/1.11  thf('27', plain,
% 0.91/1.11      (![X19 : $i]:
% 0.91/1.11         (((k1_relat_1 @ X19) != (k1_xboole_0))
% 0.91/1.11          | ((X19) = (k1_xboole_0))
% 0.91/1.11          | ~ (v1_relat_1 @ X19))),
% 0.91/1.11      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.91/1.11  thf('28', plain,
% 0.91/1.11      (((((k1_xboole_0) != (k1_xboole_0))
% 0.91/1.11         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B_1 @ sk_A))
% 0.91/1.11         | ((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))
% 0.91/1.11         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.91/1.11      inference('sup-', [status(thm)], ['26', '27'])).
% 0.91/1.11  thf('29', plain,
% 0.91/1.11      (((((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.91/1.11         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B_1 @ sk_A))))
% 0.91/1.11         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.91/1.11      inference('simplify', [status(thm)], ['28'])).
% 0.91/1.11  thf('30', plain,
% 0.91/1.11      (((~ (v1_relat_1 @ sk_B_1)
% 0.91/1.11         | ((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))
% 0.91/1.11         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.91/1.11      inference('sup-', [status(thm)], ['3', '29'])).
% 0.91/1.11  thf('31', plain, ((v1_relat_1 @ sk_B_1)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('32', plain,
% 0.91/1.11      ((((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.91/1.11         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.91/1.11      inference('demod', [status(thm)], ['30', '31'])).
% 0.91/1.11  thf('33', plain,
% 0.91/1.11      ((((k7_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))
% 0.91/1.11         <= (~ (((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.91/1.11      inference('split', [status(esa)], ['0'])).
% 0.91/1.11  thf('34', plain,
% 0.91/1.11      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.91/1.11         <= (~ (((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) & 
% 0.91/1.11             ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.91/1.11      inference('sup-', [status(thm)], ['32', '33'])).
% 0.91/1.11  thf('35', plain,
% 0.91/1.11      ((((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.91/1.11       ~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.91/1.11      inference('simplify', [status(thm)], ['34'])).
% 0.91/1.11  thf('36', plain, (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.91/1.11      inference('sat_resolution*', [status(thm)], ['2', '35'])).
% 0.91/1.11  thf('37', plain, (~ (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 0.91/1.11      inference('simpl_trail', [status(thm)], ['1', '36'])).
% 0.91/1.11  thf('38', plain,
% 0.91/1.11      ((((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.91/1.11         <= ((((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.91/1.11      inference('split', [status(esa)], ['4'])).
% 0.91/1.11  thf('39', plain,
% 0.91/1.11      ((((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.91/1.11       ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.91/1.11      inference('split', [status(esa)], ['4'])).
% 0.91/1.11  thf('40', plain, ((((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.91/1.11      inference('sat_resolution*', [status(thm)], ['2', '35', '39'])).
% 0.91/1.11  thf('41', plain, (((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.91/1.11      inference('simpl_trail', [status(thm)], ['38', '40'])).
% 0.91/1.11  thf('42', plain,
% 0.91/1.11      (![X2 : $i, X3 : $i]:
% 0.91/1.11         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C @ X3 @ X2) @ X3))),
% 0.91/1.11      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.91/1.11  thf('43', plain,
% 0.91/1.11      (![X2 : $i, X3 : $i]:
% 0.91/1.11         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C @ X3 @ X2) @ X2))),
% 0.91/1.11      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.91/1.11  thf('44', plain,
% 0.91/1.11      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.91/1.11         (~ (r2_hidden @ X20 @ X21)
% 0.91/1.11          | ~ (r2_hidden @ X20 @ (k1_relat_1 @ X22))
% 0.91/1.11          | (r2_hidden @ X20 @ (k1_relat_1 @ (k7_relat_1 @ X22 @ X21)))
% 0.91/1.11          | ~ (v1_relat_1 @ X22))),
% 0.91/1.11      inference('cnf', [status(esa)], [t86_relat_1])).
% 0.91/1.11  thf('45', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.11         ((r1_xboole_0 @ (k1_relat_1 @ X0) @ X1)
% 0.91/1.11          | ~ (v1_relat_1 @ X0)
% 0.91/1.11          | (r2_hidden @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ 
% 0.91/1.11             (k1_relat_1 @ (k7_relat_1 @ X0 @ X2)))
% 0.91/1.11          | ~ (r2_hidden @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ X2))),
% 0.91/1.11      inference('sup-', [status(thm)], ['43', '44'])).
% 0.91/1.11  thf('46', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i]:
% 0.91/1.11         ((r1_xboole_0 @ (k1_relat_1 @ X1) @ X0)
% 0.91/1.11          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ X1)) @ 
% 0.91/1.11             (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.91/1.11          | ~ (v1_relat_1 @ X1)
% 0.91/1.11          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ X0))),
% 0.91/1.11      inference('sup-', [status(thm)], ['42', '45'])).
% 0.91/1.11  thf('47', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i]:
% 0.91/1.11         (~ (v1_relat_1 @ X1)
% 0.91/1.11          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ X1)) @ 
% 0.91/1.11             (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.91/1.11          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ X0))),
% 0.91/1.11      inference('simplify', [status(thm)], ['46'])).
% 0.91/1.11  thf('48', plain,
% 0.91/1.11      (((r2_hidden @ (sk_C @ sk_A @ (k1_relat_1 @ sk_B_1)) @ 
% 0.91/1.11         (k1_relat_1 @ k1_xboole_0))
% 0.91/1.11        | (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.91/1.11        | ~ (v1_relat_1 @ sk_B_1))),
% 0.91/1.11      inference('sup+', [status(thm)], ['41', '47'])).
% 0.91/1.11  thf(t60_relat_1, axiom,
% 0.91/1.11    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.91/1.11     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.91/1.11  thf('49', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.91/1.11      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.91/1.11  thf('50', plain, ((v1_relat_1 @ sk_B_1)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('51', plain,
% 0.91/1.11      (((r2_hidden @ (sk_C @ sk_A @ (k1_relat_1 @ sk_B_1)) @ k1_xboole_0)
% 0.91/1.11        | (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.91/1.11      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.91/1.11  thf(t2_boole, axiom,
% 0.91/1.11    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.91/1.11  thf('52', plain,
% 0.91/1.11      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.91/1.11      inference('cnf', [status(esa)], [t2_boole])).
% 0.91/1.11  thf(t4_xboole_0, axiom,
% 0.91/1.11    (![A:$i,B:$i]:
% 0.91/1.11     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.91/1.11            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.91/1.11       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.91/1.11            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.91/1.11  thf('53', plain,
% 0.91/1.11      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.91/1.11         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 0.91/1.11          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.91/1.11      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.91/1.11  thf('54', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i]:
% 0.91/1.11         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.91/1.11      inference('sup-', [status(thm)], ['52', '53'])).
% 0.91/1.11  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.91/1.11  thf('55', plain, (![X12 : $i]: (r1_xboole_0 @ X12 @ k1_xboole_0)),
% 0.91/1.11      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.91/1.11  thf('56', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.91/1.11      inference('demod', [status(thm)], ['54', '55'])).
% 0.91/1.11  thf('57', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 0.91/1.11      inference('clc', [status(thm)], ['51', '56'])).
% 0.91/1.11  thf('58', plain, ($false), inference('demod', [status(thm)], ['37', '57'])).
% 0.91/1.11  
% 0.91/1.11  % SZS output end Refutation
% 0.91/1.11  
% 0.91/1.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
