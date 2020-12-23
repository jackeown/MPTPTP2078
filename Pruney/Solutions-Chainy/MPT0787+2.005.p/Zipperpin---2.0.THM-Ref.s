%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OcF89t7qqN

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:32 EST 2020

% Result     : Theorem 30.11s
% Output     : Refutation 30.11s
% Verified   : 
% Statistics : Number of formulae       :  195 (2504 expanded)
%              Number of leaves         :   33 ( 667 expanded)
%              Depth                    :   28
%              Number of atoms          : 2119 (37084 expanded)
%              Number of equality atoms :   69 ( 838 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v6_relat_2_type,type,(
    v6_relat_2: $i > $o )).

thf(r2_wellord1_type,type,(
    r2_wellord1: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_4_type,type,(
    sk_C_4: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_wellord1_type,type,(
    v1_wellord1: $i > $o )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(t37_wellord1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( v2_wellord1 @ C )
          & ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) )
       => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
        <=> ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( ( v2_wellord1 @ C )
            & ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
            & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) )
         => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
          <=> ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t37_wellord1])).

thf('0',plain,
    ( ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) )
   <= ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
    r2_hidden @ sk_B_3 @ ( k3_relat_1 @ sk_C_5 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_5 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l4_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v6_relat_2 @ A )
      <=> ! [B: $i,C: $i] :
            ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
              & ( r2_hidden @ C @ ( k3_relat_1 @ A ) )
              & ( B != C )
              & ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
              & ~ ( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) ) ) ) )).

thf('5',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v6_relat_2 @ X26 )
      | ~ ( r2_hidden @ X27 @ ( k3_relat_1 @ X26 ) )
      | ( r2_hidden @ ( k4_tarski @ X28 @ X27 ) @ X26 )
      | ( r2_hidden @ ( k4_tarski @ X27 @ X28 ) @ X26 )
      | ( X27 = X28 )
      | ~ ( r2_hidden @ X28 @ ( k3_relat_1 @ X26 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[l4_wellord1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_5 )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_C_5 ) )
      | ( sk_A = X0 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_5 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ sk_A ) @ sk_C_5 )
      | ~ ( v6_relat_2 @ sk_C_5 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_relat_1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
      <=> ( ( v1_relat_2 @ A )
          & ( v8_relat_2 @ A )
          & ( v4_relat_2 @ A )
          & ( v6_relat_2 @ A )
          & ( v1_wellord1 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X18: $i] :
      ( ~ ( v2_wellord1 @ X18 )
      | ( v6_relat_2 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('10',plain,
    ( ( v6_relat_2 @ sk_C_5 )
    | ~ ( v2_wellord1 @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_wellord1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v6_relat_2 @ sk_C_5 ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_C_5 ) )
      | ( sk_A = X0 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_5 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ sk_A ) @ sk_C_5 ) ) ),
    inference(demod,[status(thm)],['6','7','12'])).

thf('14',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B_3 @ sk_A ) @ sk_C_5 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 )
    | ( sk_A = sk_B_3 ) ),
    inference('sup-',[status(thm)],['3','13'])).

thf(d1_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k1_wellord1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ( ( D != B )
                & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i,X15: $i,X17: $i] :
      ( ( X15
       != ( k1_wellord1 @ X14 @ X13 ) )
      | ( r2_hidden @ X17 @ X15 )
      | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X13 ) @ X14 )
      | ( X17 = X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('16',plain,(
    ! [X13: $i,X14: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( X17 = X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X13 ) @ X14 )
      | ( r2_hidden @ X17 @ ( k1_wellord1 @ X14 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( sk_A = sk_B_3 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 )
    | ( r2_hidden @ sk_B_3 @ ( k1_wellord1 @ sk_C_5 @ sk_A ) )
    | ( sk_B_3 = sk_A )
    | ~ ( v1_relat_1 @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( sk_A = sk_B_3 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 )
    | ( r2_hidden @ sk_B_3 @ ( k1_wellord1 @ sk_C_5 @ sk_A ) )
    | ( sk_B_3 = sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r2_hidden @ sk_B_3 @ ( k1_wellord1 @ sk_C_5 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 )
    | ( sk_A = sk_B_3 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ( ( sk_A = sk_B_3 )
      | ( r2_hidden @ sk_B_3 @ ( k1_wellord1 @ sk_C_5 @ sk_A ) ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) )
   <= ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) ) ),
    inference(split,[status(esa)],['23'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) )
        | ~ ( r2_hidden @ X0 @ ( k1_wellord1 @ sk_C_5 @ sk_A ) ) )
   <= ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( sk_A = sk_B_3 )
      | ( r2_hidden @ sk_B_3 @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) ) ) ),
    inference('sup-',[status(thm)],['22','26'])).

thf('28',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X15
       != ( k1_wellord1 @ X14 @ X13 ) )
      | ( X16 != X13 )
      | ~ ( r2_hidden @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('29',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( r2_hidden @ X13 @ ( k1_wellord1 @ X14 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( ( sk_A = sk_B_3 )
      | ~ ( v1_relat_1 @ sk_C_5 ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_A = sk_B_3 )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_5 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(s1_xboole_0__e7_18__wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ? [C: $i] :
        ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ ( k3_relat_1 @ A ) )
            & ~ ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) )).

thf('34',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ( r2_hidden @ X30 @ ( sk_C_4 @ X31 @ X29 ) )
      | ( r2_hidden @ ( k4_tarski @ X30 @ X31 ) @ X29 )
      | ~ ( r2_hidden @ X30 @ ( k3_relat_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[s1_xboole_0__e7_18__wellord1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_5 )
      | ( r2_hidden @ sk_A @ ( sk_C_4 @ X0 @ sk_C_5 ) )
      | ~ ( v1_relat_1 @ sk_C_5 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_5 )
      | ( r2_hidden @ sk_A @ ( sk_C_4 @ X0 @ sk_C_5 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,
    ( ( r2_hidden @ sk_A @ ( sk_C_4 @ sk_B_3 @ sk_C_5 ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('40',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('41',plain,
    ( ~ ( r1_tarski @ ( sk_C_4 @ sk_B_3 @ sk_C_5 ) @ sk_A )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( r1_tarski @ ( sk_C_4 @ sk_A @ sk_C_5 ) @ sk_A )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) ) ) ),
    inference('sup-',[status(thm)],['32','41'])).

thf('43',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('44',plain,(
    ! [X29: $i,X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ( r2_hidden @ X32 @ ( k3_relat_1 @ X29 ) )
      | ~ ( r2_hidden @ X32 @ ( sk_C_4 @ X31 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[s1_xboole_0__e7_18__wellord1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( sk_C_4 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( sk_C_4 @ X1 @ X0 ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( sk_C_4 @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ( r1_tarski @ ( sk_C_4 @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( sk_C_4 @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf(t8_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( r2_wellord1 @ A @ ( k3_relat_1 @ A ) )
      <=> ( v2_wellord1 @ A ) ) ) )).

thf('49',plain,(
    ! [X33: $i] :
      ( ~ ( v2_wellord1 @ X33 )
      | ( r2_wellord1 @ X33 @ ( k3_relat_1 @ X33 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord1])).

thf(t9_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_wellord1 @ B @ A )
       => ! [C: $i] :
            ~ ( ( r1_tarski @ C @ A )
              & ( C != k1_xboole_0 )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ C )
                    & ! [E: $i] :
                        ( ( r2_hidden @ E @ C )
                       => ( r2_hidden @ ( k4_tarski @ D @ E ) @ B ) ) ) ) ) ) )).

thf('50',plain,(
    ! [X34: $i,X35: $i,X37: $i] :
      ( ~ ( r2_wellord1 @ X34 @ X35 )
      | ( r2_hidden @ ( sk_D_2 @ X37 @ X34 ) @ X37 )
      | ( X37 = k1_xboole_0 )
      | ~ ( r1_tarski @ X37 @ X35 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t9_wellord1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X1 @ ( k3_relat_1 @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D_2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ X1 @ X0 ) @ X1 )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_wellord1 @ X0 )
      | ( ( sk_C_4 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D_2 @ ( sk_C_4 @ X1 @ X0 ) @ X0 ) @ ( sk_C_4 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ ( sk_C_4 @ X1 @ X0 ) @ X0 ) @ ( sk_C_4 @ X1 @ X0 ) )
      | ( ( sk_C_4 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( sk_A = sk_B_3 )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('56',plain,
    ( ( r2_hidden @ sk_A @ ( sk_C_4 @ sk_B_3 @ sk_C_5 ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( sk_C_4 @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('58',plain,(
    ! [X33: $i] :
      ( ~ ( v2_wellord1 @ X33 )
      | ( r2_wellord1 @ X33 @ ( k3_relat_1 @ X33 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord1])).

thf('59',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( r2_wellord1 @ X34 @ X35 )
      | ~ ( r2_hidden @ X36 @ X37 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X37 @ X34 ) @ X36 ) @ X34 )
      | ( X37 = k1_xboole_0 )
      | ~ ( r1_tarski @ X37 @ X35 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t9_wellord1])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X1 @ ( k3_relat_1 @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X1 @ X0 ) @ X2 ) @ X0 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X1 @ X0 ) @ X2 ) @ X0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_wellord1 @ X0 )
      | ( ( sk_C_4 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ ( sk_C_4 @ X1 @ X0 ) @ X0 ) @ X2 ) @ X0 )
      | ~ ( r2_hidden @ X2 @ ( sk_C_4 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['57','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( sk_C_4 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ ( sk_C_4 @ X1 @ X0 ) @ X0 ) @ X2 ) @ X0 )
      | ( ( sk_C_4 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_5 )
      | ~ ( v2_wellord1 @ sk_C_5 )
      | ( ( sk_C_4 @ sk_B_3 @ sk_C_5 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ ( sk_C_4 @ sk_B_3 @ sk_C_5 ) @ sk_C_5 ) @ sk_A ) @ sk_C_5 ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['56','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v2_wellord1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( ( ( sk_C_4 @ sk_B_3 @ sk_C_5 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ ( sk_C_4 @ sk_B_3 @ sk_C_5 ) @ sk_C_5 ) @ sk_A ) @ sk_C_5 ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ! [X29: $i,X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ~ ( r2_hidden @ ( k4_tarski @ X32 @ X31 ) @ X29 )
      | ~ ( r2_hidden @ X32 @ ( sk_C_4 @ X31 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[s1_xboole_0__e7_18__wellord1])).

thf('69',plain,
    ( ( ( ( sk_C_4 @ sk_B_3 @ sk_C_5 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_D_2 @ ( sk_C_4 @ sk_B_3 @ sk_C_5 ) @ sk_C_5 ) @ ( sk_C_4 @ sk_A @ sk_C_5 ) )
      | ~ ( v1_relat_1 @ sk_C_5 ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( ( ( sk_C_4 @ sk_B_3 @ sk_C_5 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_D_2 @ ( sk_C_4 @ sk_B_3 @ sk_C_5 ) @ sk_C_5 ) @ ( sk_C_4 @ sk_A @ sk_C_5 ) ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ~ ( r2_hidden @ ( sk_D_2 @ ( sk_C_4 @ sk_A @ sk_C_5 ) @ sk_C_5 ) @ ( sk_C_4 @ sk_A @ sk_C_5 ) )
      | ( ( sk_C_4 @ sk_B_3 @ sk_C_5 )
        = k1_xboole_0 ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) ) ) ),
    inference('sup-',[status(thm)],['55','71'])).

thf('73',plain,
    ( ( sk_A = sk_B_3 )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('74',plain,
    ( ( ~ ( r2_hidden @ ( sk_D_2 @ ( sk_C_4 @ sk_A @ sk_C_5 ) @ sk_C_5 ) @ ( sk_C_4 @ sk_A @ sk_C_5 ) )
      | ( ( sk_C_4 @ sk_A @ sk_C_5 )
        = k1_xboole_0 ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_5 )
      | ~ ( v2_wellord1 @ sk_C_5 )
      | ( ( sk_C_4 @ sk_A @ sk_C_5 )
        = k1_xboole_0 )
      | ( ( sk_C_4 @ sk_A @ sk_C_5 )
        = k1_xboole_0 ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) ) ) ),
    inference('sup-',[status(thm)],['54','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v2_wellord1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( ( ( sk_C_4 @ sk_A @ sk_C_5 )
        = k1_xboole_0 )
      | ( ( sk_C_4 @ sk_A @ sk_C_5 )
        = k1_xboole_0 ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ( ( sk_C_4 @ sk_A @ sk_C_5 )
      = k1_xboole_0 )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    v1_relat_1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('81',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('82',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('84',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X15
       != ( k1_wellord1 @ X14 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ X16 @ X13 ) @ X14 )
      | ~ ( r2_hidden @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('85',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k1_wellord1 @ X14 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ X16 @ X13 ) @ X14 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_wellord1 @ X1 @ X0 ) ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['83','85'])).

thf(t30_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )).

thf('87',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X9 )
      | ( r2_hidden @ X8 @ ( k3_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ ( k3_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_wellord1 @ X1 @ X0 ) ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['83','85'])).

thf('94',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X9 )
      | ( r2_hidden @ X7 @ ( k3_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ ( k3_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ X1 @ X0 ) @ X1 )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_wellord1 @ X0 )
      | ( ( k1_wellord1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D_2 @ ( k1_wellord1 @ X0 @ X1 ) @ X0 ) @ ( k1_wellord1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ ( k1_wellord1 @ X0 @ X1 ) @ X0 ) @ ( k1_wellord1 @ X0 @ X1 ) )
      | ( ( k1_wellord1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_wellord1 @ X1 )
      | ( ( k1_wellord1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k1_wellord1 @ X1 @ X0 ) @ ( sk_D_2 @ ( k1_wellord1 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( v2_wellord1 @ X0 )
      | ( ( k1_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','91'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_wellord1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_wellord1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v2_wellord1 @ sk_C_5 ) ) ),
    inference('sup-',[status(thm)],['80','109'])).

thf('111',plain,(
    v2_wellord1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 )
    | ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['42','79','112'])).

thf('114',plain,(
    ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','113'])).

thf('115',plain,(
    ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) ) ),
    inference(simpl_trail,[status(thm)],['1','114'])).

thf('116',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 ) ),
    inference(split,[status(esa)],['23'])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_wellord1 @ X1 @ X0 ) ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['83','85'])).

thf(l2_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v8_relat_2 @ A )
      <=> ! [B: $i,C: $i,D: $i] :
            ( ( ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
              & ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) )
           => ( r2_hidden @ ( k4_tarski @ B @ D ) @ A ) ) ) ) )).

thf('118',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( v8_relat_2 @ X19 )
      | ~ ( r2_hidden @ ( k4_tarski @ X20 @ X21 ) @ X19 )
      | ~ ( r2_hidden @ ( k4_tarski @ X21 @ X22 ) @ X19 )
      | ( r2_hidden @ ( k4_tarski @ X20 @ X22 ) @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l2_wellord1])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) @ X3 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X3 ) @ X0 )
      | ~ ( v8_relat_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v8_relat_2 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X3 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) @ X3 ) @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_C_5 )
        | ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ X0 )
        | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_5 @ sk_A ) ) @ sk_B_3 ) @ sk_C_5 )
        | ~ ( v8_relat_2 @ sk_C_5 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['116','120'])).

thf('122',plain,(
    v1_relat_1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v1_relat_1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X18: $i] :
      ( ~ ( v2_wellord1 @ X18 )
      | ( v8_relat_2 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('125',plain,
    ( ( v8_relat_2 @ sk_C_5 )
    | ~ ( v2_wellord1 @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    v2_wellord1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v8_relat_2 @ sk_C_5 ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ X0 )
        | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_5 @ sk_A ) ) @ sk_B_3 ) @ sk_C_5 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 ) ),
    inference(demod,[status(thm)],['121','122','127'])).

thf('129',plain,(
    ! [X13: $i,X14: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( X17 = X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X13 ) @ X14 )
      | ( r2_hidden @ X17 @ ( k1_wellord1 @ X14 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('130',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_5 @ sk_A ) ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) )
        | ( ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_5 @ sk_A ) )
          = sk_B_3 )
        | ~ ( v1_relat_1 @ sk_C_5 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    v1_relat_1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_5 @ sk_A ) ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) )
        | ( ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_5 @ sk_A ) )
          = sk_B_3 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) ) ),
    inference(split,[status(esa)],['23'])).

thf('134',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 ),
    inference('sat_resolution*',[status(thm)],['2','113','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_5 @ sk_A ) ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) )
      | ( ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_5 @ sk_A ) )
        = sk_B_3 ) ) ),
    inference(simpl_trail,[status(thm)],['132','134'])).

thf('136',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('137',plain,
    ( ( ( sk_C @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) @ ( k1_wellord1 @ sk_C_5 @ sk_A ) )
      = sk_B_3 )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) )
    | ( ( sk_C @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) @ ( k1_wellord1 @ sk_C_5 @ sk_A ) )
      = sk_B_3 ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) ) ),
    inference(simpl_trail,[status(thm)],['1','114'])).

thf('140',plain,
    ( ( sk_C @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) @ ( k1_wellord1 @ sk_C_5 @ sk_A ) )
    = sk_B_3 ),
    inference(clc,[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_wellord1 @ X1 @ X0 ) ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['83','85'])).

thf(l3_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v4_relat_2 @ A )
      <=> ! [B: $i,C: $i] :
            ( ( ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
              & ( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) )
           => ( B = C ) ) ) ) )).

thf('142',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v4_relat_2 @ X23 )
      | ( X25 = X24 )
      | ~ ( r2_hidden @ ( k4_tarski @ X24 @ X25 ) @ X23 )
      | ~ ( r2_hidden @ ( k4_tarski @ X25 @ X24 ) @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l3_wellord1])).

thf('143',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) ) @ X0 )
      | ( X1
        = ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) )
      | ~ ( v4_relat_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v4_relat_2 @ X0 )
      | ( X1
        = ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) ) @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 )
    | ~ ( v1_relat_1 @ sk_C_5 )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) )
    | ( sk_A
      = ( sk_C @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) @ ( k1_wellord1 @ sk_C_5 @ sk_A ) ) )
    | ~ ( v4_relat_2 @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['140','144'])).

thf('146',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 ) ),
    inference(split,[status(esa)],['23'])).

thf('147',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 ),
    inference('sat_resolution*',[status(thm)],['2','113','133'])).

thf('148',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 ),
    inference(simpl_trail,[status(thm)],['146','147'])).

thf('149',plain,(
    v1_relat_1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( sk_C @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) @ ( k1_wellord1 @ sk_C_5 @ sk_A ) )
    = sk_B_3 ),
    inference(clc,[status(thm)],['138','139'])).

thf('151',plain,(
    v1_relat_1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    ! [X18: $i] :
      ( ~ ( v2_wellord1 @ X18 )
      | ( v4_relat_2 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('153',plain,
    ( ( v4_relat_2 @ sk_C_5 )
    | ~ ( v2_wellord1 @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    v2_wellord1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v4_relat_2 @ sk_C_5 ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) )
    | ( sk_A = sk_B_3 ) ),
    inference(demod,[status(thm)],['145','148','149','150','155'])).

thf('157',plain,(
    ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) ) ),
    inference(simpl_trail,[status(thm)],['1','114'])).

thf('158',plain,(
    sk_A = sk_B_3 ),
    inference(clc,[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['81'])).

thf('160',plain,(
    $false ),
    inference(demod,[status(thm)],['115','158','159'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OcF89t7qqN
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:23:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 30.11/30.28  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 30.11/30.28  % Solved by: fo/fo7.sh
% 30.11/30.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 30.11/30.28  % done 17138 iterations in 29.813s
% 30.11/30.28  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 30.11/30.28  % SZS output start Refutation
% 30.11/30.28  thf(v1_relat_2_type, type, v1_relat_2: $i > $o).
% 30.11/30.28  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 30.11/30.28  thf(v8_relat_2_type, type, v8_relat_2: $i > $o).
% 30.11/30.28  thf(v4_relat_2_type, type, v4_relat_2: $i > $o).
% 30.11/30.28  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 30.11/30.28  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 30.11/30.28  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 30.11/30.28  thf(sk_B_3_type, type, sk_B_3: $i).
% 30.11/30.28  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 30.11/30.28  thf(v6_relat_2_type, type, v6_relat_2: $i > $o).
% 30.11/30.28  thf(r2_wellord1_type, type, r2_wellord1: $i > $i > $o).
% 30.11/30.28  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 30.11/30.28  thf(sk_C_4_type, type, sk_C_4: $i > $i > $i).
% 30.11/30.28  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 30.11/30.28  thf(v1_wellord1_type, type, v1_wellord1: $i > $o).
% 30.11/30.28  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 30.11/30.28  thf(sk_C_5_type, type, sk_C_5: $i).
% 30.11/30.28  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 30.11/30.28  thf(sk_A_type, type, sk_A: $i).
% 30.11/30.28  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 30.11/30.28  thf(t37_wellord1, conjecture,
% 30.11/30.28    (![A:$i,B:$i,C:$i]:
% 30.11/30.28     ( ( v1_relat_1 @ C ) =>
% 30.11/30.28       ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 30.11/30.28           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) =>
% 30.11/30.28         ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 30.11/30.28           ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) ))).
% 30.11/30.28  thf(zf_stmt_0, negated_conjecture,
% 30.11/30.28    (~( ![A:$i,B:$i,C:$i]:
% 30.11/30.28        ( ( v1_relat_1 @ C ) =>
% 30.11/30.28          ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 30.11/30.28              ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) =>
% 30.11/30.28            ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 30.11/30.28              ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) ) )),
% 30.11/30.28    inference('cnf.neg', [status(esa)], [t37_wellord1])).
% 30.11/30.28  thf('0', plain,
% 30.11/30.28      ((~ (r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 30.11/30.28           (k1_wellord1 @ sk_C_5 @ sk_B_3))
% 30.11/30.28        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5))),
% 30.11/30.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.11/30.28  thf('1', plain,
% 30.11/30.28      ((~ (r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 30.11/30.28           (k1_wellord1 @ sk_C_5 @ sk_B_3)))
% 30.11/30.28         <= (~
% 30.11/30.28             ((r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 30.11/30.28               (k1_wellord1 @ sk_C_5 @ sk_B_3))))),
% 30.11/30.28      inference('split', [status(esa)], ['0'])).
% 30.11/30.28  thf('2', plain,
% 30.11/30.28      (~
% 30.11/30.28       ((r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 30.11/30.28         (k1_wellord1 @ sk_C_5 @ sk_B_3))) | 
% 30.11/30.28       ~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5))),
% 30.11/30.28      inference('split', [status(esa)], ['0'])).
% 30.11/30.28  thf('3', plain, ((r2_hidden @ sk_B_3 @ (k3_relat_1 @ sk_C_5))),
% 30.11/30.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.11/30.28  thf('4', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_5))),
% 30.11/30.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.11/30.28  thf(l4_wellord1, axiom,
% 30.11/30.28    (![A:$i]:
% 30.11/30.28     ( ( v1_relat_1 @ A ) =>
% 30.11/30.28       ( ( v6_relat_2 @ A ) <=>
% 30.11/30.28         ( ![B:$i,C:$i]:
% 30.11/30.28           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 30.11/30.28                ( r2_hidden @ C @ ( k3_relat_1 @ A ) ) & ( ( B ) != ( C ) ) & 
% 30.11/30.28                ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) & 
% 30.11/30.28                ( ~( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) ) ) ) ) ) ))).
% 30.11/30.28  thf('5', plain,
% 30.11/30.28      (![X26 : $i, X27 : $i, X28 : $i]:
% 30.11/30.28         (~ (v6_relat_2 @ X26)
% 30.11/30.28          | ~ (r2_hidden @ X27 @ (k3_relat_1 @ X26))
% 30.11/30.28          | (r2_hidden @ (k4_tarski @ X28 @ X27) @ X26)
% 30.11/30.28          | (r2_hidden @ (k4_tarski @ X27 @ X28) @ X26)
% 30.11/30.28          | ((X27) = (X28))
% 30.11/30.28          | ~ (r2_hidden @ X28 @ (k3_relat_1 @ X26))
% 30.11/30.28          | ~ (v1_relat_1 @ X26))),
% 30.11/30.28      inference('cnf', [status(esa)], [l4_wellord1])).
% 30.11/30.28  thf('6', plain,
% 30.11/30.28      (![X0 : $i]:
% 30.11/30.28         (~ (v1_relat_1 @ sk_C_5)
% 30.11/30.28          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C_5))
% 30.11/30.28          | ((sk_A) = (X0))
% 30.11/30.28          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_5)
% 30.11/30.28          | (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ sk_C_5)
% 30.11/30.28          | ~ (v6_relat_2 @ sk_C_5))),
% 30.11/30.28      inference('sup-', [status(thm)], ['4', '5'])).
% 30.11/30.28  thf('7', plain, ((v1_relat_1 @ sk_C_5)),
% 30.11/30.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.11/30.28  thf('8', plain, ((v1_relat_1 @ sk_C_5)),
% 30.11/30.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.11/30.28  thf(d4_wellord1, axiom,
% 30.11/30.28    (![A:$i]:
% 30.11/30.28     ( ( v1_relat_1 @ A ) =>
% 30.11/30.28       ( ( v2_wellord1 @ A ) <=>
% 30.11/30.28         ( ( v1_relat_2 @ A ) & ( v8_relat_2 @ A ) & ( v4_relat_2 @ A ) & 
% 30.11/30.28           ( v6_relat_2 @ A ) & ( v1_wellord1 @ A ) ) ) ))).
% 30.11/30.28  thf('9', plain,
% 30.11/30.28      (![X18 : $i]:
% 30.11/30.28         (~ (v2_wellord1 @ X18) | (v6_relat_2 @ X18) | ~ (v1_relat_1 @ X18))),
% 30.11/30.28      inference('cnf', [status(esa)], [d4_wellord1])).
% 30.11/30.28  thf('10', plain, (((v6_relat_2 @ sk_C_5) | ~ (v2_wellord1 @ sk_C_5))),
% 30.11/30.28      inference('sup-', [status(thm)], ['8', '9'])).
% 30.11/30.28  thf('11', plain, ((v2_wellord1 @ sk_C_5)),
% 30.11/30.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.11/30.28  thf('12', plain, ((v6_relat_2 @ sk_C_5)),
% 30.11/30.28      inference('demod', [status(thm)], ['10', '11'])).
% 30.11/30.28  thf('13', plain,
% 30.11/30.28      (![X0 : $i]:
% 30.11/30.28         (~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C_5))
% 30.11/30.28          | ((sk_A) = (X0))
% 30.11/30.28          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_5)
% 30.11/30.28          | (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ sk_C_5))),
% 30.11/30.28      inference('demod', [status(thm)], ['6', '7', '12'])).
% 30.11/30.28  thf('14', plain,
% 30.11/30.28      (((r2_hidden @ (k4_tarski @ sk_B_3 @ sk_A) @ sk_C_5)
% 30.11/30.28        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)
% 30.11/30.28        | ((sk_A) = (sk_B_3)))),
% 30.11/30.28      inference('sup-', [status(thm)], ['3', '13'])).
% 30.11/30.28  thf(d1_wellord1, axiom,
% 30.11/30.28    (![A:$i]:
% 30.11/30.28     ( ( v1_relat_1 @ A ) =>
% 30.11/30.28       ( ![B:$i,C:$i]:
% 30.11/30.28         ( ( ( C ) = ( k1_wellord1 @ A @ B ) ) <=>
% 30.11/30.28           ( ![D:$i]:
% 30.11/30.28             ( ( r2_hidden @ D @ C ) <=>
% 30.11/30.28               ( ( ( D ) != ( B ) ) & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) ) ))).
% 30.11/30.28  thf('15', plain,
% 30.11/30.28      (![X13 : $i, X14 : $i, X15 : $i, X17 : $i]:
% 30.11/30.28         (((X15) != (k1_wellord1 @ X14 @ X13))
% 30.11/30.28          | (r2_hidden @ X17 @ X15)
% 30.11/30.28          | ~ (r2_hidden @ (k4_tarski @ X17 @ X13) @ X14)
% 30.11/30.28          | ((X17) = (X13))
% 30.11/30.28          | ~ (v1_relat_1 @ X14))),
% 30.11/30.28      inference('cnf', [status(esa)], [d1_wellord1])).
% 30.11/30.28  thf('16', plain,
% 30.11/30.28      (![X13 : $i, X14 : $i, X17 : $i]:
% 30.11/30.28         (~ (v1_relat_1 @ X14)
% 30.11/30.28          | ((X17) = (X13))
% 30.11/30.28          | ~ (r2_hidden @ (k4_tarski @ X17 @ X13) @ X14)
% 30.11/30.28          | (r2_hidden @ X17 @ (k1_wellord1 @ X14 @ X13)))),
% 30.11/30.28      inference('simplify', [status(thm)], ['15'])).
% 30.11/30.28  thf('17', plain,
% 30.11/30.28      ((((sk_A) = (sk_B_3))
% 30.11/30.28        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)
% 30.11/30.28        | (r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_5 @ sk_A))
% 30.11/30.28        | ((sk_B_3) = (sk_A))
% 30.11/30.28        | ~ (v1_relat_1 @ sk_C_5))),
% 30.11/30.28      inference('sup-', [status(thm)], ['14', '16'])).
% 30.11/30.28  thf('18', plain, ((v1_relat_1 @ sk_C_5)),
% 30.11/30.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.11/30.28  thf('19', plain,
% 30.11/30.28      ((((sk_A) = (sk_B_3))
% 30.11/30.28        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)
% 30.11/30.28        | (r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_5 @ sk_A))
% 30.11/30.28        | ((sk_B_3) = (sk_A)))),
% 30.11/30.28      inference('demod', [status(thm)], ['17', '18'])).
% 30.11/30.28  thf('20', plain,
% 30.11/30.28      (((r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_5 @ sk_A))
% 30.11/30.28        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)
% 30.11/30.28        | ((sk_A) = (sk_B_3)))),
% 30.11/30.28      inference('simplify', [status(thm)], ['19'])).
% 30.11/30.28  thf('21', plain,
% 30.11/30.28      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5))
% 30.11/30.28         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)))),
% 30.11/30.28      inference('split', [status(esa)], ['0'])).
% 30.11/30.28  thf('22', plain,
% 30.11/30.28      (((((sk_A) = (sk_B_3))
% 30.11/30.28         | (r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_5 @ sk_A))))
% 30.11/30.28         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)))),
% 30.11/30.28      inference('sup-', [status(thm)], ['20', '21'])).
% 30.11/30.28  thf('23', plain,
% 30.11/30.28      (((r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 30.11/30.28         (k1_wellord1 @ sk_C_5 @ sk_B_3))
% 30.11/30.28        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5))),
% 30.11/30.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.11/30.28  thf('24', plain,
% 30.11/30.28      (((r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 30.11/30.28         (k1_wellord1 @ sk_C_5 @ sk_B_3)))
% 30.11/30.28         <= (((r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 30.11/30.28               (k1_wellord1 @ sk_C_5 @ sk_B_3))))),
% 30.11/30.28      inference('split', [status(esa)], ['23'])).
% 30.11/30.28  thf(d3_tarski, axiom,
% 30.11/30.28    (![A:$i,B:$i]:
% 30.11/30.28     ( ( r1_tarski @ A @ B ) <=>
% 30.11/30.28       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 30.11/30.28  thf('25', plain,
% 30.11/30.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.11/30.28         (~ (r2_hidden @ X0 @ X1)
% 30.11/30.28          | (r2_hidden @ X0 @ X2)
% 30.11/30.28          | ~ (r1_tarski @ X1 @ X2))),
% 30.11/30.28      inference('cnf', [status(esa)], [d3_tarski])).
% 30.11/30.28  thf('26', plain,
% 30.11/30.28      ((![X0 : $i]:
% 30.11/30.28          ((r2_hidden @ X0 @ (k1_wellord1 @ sk_C_5 @ sk_B_3))
% 30.11/30.28           | ~ (r2_hidden @ X0 @ (k1_wellord1 @ sk_C_5 @ sk_A))))
% 30.11/30.28         <= (((r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 30.11/30.28               (k1_wellord1 @ sk_C_5 @ sk_B_3))))),
% 30.11/30.28      inference('sup-', [status(thm)], ['24', '25'])).
% 30.11/30.28  thf('27', plain,
% 30.11/30.28      (((((sk_A) = (sk_B_3))
% 30.11/30.28         | (r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_5 @ sk_B_3))))
% 30.11/30.28         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)) & 
% 30.11/30.28             ((r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 30.11/30.28               (k1_wellord1 @ sk_C_5 @ sk_B_3))))),
% 30.11/30.28      inference('sup-', [status(thm)], ['22', '26'])).
% 30.11/30.28  thf('28', plain,
% 30.11/30.28      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 30.11/30.28         (((X15) != (k1_wellord1 @ X14 @ X13))
% 30.11/30.28          | ((X16) != (X13))
% 30.11/30.28          | ~ (r2_hidden @ X16 @ X15)
% 30.11/30.28          | ~ (v1_relat_1 @ X14))),
% 30.11/30.28      inference('cnf', [status(esa)], [d1_wellord1])).
% 30.11/30.28  thf('29', plain,
% 30.11/30.28      (![X13 : $i, X14 : $i]:
% 30.11/30.28         (~ (v1_relat_1 @ X14)
% 30.11/30.28          | ~ (r2_hidden @ X13 @ (k1_wellord1 @ X14 @ X13)))),
% 30.11/30.28      inference('simplify', [status(thm)], ['28'])).
% 30.11/30.28  thf('30', plain,
% 30.11/30.28      (((((sk_A) = (sk_B_3)) | ~ (v1_relat_1 @ sk_C_5)))
% 30.11/30.28         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)) & 
% 30.11/30.28             ((r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 30.11/30.28               (k1_wellord1 @ sk_C_5 @ sk_B_3))))),
% 30.11/30.28      inference('sup-', [status(thm)], ['27', '29'])).
% 30.11/30.28  thf('31', plain, ((v1_relat_1 @ sk_C_5)),
% 30.11/30.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.11/30.28  thf('32', plain,
% 30.11/30.28      ((((sk_A) = (sk_B_3)))
% 30.11/30.28         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)) & 
% 30.11/30.28             ((r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 30.11/30.28               (k1_wellord1 @ sk_C_5 @ sk_B_3))))),
% 30.11/30.28      inference('demod', [status(thm)], ['30', '31'])).
% 30.11/30.28  thf('33', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_5))),
% 30.11/30.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.11/30.28  thf(s1_xboole_0__e7_18__wellord1, axiom,
% 30.11/30.28    (![A:$i,B:$i]:
% 30.11/30.28     ( ( v1_relat_1 @ A ) =>
% 30.11/30.28       ( ?[C:$i]:
% 30.11/30.28         ( ![D:$i]:
% 30.11/30.28           ( ( r2_hidden @ D @ C ) <=>
% 30.11/30.28             ( ( r2_hidden @ D @ ( k3_relat_1 @ A ) ) & 
% 30.11/30.28               ( ~( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) ) ))).
% 30.11/30.28  thf('34', plain,
% 30.11/30.28      (![X29 : $i, X30 : $i, X31 : $i]:
% 30.11/30.28         (~ (v1_relat_1 @ X29)
% 30.11/30.28          | (r2_hidden @ X30 @ (sk_C_4 @ X31 @ X29))
% 30.11/30.28          | (r2_hidden @ (k4_tarski @ X30 @ X31) @ X29)
% 30.11/30.28          | ~ (r2_hidden @ X30 @ (k3_relat_1 @ X29)))),
% 30.11/30.28      inference('cnf', [status(esa)], [s1_xboole_0__e7_18__wellord1])).
% 30.11/30.28  thf('35', plain,
% 30.11/30.28      (![X0 : $i]:
% 30.11/30.28         ((r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_5)
% 30.11/30.28          | (r2_hidden @ sk_A @ (sk_C_4 @ X0 @ sk_C_5))
% 30.11/30.28          | ~ (v1_relat_1 @ sk_C_5))),
% 30.11/30.28      inference('sup-', [status(thm)], ['33', '34'])).
% 30.11/30.28  thf('36', plain, ((v1_relat_1 @ sk_C_5)),
% 30.11/30.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.11/30.28  thf('37', plain,
% 30.11/30.28      (![X0 : $i]:
% 30.11/30.28         ((r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_5)
% 30.11/30.28          | (r2_hidden @ sk_A @ (sk_C_4 @ X0 @ sk_C_5)))),
% 30.11/30.28      inference('demod', [status(thm)], ['35', '36'])).
% 30.11/30.28  thf('38', plain,
% 30.11/30.28      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5))
% 30.11/30.28         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)))),
% 30.11/30.28      inference('split', [status(esa)], ['0'])).
% 30.11/30.28  thf('39', plain,
% 30.11/30.28      (((r2_hidden @ sk_A @ (sk_C_4 @ sk_B_3 @ sk_C_5)))
% 30.11/30.28         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)))),
% 30.11/30.28      inference('sup-', [status(thm)], ['37', '38'])).
% 30.11/30.28  thf(t7_ordinal1, axiom,
% 30.11/30.28    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 30.11/30.28  thf('40', plain,
% 30.11/30.28      (![X10 : $i, X11 : $i]:
% 30.11/30.28         (~ (r2_hidden @ X10 @ X11) | ~ (r1_tarski @ X11 @ X10))),
% 30.11/30.28      inference('cnf', [status(esa)], [t7_ordinal1])).
% 30.11/30.28  thf('41', plain,
% 30.11/30.28      ((~ (r1_tarski @ (sk_C_4 @ sk_B_3 @ sk_C_5) @ sk_A))
% 30.11/30.28         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)))),
% 30.11/30.28      inference('sup-', [status(thm)], ['39', '40'])).
% 30.11/30.28  thf('42', plain,
% 30.11/30.28      ((~ (r1_tarski @ (sk_C_4 @ sk_A @ sk_C_5) @ sk_A))
% 30.11/30.28         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)) & 
% 30.11/30.28             ((r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 30.11/30.28               (k1_wellord1 @ sk_C_5 @ sk_B_3))))),
% 30.11/30.28      inference('sup-', [status(thm)], ['32', '41'])).
% 30.11/30.28  thf('43', plain,
% 30.11/30.28      (![X1 : $i, X3 : $i]:
% 30.11/30.28         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 30.11/30.28      inference('cnf', [status(esa)], [d3_tarski])).
% 30.11/30.28  thf('44', plain,
% 30.11/30.28      (![X29 : $i, X31 : $i, X32 : $i]:
% 30.11/30.28         (~ (v1_relat_1 @ X29)
% 30.11/30.28          | (r2_hidden @ X32 @ (k3_relat_1 @ X29))
% 30.11/30.28          | ~ (r2_hidden @ X32 @ (sk_C_4 @ X31 @ X29)))),
% 30.11/30.28      inference('cnf', [status(esa)], [s1_xboole_0__e7_18__wellord1])).
% 30.11/30.28  thf('45', plain,
% 30.11/30.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.11/30.28         ((r1_tarski @ (sk_C_4 @ X1 @ X0) @ X2)
% 30.11/30.28          | (r2_hidden @ (sk_C @ X2 @ (sk_C_4 @ X1 @ X0)) @ (k3_relat_1 @ X0))
% 30.11/30.28          | ~ (v1_relat_1 @ X0))),
% 30.11/30.28      inference('sup-', [status(thm)], ['43', '44'])).
% 30.11/30.28  thf('46', plain,
% 30.11/30.28      (![X1 : $i, X3 : $i]:
% 30.11/30.28         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 30.11/30.28      inference('cnf', [status(esa)], [d3_tarski])).
% 30.11/30.28  thf('47', plain,
% 30.11/30.28      (![X0 : $i, X1 : $i]:
% 30.11/30.28         (~ (v1_relat_1 @ X0)
% 30.11/30.28          | (r1_tarski @ (sk_C_4 @ X1 @ X0) @ (k3_relat_1 @ X0))
% 30.11/30.28          | (r1_tarski @ (sk_C_4 @ X1 @ X0) @ (k3_relat_1 @ X0)))),
% 30.11/30.28      inference('sup-', [status(thm)], ['45', '46'])).
% 30.11/30.28  thf('48', plain,
% 30.11/30.28      (![X0 : $i, X1 : $i]:
% 30.11/30.28         ((r1_tarski @ (sk_C_4 @ X1 @ X0) @ (k3_relat_1 @ X0))
% 30.11/30.28          | ~ (v1_relat_1 @ X0))),
% 30.11/30.28      inference('simplify', [status(thm)], ['47'])).
% 30.11/30.28  thf(t8_wellord1, axiom,
% 30.11/30.28    (![A:$i]:
% 30.11/30.28     ( ( v1_relat_1 @ A ) =>
% 30.11/30.28       ( ( r2_wellord1 @ A @ ( k3_relat_1 @ A ) ) <=> ( v2_wellord1 @ A ) ) ))).
% 30.11/30.28  thf('49', plain,
% 30.11/30.28      (![X33 : $i]:
% 30.11/30.28         (~ (v2_wellord1 @ X33)
% 30.11/30.28          | (r2_wellord1 @ X33 @ (k3_relat_1 @ X33))
% 30.11/30.28          | ~ (v1_relat_1 @ X33))),
% 30.11/30.28      inference('cnf', [status(esa)], [t8_wellord1])).
% 30.11/30.28  thf(t9_wellord1, axiom,
% 30.11/30.28    (![A:$i,B:$i]:
% 30.11/30.28     ( ( v1_relat_1 @ B ) =>
% 30.11/30.28       ( ( r2_wellord1 @ B @ A ) =>
% 30.11/30.28         ( ![C:$i]:
% 30.11/30.28           ( ~( ( r1_tarski @ C @ A ) & ( ( C ) != ( k1_xboole_0 ) ) & 
% 30.11/30.28                ( ![D:$i]:
% 30.11/30.28                  ( ~( ( r2_hidden @ D @ C ) & 
% 30.11/30.28                       ( ![E:$i]:
% 30.11/30.28                         ( ( r2_hidden @ E @ C ) =>
% 30.11/30.28                           ( r2_hidden @ ( k4_tarski @ D @ E ) @ B ) ) ) ) ) ) ) ) ) ) ))).
% 30.11/30.28  thf('50', plain,
% 30.11/30.28      (![X34 : $i, X35 : $i, X37 : $i]:
% 30.11/30.28         (~ (r2_wellord1 @ X34 @ X35)
% 30.11/30.28          | (r2_hidden @ (sk_D_2 @ X37 @ X34) @ X37)
% 30.11/30.28          | ((X37) = (k1_xboole_0))
% 30.11/30.28          | ~ (r1_tarski @ X37 @ X35)
% 30.11/30.28          | ~ (v1_relat_1 @ X34))),
% 30.11/30.28      inference('cnf', [status(esa)], [t9_wellord1])).
% 30.11/30.28  thf('51', plain,
% 30.11/30.28      (![X0 : $i, X1 : $i]:
% 30.11/30.28         (~ (v1_relat_1 @ X0)
% 30.11/30.28          | ~ (v2_wellord1 @ X0)
% 30.11/30.28          | ~ (v1_relat_1 @ X0)
% 30.11/30.28          | ~ (r1_tarski @ X1 @ (k3_relat_1 @ X0))
% 30.11/30.28          | ((X1) = (k1_xboole_0))
% 30.11/30.28          | (r2_hidden @ (sk_D_2 @ X1 @ X0) @ X1))),
% 30.11/30.28      inference('sup-', [status(thm)], ['49', '50'])).
% 30.11/30.28  thf('52', plain,
% 30.11/30.28      (![X0 : $i, X1 : $i]:
% 30.11/30.28         ((r2_hidden @ (sk_D_2 @ X1 @ X0) @ X1)
% 30.11/30.28          | ((X1) = (k1_xboole_0))
% 30.11/30.28          | ~ (r1_tarski @ X1 @ (k3_relat_1 @ X0))
% 30.11/30.28          | ~ (v2_wellord1 @ X0)
% 30.11/30.28          | ~ (v1_relat_1 @ X0))),
% 30.11/30.28      inference('simplify', [status(thm)], ['51'])).
% 30.11/30.28  thf('53', plain,
% 30.11/30.28      (![X0 : $i, X1 : $i]:
% 30.11/30.28         (~ (v1_relat_1 @ X0)
% 30.11/30.28          | ~ (v1_relat_1 @ X0)
% 30.11/30.28          | ~ (v2_wellord1 @ X0)
% 30.11/30.28          | ((sk_C_4 @ X1 @ X0) = (k1_xboole_0))
% 30.11/30.28          | (r2_hidden @ (sk_D_2 @ (sk_C_4 @ X1 @ X0) @ X0) @ 
% 30.11/30.28             (sk_C_4 @ X1 @ X0)))),
% 30.11/30.28      inference('sup-', [status(thm)], ['48', '52'])).
% 30.11/30.28  thf('54', plain,
% 30.11/30.28      (![X0 : $i, X1 : $i]:
% 30.11/30.28         ((r2_hidden @ (sk_D_2 @ (sk_C_4 @ X1 @ X0) @ X0) @ (sk_C_4 @ X1 @ X0))
% 30.11/30.28          | ((sk_C_4 @ X1 @ X0) = (k1_xboole_0))
% 30.11/30.28          | ~ (v2_wellord1 @ X0)
% 30.11/30.28          | ~ (v1_relat_1 @ X0))),
% 30.11/30.28      inference('simplify', [status(thm)], ['53'])).
% 30.11/30.28  thf('55', plain,
% 30.11/30.28      ((((sk_A) = (sk_B_3)))
% 30.11/30.28         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)) & 
% 30.11/30.28             ((r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 30.11/30.28               (k1_wellord1 @ sk_C_5 @ sk_B_3))))),
% 30.11/30.28      inference('demod', [status(thm)], ['30', '31'])).
% 30.11/30.28  thf('56', plain,
% 30.11/30.28      (((r2_hidden @ sk_A @ (sk_C_4 @ sk_B_3 @ sk_C_5)))
% 30.11/30.28         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)))),
% 30.11/30.28      inference('sup-', [status(thm)], ['37', '38'])).
% 30.11/30.28  thf('57', plain,
% 30.11/30.28      (![X0 : $i, X1 : $i]:
% 30.11/30.28         ((r1_tarski @ (sk_C_4 @ X1 @ X0) @ (k3_relat_1 @ X0))
% 30.11/30.28          | ~ (v1_relat_1 @ X0))),
% 30.11/30.28      inference('simplify', [status(thm)], ['47'])).
% 30.11/30.28  thf('58', plain,
% 30.11/30.28      (![X33 : $i]:
% 30.11/30.28         (~ (v2_wellord1 @ X33)
% 30.11/30.28          | (r2_wellord1 @ X33 @ (k3_relat_1 @ X33))
% 30.11/30.28          | ~ (v1_relat_1 @ X33))),
% 30.11/30.28      inference('cnf', [status(esa)], [t8_wellord1])).
% 30.11/30.28  thf('59', plain,
% 30.11/30.28      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 30.11/30.28         (~ (r2_wellord1 @ X34 @ X35)
% 30.11/30.28          | ~ (r2_hidden @ X36 @ X37)
% 30.11/30.28          | (r2_hidden @ (k4_tarski @ (sk_D_2 @ X37 @ X34) @ X36) @ X34)
% 30.11/30.28          | ((X37) = (k1_xboole_0))
% 30.11/30.28          | ~ (r1_tarski @ X37 @ X35)
% 30.11/30.28          | ~ (v1_relat_1 @ X34))),
% 30.11/30.28      inference('cnf', [status(esa)], [t9_wellord1])).
% 30.11/30.28  thf('60', plain,
% 30.11/30.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.11/30.28         (~ (v1_relat_1 @ X0)
% 30.11/30.28          | ~ (v2_wellord1 @ X0)
% 30.11/30.28          | ~ (v1_relat_1 @ X0)
% 30.11/30.28          | ~ (r1_tarski @ X1 @ (k3_relat_1 @ X0))
% 30.11/30.28          | ((X1) = (k1_xboole_0))
% 30.11/30.28          | (r2_hidden @ (k4_tarski @ (sk_D_2 @ X1 @ X0) @ X2) @ X0)
% 30.11/30.28          | ~ (r2_hidden @ X2 @ X1))),
% 30.11/30.28      inference('sup-', [status(thm)], ['58', '59'])).
% 30.11/30.28  thf('61', plain,
% 30.11/30.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.11/30.28         (~ (r2_hidden @ X2 @ X1)
% 30.11/30.28          | (r2_hidden @ (k4_tarski @ (sk_D_2 @ X1 @ X0) @ X2) @ X0)
% 30.11/30.28          | ((X1) = (k1_xboole_0))
% 30.11/30.28          | ~ (r1_tarski @ X1 @ (k3_relat_1 @ X0))
% 30.11/30.28          | ~ (v2_wellord1 @ X0)
% 30.11/30.28          | ~ (v1_relat_1 @ X0))),
% 30.11/30.28      inference('simplify', [status(thm)], ['60'])).
% 30.11/30.28  thf('62', plain,
% 30.11/30.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.11/30.28         (~ (v1_relat_1 @ X0)
% 30.11/30.28          | ~ (v1_relat_1 @ X0)
% 30.11/30.28          | ~ (v2_wellord1 @ X0)
% 30.11/30.28          | ((sk_C_4 @ X1 @ X0) = (k1_xboole_0))
% 30.11/30.28          | (r2_hidden @ 
% 30.11/30.28             (k4_tarski @ (sk_D_2 @ (sk_C_4 @ X1 @ X0) @ X0) @ X2) @ X0)
% 30.11/30.28          | ~ (r2_hidden @ X2 @ (sk_C_4 @ X1 @ X0)))),
% 30.11/30.28      inference('sup-', [status(thm)], ['57', '61'])).
% 30.11/30.28  thf('63', plain,
% 30.11/30.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.11/30.28         (~ (r2_hidden @ X2 @ (sk_C_4 @ X1 @ X0))
% 30.11/30.28          | (r2_hidden @ 
% 30.11/30.28             (k4_tarski @ (sk_D_2 @ (sk_C_4 @ X1 @ X0) @ X0) @ X2) @ X0)
% 30.11/30.28          | ((sk_C_4 @ X1 @ X0) = (k1_xboole_0))
% 30.11/30.28          | ~ (v2_wellord1 @ X0)
% 30.11/30.28          | ~ (v1_relat_1 @ X0))),
% 30.11/30.28      inference('simplify', [status(thm)], ['62'])).
% 30.11/30.28  thf('64', plain,
% 30.11/30.28      (((~ (v1_relat_1 @ sk_C_5)
% 30.11/30.28         | ~ (v2_wellord1 @ sk_C_5)
% 30.11/30.28         | ((sk_C_4 @ sk_B_3 @ sk_C_5) = (k1_xboole_0))
% 30.11/30.28         | (r2_hidden @ 
% 30.11/30.28            (k4_tarski @ (sk_D_2 @ (sk_C_4 @ sk_B_3 @ sk_C_5) @ sk_C_5) @ sk_A) @ 
% 30.11/30.28            sk_C_5)))
% 30.11/30.28         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)))),
% 30.11/30.28      inference('sup-', [status(thm)], ['56', '63'])).
% 30.11/30.28  thf('65', plain, ((v1_relat_1 @ sk_C_5)),
% 30.11/30.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.11/30.28  thf('66', plain, ((v2_wellord1 @ sk_C_5)),
% 30.11/30.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.11/30.28  thf('67', plain,
% 30.11/30.28      (((((sk_C_4 @ sk_B_3 @ sk_C_5) = (k1_xboole_0))
% 30.11/30.28         | (r2_hidden @ 
% 30.11/30.28            (k4_tarski @ (sk_D_2 @ (sk_C_4 @ sk_B_3 @ sk_C_5) @ sk_C_5) @ sk_A) @ 
% 30.11/30.28            sk_C_5)))
% 30.11/30.28         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)))),
% 30.11/30.28      inference('demod', [status(thm)], ['64', '65', '66'])).
% 30.11/30.28  thf('68', plain,
% 30.11/30.28      (![X29 : $i, X31 : $i, X32 : $i]:
% 30.11/30.28         (~ (v1_relat_1 @ X29)
% 30.11/30.28          | ~ (r2_hidden @ (k4_tarski @ X32 @ X31) @ X29)
% 30.11/30.28          | ~ (r2_hidden @ X32 @ (sk_C_4 @ X31 @ X29)))),
% 30.11/30.28      inference('cnf', [status(esa)], [s1_xboole_0__e7_18__wellord1])).
% 30.11/30.28  thf('69', plain,
% 30.11/30.28      (((((sk_C_4 @ sk_B_3 @ sk_C_5) = (k1_xboole_0))
% 30.11/30.28         | ~ (r2_hidden @ (sk_D_2 @ (sk_C_4 @ sk_B_3 @ sk_C_5) @ sk_C_5) @ 
% 30.11/30.28              (sk_C_4 @ sk_A @ sk_C_5))
% 30.11/30.28         | ~ (v1_relat_1 @ sk_C_5)))
% 30.11/30.28         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)))),
% 30.11/30.28      inference('sup-', [status(thm)], ['67', '68'])).
% 30.11/30.28  thf('70', plain, ((v1_relat_1 @ sk_C_5)),
% 30.11/30.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.11/30.28  thf('71', plain,
% 30.11/30.28      (((((sk_C_4 @ sk_B_3 @ sk_C_5) = (k1_xboole_0))
% 30.11/30.28         | ~ (r2_hidden @ (sk_D_2 @ (sk_C_4 @ sk_B_3 @ sk_C_5) @ sk_C_5) @ 
% 30.11/30.28              (sk_C_4 @ sk_A @ sk_C_5))))
% 30.11/30.28         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)))),
% 30.11/30.28      inference('demod', [status(thm)], ['69', '70'])).
% 30.11/30.28  thf('72', plain,
% 30.11/30.28      (((~ (r2_hidden @ (sk_D_2 @ (sk_C_4 @ sk_A @ sk_C_5) @ sk_C_5) @ 
% 30.11/30.28            (sk_C_4 @ sk_A @ sk_C_5))
% 30.11/30.28         | ((sk_C_4 @ sk_B_3 @ sk_C_5) = (k1_xboole_0))))
% 30.11/30.28         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)) & 
% 30.11/30.28             ((r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 30.11/30.28               (k1_wellord1 @ sk_C_5 @ sk_B_3))))),
% 30.11/30.28      inference('sup-', [status(thm)], ['55', '71'])).
% 30.11/30.28  thf('73', plain,
% 30.11/30.28      ((((sk_A) = (sk_B_3)))
% 30.11/30.28         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)) & 
% 30.11/30.28             ((r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 30.11/30.28               (k1_wellord1 @ sk_C_5 @ sk_B_3))))),
% 30.11/30.28      inference('demod', [status(thm)], ['30', '31'])).
% 30.11/30.28  thf('74', plain,
% 30.11/30.28      (((~ (r2_hidden @ (sk_D_2 @ (sk_C_4 @ sk_A @ sk_C_5) @ sk_C_5) @ 
% 30.11/30.28            (sk_C_4 @ sk_A @ sk_C_5))
% 30.11/30.28         | ((sk_C_4 @ sk_A @ sk_C_5) = (k1_xboole_0))))
% 30.11/30.28         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)) & 
% 30.11/30.28             ((r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 30.11/30.28               (k1_wellord1 @ sk_C_5 @ sk_B_3))))),
% 30.11/30.28      inference('demod', [status(thm)], ['72', '73'])).
% 30.11/30.28  thf('75', plain,
% 30.11/30.28      (((~ (v1_relat_1 @ sk_C_5)
% 30.11/30.28         | ~ (v2_wellord1 @ sk_C_5)
% 30.11/30.28         | ((sk_C_4 @ sk_A @ sk_C_5) = (k1_xboole_0))
% 30.11/30.28         | ((sk_C_4 @ sk_A @ sk_C_5) = (k1_xboole_0))))
% 30.11/30.28         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)) & 
% 30.11/30.28             ((r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 30.11/30.28               (k1_wellord1 @ sk_C_5 @ sk_B_3))))),
% 30.11/30.28      inference('sup-', [status(thm)], ['54', '74'])).
% 30.11/30.28  thf('76', plain, ((v1_relat_1 @ sk_C_5)),
% 30.11/30.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.11/30.28  thf('77', plain, ((v2_wellord1 @ sk_C_5)),
% 30.11/30.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.11/30.28  thf('78', plain,
% 30.11/30.28      (((((sk_C_4 @ sk_A @ sk_C_5) = (k1_xboole_0))
% 30.11/30.28         | ((sk_C_4 @ sk_A @ sk_C_5) = (k1_xboole_0))))
% 30.11/30.28         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)) & 
% 30.11/30.28             ((r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 30.11/30.28               (k1_wellord1 @ sk_C_5 @ sk_B_3))))),
% 30.11/30.28      inference('demod', [status(thm)], ['75', '76', '77'])).
% 30.11/30.28  thf('79', plain,
% 30.11/30.28      ((((sk_C_4 @ sk_A @ sk_C_5) = (k1_xboole_0)))
% 30.11/30.28         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)) & 
% 30.11/30.28             ((r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 30.11/30.28               (k1_wellord1 @ sk_C_5 @ sk_B_3))))),
% 30.11/30.28      inference('simplify', [status(thm)], ['78'])).
% 30.11/30.28  thf('80', plain, ((v1_relat_1 @ sk_C_5)),
% 30.11/30.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.11/30.28  thf(d10_xboole_0, axiom,
% 30.11/30.28    (![A:$i,B:$i]:
% 30.11/30.28     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 30.11/30.28  thf('81', plain,
% 30.11/30.28      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 30.11/30.28      inference('cnf', [status(esa)], [d10_xboole_0])).
% 30.11/30.28  thf('82', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 30.11/30.28      inference('simplify', [status(thm)], ['81'])).
% 30.11/30.28  thf('83', plain,
% 30.11/30.28      (![X1 : $i, X3 : $i]:
% 30.11/30.28         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 30.11/30.28      inference('cnf', [status(esa)], [d3_tarski])).
% 30.11/30.28  thf('84', plain,
% 30.11/30.28      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 30.11/30.28         (((X15) != (k1_wellord1 @ X14 @ X13))
% 30.11/30.28          | (r2_hidden @ (k4_tarski @ X16 @ X13) @ X14)
% 30.11/30.28          | ~ (r2_hidden @ X16 @ X15)
% 30.11/30.28          | ~ (v1_relat_1 @ X14))),
% 30.11/30.28      inference('cnf', [status(esa)], [d1_wellord1])).
% 30.11/30.28  thf('85', plain,
% 30.11/30.28      (![X13 : $i, X14 : $i, X16 : $i]:
% 30.11/30.28         (~ (v1_relat_1 @ X14)
% 30.11/30.28          | ~ (r2_hidden @ X16 @ (k1_wellord1 @ X14 @ X13))
% 30.11/30.28          | (r2_hidden @ (k4_tarski @ X16 @ X13) @ X14))),
% 30.11/30.28      inference('simplify', [status(thm)], ['84'])).
% 30.11/30.28  thf('86', plain,
% 30.11/30.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.11/30.28         ((r1_tarski @ (k1_wellord1 @ X1 @ X0) @ X2)
% 30.11/30.28          | (r2_hidden @ 
% 30.11/30.28             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X1 @ X0)) @ X0) @ X1)
% 30.11/30.28          | ~ (v1_relat_1 @ X1))),
% 30.11/30.28      inference('sup-', [status(thm)], ['83', '85'])).
% 30.11/30.28  thf(t30_relat_1, axiom,
% 30.11/30.28    (![A:$i,B:$i,C:$i]:
% 30.11/30.28     ( ( v1_relat_1 @ C ) =>
% 30.11/30.28       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 30.11/30.28         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 30.11/30.28           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ))).
% 30.11/30.28  thf('87', plain,
% 30.11/30.28      (![X7 : $i, X8 : $i, X9 : $i]:
% 30.11/30.28         (~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ X9)
% 30.11/30.28          | (r2_hidden @ X8 @ (k3_relat_1 @ X9))
% 30.11/30.28          | ~ (v1_relat_1 @ X9))),
% 30.11/30.28      inference('cnf', [status(esa)], [t30_relat_1])).
% 30.11/30.28  thf('88', plain,
% 30.11/30.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.11/30.28         (~ (v1_relat_1 @ X0)
% 30.11/30.28          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 30.11/30.28          | ~ (v1_relat_1 @ X0)
% 30.11/30.28          | (r2_hidden @ X1 @ (k3_relat_1 @ X0)))),
% 30.11/30.28      inference('sup-', [status(thm)], ['86', '87'])).
% 30.11/30.28  thf('89', plain,
% 30.11/30.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.11/30.28         ((r2_hidden @ X1 @ (k3_relat_1 @ X0))
% 30.11/30.28          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 30.11/30.28          | ~ (v1_relat_1 @ X0))),
% 30.11/30.28      inference('simplify', [status(thm)], ['88'])).
% 30.11/30.28  thf('90', plain,
% 30.11/30.28      (![X10 : $i, X11 : $i]:
% 30.11/30.28         (~ (r2_hidden @ X10 @ X11) | ~ (r1_tarski @ X11 @ X10))),
% 30.11/30.28      inference('cnf', [status(esa)], [t7_ordinal1])).
% 30.11/30.28  thf('91', plain,
% 30.11/30.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.11/30.28         (~ (v1_relat_1 @ X0)
% 30.11/30.28          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 30.11/30.28          | ~ (r1_tarski @ (k3_relat_1 @ X0) @ X1))),
% 30.11/30.28      inference('sup-', [status(thm)], ['89', '90'])).
% 30.11/30.28  thf('92', plain,
% 30.11/30.28      (![X0 : $i, X1 : $i]:
% 30.11/30.28         ((r1_tarski @ (k1_wellord1 @ X0 @ (k3_relat_1 @ X0)) @ X1)
% 30.11/30.28          | ~ (v1_relat_1 @ X0))),
% 30.11/30.28      inference('sup-', [status(thm)], ['82', '91'])).
% 30.11/30.28  thf('93', plain,
% 30.11/30.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.11/30.28         ((r1_tarski @ (k1_wellord1 @ X1 @ X0) @ X2)
% 30.11/30.28          | (r2_hidden @ 
% 30.11/30.28             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X1 @ X0)) @ X0) @ X1)
% 30.11/30.28          | ~ (v1_relat_1 @ X1))),
% 30.11/30.28      inference('sup-', [status(thm)], ['83', '85'])).
% 30.11/30.28  thf('94', plain,
% 30.11/30.28      (![X7 : $i, X8 : $i, X9 : $i]:
% 30.11/30.28         (~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ X9)
% 30.11/30.28          | (r2_hidden @ X7 @ (k3_relat_1 @ X9))
% 30.11/30.28          | ~ (v1_relat_1 @ X9))),
% 30.11/30.28      inference('cnf', [status(esa)], [t30_relat_1])).
% 30.11/30.28  thf('95', plain,
% 30.11/30.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.11/30.28         (~ (v1_relat_1 @ X0)
% 30.11/30.28          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 30.11/30.28          | ~ (v1_relat_1 @ X0)
% 30.11/30.28          | (r2_hidden @ (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1)) @ 
% 30.11/30.28             (k3_relat_1 @ X0)))),
% 30.11/30.28      inference('sup-', [status(thm)], ['93', '94'])).
% 30.11/30.28  thf('96', plain,
% 30.11/30.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.11/30.28         ((r2_hidden @ (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1)) @ 
% 30.11/30.28           (k3_relat_1 @ X0))
% 30.11/30.28          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 30.11/30.28          | ~ (v1_relat_1 @ X0))),
% 30.11/30.28      inference('simplify', [status(thm)], ['95'])).
% 30.11/30.28  thf('97', plain,
% 30.11/30.28      (![X1 : $i, X3 : $i]:
% 30.11/30.28         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 30.11/30.28      inference('cnf', [status(esa)], [d3_tarski])).
% 30.11/30.28  thf('98', plain,
% 30.11/30.28      (![X0 : $i, X1 : $i]:
% 30.11/30.28         (~ (v1_relat_1 @ X0)
% 30.11/30.28          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ (k3_relat_1 @ X0))
% 30.11/30.28          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ (k3_relat_1 @ X0)))),
% 30.11/30.28      inference('sup-', [status(thm)], ['96', '97'])).
% 30.11/30.28  thf('99', plain,
% 30.11/30.28      (![X0 : $i, X1 : $i]:
% 30.11/30.28         ((r1_tarski @ (k1_wellord1 @ X0 @ X1) @ (k3_relat_1 @ X0))
% 30.11/30.28          | ~ (v1_relat_1 @ X0))),
% 30.11/30.28      inference('simplify', [status(thm)], ['98'])).
% 30.11/30.28  thf('100', plain,
% 30.11/30.28      (![X0 : $i, X1 : $i]:
% 30.11/30.28         ((r2_hidden @ (sk_D_2 @ X1 @ X0) @ X1)
% 30.11/30.28          | ((X1) = (k1_xboole_0))
% 30.11/30.28          | ~ (r1_tarski @ X1 @ (k3_relat_1 @ X0))
% 30.11/30.28          | ~ (v2_wellord1 @ X0)
% 30.11/30.28          | ~ (v1_relat_1 @ X0))),
% 30.11/30.28      inference('simplify', [status(thm)], ['51'])).
% 30.11/30.28  thf('101', plain,
% 30.11/30.28      (![X0 : $i, X1 : $i]:
% 30.11/30.28         (~ (v1_relat_1 @ X0)
% 30.11/30.28          | ~ (v1_relat_1 @ X0)
% 30.11/30.28          | ~ (v2_wellord1 @ X0)
% 30.11/30.28          | ((k1_wellord1 @ X0 @ X1) = (k1_xboole_0))
% 30.11/30.28          | (r2_hidden @ (sk_D_2 @ (k1_wellord1 @ X0 @ X1) @ X0) @ 
% 30.11/30.28             (k1_wellord1 @ X0 @ X1)))),
% 30.11/30.28      inference('sup-', [status(thm)], ['99', '100'])).
% 30.11/30.28  thf('102', plain,
% 30.11/30.28      (![X0 : $i, X1 : $i]:
% 30.11/30.28         ((r2_hidden @ (sk_D_2 @ (k1_wellord1 @ X0 @ X1) @ X0) @ 
% 30.11/30.28           (k1_wellord1 @ X0 @ X1))
% 30.11/30.29          | ((k1_wellord1 @ X0 @ X1) = (k1_xboole_0))
% 30.11/30.29          | ~ (v2_wellord1 @ X0)
% 30.11/30.29          | ~ (v1_relat_1 @ X0))),
% 30.11/30.29      inference('simplify', [status(thm)], ['101'])).
% 30.11/30.29  thf('103', plain,
% 30.11/30.29      (![X10 : $i, X11 : $i]:
% 30.11/30.29         (~ (r2_hidden @ X10 @ X11) | ~ (r1_tarski @ X11 @ X10))),
% 30.11/30.29      inference('cnf', [status(esa)], [t7_ordinal1])).
% 30.11/30.29  thf('104', plain,
% 30.11/30.29      (![X0 : $i, X1 : $i]:
% 30.11/30.29         (~ (v1_relat_1 @ X1)
% 30.11/30.29          | ~ (v2_wellord1 @ X1)
% 30.11/30.29          | ((k1_wellord1 @ X1 @ X0) = (k1_xboole_0))
% 30.11/30.29          | ~ (r1_tarski @ (k1_wellord1 @ X1 @ X0) @ 
% 30.11/30.29               (sk_D_2 @ (k1_wellord1 @ X1 @ X0) @ X1)))),
% 30.11/30.29      inference('sup-', [status(thm)], ['102', '103'])).
% 30.11/30.29  thf('105', plain,
% 30.11/30.29      (![X0 : $i]:
% 30.11/30.29         (~ (v1_relat_1 @ X0)
% 30.11/30.29          | ((k1_wellord1 @ X0 @ (k3_relat_1 @ X0)) = (k1_xboole_0))
% 30.11/30.29          | ~ (v2_wellord1 @ X0)
% 30.11/30.29          | ~ (v1_relat_1 @ X0))),
% 30.11/30.29      inference('sup-', [status(thm)], ['92', '104'])).
% 30.11/30.29  thf('106', plain,
% 30.11/30.29      (![X0 : $i]:
% 30.11/30.29         (~ (v2_wellord1 @ X0)
% 30.11/30.29          | ((k1_wellord1 @ X0 @ (k3_relat_1 @ X0)) = (k1_xboole_0))
% 30.11/30.29          | ~ (v1_relat_1 @ X0))),
% 30.11/30.29      inference('simplify', [status(thm)], ['105'])).
% 30.11/30.29  thf('107', plain,
% 30.11/30.29      (![X0 : $i, X1 : $i]:
% 30.11/30.29         ((r1_tarski @ (k1_wellord1 @ X0 @ (k3_relat_1 @ X0)) @ X1)
% 30.11/30.29          | ~ (v1_relat_1 @ X0))),
% 30.11/30.29      inference('sup-', [status(thm)], ['82', '91'])).
% 30.11/30.29  thf('108', plain,
% 30.11/30.29      (![X0 : $i, X1 : $i]:
% 30.11/30.29         ((r1_tarski @ k1_xboole_0 @ X0)
% 30.11/30.29          | ~ (v1_relat_1 @ X1)
% 30.11/30.29          | ~ (v2_wellord1 @ X1)
% 30.11/30.29          | ~ (v1_relat_1 @ X1))),
% 30.11/30.29      inference('sup+', [status(thm)], ['106', '107'])).
% 30.11/30.29  thf('109', plain,
% 30.11/30.29      (![X0 : $i, X1 : $i]:
% 30.11/30.29         (~ (v2_wellord1 @ X1)
% 30.11/30.29          | ~ (v1_relat_1 @ X1)
% 30.11/30.29          | (r1_tarski @ k1_xboole_0 @ X0))),
% 30.11/30.29      inference('simplify', [status(thm)], ['108'])).
% 30.11/30.29  thf('110', plain,
% 30.11/30.29      (![X0 : $i]: ((r1_tarski @ k1_xboole_0 @ X0) | ~ (v2_wellord1 @ sk_C_5))),
% 30.11/30.29      inference('sup-', [status(thm)], ['80', '109'])).
% 30.11/30.29  thf('111', plain, ((v2_wellord1 @ sk_C_5)),
% 30.11/30.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.11/30.29  thf('112', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 30.11/30.29      inference('demod', [status(thm)], ['110', '111'])).
% 30.11/30.29  thf('113', plain,
% 30.11/30.29      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)) | 
% 30.11/30.29       ~
% 30.11/30.29       ((r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 30.11/30.29         (k1_wellord1 @ sk_C_5 @ sk_B_3)))),
% 30.11/30.29      inference('demod', [status(thm)], ['42', '79', '112'])).
% 30.11/30.29  thf('114', plain,
% 30.11/30.29      (~
% 30.11/30.29       ((r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 30.11/30.29         (k1_wellord1 @ sk_C_5 @ sk_B_3)))),
% 30.11/30.29      inference('sat_resolution*', [status(thm)], ['2', '113'])).
% 30.11/30.29  thf('115', plain,
% 30.11/30.29      (~ (r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 30.11/30.29          (k1_wellord1 @ sk_C_5 @ sk_B_3))),
% 30.11/30.29      inference('simpl_trail', [status(thm)], ['1', '114'])).
% 30.11/30.29  thf('116', plain,
% 30.11/30.29      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5))
% 30.11/30.29         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)))),
% 30.11/30.29      inference('split', [status(esa)], ['23'])).
% 30.11/30.29  thf('117', plain,
% 30.11/30.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.11/30.29         ((r1_tarski @ (k1_wellord1 @ X1 @ X0) @ X2)
% 30.11/30.29          | (r2_hidden @ 
% 30.11/30.29             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X1 @ X0)) @ X0) @ X1)
% 30.11/30.29          | ~ (v1_relat_1 @ X1))),
% 30.11/30.29      inference('sup-', [status(thm)], ['83', '85'])).
% 30.11/30.29  thf(l2_wellord1, axiom,
% 30.11/30.29    (![A:$i]:
% 30.11/30.29     ( ( v1_relat_1 @ A ) =>
% 30.11/30.29       ( ( v8_relat_2 @ A ) <=>
% 30.11/30.29         ( ![B:$i,C:$i,D:$i]:
% 30.11/30.29           ( ( ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) & 
% 30.11/30.29               ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) =>
% 30.11/30.29             ( r2_hidden @ ( k4_tarski @ B @ D ) @ A ) ) ) ) ))).
% 30.11/30.29  thf('118', plain,
% 30.11/30.29      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 30.11/30.29         (~ (v8_relat_2 @ X19)
% 30.11/30.29          | ~ (r2_hidden @ (k4_tarski @ X20 @ X21) @ X19)
% 30.11/30.29          | ~ (r2_hidden @ (k4_tarski @ X21 @ X22) @ X19)
% 30.11/30.29          | (r2_hidden @ (k4_tarski @ X20 @ X22) @ X19)
% 30.11/30.29          | ~ (v1_relat_1 @ X19))),
% 30.11/30.29      inference('cnf', [status(esa)], [l2_wellord1])).
% 30.11/30.29  thf('119', plain,
% 30.11/30.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 30.11/30.29         (~ (v1_relat_1 @ X0)
% 30.11/30.29          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 30.11/30.29          | ~ (v1_relat_1 @ X0)
% 30.11/30.29          | (r2_hidden @ 
% 30.11/30.29             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1)) @ X3) @ X0)
% 30.11/30.29          | ~ (r2_hidden @ (k4_tarski @ X1 @ X3) @ X0)
% 30.11/30.29          | ~ (v8_relat_2 @ X0))),
% 30.11/30.29      inference('sup-', [status(thm)], ['117', '118'])).
% 30.11/30.29  thf('120', plain,
% 30.11/30.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 30.11/30.29         (~ (v8_relat_2 @ X0)
% 30.11/30.29          | ~ (r2_hidden @ (k4_tarski @ X1 @ X3) @ X0)
% 30.11/30.29          | (r2_hidden @ 
% 30.11/30.29             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1)) @ X3) @ X0)
% 30.11/30.29          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 30.11/30.29          | ~ (v1_relat_1 @ X0))),
% 30.11/30.29      inference('simplify', [status(thm)], ['119'])).
% 30.11/30.29  thf('121', plain,
% 30.11/30.29      ((![X0 : $i]:
% 30.11/30.29          (~ (v1_relat_1 @ sk_C_5)
% 30.11/30.29           | (r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ X0)
% 30.11/30.29           | (r2_hidden @ 
% 30.11/30.29              (k4_tarski @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_5 @ sk_A)) @ sk_B_3) @ 
% 30.11/30.29              sk_C_5)
% 30.11/30.29           | ~ (v8_relat_2 @ sk_C_5)))
% 30.11/30.29         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)))),
% 30.11/30.29      inference('sup-', [status(thm)], ['116', '120'])).
% 30.11/30.29  thf('122', plain, ((v1_relat_1 @ sk_C_5)),
% 30.11/30.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.11/30.29  thf('123', plain, ((v1_relat_1 @ sk_C_5)),
% 30.11/30.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.11/30.29  thf('124', plain,
% 30.11/30.29      (![X18 : $i]:
% 30.11/30.29         (~ (v2_wellord1 @ X18) | (v8_relat_2 @ X18) | ~ (v1_relat_1 @ X18))),
% 30.11/30.29      inference('cnf', [status(esa)], [d4_wellord1])).
% 30.11/30.29  thf('125', plain, (((v8_relat_2 @ sk_C_5) | ~ (v2_wellord1 @ sk_C_5))),
% 30.11/30.29      inference('sup-', [status(thm)], ['123', '124'])).
% 30.11/30.29  thf('126', plain, ((v2_wellord1 @ sk_C_5)),
% 30.11/30.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.11/30.29  thf('127', plain, ((v8_relat_2 @ sk_C_5)),
% 30.11/30.29      inference('demod', [status(thm)], ['125', '126'])).
% 30.11/30.29  thf('128', plain,
% 30.11/30.29      ((![X0 : $i]:
% 30.11/30.29          ((r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ X0)
% 30.11/30.29           | (r2_hidden @ 
% 30.11/30.29              (k4_tarski @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_5 @ sk_A)) @ sk_B_3) @ 
% 30.11/30.29              sk_C_5)))
% 30.11/30.29         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)))),
% 30.11/30.29      inference('demod', [status(thm)], ['121', '122', '127'])).
% 30.11/30.29  thf('129', plain,
% 30.11/30.29      (![X13 : $i, X14 : $i, X17 : $i]:
% 30.11/30.29         (~ (v1_relat_1 @ X14)
% 30.11/30.29          | ((X17) = (X13))
% 30.11/30.29          | ~ (r2_hidden @ (k4_tarski @ X17 @ X13) @ X14)
% 30.11/30.29          | (r2_hidden @ X17 @ (k1_wellord1 @ X14 @ X13)))),
% 30.11/30.29      inference('simplify', [status(thm)], ['15'])).
% 30.11/30.29  thf('130', plain,
% 30.11/30.29      ((![X0 : $i]:
% 30.11/30.29          ((r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ X0)
% 30.11/30.29           | (r2_hidden @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_5 @ sk_A)) @ 
% 30.11/30.29              (k1_wellord1 @ sk_C_5 @ sk_B_3))
% 30.11/30.29           | ((sk_C @ X0 @ (k1_wellord1 @ sk_C_5 @ sk_A)) = (sk_B_3))
% 30.11/30.29           | ~ (v1_relat_1 @ sk_C_5)))
% 30.11/30.29         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)))),
% 30.11/30.29      inference('sup-', [status(thm)], ['128', '129'])).
% 30.11/30.29  thf('131', plain, ((v1_relat_1 @ sk_C_5)),
% 30.11/30.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.11/30.29  thf('132', plain,
% 30.11/30.29      ((![X0 : $i]:
% 30.11/30.29          ((r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ X0)
% 30.11/30.29           | (r2_hidden @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_5 @ sk_A)) @ 
% 30.11/30.29              (k1_wellord1 @ sk_C_5 @ sk_B_3))
% 30.11/30.29           | ((sk_C @ X0 @ (k1_wellord1 @ sk_C_5 @ sk_A)) = (sk_B_3))))
% 30.11/30.29         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)))),
% 30.11/30.29      inference('demod', [status(thm)], ['130', '131'])).
% 30.11/30.29  thf('133', plain,
% 30.11/30.29      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)) | 
% 30.11/30.29       ((r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 30.11/30.29         (k1_wellord1 @ sk_C_5 @ sk_B_3)))),
% 30.11/30.29      inference('split', [status(esa)], ['23'])).
% 30.11/30.29  thf('134', plain, (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5))),
% 30.11/30.29      inference('sat_resolution*', [status(thm)], ['2', '113', '133'])).
% 30.11/30.29  thf('135', plain,
% 30.11/30.29      (![X0 : $i]:
% 30.11/30.29         ((r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ X0)
% 30.11/30.29          | (r2_hidden @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_5 @ sk_A)) @ 
% 30.11/30.29             (k1_wellord1 @ sk_C_5 @ sk_B_3))
% 30.11/30.29          | ((sk_C @ X0 @ (k1_wellord1 @ sk_C_5 @ sk_A)) = (sk_B_3)))),
% 30.11/30.29      inference('simpl_trail', [status(thm)], ['132', '134'])).
% 30.11/30.29  thf('136', plain,
% 30.11/30.29      (![X1 : $i, X3 : $i]:
% 30.11/30.29         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 30.11/30.29      inference('cnf', [status(esa)], [d3_tarski])).
% 30.11/30.29  thf('137', plain,
% 30.11/30.29      ((((sk_C @ (k1_wellord1 @ sk_C_5 @ sk_B_3) @ 
% 30.11/30.29          (k1_wellord1 @ sk_C_5 @ sk_A)) = (sk_B_3))
% 30.11/30.29        | (r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 30.11/30.29           (k1_wellord1 @ sk_C_5 @ sk_B_3))
% 30.11/30.29        | (r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 30.11/30.29           (k1_wellord1 @ sk_C_5 @ sk_B_3)))),
% 30.11/30.29      inference('sup-', [status(thm)], ['135', '136'])).
% 30.11/30.29  thf('138', plain,
% 30.11/30.29      (((r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 30.11/30.29         (k1_wellord1 @ sk_C_5 @ sk_B_3))
% 30.11/30.29        | ((sk_C @ (k1_wellord1 @ sk_C_5 @ sk_B_3) @ 
% 30.11/30.29            (k1_wellord1 @ sk_C_5 @ sk_A)) = (sk_B_3)))),
% 30.11/30.29      inference('simplify', [status(thm)], ['137'])).
% 30.11/30.29  thf('139', plain,
% 30.11/30.29      (~ (r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 30.11/30.29          (k1_wellord1 @ sk_C_5 @ sk_B_3))),
% 30.11/30.29      inference('simpl_trail', [status(thm)], ['1', '114'])).
% 30.11/30.29  thf('140', plain,
% 30.11/30.29      (((sk_C @ (k1_wellord1 @ sk_C_5 @ sk_B_3) @ (k1_wellord1 @ sk_C_5 @ sk_A))
% 30.11/30.29         = (sk_B_3))),
% 30.11/30.29      inference('clc', [status(thm)], ['138', '139'])).
% 30.11/30.29  thf('141', plain,
% 30.11/30.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.11/30.29         ((r1_tarski @ (k1_wellord1 @ X1 @ X0) @ X2)
% 30.11/30.29          | (r2_hidden @ 
% 30.11/30.29             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X1 @ X0)) @ X0) @ X1)
% 30.11/30.29          | ~ (v1_relat_1 @ X1))),
% 30.11/30.29      inference('sup-', [status(thm)], ['83', '85'])).
% 30.11/30.29  thf(l3_wellord1, axiom,
% 30.11/30.29    (![A:$i]:
% 30.11/30.29     ( ( v1_relat_1 @ A ) =>
% 30.11/30.29       ( ( v4_relat_2 @ A ) <=>
% 30.11/30.29         ( ![B:$i,C:$i]:
% 30.11/30.29           ( ( ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) & 
% 30.11/30.29               ( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) ) =>
% 30.11/30.29             ( ( B ) = ( C ) ) ) ) ) ))).
% 30.11/30.29  thf('142', plain,
% 30.11/30.29      (![X23 : $i, X24 : $i, X25 : $i]:
% 30.11/30.29         (~ (v4_relat_2 @ X23)
% 30.11/30.29          | ((X25) = (X24))
% 30.11/30.29          | ~ (r2_hidden @ (k4_tarski @ X24 @ X25) @ X23)
% 30.11/30.29          | ~ (r2_hidden @ (k4_tarski @ X25 @ X24) @ X23)
% 30.11/30.29          | ~ (v1_relat_1 @ X23))),
% 30.11/30.29      inference('cnf', [status(esa)], [l3_wellord1])).
% 30.11/30.29  thf('143', plain,
% 30.11/30.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.11/30.29         (~ (v1_relat_1 @ X0)
% 30.11/30.29          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 30.11/30.29          | ~ (v1_relat_1 @ X0)
% 30.11/30.29          | ~ (r2_hidden @ 
% 30.11/30.29               (k4_tarski @ X1 @ (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1))) @ X0)
% 30.11/30.29          | ((X1) = (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1)))
% 30.11/30.29          | ~ (v4_relat_2 @ X0))),
% 30.11/30.29      inference('sup-', [status(thm)], ['141', '142'])).
% 30.11/30.29  thf('144', plain,
% 30.11/30.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.11/30.29         (~ (v4_relat_2 @ X0)
% 30.11/30.29          | ((X1) = (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1)))
% 30.11/30.29          | ~ (r2_hidden @ 
% 30.11/30.29               (k4_tarski @ X1 @ (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1))) @ X0)
% 30.11/30.29          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 30.11/30.29          | ~ (v1_relat_1 @ X0))),
% 30.11/30.29      inference('simplify', [status(thm)], ['143'])).
% 30.11/30.29  thf('145', plain,
% 30.11/30.29      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)
% 30.11/30.29        | ~ (v1_relat_1 @ sk_C_5)
% 30.11/30.29        | (r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 30.11/30.29           (k1_wellord1 @ sk_C_5 @ sk_B_3))
% 30.11/30.29        | ((sk_A)
% 30.11/30.29            = (sk_C @ (k1_wellord1 @ sk_C_5 @ sk_B_3) @ 
% 30.11/30.29               (k1_wellord1 @ sk_C_5 @ sk_A)))
% 30.11/30.29        | ~ (v4_relat_2 @ sk_C_5))),
% 30.11/30.29      inference('sup-', [status(thm)], ['140', '144'])).
% 30.11/30.29  thf('146', plain,
% 30.11/30.29      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5))
% 30.11/30.29         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)))),
% 30.11/30.29      inference('split', [status(esa)], ['23'])).
% 30.11/30.29  thf('147', plain, (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5))),
% 30.11/30.29      inference('sat_resolution*', [status(thm)], ['2', '113', '133'])).
% 30.11/30.29  thf('148', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)),
% 30.11/30.29      inference('simpl_trail', [status(thm)], ['146', '147'])).
% 30.11/30.29  thf('149', plain, ((v1_relat_1 @ sk_C_5)),
% 30.11/30.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.11/30.29  thf('150', plain,
% 30.11/30.29      (((sk_C @ (k1_wellord1 @ sk_C_5 @ sk_B_3) @ (k1_wellord1 @ sk_C_5 @ sk_A))
% 30.11/30.29         = (sk_B_3))),
% 30.11/30.29      inference('clc', [status(thm)], ['138', '139'])).
% 30.11/30.29  thf('151', plain, ((v1_relat_1 @ sk_C_5)),
% 30.11/30.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.11/30.29  thf('152', plain,
% 30.11/30.29      (![X18 : $i]:
% 30.11/30.29         (~ (v2_wellord1 @ X18) | (v4_relat_2 @ X18) | ~ (v1_relat_1 @ X18))),
% 30.11/30.29      inference('cnf', [status(esa)], [d4_wellord1])).
% 30.11/30.29  thf('153', plain, (((v4_relat_2 @ sk_C_5) | ~ (v2_wellord1 @ sk_C_5))),
% 30.11/30.29      inference('sup-', [status(thm)], ['151', '152'])).
% 30.11/30.29  thf('154', plain, ((v2_wellord1 @ sk_C_5)),
% 30.11/30.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.11/30.29  thf('155', plain, ((v4_relat_2 @ sk_C_5)),
% 30.11/30.29      inference('demod', [status(thm)], ['153', '154'])).
% 30.11/30.29  thf('156', plain,
% 30.11/30.29      (((r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 30.11/30.29         (k1_wellord1 @ sk_C_5 @ sk_B_3))
% 30.11/30.29        | ((sk_A) = (sk_B_3)))),
% 30.11/30.29      inference('demod', [status(thm)], ['145', '148', '149', '150', '155'])).
% 30.11/30.29  thf('157', plain,
% 30.11/30.29      (~ (r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 30.11/30.29          (k1_wellord1 @ sk_C_5 @ sk_B_3))),
% 30.11/30.29      inference('simpl_trail', [status(thm)], ['1', '114'])).
% 30.11/30.29  thf('158', plain, (((sk_A) = (sk_B_3))),
% 30.11/30.29      inference('clc', [status(thm)], ['156', '157'])).
% 30.11/30.29  thf('159', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 30.11/30.29      inference('simplify', [status(thm)], ['81'])).
% 30.11/30.29  thf('160', plain, ($false),
% 30.11/30.29      inference('demod', [status(thm)], ['115', '158', '159'])).
% 30.11/30.29  
% 30.11/30.29  % SZS output end Refutation
% 30.11/30.29  
% 30.11/30.29  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
