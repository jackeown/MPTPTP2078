%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tVLZcA857Y

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:32 EST 2020

% Result     : Theorem 1.91s
% Output     : Refutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :  188 (2414 expanded)
%              Number of leaves         :   33 ( 647 expanded)
%              Depth                    :   28
%              Number of atoms          : 1995 (36146 expanded)
%              Number of equality atoms :   68 ( 817 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(sk_C_6_type,type,(
    sk_C_6: $i )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_wellord1_type,type,(
    v1_wellord1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_4_type,type,(
    sk_C_4: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v6_relat_2_type,type,(
    v6_relat_2: $i > $o )).

thf(sk_C_5_type,type,(
    sk_C_5: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ( ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) )
   <= ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
    r2_hidden @ sk_B_3 @ ( k3_relat_1 @ sk_C_6 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_6 ) ),
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
      ( ~ ( v1_relat_1 @ sk_C_6 )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_C_6 ) )
      | ( sk_A = X0 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_6 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ sk_A ) @ sk_C_6 )
      | ~ ( v6_relat_2 @ sk_C_6 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_relat_1 @ sk_C_6 ),
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
    ( ( v6_relat_2 @ sk_C_6 )
    | ~ ( v2_wellord1 @ sk_C_6 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_wellord1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v6_relat_2 @ sk_C_6 ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_C_6 ) )
      | ( sk_A = X0 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_6 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ sk_A ) @ sk_C_6 ) ) ),
    inference(demod,[status(thm)],['6','7','12'])).

thf('14',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B_3 @ sk_A ) @ sk_C_6 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
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
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
    | ( r2_hidden @ sk_B_3 @ ( k1_wellord1 @ sk_C_6 @ sk_A ) )
    | ( sk_B_3 = sk_A )
    | ~ ( v1_relat_1 @ sk_C_6 ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( sk_A = sk_B_3 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
    | ( r2_hidden @ sk_B_3 @ ( k1_wellord1 @ sk_C_6 @ sk_A ) )
    | ( sk_B_3 = sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r2_hidden @ sk_B_3 @ ( k1_wellord1 @ sk_C_6 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
    | ( sk_A = sk_B_3 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ( ( sk_A = sk_B_3 )
      | ( r2_hidden @ sk_B_3 @ ( k1_wellord1 @ sk_C_6 @ sk_A ) ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) )
   <= ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ),
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
        ( ( r2_hidden @ X0 @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) )
        | ~ ( r2_hidden @ X0 @ ( k1_wellord1 @ sk_C_6 @ sk_A ) ) )
   <= ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( sk_A = sk_B_3 )
      | ( r2_hidden @ sk_B_3 @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ) ),
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
      | ~ ( v1_relat_1 @ sk_C_6 ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_A = sk_B_3 )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_6 ) ),
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
      ( ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_6 )
      | ( r2_hidden @ sk_A @ ( sk_C_4 @ X0 @ sk_C_6 ) )
      | ~ ( v1_relat_1 @ sk_C_6 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_6 )
      | ( r2_hidden @ sk_A @ ( sk_C_4 @ X0 @ sk_C_6 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,
    ( ( r2_hidden @ sk_A @ ( sk_C_4 @ sk_B_3 @ sk_C_6 ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ) ),
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
    ( ~ ( r1_tarski @ ( sk_C_4 @ sk_B_3 @ sk_C_6 ) @ sk_A )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( r1_tarski @ ( sk_C_4 @ sk_A @ sk_C_6 ) @ sk_A )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ) ),
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

thf(t10_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
       => ! [B: $i] :
            ~ ( ( r1_tarski @ B @ ( k3_relat_1 @ A ) )
              & ( B != k1_xboole_0 )
              & ! [C: $i] :
                  ~ ( ( r2_hidden @ C @ B )
                    & ! [D: $i] :
                        ( ( r2_hidden @ D @ B )
                       => ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ) ) )).

thf('49',plain,(
    ! [X33: $i,X35: $i] :
      ( ~ ( v2_wellord1 @ X33 )
      | ( r2_hidden @ ( sk_C_5 @ X35 @ X33 ) @ X35 )
      | ( X35 = k1_xboole_0 )
      | ~ ( r1_tarski @ X35 @ ( k3_relat_1 @ X33 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( sk_C_4 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_5 @ ( sk_C_4 @ X1 @ X0 ) @ X0 ) @ ( sk_C_4 @ X1 @ X0 ) )
      | ~ ( v2_wellord1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_wellord1 @ X0 )
      | ( r2_hidden @ ( sk_C_5 @ ( sk_C_4 @ X1 @ X0 ) @ X0 ) @ ( sk_C_4 @ X1 @ X0 ) )
      | ( ( sk_C_4 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( sk_A = sk_B_3 )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('53',plain,
    ( ( r2_hidden @ sk_A @ ( sk_C_4 @ sk_B_3 @ sk_C_6 ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( sk_C_4 @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('55',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v2_wellord1 @ X33 )
      | ~ ( r2_hidden @ X34 @ X35 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_5 @ X35 @ X33 ) @ X34 ) @ X33 )
      | ( X35 = k1_xboole_0 )
      | ~ ( r1_tarski @ X35 @ ( k3_relat_1 @ X33 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( sk_C_4 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_5 @ ( sk_C_4 @ X1 @ X0 ) @ X0 ) @ X2 ) @ X0 )
      | ~ ( r2_hidden @ X2 @ ( sk_C_4 @ X1 @ X0 ) )
      | ~ ( v2_wellord1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v2_wellord1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( sk_C_4 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_5 @ ( sk_C_4 @ X1 @ X0 ) @ X0 ) @ X2 ) @ X0 )
      | ( ( sk_C_4 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_6 )
      | ( ( sk_C_4 @ sk_B_3 @ sk_C_6 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_5 @ ( sk_C_4 @ sk_B_3 @ sk_C_6 ) @ sk_C_6 ) @ sk_A ) @ sk_C_6 )
      | ~ ( v2_wellord1 @ sk_C_6 ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ) ),
    inference('sup-',[status(thm)],['53','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v2_wellord1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( ( ( sk_C_4 @ sk_B_3 @ sk_C_6 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_5 @ ( sk_C_4 @ sk_B_3 @ sk_C_6 ) @ sk_C_6 ) @ sk_A ) @ sk_C_6 ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ! [X29: $i,X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ~ ( r2_hidden @ ( k4_tarski @ X32 @ X31 ) @ X29 )
      | ~ ( r2_hidden @ X32 @ ( sk_C_4 @ X31 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[s1_xboole_0__e7_18__wellord1])).

thf('63',plain,
    ( ( ( ( sk_C_4 @ sk_B_3 @ sk_C_6 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_C_5 @ ( sk_C_4 @ sk_B_3 @ sk_C_6 ) @ sk_C_6 ) @ ( sk_C_4 @ sk_A @ sk_C_6 ) )
      | ~ ( v1_relat_1 @ sk_C_6 ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( ( ( sk_C_4 @ sk_B_3 @ sk_C_6 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_C_5 @ ( sk_C_4 @ sk_B_3 @ sk_C_6 ) @ sk_C_6 ) @ ( sk_C_4 @ sk_A @ sk_C_6 ) ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ~ ( r2_hidden @ ( sk_C_5 @ ( sk_C_4 @ sk_A @ sk_C_6 ) @ sk_C_6 ) @ ( sk_C_4 @ sk_A @ sk_C_6 ) )
      | ( ( sk_C_4 @ sk_B_3 @ sk_C_6 )
        = k1_xboole_0 ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ) ),
    inference('sup-',[status(thm)],['52','65'])).

thf('67',plain,
    ( ( sk_A = sk_B_3 )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('68',plain,
    ( ( ~ ( r2_hidden @ ( sk_C_5 @ ( sk_C_4 @ sk_A @ sk_C_6 ) @ sk_C_6 ) @ ( sk_C_4 @ sk_A @ sk_C_6 ) )
      | ( ( sk_C_4 @ sk_A @ sk_C_6 )
        = k1_xboole_0 ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_6 )
      | ( ( sk_C_4 @ sk_A @ sk_C_6 )
        = k1_xboole_0 )
      | ~ ( v2_wellord1 @ sk_C_6 )
      | ( ( sk_C_4 @ sk_A @ sk_C_6 )
        = k1_xboole_0 ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ) ),
    inference('sup-',[status(thm)],['51','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v2_wellord1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( ( ( sk_C_4 @ sk_A @ sk_C_6 )
        = k1_xboole_0 )
      | ( ( sk_C_4 @ sk_A @ sk_C_6 )
        = k1_xboole_0 ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,
    ( ( ( sk_C_4 @ sk_A @ sk_C_6 )
      = k1_xboole_0 )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    v1_relat_1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_relat_1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('76',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('77',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('79',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X15
       != ( k1_wellord1 @ X14 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ X16 @ X13 ) @ X14 )
      | ~ ( r2_hidden @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('80',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k1_wellord1 @ X14 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ X16 @ X13 ) @ X14 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_wellord1 @ X1 @ X0 ) ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['78','80'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('82',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X9 )
      | ( r2_hidden @ X8 @ ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('86',plain,(
    ! [X33: $i,X35: $i] :
      ( ~ ( v2_wellord1 @ X33 )
      | ( r2_hidden @ ( sk_C_5 @ X35 @ X33 ) @ X35 )
      | ( X35 = k1_xboole_0 )
      | ~ ( r1_tarski @ X35 @ ( k3_relat_1 @ X33 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord1])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ X1 @ ( k2_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_wellord1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_5 @ ( k1_wellord1 @ X2 @ X1 ) @ X0 ) @ ( k1_wellord1 @ X2 @ X1 ) )
      | ~ ( v2_wellord1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v2_wellord1 @ X2 )
      | ( ( k1_wellord1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ X0 @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ ( k1_wellord1 @ X1 @ X0 ) @ ( sk_C_5 @ ( k1_wellord1 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ X1 @ ( k2_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ X1 @ ( k2_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_wellord1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ~ ( v2_wellord1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v2_wellord1 @ X0 )
      | ( ( k1_wellord1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k2_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k1_wellord1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v2_wellord1 @ X2 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_wellord1 @ X1 )
      | ( ( k1_wellord1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_wellord1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v2_wellord1 @ sk_C_6 ) ) ),
    inference('sup-',[status(thm)],['75','94'])).

thf('96',plain,(
    v2_wellord1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_wellord1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('100',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X0 @ ( k2_relat_1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['97','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['74','104'])).

thf('106',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
    | ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['42','73','105'])).

thf('107',plain,(
    ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','106'])).

thf('108',plain,(
    ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ),
    inference(simpl_trail,[status(thm)],['1','107'])).

thf('109',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ) ),
    inference(split,[status(esa)],['23'])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_wellord1 @ X1 @ X0 ) ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['78','80'])).

thf(l2_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v8_relat_2 @ A )
      <=> ! [B: $i,C: $i,D: $i] :
            ( ( ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
              & ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) )
           => ( r2_hidden @ ( k4_tarski @ B @ D ) @ A ) ) ) ) )).

thf('111',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( v8_relat_2 @ X19 )
      | ~ ( r2_hidden @ ( k4_tarski @ X20 @ X21 ) @ X19 )
      | ~ ( r2_hidden @ ( k4_tarski @ X21 @ X22 ) @ X19 )
      | ( r2_hidden @ ( k4_tarski @ X20 @ X22 ) @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l2_wellord1])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) @ X3 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X3 ) @ X0 )
      | ~ ( v8_relat_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v8_relat_2 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X3 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) @ X3 ) @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_C_6 )
        | ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ X0 )
        | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_6 @ sk_A ) ) @ sk_B_3 ) @ sk_C_6 )
        | ~ ( v8_relat_2 @ sk_C_6 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ) ),
    inference('sup-',[status(thm)],['109','113'])).

thf('115',plain,(
    v1_relat_1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_relat_1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X18: $i] :
      ( ~ ( v2_wellord1 @ X18 )
      | ( v8_relat_2 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('118',plain,
    ( ( v8_relat_2 @ sk_C_6 )
    | ~ ( v2_wellord1 @ sk_C_6 ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    v2_wellord1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v8_relat_2 @ sk_C_6 ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ X0 )
        | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_6 @ sk_A ) ) @ sk_B_3 ) @ sk_C_6 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ) ),
    inference(demod,[status(thm)],['114','115','120'])).

thf('122',plain,(
    ! [X13: $i,X14: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( X17 = X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X13 ) @ X14 )
      | ( r2_hidden @ X17 @ ( k1_wellord1 @ X14 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('123',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_6 @ sk_A ) ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) )
        | ( ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_6 @ sk_A ) )
          = sk_B_3 )
        | ~ ( v1_relat_1 @ sk_C_6 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v1_relat_1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_6 @ sk_A ) ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) )
        | ( ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_6 @ sk_A ) )
          = sk_B_3 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ),
    inference(split,[status(esa)],['23'])).

thf('127',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ),
    inference('sat_resolution*',[status(thm)],['2','106','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_6 @ sk_A ) ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) )
      | ( ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_6 @ sk_A ) )
        = sk_B_3 ) ) ),
    inference(simpl_trail,[status(thm)],['125','127'])).

thf('129',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('130',plain,
    ( ( ( sk_C @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) @ ( k1_wellord1 @ sk_C_6 @ sk_A ) )
      = sk_B_3 )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) )
    | ( ( sk_C @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) @ ( k1_wellord1 @ sk_C_6 @ sk_A ) )
      = sk_B_3 ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ),
    inference(simpl_trail,[status(thm)],['1','107'])).

thf('133',plain,
    ( ( sk_C @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) @ ( k1_wellord1 @ sk_C_6 @ sk_A ) )
    = sk_B_3 ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_wellord1 @ X1 @ X0 ) ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['78','80'])).

thf(l3_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v4_relat_2 @ A )
      <=> ! [B: $i,C: $i] :
            ( ( ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
              & ( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) )
           => ( B = C ) ) ) ) )).

thf('135',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v4_relat_2 @ X23 )
      | ( X25 = X24 )
      | ~ ( r2_hidden @ ( k4_tarski @ X24 @ X25 ) @ X23 )
      | ~ ( r2_hidden @ ( k4_tarski @ X25 @ X24 ) @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l3_wellord1])).

thf('136',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) ) @ X0 )
      | ( X1
        = ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) )
      | ~ ( v4_relat_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v4_relat_2 @ X0 )
      | ( X1
        = ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) ) @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
    | ~ ( v1_relat_1 @ sk_C_6 )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) )
    | ( sk_A
      = ( sk_C @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) @ ( k1_wellord1 @ sk_C_6 @ sk_A ) ) )
    | ~ ( v4_relat_2 @ sk_C_6 ) ),
    inference('sup-',[status(thm)],['133','137'])).

thf('139',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ) ),
    inference(split,[status(esa)],['23'])).

thf('140',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ),
    inference('sat_resolution*',[status(thm)],['2','106','126'])).

thf('141',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ),
    inference(simpl_trail,[status(thm)],['139','140'])).

thf('142',plain,(
    v1_relat_1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( sk_C @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) @ ( k1_wellord1 @ sk_C_6 @ sk_A ) )
    = sk_B_3 ),
    inference(clc,[status(thm)],['131','132'])).

thf('144',plain,(
    v1_relat_1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    ! [X18: $i] :
      ( ~ ( v2_wellord1 @ X18 )
      | ( v4_relat_2 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('146',plain,
    ( ( v4_relat_2 @ sk_C_6 )
    | ~ ( v2_wellord1 @ sk_C_6 ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    v2_wellord1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v4_relat_2 @ sk_C_6 ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) )
    | ( sk_A = sk_B_3 ) ),
    inference(demod,[status(thm)],['138','141','142','143','148'])).

thf('150',plain,(
    ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ),
    inference(simpl_trail,[status(thm)],['1','107'])).

thf('151',plain,(
    sk_A = sk_B_3 ),
    inference(clc,[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('153',plain,(
    $false ),
    inference(demod,[status(thm)],['108','151','152'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tVLZcA857Y
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:56:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.91/2.09  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.91/2.09  % Solved by: fo/fo7.sh
% 1.91/2.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.91/2.09  % done 2385 iterations in 1.634s
% 1.91/2.09  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.91/2.09  % SZS output start Refutation
% 1.91/2.09  thf(sk_B_3_type, type, sk_B_3: $i).
% 1.91/2.09  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 1.91/2.09  thf(sk_C_6_type, type, sk_C_6: $i).
% 1.91/2.09  thf(v1_relat_2_type, type, v1_relat_2: $i > $o).
% 1.91/2.09  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 1.91/2.09  thf(v8_relat_2_type, type, v8_relat_2: $i > $o).
% 1.91/2.09  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.91/2.09  thf(sk_A_type, type, sk_A: $i).
% 1.91/2.09  thf(v1_wellord1_type, type, v1_wellord1: $i > $o).
% 1.91/2.09  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.91/2.09  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.91/2.09  thf(sk_C_4_type, type, sk_C_4: $i > $i > $i).
% 1.91/2.09  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 1.91/2.09  thf(v4_relat_2_type, type, v4_relat_2: $i > $o).
% 1.91/2.09  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.91/2.09  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.91/2.09  thf(v6_relat_2_type, type, v6_relat_2: $i > $o).
% 1.91/2.09  thf(sk_C_5_type, type, sk_C_5: $i > $i > $i).
% 1.91/2.09  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.91/2.09  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.91/2.09  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.91/2.09  thf(t37_wellord1, conjecture,
% 1.91/2.09    (![A:$i,B:$i,C:$i]:
% 1.91/2.09     ( ( v1_relat_1 @ C ) =>
% 1.91/2.09       ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 1.91/2.09           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) =>
% 1.91/2.09         ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 1.91/2.09           ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) ))).
% 1.91/2.09  thf(zf_stmt_0, negated_conjecture,
% 1.91/2.09    (~( ![A:$i,B:$i,C:$i]:
% 1.91/2.09        ( ( v1_relat_1 @ C ) =>
% 1.91/2.09          ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 1.91/2.09              ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) =>
% 1.91/2.09            ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 1.91/2.09              ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) ) )),
% 1.91/2.09    inference('cnf.neg', [status(esa)], [t37_wellord1])).
% 1.91/2.09  thf('0', plain,
% 1.91/2.09      ((~ (r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 1.91/2.09           (k1_wellord1 @ sk_C_6 @ sk_B_3))
% 1.91/2.09        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6))),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf('1', plain,
% 1.91/2.09      ((~ (r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 1.91/2.09           (k1_wellord1 @ sk_C_6 @ sk_B_3)))
% 1.91/2.09         <= (~
% 1.91/2.09             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 1.91/2.09               (k1_wellord1 @ sk_C_6 @ sk_B_3))))),
% 1.91/2.09      inference('split', [status(esa)], ['0'])).
% 1.91/2.09  thf('2', plain,
% 1.91/2.09      (~
% 1.91/2.09       ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 1.91/2.09         (k1_wellord1 @ sk_C_6 @ sk_B_3))) | 
% 1.91/2.09       ~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6))),
% 1.91/2.09      inference('split', [status(esa)], ['0'])).
% 1.91/2.09  thf('3', plain, ((r2_hidden @ sk_B_3 @ (k3_relat_1 @ sk_C_6))),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf('4', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_6))),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf(l4_wellord1, axiom,
% 1.91/2.09    (![A:$i]:
% 1.91/2.09     ( ( v1_relat_1 @ A ) =>
% 1.91/2.09       ( ( v6_relat_2 @ A ) <=>
% 1.91/2.09         ( ![B:$i,C:$i]:
% 1.91/2.09           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 1.91/2.09                ( r2_hidden @ C @ ( k3_relat_1 @ A ) ) & ( ( B ) != ( C ) ) & 
% 1.91/2.09                ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) & 
% 1.91/2.09                ( ~( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) ) ) ) ) ) ))).
% 1.91/2.09  thf('5', plain,
% 1.91/2.09      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.91/2.09         (~ (v6_relat_2 @ X26)
% 1.91/2.09          | ~ (r2_hidden @ X27 @ (k3_relat_1 @ X26))
% 1.91/2.09          | (r2_hidden @ (k4_tarski @ X28 @ X27) @ X26)
% 1.91/2.09          | (r2_hidden @ (k4_tarski @ X27 @ X28) @ X26)
% 1.91/2.09          | ((X27) = (X28))
% 1.91/2.09          | ~ (r2_hidden @ X28 @ (k3_relat_1 @ X26))
% 1.91/2.09          | ~ (v1_relat_1 @ X26))),
% 1.91/2.09      inference('cnf', [status(esa)], [l4_wellord1])).
% 1.91/2.09  thf('6', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         (~ (v1_relat_1 @ sk_C_6)
% 1.91/2.09          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C_6))
% 1.91/2.09          | ((sk_A) = (X0))
% 1.91/2.09          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_6)
% 1.91/2.09          | (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ sk_C_6)
% 1.91/2.09          | ~ (v6_relat_2 @ sk_C_6))),
% 1.91/2.09      inference('sup-', [status(thm)], ['4', '5'])).
% 1.91/2.09  thf('7', plain, ((v1_relat_1 @ sk_C_6)),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf('8', plain, ((v1_relat_1 @ sk_C_6)),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf(d4_wellord1, axiom,
% 1.91/2.09    (![A:$i]:
% 1.91/2.09     ( ( v1_relat_1 @ A ) =>
% 1.91/2.09       ( ( v2_wellord1 @ A ) <=>
% 1.91/2.09         ( ( v1_relat_2 @ A ) & ( v8_relat_2 @ A ) & ( v4_relat_2 @ A ) & 
% 1.91/2.09           ( v6_relat_2 @ A ) & ( v1_wellord1 @ A ) ) ) ))).
% 1.91/2.09  thf('9', plain,
% 1.91/2.09      (![X18 : $i]:
% 1.91/2.09         (~ (v2_wellord1 @ X18) | (v6_relat_2 @ X18) | ~ (v1_relat_1 @ X18))),
% 1.91/2.09      inference('cnf', [status(esa)], [d4_wellord1])).
% 1.91/2.09  thf('10', plain, (((v6_relat_2 @ sk_C_6) | ~ (v2_wellord1 @ sk_C_6))),
% 1.91/2.09      inference('sup-', [status(thm)], ['8', '9'])).
% 1.91/2.09  thf('11', plain, ((v2_wellord1 @ sk_C_6)),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf('12', plain, ((v6_relat_2 @ sk_C_6)),
% 1.91/2.09      inference('demod', [status(thm)], ['10', '11'])).
% 1.91/2.09  thf('13', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         (~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C_6))
% 1.91/2.09          | ((sk_A) = (X0))
% 1.91/2.09          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_6)
% 1.91/2.09          | (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ sk_C_6))),
% 1.91/2.09      inference('demod', [status(thm)], ['6', '7', '12'])).
% 1.91/2.09  thf('14', plain,
% 1.91/2.09      (((r2_hidden @ (k4_tarski @ sk_B_3 @ sk_A) @ sk_C_6)
% 1.91/2.09        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)
% 1.91/2.09        | ((sk_A) = (sk_B_3)))),
% 1.91/2.09      inference('sup-', [status(thm)], ['3', '13'])).
% 1.91/2.09  thf(d1_wellord1, axiom,
% 1.91/2.09    (![A:$i]:
% 1.91/2.09     ( ( v1_relat_1 @ A ) =>
% 1.91/2.09       ( ![B:$i,C:$i]:
% 1.91/2.09         ( ( ( C ) = ( k1_wellord1 @ A @ B ) ) <=>
% 1.91/2.09           ( ![D:$i]:
% 1.91/2.09             ( ( r2_hidden @ D @ C ) <=>
% 1.91/2.09               ( ( ( D ) != ( B ) ) & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) ) ))).
% 1.91/2.09  thf('15', plain,
% 1.91/2.09      (![X13 : $i, X14 : $i, X15 : $i, X17 : $i]:
% 1.91/2.09         (((X15) != (k1_wellord1 @ X14 @ X13))
% 1.91/2.09          | (r2_hidden @ X17 @ X15)
% 1.91/2.09          | ~ (r2_hidden @ (k4_tarski @ X17 @ X13) @ X14)
% 1.91/2.09          | ((X17) = (X13))
% 1.91/2.09          | ~ (v1_relat_1 @ X14))),
% 1.91/2.09      inference('cnf', [status(esa)], [d1_wellord1])).
% 1.91/2.09  thf('16', plain,
% 1.91/2.09      (![X13 : $i, X14 : $i, X17 : $i]:
% 1.91/2.09         (~ (v1_relat_1 @ X14)
% 1.91/2.09          | ((X17) = (X13))
% 1.91/2.09          | ~ (r2_hidden @ (k4_tarski @ X17 @ X13) @ X14)
% 1.91/2.09          | (r2_hidden @ X17 @ (k1_wellord1 @ X14 @ X13)))),
% 1.91/2.09      inference('simplify', [status(thm)], ['15'])).
% 1.91/2.09  thf('17', plain,
% 1.91/2.09      ((((sk_A) = (sk_B_3))
% 1.91/2.09        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)
% 1.91/2.09        | (r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_6 @ sk_A))
% 1.91/2.09        | ((sk_B_3) = (sk_A))
% 1.91/2.09        | ~ (v1_relat_1 @ sk_C_6))),
% 1.91/2.09      inference('sup-', [status(thm)], ['14', '16'])).
% 1.91/2.09  thf('18', plain, ((v1_relat_1 @ sk_C_6)),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf('19', plain,
% 1.91/2.09      ((((sk_A) = (sk_B_3))
% 1.91/2.09        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)
% 1.91/2.09        | (r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_6 @ sk_A))
% 1.91/2.09        | ((sk_B_3) = (sk_A)))),
% 1.91/2.09      inference('demod', [status(thm)], ['17', '18'])).
% 1.91/2.09  thf('20', plain,
% 1.91/2.09      (((r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_6 @ sk_A))
% 1.91/2.09        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)
% 1.91/2.09        | ((sk_A) = (sk_B_3)))),
% 1.91/2.09      inference('simplify', [status(thm)], ['19'])).
% 1.91/2.09  thf('21', plain,
% 1.91/2.09      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6))
% 1.91/2.09         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)))),
% 1.91/2.09      inference('split', [status(esa)], ['0'])).
% 1.91/2.09  thf('22', plain,
% 1.91/2.09      (((((sk_A) = (sk_B_3))
% 1.91/2.09         | (r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_6 @ sk_A))))
% 1.91/2.09         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)))),
% 1.91/2.09      inference('sup-', [status(thm)], ['20', '21'])).
% 1.91/2.09  thf('23', plain,
% 1.91/2.09      (((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 1.91/2.09         (k1_wellord1 @ sk_C_6 @ sk_B_3))
% 1.91/2.09        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6))),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf('24', plain,
% 1.91/2.09      (((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 1.91/2.09         (k1_wellord1 @ sk_C_6 @ sk_B_3)))
% 1.91/2.09         <= (((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 1.91/2.09               (k1_wellord1 @ sk_C_6 @ sk_B_3))))),
% 1.91/2.09      inference('split', [status(esa)], ['23'])).
% 1.91/2.09  thf(d3_tarski, axiom,
% 1.91/2.09    (![A:$i,B:$i]:
% 1.91/2.09     ( ( r1_tarski @ A @ B ) <=>
% 1.91/2.09       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.91/2.09  thf('25', plain,
% 1.91/2.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.09         (~ (r2_hidden @ X0 @ X1)
% 1.91/2.09          | (r2_hidden @ X0 @ X2)
% 1.91/2.09          | ~ (r1_tarski @ X1 @ X2))),
% 1.91/2.09      inference('cnf', [status(esa)], [d3_tarski])).
% 1.91/2.09  thf('26', plain,
% 1.91/2.09      ((![X0 : $i]:
% 1.91/2.09          ((r2_hidden @ X0 @ (k1_wellord1 @ sk_C_6 @ sk_B_3))
% 1.91/2.09           | ~ (r2_hidden @ X0 @ (k1_wellord1 @ sk_C_6 @ sk_A))))
% 1.91/2.09         <= (((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 1.91/2.09               (k1_wellord1 @ sk_C_6 @ sk_B_3))))),
% 1.91/2.09      inference('sup-', [status(thm)], ['24', '25'])).
% 1.91/2.09  thf('27', plain,
% 1.91/2.09      (((((sk_A) = (sk_B_3))
% 1.91/2.09         | (r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_6 @ sk_B_3))))
% 1.91/2.09         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)) & 
% 1.91/2.09             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 1.91/2.09               (k1_wellord1 @ sk_C_6 @ sk_B_3))))),
% 1.91/2.09      inference('sup-', [status(thm)], ['22', '26'])).
% 1.91/2.09  thf('28', plain,
% 1.91/2.09      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 1.91/2.09         (((X15) != (k1_wellord1 @ X14 @ X13))
% 1.91/2.09          | ((X16) != (X13))
% 1.91/2.09          | ~ (r2_hidden @ X16 @ X15)
% 1.91/2.09          | ~ (v1_relat_1 @ X14))),
% 1.91/2.09      inference('cnf', [status(esa)], [d1_wellord1])).
% 1.91/2.09  thf('29', plain,
% 1.91/2.09      (![X13 : $i, X14 : $i]:
% 1.91/2.09         (~ (v1_relat_1 @ X14)
% 1.91/2.09          | ~ (r2_hidden @ X13 @ (k1_wellord1 @ X14 @ X13)))),
% 1.91/2.09      inference('simplify', [status(thm)], ['28'])).
% 1.91/2.09  thf('30', plain,
% 1.91/2.09      (((((sk_A) = (sk_B_3)) | ~ (v1_relat_1 @ sk_C_6)))
% 1.91/2.09         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)) & 
% 1.91/2.09             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 1.91/2.09               (k1_wellord1 @ sk_C_6 @ sk_B_3))))),
% 1.91/2.09      inference('sup-', [status(thm)], ['27', '29'])).
% 1.91/2.09  thf('31', plain, ((v1_relat_1 @ sk_C_6)),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf('32', plain,
% 1.91/2.09      ((((sk_A) = (sk_B_3)))
% 1.91/2.09         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)) & 
% 1.91/2.09             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 1.91/2.09               (k1_wellord1 @ sk_C_6 @ sk_B_3))))),
% 1.91/2.09      inference('demod', [status(thm)], ['30', '31'])).
% 1.91/2.09  thf('33', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_6))),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf(s1_xboole_0__e7_18__wellord1, axiom,
% 1.91/2.09    (![A:$i,B:$i]:
% 1.91/2.09     ( ( v1_relat_1 @ A ) =>
% 1.91/2.09       ( ?[C:$i]:
% 1.91/2.09         ( ![D:$i]:
% 1.91/2.09           ( ( r2_hidden @ D @ C ) <=>
% 1.91/2.09             ( ( r2_hidden @ D @ ( k3_relat_1 @ A ) ) & 
% 1.91/2.09               ( ~( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) ) ))).
% 1.91/2.09  thf('34', plain,
% 1.91/2.09      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.91/2.09         (~ (v1_relat_1 @ X29)
% 1.91/2.09          | (r2_hidden @ X30 @ (sk_C_4 @ X31 @ X29))
% 1.91/2.09          | (r2_hidden @ (k4_tarski @ X30 @ X31) @ X29)
% 1.91/2.09          | ~ (r2_hidden @ X30 @ (k3_relat_1 @ X29)))),
% 1.91/2.09      inference('cnf', [status(esa)], [s1_xboole_0__e7_18__wellord1])).
% 1.91/2.09  thf('35', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         ((r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_6)
% 1.91/2.09          | (r2_hidden @ sk_A @ (sk_C_4 @ X0 @ sk_C_6))
% 1.91/2.09          | ~ (v1_relat_1 @ sk_C_6))),
% 1.91/2.09      inference('sup-', [status(thm)], ['33', '34'])).
% 1.91/2.09  thf('36', plain, ((v1_relat_1 @ sk_C_6)),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf('37', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         ((r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_6)
% 1.91/2.09          | (r2_hidden @ sk_A @ (sk_C_4 @ X0 @ sk_C_6)))),
% 1.91/2.09      inference('demod', [status(thm)], ['35', '36'])).
% 1.91/2.09  thf('38', plain,
% 1.91/2.09      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6))
% 1.91/2.09         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)))),
% 1.91/2.09      inference('split', [status(esa)], ['0'])).
% 1.91/2.09  thf('39', plain,
% 1.91/2.09      (((r2_hidden @ sk_A @ (sk_C_4 @ sk_B_3 @ sk_C_6)))
% 1.91/2.09         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)))),
% 1.91/2.09      inference('sup-', [status(thm)], ['37', '38'])).
% 1.91/2.09  thf(t7_ordinal1, axiom,
% 1.91/2.09    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.91/2.09  thf('40', plain,
% 1.91/2.09      (![X10 : $i, X11 : $i]:
% 1.91/2.09         (~ (r2_hidden @ X10 @ X11) | ~ (r1_tarski @ X11 @ X10))),
% 1.91/2.09      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.91/2.09  thf('41', plain,
% 1.91/2.09      ((~ (r1_tarski @ (sk_C_4 @ sk_B_3 @ sk_C_6) @ sk_A))
% 1.91/2.09         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)))),
% 1.91/2.09      inference('sup-', [status(thm)], ['39', '40'])).
% 1.91/2.09  thf('42', plain,
% 1.91/2.09      ((~ (r1_tarski @ (sk_C_4 @ sk_A @ sk_C_6) @ sk_A))
% 1.91/2.09         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)) & 
% 1.91/2.09             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 1.91/2.09               (k1_wellord1 @ sk_C_6 @ sk_B_3))))),
% 1.91/2.09      inference('sup-', [status(thm)], ['32', '41'])).
% 1.91/2.09  thf('43', plain,
% 1.91/2.09      (![X1 : $i, X3 : $i]:
% 1.91/2.09         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.91/2.09      inference('cnf', [status(esa)], [d3_tarski])).
% 1.91/2.09  thf('44', plain,
% 1.91/2.09      (![X29 : $i, X31 : $i, X32 : $i]:
% 1.91/2.09         (~ (v1_relat_1 @ X29)
% 1.91/2.09          | (r2_hidden @ X32 @ (k3_relat_1 @ X29))
% 1.91/2.09          | ~ (r2_hidden @ X32 @ (sk_C_4 @ X31 @ X29)))),
% 1.91/2.09      inference('cnf', [status(esa)], [s1_xboole_0__e7_18__wellord1])).
% 1.91/2.09  thf('45', plain,
% 1.91/2.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.09         ((r1_tarski @ (sk_C_4 @ X1 @ X0) @ X2)
% 1.91/2.09          | (r2_hidden @ (sk_C @ X2 @ (sk_C_4 @ X1 @ X0)) @ (k3_relat_1 @ X0))
% 1.91/2.09          | ~ (v1_relat_1 @ X0))),
% 1.91/2.09      inference('sup-', [status(thm)], ['43', '44'])).
% 1.91/2.09  thf('46', plain,
% 1.91/2.09      (![X1 : $i, X3 : $i]:
% 1.91/2.09         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.91/2.09      inference('cnf', [status(esa)], [d3_tarski])).
% 1.91/2.09  thf('47', plain,
% 1.91/2.09      (![X0 : $i, X1 : $i]:
% 1.91/2.09         (~ (v1_relat_1 @ X0)
% 1.91/2.09          | (r1_tarski @ (sk_C_4 @ X1 @ X0) @ (k3_relat_1 @ X0))
% 1.91/2.09          | (r1_tarski @ (sk_C_4 @ X1 @ X0) @ (k3_relat_1 @ X0)))),
% 1.91/2.09      inference('sup-', [status(thm)], ['45', '46'])).
% 1.91/2.09  thf('48', plain,
% 1.91/2.09      (![X0 : $i, X1 : $i]:
% 1.91/2.09         ((r1_tarski @ (sk_C_4 @ X1 @ X0) @ (k3_relat_1 @ X0))
% 1.91/2.09          | ~ (v1_relat_1 @ X0))),
% 1.91/2.09      inference('simplify', [status(thm)], ['47'])).
% 1.91/2.09  thf(t10_wellord1, axiom,
% 1.91/2.09    (![A:$i]:
% 1.91/2.09     ( ( v1_relat_1 @ A ) =>
% 1.91/2.09       ( ( v2_wellord1 @ A ) =>
% 1.91/2.09         ( ![B:$i]:
% 1.91/2.09           ( ~( ( r1_tarski @ B @ ( k3_relat_1 @ A ) ) & 
% 1.91/2.09                ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.91/2.09                ( ![C:$i]:
% 1.91/2.09                  ( ~( ( r2_hidden @ C @ B ) & 
% 1.91/2.09                       ( ![D:$i]:
% 1.91/2.09                         ( ( r2_hidden @ D @ B ) =>
% 1.91/2.09                           ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ) ) ) ) ) ) ))).
% 1.91/2.09  thf('49', plain,
% 1.91/2.09      (![X33 : $i, X35 : $i]:
% 1.91/2.09         (~ (v2_wellord1 @ X33)
% 1.91/2.09          | (r2_hidden @ (sk_C_5 @ X35 @ X33) @ X35)
% 1.91/2.09          | ((X35) = (k1_xboole_0))
% 1.91/2.09          | ~ (r1_tarski @ X35 @ (k3_relat_1 @ X33))
% 1.91/2.09          | ~ (v1_relat_1 @ X33))),
% 1.91/2.09      inference('cnf', [status(esa)], [t10_wellord1])).
% 1.91/2.09  thf('50', plain,
% 1.91/2.09      (![X0 : $i, X1 : $i]:
% 1.91/2.09         (~ (v1_relat_1 @ X0)
% 1.91/2.09          | ~ (v1_relat_1 @ X0)
% 1.91/2.09          | ((sk_C_4 @ X1 @ X0) = (k1_xboole_0))
% 1.91/2.09          | (r2_hidden @ (sk_C_5 @ (sk_C_4 @ X1 @ X0) @ X0) @ 
% 1.91/2.09             (sk_C_4 @ X1 @ X0))
% 1.91/2.09          | ~ (v2_wellord1 @ X0))),
% 1.91/2.09      inference('sup-', [status(thm)], ['48', '49'])).
% 1.91/2.09  thf('51', plain,
% 1.91/2.09      (![X0 : $i, X1 : $i]:
% 1.91/2.09         (~ (v2_wellord1 @ X0)
% 1.91/2.09          | (r2_hidden @ (sk_C_5 @ (sk_C_4 @ X1 @ X0) @ X0) @ 
% 1.91/2.09             (sk_C_4 @ X1 @ X0))
% 1.91/2.09          | ((sk_C_4 @ X1 @ X0) = (k1_xboole_0))
% 1.91/2.09          | ~ (v1_relat_1 @ X0))),
% 1.91/2.09      inference('simplify', [status(thm)], ['50'])).
% 1.91/2.09  thf('52', plain,
% 1.91/2.09      ((((sk_A) = (sk_B_3)))
% 1.91/2.09         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)) & 
% 1.91/2.09             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 1.91/2.09               (k1_wellord1 @ sk_C_6 @ sk_B_3))))),
% 1.91/2.09      inference('demod', [status(thm)], ['30', '31'])).
% 1.91/2.09  thf('53', plain,
% 1.91/2.09      (((r2_hidden @ sk_A @ (sk_C_4 @ sk_B_3 @ sk_C_6)))
% 1.91/2.09         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)))),
% 1.91/2.09      inference('sup-', [status(thm)], ['37', '38'])).
% 1.91/2.09  thf('54', plain,
% 1.91/2.09      (![X0 : $i, X1 : $i]:
% 1.91/2.09         ((r1_tarski @ (sk_C_4 @ X1 @ X0) @ (k3_relat_1 @ X0))
% 1.91/2.09          | ~ (v1_relat_1 @ X0))),
% 1.91/2.09      inference('simplify', [status(thm)], ['47'])).
% 1.91/2.09  thf('55', plain,
% 1.91/2.09      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.91/2.09         (~ (v2_wellord1 @ X33)
% 1.91/2.09          | ~ (r2_hidden @ X34 @ X35)
% 1.91/2.09          | (r2_hidden @ (k4_tarski @ (sk_C_5 @ X35 @ X33) @ X34) @ X33)
% 1.91/2.09          | ((X35) = (k1_xboole_0))
% 1.91/2.09          | ~ (r1_tarski @ X35 @ (k3_relat_1 @ X33))
% 1.91/2.09          | ~ (v1_relat_1 @ X33))),
% 1.91/2.09      inference('cnf', [status(esa)], [t10_wellord1])).
% 1.91/2.09  thf('56', plain,
% 1.91/2.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.09         (~ (v1_relat_1 @ X0)
% 1.91/2.09          | ~ (v1_relat_1 @ X0)
% 1.91/2.09          | ((sk_C_4 @ X1 @ X0) = (k1_xboole_0))
% 1.91/2.09          | (r2_hidden @ 
% 1.91/2.09             (k4_tarski @ (sk_C_5 @ (sk_C_4 @ X1 @ X0) @ X0) @ X2) @ X0)
% 1.91/2.09          | ~ (r2_hidden @ X2 @ (sk_C_4 @ X1 @ X0))
% 1.91/2.09          | ~ (v2_wellord1 @ X0))),
% 1.91/2.09      inference('sup-', [status(thm)], ['54', '55'])).
% 1.91/2.09  thf('57', plain,
% 1.91/2.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.09         (~ (v2_wellord1 @ X0)
% 1.91/2.09          | ~ (r2_hidden @ X2 @ (sk_C_4 @ X1 @ X0))
% 1.91/2.09          | (r2_hidden @ 
% 1.91/2.09             (k4_tarski @ (sk_C_5 @ (sk_C_4 @ X1 @ X0) @ X0) @ X2) @ X0)
% 1.91/2.09          | ((sk_C_4 @ X1 @ X0) = (k1_xboole_0))
% 1.91/2.09          | ~ (v1_relat_1 @ X0))),
% 1.91/2.09      inference('simplify', [status(thm)], ['56'])).
% 1.91/2.09  thf('58', plain,
% 1.91/2.09      (((~ (v1_relat_1 @ sk_C_6)
% 1.91/2.09         | ((sk_C_4 @ sk_B_3 @ sk_C_6) = (k1_xboole_0))
% 1.91/2.09         | (r2_hidden @ 
% 1.91/2.09            (k4_tarski @ (sk_C_5 @ (sk_C_4 @ sk_B_3 @ sk_C_6) @ sk_C_6) @ sk_A) @ 
% 1.91/2.09            sk_C_6)
% 1.91/2.09         | ~ (v2_wellord1 @ sk_C_6)))
% 1.91/2.09         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)))),
% 1.91/2.09      inference('sup-', [status(thm)], ['53', '57'])).
% 1.91/2.09  thf('59', plain, ((v1_relat_1 @ sk_C_6)),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf('60', plain, ((v2_wellord1 @ sk_C_6)),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf('61', plain,
% 1.91/2.09      (((((sk_C_4 @ sk_B_3 @ sk_C_6) = (k1_xboole_0))
% 1.91/2.09         | (r2_hidden @ 
% 1.91/2.09            (k4_tarski @ (sk_C_5 @ (sk_C_4 @ sk_B_3 @ sk_C_6) @ sk_C_6) @ sk_A) @ 
% 1.91/2.09            sk_C_6)))
% 1.91/2.09         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)))),
% 1.91/2.09      inference('demod', [status(thm)], ['58', '59', '60'])).
% 1.91/2.09  thf('62', plain,
% 1.91/2.09      (![X29 : $i, X31 : $i, X32 : $i]:
% 1.91/2.09         (~ (v1_relat_1 @ X29)
% 1.91/2.09          | ~ (r2_hidden @ (k4_tarski @ X32 @ X31) @ X29)
% 1.91/2.09          | ~ (r2_hidden @ X32 @ (sk_C_4 @ X31 @ X29)))),
% 1.91/2.09      inference('cnf', [status(esa)], [s1_xboole_0__e7_18__wellord1])).
% 1.91/2.09  thf('63', plain,
% 1.91/2.09      (((((sk_C_4 @ sk_B_3 @ sk_C_6) = (k1_xboole_0))
% 1.91/2.09         | ~ (r2_hidden @ (sk_C_5 @ (sk_C_4 @ sk_B_3 @ sk_C_6) @ sk_C_6) @ 
% 1.91/2.09              (sk_C_4 @ sk_A @ sk_C_6))
% 1.91/2.09         | ~ (v1_relat_1 @ sk_C_6)))
% 1.91/2.09         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)))),
% 1.91/2.09      inference('sup-', [status(thm)], ['61', '62'])).
% 1.91/2.09  thf('64', plain, ((v1_relat_1 @ sk_C_6)),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf('65', plain,
% 1.91/2.09      (((((sk_C_4 @ sk_B_3 @ sk_C_6) = (k1_xboole_0))
% 1.91/2.09         | ~ (r2_hidden @ (sk_C_5 @ (sk_C_4 @ sk_B_3 @ sk_C_6) @ sk_C_6) @ 
% 1.91/2.09              (sk_C_4 @ sk_A @ sk_C_6))))
% 1.91/2.09         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)))),
% 1.91/2.09      inference('demod', [status(thm)], ['63', '64'])).
% 1.91/2.09  thf('66', plain,
% 1.91/2.09      (((~ (r2_hidden @ (sk_C_5 @ (sk_C_4 @ sk_A @ sk_C_6) @ sk_C_6) @ 
% 1.91/2.09            (sk_C_4 @ sk_A @ sk_C_6))
% 1.91/2.09         | ((sk_C_4 @ sk_B_3 @ sk_C_6) = (k1_xboole_0))))
% 1.91/2.09         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)) & 
% 1.91/2.09             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 1.91/2.09               (k1_wellord1 @ sk_C_6 @ sk_B_3))))),
% 1.91/2.09      inference('sup-', [status(thm)], ['52', '65'])).
% 1.91/2.09  thf('67', plain,
% 1.91/2.09      ((((sk_A) = (sk_B_3)))
% 1.91/2.09         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)) & 
% 1.91/2.09             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 1.91/2.09               (k1_wellord1 @ sk_C_6 @ sk_B_3))))),
% 1.91/2.09      inference('demod', [status(thm)], ['30', '31'])).
% 1.91/2.09  thf('68', plain,
% 1.91/2.09      (((~ (r2_hidden @ (sk_C_5 @ (sk_C_4 @ sk_A @ sk_C_6) @ sk_C_6) @ 
% 1.91/2.09            (sk_C_4 @ sk_A @ sk_C_6))
% 1.91/2.09         | ((sk_C_4 @ sk_A @ sk_C_6) = (k1_xboole_0))))
% 1.91/2.09         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)) & 
% 1.91/2.09             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 1.91/2.09               (k1_wellord1 @ sk_C_6 @ sk_B_3))))),
% 1.91/2.09      inference('demod', [status(thm)], ['66', '67'])).
% 1.91/2.09  thf('69', plain,
% 1.91/2.09      (((~ (v1_relat_1 @ sk_C_6)
% 1.91/2.09         | ((sk_C_4 @ sk_A @ sk_C_6) = (k1_xboole_0))
% 1.91/2.09         | ~ (v2_wellord1 @ sk_C_6)
% 1.91/2.09         | ((sk_C_4 @ sk_A @ sk_C_6) = (k1_xboole_0))))
% 1.91/2.09         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)) & 
% 1.91/2.09             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 1.91/2.09               (k1_wellord1 @ sk_C_6 @ sk_B_3))))),
% 1.91/2.10      inference('sup-', [status(thm)], ['51', '68'])).
% 1.91/2.10  thf('70', plain, ((v1_relat_1 @ sk_C_6)),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf('71', plain, ((v2_wellord1 @ sk_C_6)),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf('72', plain,
% 1.91/2.10      (((((sk_C_4 @ sk_A @ sk_C_6) = (k1_xboole_0))
% 1.91/2.10         | ((sk_C_4 @ sk_A @ sk_C_6) = (k1_xboole_0))))
% 1.91/2.10         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)) & 
% 1.91/2.10             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 1.91/2.10               (k1_wellord1 @ sk_C_6 @ sk_B_3))))),
% 1.91/2.10      inference('demod', [status(thm)], ['69', '70', '71'])).
% 1.91/2.10  thf('73', plain,
% 1.91/2.10      ((((sk_C_4 @ sk_A @ sk_C_6) = (k1_xboole_0)))
% 1.91/2.10         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)) & 
% 1.91/2.10             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 1.91/2.10               (k1_wellord1 @ sk_C_6 @ sk_B_3))))),
% 1.91/2.10      inference('simplify', [status(thm)], ['72'])).
% 1.91/2.10  thf('74', plain, ((v1_relat_1 @ sk_C_6)),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf('75', plain, ((v1_relat_1 @ sk_C_6)),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf(d10_xboole_0, axiom,
% 1.91/2.10    (![A:$i,B:$i]:
% 1.91/2.10     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.91/2.10  thf('76', plain,
% 1.91/2.10      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 1.91/2.10      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.91/2.10  thf('77', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 1.91/2.10      inference('simplify', [status(thm)], ['76'])).
% 1.91/2.10  thf('78', plain,
% 1.91/2.10      (![X1 : $i, X3 : $i]:
% 1.91/2.10         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.91/2.10      inference('cnf', [status(esa)], [d3_tarski])).
% 1.91/2.10  thf('79', plain,
% 1.91/2.10      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 1.91/2.10         (((X15) != (k1_wellord1 @ X14 @ X13))
% 1.91/2.10          | (r2_hidden @ (k4_tarski @ X16 @ X13) @ X14)
% 1.91/2.10          | ~ (r2_hidden @ X16 @ X15)
% 1.91/2.10          | ~ (v1_relat_1 @ X14))),
% 1.91/2.10      inference('cnf', [status(esa)], [d1_wellord1])).
% 1.91/2.10  thf('80', plain,
% 1.91/2.10      (![X13 : $i, X14 : $i, X16 : $i]:
% 1.91/2.10         (~ (v1_relat_1 @ X14)
% 1.91/2.10          | ~ (r2_hidden @ X16 @ (k1_wellord1 @ X14 @ X13))
% 1.91/2.10          | (r2_hidden @ (k4_tarski @ X16 @ X13) @ X14))),
% 1.91/2.10      inference('simplify', [status(thm)], ['79'])).
% 1.91/2.10  thf('81', plain,
% 1.91/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.10         ((r1_tarski @ (k1_wellord1 @ X1 @ X0) @ X2)
% 1.91/2.10          | (r2_hidden @ 
% 1.91/2.10             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X1 @ X0)) @ X0) @ X1)
% 1.91/2.10          | ~ (v1_relat_1 @ X1))),
% 1.91/2.10      inference('sup-', [status(thm)], ['78', '80'])).
% 1.91/2.10  thf(t20_relat_1, axiom,
% 1.91/2.10    (![A:$i,B:$i,C:$i]:
% 1.91/2.10     ( ( v1_relat_1 @ C ) =>
% 1.91/2.10       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 1.91/2.10         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 1.91/2.10           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 1.91/2.10  thf('82', plain,
% 1.91/2.10      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.91/2.10         (~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ X9)
% 1.91/2.10          | (r2_hidden @ X8 @ (k2_relat_1 @ X9))
% 1.91/2.10          | ~ (v1_relat_1 @ X9))),
% 1.91/2.10      inference('cnf', [status(esa)], [t20_relat_1])).
% 1.91/2.10  thf('83', plain,
% 1.91/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.10         (~ (v1_relat_1 @ X0)
% 1.91/2.10          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 1.91/2.10          | ~ (v1_relat_1 @ X0)
% 1.91/2.10          | (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 1.91/2.10      inference('sup-', [status(thm)], ['81', '82'])).
% 1.91/2.10  thf('84', plain,
% 1.91/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.10         ((r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 1.91/2.10          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 1.91/2.10          | ~ (v1_relat_1 @ X0))),
% 1.91/2.10      inference('simplify', [status(thm)], ['83'])).
% 1.91/2.10  thf('85', plain,
% 1.91/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.10         ((r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 1.91/2.10          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 1.91/2.10          | ~ (v1_relat_1 @ X0))),
% 1.91/2.10      inference('simplify', [status(thm)], ['83'])).
% 1.91/2.10  thf('86', plain,
% 1.91/2.10      (![X33 : $i, X35 : $i]:
% 1.91/2.10         (~ (v2_wellord1 @ X33)
% 1.91/2.10          | (r2_hidden @ (sk_C_5 @ X35 @ X33) @ X35)
% 1.91/2.10          | ((X35) = (k1_xboole_0))
% 1.91/2.10          | ~ (r1_tarski @ X35 @ (k3_relat_1 @ X33))
% 1.91/2.10          | ~ (v1_relat_1 @ X33))),
% 1.91/2.10      inference('cnf', [status(esa)], [t10_wellord1])).
% 1.91/2.10  thf('87', plain,
% 1.91/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.10         (~ (v1_relat_1 @ X2)
% 1.91/2.10          | (r2_hidden @ X1 @ (k2_relat_1 @ X2))
% 1.91/2.10          | ~ (v1_relat_1 @ X0)
% 1.91/2.10          | ((k1_wellord1 @ X2 @ X1) = (k1_xboole_0))
% 1.91/2.10          | (r2_hidden @ (sk_C_5 @ (k1_wellord1 @ X2 @ X1) @ X0) @ 
% 1.91/2.10             (k1_wellord1 @ X2 @ X1))
% 1.91/2.10          | ~ (v2_wellord1 @ X0))),
% 1.91/2.10      inference('sup-', [status(thm)], ['85', '86'])).
% 1.91/2.10  thf('88', plain,
% 1.91/2.10      (![X10 : $i, X11 : $i]:
% 1.91/2.10         (~ (r2_hidden @ X10 @ X11) | ~ (r1_tarski @ X11 @ X10))),
% 1.91/2.10      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.91/2.10  thf('89', plain,
% 1.91/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.10         (~ (v2_wellord1 @ X2)
% 1.91/2.10          | ((k1_wellord1 @ X1 @ X0) = (k1_xboole_0))
% 1.91/2.10          | ~ (v1_relat_1 @ X2)
% 1.91/2.10          | (r2_hidden @ X0 @ (k2_relat_1 @ X1))
% 1.91/2.10          | ~ (v1_relat_1 @ X1)
% 1.91/2.10          | ~ (r1_tarski @ (k1_wellord1 @ X1 @ X0) @ 
% 1.91/2.10               (sk_C_5 @ (k1_wellord1 @ X1 @ X0) @ X2)))),
% 1.91/2.10      inference('sup-', [status(thm)], ['87', '88'])).
% 1.91/2.10  thf('90', plain,
% 1.91/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.10         (~ (v1_relat_1 @ X2)
% 1.91/2.10          | (r2_hidden @ X1 @ (k2_relat_1 @ X2))
% 1.91/2.10          | ~ (v1_relat_1 @ X2)
% 1.91/2.10          | (r2_hidden @ X1 @ (k2_relat_1 @ X2))
% 1.91/2.10          | ~ (v1_relat_1 @ X0)
% 1.91/2.10          | ((k1_wellord1 @ X2 @ X1) = (k1_xboole_0))
% 1.91/2.10          | ~ (v2_wellord1 @ X0))),
% 1.91/2.10      inference('sup-', [status(thm)], ['84', '89'])).
% 1.91/2.10  thf('91', plain,
% 1.91/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.10         (~ (v2_wellord1 @ X0)
% 1.91/2.10          | ((k1_wellord1 @ X2 @ X1) = (k1_xboole_0))
% 1.91/2.10          | ~ (v1_relat_1 @ X0)
% 1.91/2.10          | (r2_hidden @ X1 @ (k2_relat_1 @ X2))
% 1.91/2.10          | ~ (v1_relat_1 @ X2))),
% 1.91/2.10      inference('simplify', [status(thm)], ['90'])).
% 1.91/2.10  thf('92', plain,
% 1.91/2.10      (![X10 : $i, X11 : $i]:
% 1.91/2.10         (~ (r2_hidden @ X10 @ X11) | ~ (r1_tarski @ X11 @ X10))),
% 1.91/2.10      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.91/2.10  thf('93', plain,
% 1.91/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.10         (~ (v1_relat_1 @ X0)
% 1.91/2.10          | ~ (v1_relat_1 @ X2)
% 1.91/2.10          | ((k1_wellord1 @ X0 @ X1) = (k1_xboole_0))
% 1.91/2.10          | ~ (v2_wellord1 @ X2)
% 1.91/2.10          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 1.91/2.10      inference('sup-', [status(thm)], ['91', '92'])).
% 1.91/2.10  thf('94', plain,
% 1.91/2.10      (![X0 : $i, X1 : $i]:
% 1.91/2.10         (~ (v2_wellord1 @ X1)
% 1.91/2.10          | ((k1_wellord1 @ X0 @ (k2_relat_1 @ X0)) = (k1_xboole_0))
% 1.91/2.10          | ~ (v1_relat_1 @ X1)
% 1.91/2.10          | ~ (v1_relat_1 @ X0))),
% 1.91/2.10      inference('sup-', [status(thm)], ['77', '93'])).
% 1.91/2.10  thf('95', plain,
% 1.91/2.10      (![X0 : $i]:
% 1.91/2.10         (~ (v1_relat_1 @ X0)
% 1.91/2.10          | ((k1_wellord1 @ X0 @ (k2_relat_1 @ X0)) = (k1_xboole_0))
% 1.91/2.10          | ~ (v2_wellord1 @ sk_C_6))),
% 1.91/2.10      inference('sup-', [status(thm)], ['75', '94'])).
% 1.91/2.10  thf('96', plain, ((v2_wellord1 @ sk_C_6)),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf('97', plain,
% 1.91/2.10      (![X0 : $i]:
% 1.91/2.10         (~ (v1_relat_1 @ X0)
% 1.91/2.10          | ((k1_wellord1 @ X0 @ (k2_relat_1 @ X0)) = (k1_xboole_0)))),
% 1.91/2.10      inference('demod', [status(thm)], ['95', '96'])).
% 1.91/2.10  thf('98', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 1.91/2.10      inference('simplify', [status(thm)], ['76'])).
% 1.91/2.10  thf('99', plain,
% 1.91/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.10         ((r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 1.91/2.10          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 1.91/2.10          | ~ (v1_relat_1 @ X0))),
% 1.91/2.10      inference('simplify', [status(thm)], ['83'])).
% 1.91/2.10  thf('100', plain,
% 1.91/2.10      (![X10 : $i, X11 : $i]:
% 1.91/2.10         (~ (r2_hidden @ X10 @ X11) | ~ (r1_tarski @ X11 @ X10))),
% 1.91/2.10      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.91/2.10  thf('101', plain,
% 1.91/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.10         (~ (v1_relat_1 @ X0)
% 1.91/2.10          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 1.91/2.10          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 1.91/2.10      inference('sup-', [status(thm)], ['99', '100'])).
% 1.91/2.10  thf('102', plain,
% 1.91/2.10      (![X0 : $i, X1 : $i]:
% 1.91/2.10         ((r1_tarski @ (k1_wellord1 @ X0 @ (k2_relat_1 @ X0)) @ X1)
% 1.91/2.10          | ~ (v1_relat_1 @ X0))),
% 1.91/2.10      inference('sup-', [status(thm)], ['98', '101'])).
% 1.91/2.10  thf('103', plain,
% 1.91/2.10      (![X0 : $i, X1 : $i]:
% 1.91/2.10         ((r1_tarski @ k1_xboole_0 @ X0)
% 1.91/2.10          | ~ (v1_relat_1 @ X1)
% 1.91/2.10          | ~ (v1_relat_1 @ X1))),
% 1.91/2.10      inference('sup+', [status(thm)], ['97', '102'])).
% 1.91/2.10  thf('104', plain,
% 1.91/2.10      (![X0 : $i, X1 : $i]:
% 1.91/2.10         (~ (v1_relat_1 @ X1) | (r1_tarski @ k1_xboole_0 @ X0))),
% 1.91/2.10      inference('simplify', [status(thm)], ['103'])).
% 1.91/2.10  thf('105', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.91/2.10      inference('sup-', [status(thm)], ['74', '104'])).
% 1.91/2.10  thf('106', plain,
% 1.91/2.10      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)) | 
% 1.91/2.10       ~
% 1.91/2.10       ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 1.91/2.10         (k1_wellord1 @ sk_C_6 @ sk_B_3)))),
% 1.91/2.10      inference('demod', [status(thm)], ['42', '73', '105'])).
% 1.91/2.10  thf('107', plain,
% 1.91/2.10      (~
% 1.91/2.10       ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 1.91/2.10         (k1_wellord1 @ sk_C_6 @ sk_B_3)))),
% 1.91/2.10      inference('sat_resolution*', [status(thm)], ['2', '106'])).
% 1.91/2.10  thf('108', plain,
% 1.91/2.10      (~ (r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 1.91/2.10          (k1_wellord1 @ sk_C_6 @ sk_B_3))),
% 1.91/2.10      inference('simpl_trail', [status(thm)], ['1', '107'])).
% 1.91/2.10  thf('109', plain,
% 1.91/2.10      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6))
% 1.91/2.10         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)))),
% 1.91/2.10      inference('split', [status(esa)], ['23'])).
% 1.91/2.10  thf('110', plain,
% 1.91/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.10         ((r1_tarski @ (k1_wellord1 @ X1 @ X0) @ X2)
% 1.91/2.10          | (r2_hidden @ 
% 1.91/2.10             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X1 @ X0)) @ X0) @ X1)
% 1.91/2.10          | ~ (v1_relat_1 @ X1))),
% 1.91/2.10      inference('sup-', [status(thm)], ['78', '80'])).
% 1.91/2.10  thf(l2_wellord1, axiom,
% 1.91/2.10    (![A:$i]:
% 1.91/2.10     ( ( v1_relat_1 @ A ) =>
% 1.91/2.10       ( ( v8_relat_2 @ A ) <=>
% 1.91/2.10         ( ![B:$i,C:$i,D:$i]:
% 1.91/2.10           ( ( ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) & 
% 1.91/2.10               ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) =>
% 1.91/2.10             ( r2_hidden @ ( k4_tarski @ B @ D ) @ A ) ) ) ) ))).
% 1.91/2.10  thf('111', plain,
% 1.91/2.10      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.91/2.10         (~ (v8_relat_2 @ X19)
% 1.91/2.10          | ~ (r2_hidden @ (k4_tarski @ X20 @ X21) @ X19)
% 1.91/2.10          | ~ (r2_hidden @ (k4_tarski @ X21 @ X22) @ X19)
% 1.91/2.10          | (r2_hidden @ (k4_tarski @ X20 @ X22) @ X19)
% 1.91/2.10          | ~ (v1_relat_1 @ X19))),
% 1.91/2.10      inference('cnf', [status(esa)], [l2_wellord1])).
% 1.91/2.10  thf('112', plain,
% 1.91/2.10      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.91/2.10         (~ (v1_relat_1 @ X0)
% 1.91/2.10          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 1.91/2.10          | ~ (v1_relat_1 @ X0)
% 1.91/2.10          | (r2_hidden @ 
% 1.91/2.10             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1)) @ X3) @ X0)
% 1.91/2.10          | ~ (r2_hidden @ (k4_tarski @ X1 @ X3) @ X0)
% 1.91/2.10          | ~ (v8_relat_2 @ X0))),
% 1.91/2.10      inference('sup-', [status(thm)], ['110', '111'])).
% 1.91/2.10  thf('113', plain,
% 1.91/2.10      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.91/2.10         (~ (v8_relat_2 @ X0)
% 1.91/2.10          | ~ (r2_hidden @ (k4_tarski @ X1 @ X3) @ X0)
% 1.91/2.10          | (r2_hidden @ 
% 1.91/2.10             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1)) @ X3) @ X0)
% 1.91/2.10          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 1.91/2.10          | ~ (v1_relat_1 @ X0))),
% 1.91/2.10      inference('simplify', [status(thm)], ['112'])).
% 1.91/2.10  thf('114', plain,
% 1.91/2.10      ((![X0 : $i]:
% 1.91/2.10          (~ (v1_relat_1 @ sk_C_6)
% 1.91/2.10           | (r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ X0)
% 1.91/2.10           | (r2_hidden @ 
% 1.91/2.10              (k4_tarski @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_6 @ sk_A)) @ sk_B_3) @ 
% 1.91/2.10              sk_C_6)
% 1.91/2.10           | ~ (v8_relat_2 @ sk_C_6)))
% 1.91/2.10         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)))),
% 1.91/2.10      inference('sup-', [status(thm)], ['109', '113'])).
% 1.91/2.10  thf('115', plain, ((v1_relat_1 @ sk_C_6)),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf('116', plain, ((v1_relat_1 @ sk_C_6)),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf('117', plain,
% 1.91/2.10      (![X18 : $i]:
% 1.91/2.10         (~ (v2_wellord1 @ X18) | (v8_relat_2 @ X18) | ~ (v1_relat_1 @ X18))),
% 1.91/2.10      inference('cnf', [status(esa)], [d4_wellord1])).
% 1.91/2.10  thf('118', plain, (((v8_relat_2 @ sk_C_6) | ~ (v2_wellord1 @ sk_C_6))),
% 1.91/2.10      inference('sup-', [status(thm)], ['116', '117'])).
% 1.91/2.10  thf('119', plain, ((v2_wellord1 @ sk_C_6)),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf('120', plain, ((v8_relat_2 @ sk_C_6)),
% 1.91/2.10      inference('demod', [status(thm)], ['118', '119'])).
% 1.91/2.10  thf('121', plain,
% 1.91/2.10      ((![X0 : $i]:
% 1.91/2.10          ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ X0)
% 1.91/2.10           | (r2_hidden @ 
% 1.91/2.10              (k4_tarski @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_6 @ sk_A)) @ sk_B_3) @ 
% 1.91/2.10              sk_C_6)))
% 1.91/2.10         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)))),
% 1.91/2.10      inference('demod', [status(thm)], ['114', '115', '120'])).
% 1.91/2.10  thf('122', plain,
% 1.91/2.10      (![X13 : $i, X14 : $i, X17 : $i]:
% 1.91/2.10         (~ (v1_relat_1 @ X14)
% 1.91/2.10          | ((X17) = (X13))
% 1.91/2.10          | ~ (r2_hidden @ (k4_tarski @ X17 @ X13) @ X14)
% 1.91/2.10          | (r2_hidden @ X17 @ (k1_wellord1 @ X14 @ X13)))),
% 1.91/2.10      inference('simplify', [status(thm)], ['15'])).
% 1.91/2.10  thf('123', plain,
% 1.91/2.10      ((![X0 : $i]:
% 1.91/2.10          ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ X0)
% 1.91/2.10           | (r2_hidden @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_6 @ sk_A)) @ 
% 1.91/2.10              (k1_wellord1 @ sk_C_6 @ sk_B_3))
% 1.91/2.10           | ((sk_C @ X0 @ (k1_wellord1 @ sk_C_6 @ sk_A)) = (sk_B_3))
% 1.91/2.10           | ~ (v1_relat_1 @ sk_C_6)))
% 1.91/2.10         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)))),
% 1.91/2.10      inference('sup-', [status(thm)], ['121', '122'])).
% 1.91/2.10  thf('124', plain, ((v1_relat_1 @ sk_C_6)),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf('125', plain,
% 1.91/2.10      ((![X0 : $i]:
% 1.91/2.10          ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ X0)
% 1.91/2.10           | (r2_hidden @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_6 @ sk_A)) @ 
% 1.91/2.10              (k1_wellord1 @ sk_C_6 @ sk_B_3))
% 1.91/2.10           | ((sk_C @ X0 @ (k1_wellord1 @ sk_C_6 @ sk_A)) = (sk_B_3))))
% 1.91/2.10         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)))),
% 1.91/2.10      inference('demod', [status(thm)], ['123', '124'])).
% 1.91/2.10  thf('126', plain,
% 1.91/2.10      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)) | 
% 1.91/2.10       ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 1.91/2.10         (k1_wellord1 @ sk_C_6 @ sk_B_3)))),
% 1.91/2.10      inference('split', [status(esa)], ['23'])).
% 1.91/2.10  thf('127', plain, (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6))),
% 1.91/2.10      inference('sat_resolution*', [status(thm)], ['2', '106', '126'])).
% 1.91/2.10  thf('128', plain,
% 1.91/2.10      (![X0 : $i]:
% 1.91/2.10         ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ X0)
% 1.91/2.10          | (r2_hidden @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_6 @ sk_A)) @ 
% 1.91/2.10             (k1_wellord1 @ sk_C_6 @ sk_B_3))
% 1.91/2.10          | ((sk_C @ X0 @ (k1_wellord1 @ sk_C_6 @ sk_A)) = (sk_B_3)))),
% 1.91/2.10      inference('simpl_trail', [status(thm)], ['125', '127'])).
% 1.91/2.10  thf('129', plain,
% 1.91/2.10      (![X1 : $i, X3 : $i]:
% 1.91/2.10         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.91/2.10      inference('cnf', [status(esa)], [d3_tarski])).
% 1.91/2.10  thf('130', plain,
% 1.91/2.10      ((((sk_C @ (k1_wellord1 @ sk_C_6 @ sk_B_3) @ 
% 1.91/2.10          (k1_wellord1 @ sk_C_6 @ sk_A)) = (sk_B_3))
% 1.91/2.10        | (r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 1.91/2.10           (k1_wellord1 @ sk_C_6 @ sk_B_3))
% 1.91/2.10        | (r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 1.91/2.10           (k1_wellord1 @ sk_C_6 @ sk_B_3)))),
% 1.91/2.10      inference('sup-', [status(thm)], ['128', '129'])).
% 1.91/2.10  thf('131', plain,
% 1.91/2.10      (((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 1.91/2.10         (k1_wellord1 @ sk_C_6 @ sk_B_3))
% 1.91/2.10        | ((sk_C @ (k1_wellord1 @ sk_C_6 @ sk_B_3) @ 
% 1.91/2.10            (k1_wellord1 @ sk_C_6 @ sk_A)) = (sk_B_3)))),
% 1.91/2.10      inference('simplify', [status(thm)], ['130'])).
% 1.91/2.10  thf('132', plain,
% 1.91/2.10      (~ (r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 1.91/2.10          (k1_wellord1 @ sk_C_6 @ sk_B_3))),
% 1.91/2.10      inference('simpl_trail', [status(thm)], ['1', '107'])).
% 1.91/2.10  thf('133', plain,
% 1.91/2.10      (((sk_C @ (k1_wellord1 @ sk_C_6 @ sk_B_3) @ (k1_wellord1 @ sk_C_6 @ sk_A))
% 1.91/2.10         = (sk_B_3))),
% 1.91/2.10      inference('clc', [status(thm)], ['131', '132'])).
% 1.91/2.10  thf('134', plain,
% 1.91/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.10         ((r1_tarski @ (k1_wellord1 @ X1 @ X0) @ X2)
% 1.91/2.10          | (r2_hidden @ 
% 1.91/2.10             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X1 @ X0)) @ X0) @ X1)
% 1.91/2.10          | ~ (v1_relat_1 @ X1))),
% 1.91/2.10      inference('sup-', [status(thm)], ['78', '80'])).
% 1.91/2.10  thf(l3_wellord1, axiom,
% 1.91/2.10    (![A:$i]:
% 1.91/2.10     ( ( v1_relat_1 @ A ) =>
% 1.91/2.10       ( ( v4_relat_2 @ A ) <=>
% 1.91/2.10         ( ![B:$i,C:$i]:
% 1.91/2.10           ( ( ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) & 
% 1.91/2.10               ( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) ) =>
% 1.91/2.10             ( ( B ) = ( C ) ) ) ) ) ))).
% 1.91/2.10  thf('135', plain,
% 1.91/2.10      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.91/2.10         (~ (v4_relat_2 @ X23)
% 1.91/2.10          | ((X25) = (X24))
% 1.91/2.10          | ~ (r2_hidden @ (k4_tarski @ X24 @ X25) @ X23)
% 1.91/2.10          | ~ (r2_hidden @ (k4_tarski @ X25 @ X24) @ X23)
% 1.91/2.10          | ~ (v1_relat_1 @ X23))),
% 1.91/2.10      inference('cnf', [status(esa)], [l3_wellord1])).
% 1.91/2.10  thf('136', plain,
% 1.91/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.10         (~ (v1_relat_1 @ X0)
% 1.91/2.10          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 1.91/2.10          | ~ (v1_relat_1 @ X0)
% 1.91/2.10          | ~ (r2_hidden @ 
% 1.91/2.10               (k4_tarski @ X1 @ (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1))) @ X0)
% 1.91/2.10          | ((X1) = (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1)))
% 1.91/2.10          | ~ (v4_relat_2 @ X0))),
% 1.91/2.10      inference('sup-', [status(thm)], ['134', '135'])).
% 1.91/2.10  thf('137', plain,
% 1.91/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.10         (~ (v4_relat_2 @ X0)
% 1.91/2.10          | ((X1) = (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1)))
% 1.91/2.10          | ~ (r2_hidden @ 
% 1.91/2.10               (k4_tarski @ X1 @ (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1))) @ X0)
% 1.91/2.10          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 1.91/2.10          | ~ (v1_relat_1 @ X0))),
% 1.91/2.10      inference('simplify', [status(thm)], ['136'])).
% 1.91/2.10  thf('138', plain,
% 1.91/2.10      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)
% 1.91/2.10        | ~ (v1_relat_1 @ sk_C_6)
% 1.91/2.10        | (r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 1.91/2.10           (k1_wellord1 @ sk_C_6 @ sk_B_3))
% 1.91/2.10        | ((sk_A)
% 1.91/2.10            = (sk_C @ (k1_wellord1 @ sk_C_6 @ sk_B_3) @ 
% 1.91/2.10               (k1_wellord1 @ sk_C_6 @ sk_A)))
% 1.91/2.10        | ~ (v4_relat_2 @ sk_C_6))),
% 1.91/2.10      inference('sup-', [status(thm)], ['133', '137'])).
% 1.91/2.10  thf('139', plain,
% 1.91/2.10      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6))
% 1.91/2.10         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)))),
% 1.91/2.10      inference('split', [status(esa)], ['23'])).
% 1.91/2.10  thf('140', plain, (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6))),
% 1.91/2.10      inference('sat_resolution*', [status(thm)], ['2', '106', '126'])).
% 1.91/2.10  thf('141', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)),
% 1.91/2.10      inference('simpl_trail', [status(thm)], ['139', '140'])).
% 1.91/2.10  thf('142', plain, ((v1_relat_1 @ sk_C_6)),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf('143', plain,
% 1.91/2.10      (((sk_C @ (k1_wellord1 @ sk_C_6 @ sk_B_3) @ (k1_wellord1 @ sk_C_6 @ sk_A))
% 1.91/2.10         = (sk_B_3))),
% 1.91/2.10      inference('clc', [status(thm)], ['131', '132'])).
% 1.91/2.10  thf('144', plain, ((v1_relat_1 @ sk_C_6)),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf('145', plain,
% 1.91/2.10      (![X18 : $i]:
% 1.91/2.10         (~ (v2_wellord1 @ X18) | (v4_relat_2 @ X18) | ~ (v1_relat_1 @ X18))),
% 1.91/2.10      inference('cnf', [status(esa)], [d4_wellord1])).
% 1.91/2.10  thf('146', plain, (((v4_relat_2 @ sk_C_6) | ~ (v2_wellord1 @ sk_C_6))),
% 1.91/2.10      inference('sup-', [status(thm)], ['144', '145'])).
% 1.91/2.10  thf('147', plain, ((v2_wellord1 @ sk_C_6)),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf('148', plain, ((v4_relat_2 @ sk_C_6)),
% 1.91/2.10      inference('demod', [status(thm)], ['146', '147'])).
% 1.91/2.10  thf('149', plain,
% 1.91/2.10      (((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 1.91/2.10         (k1_wellord1 @ sk_C_6 @ sk_B_3))
% 1.91/2.10        | ((sk_A) = (sk_B_3)))),
% 1.91/2.10      inference('demod', [status(thm)], ['138', '141', '142', '143', '148'])).
% 1.91/2.10  thf('150', plain,
% 1.91/2.10      (~ (r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 1.91/2.10          (k1_wellord1 @ sk_C_6 @ sk_B_3))),
% 1.91/2.10      inference('simpl_trail', [status(thm)], ['1', '107'])).
% 1.91/2.10  thf('151', plain, (((sk_A) = (sk_B_3))),
% 1.91/2.10      inference('clc', [status(thm)], ['149', '150'])).
% 1.91/2.10  thf('152', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 1.91/2.10      inference('simplify', [status(thm)], ['76'])).
% 1.91/2.10  thf('153', plain, ($false),
% 1.91/2.10      inference('demod', [status(thm)], ['108', '151', '152'])).
% 1.91/2.10  
% 1.91/2.10  % SZS output end Refutation
% 1.91/2.10  
% 1.93/2.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
