%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fXRz2dMYOQ

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:32 EST 2020

% Result     : Theorem 4.70s
% Output     : Refutation 4.70s
% Verified   : 
% Statistics : Number of formulae       :  189 (2419 expanded)
%              Number of leaves         :   31 ( 645 expanded)
%              Depth                    :   28
%              Number of atoms          : 2051 (36062 expanded)
%              Number of equality atoms :   65 ( 796 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(sk_C_6_type,type,(
    sk_C_6: $i )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_5_type,type,(
    sk_C_5: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v6_relat_2_type,type,(
    v6_relat_2: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_wellord1_type,type,(
    v1_wellord1: $i > $o )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_4_type,type,(
    sk_C_4: $i > $i > $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

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

thf('4',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ( r2_hidden @ X30 @ ( sk_C_4 @ X31 @ X29 ) )
      | ( r2_hidden @ ( k4_tarski @ X30 @ X31 ) @ X29 )
      | ~ ( r2_hidden @ X30 @ ( k3_relat_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[s1_xboole_0__e7_18__wellord1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_6 )
      | ( r2_hidden @ sk_A @ ( sk_C_4 @ X0 @ sk_C_6 ) )
      | ~ ( v1_relat_1 @ sk_C_6 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_6 )
      | ( r2_hidden @ sk_A @ ( sk_C_4 @ X0 @ sk_C_6 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    r2_hidden @ sk_B_3 @ ( k3_relat_1 @ sk_C_6 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
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

thf('10',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v6_relat_2 @ X26 )
      | ~ ( r2_hidden @ X27 @ ( k3_relat_1 @ X26 ) )
      | ( r2_hidden @ ( k4_tarski @ X28 @ X27 ) @ X26 )
      | ( r2_hidden @ ( k4_tarski @ X27 @ X28 ) @ X26 )
      | ( X27 = X28 )
      | ~ ( r2_hidden @ X28 @ ( k3_relat_1 @ X26 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[l4_wellord1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_6 )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_C_6 ) )
      | ( sk_A = X0 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_6 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ sk_A ) @ sk_C_6 )
      | ~ ( v6_relat_2 @ sk_C_6 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
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

thf('14',plain,(
    ! [X18: $i] :
      ( ~ ( v2_wellord1 @ X18 )
      | ( v6_relat_2 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('15',plain,
    ( ( v6_relat_2 @ sk_C_6 )
    | ~ ( v2_wellord1 @ sk_C_6 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v2_wellord1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v6_relat_2 @ sk_C_6 ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_C_6 ) )
      | ( sk_A = X0 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_6 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ sk_A ) @ sk_C_6 ) ) ),
    inference(demod,[status(thm)],['11','12','17'])).

thf('19',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B_3 @ sk_A ) @ sk_C_6 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
    | ( sk_A = sk_B_3 ) ),
    inference('sup-',[status(thm)],['8','18'])).

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

thf('20',plain,(
    ! [X13: $i,X14: $i,X15: $i,X17: $i] :
      ( ( X15
       != ( k1_wellord1 @ X14 @ X13 ) )
      | ( r2_hidden @ X17 @ X15 )
      | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X13 ) @ X14 )
      | ( X17 = X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('21',plain,(
    ! [X13: $i,X14: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( X17 = X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X13 ) @ X14 )
      | ( r2_hidden @ X17 @ ( k1_wellord1 @ X14 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( sk_A = sk_B_3 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
    | ( r2_hidden @ sk_B_3 @ ( k1_wellord1 @ sk_C_6 @ sk_A ) )
    | ( sk_B_3 = sk_A )
    | ~ ( v1_relat_1 @ sk_C_6 ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( sk_A = sk_B_3 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
    | ( r2_hidden @ sk_B_3 @ ( k1_wellord1 @ sk_C_6 @ sk_A ) )
    | ( sk_B_3 = sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r2_hidden @ sk_B_3 @ ( k1_wellord1 @ sk_C_6 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
    | ( sk_A = sk_B_3 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,
    ( ( ( sk_A = sk_B_3 )
      | ( r2_hidden @ sk_B_3 @ ( k1_wellord1 @ sk_C_6 @ sk_A ) ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) )
   <= ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ),
    inference(split,[status(esa)],['28'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) )
        | ~ ( r2_hidden @ X0 @ ( k1_wellord1 @ sk_C_6 @ sk_A ) ) )
   <= ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( sk_A = sk_B_3 )
      | ( r2_hidden @ sk_B_3 @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X15
       != ( k1_wellord1 @ X14 @ X13 ) )
      | ( X16 != X13 )
      | ~ ( r2_hidden @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('34',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( r2_hidden @ X13 @ ( k1_wellord1 @ X14 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( ( sk_A = sk_B_3 )
      | ~ ( v1_relat_1 @ sk_C_6 ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( sk_A = sk_B_3 )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_A ) @ sk_C_6 )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( r2_hidden @ sk_A @ ( sk_C_4 @ sk_A @ sk_C_6 ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ) ),
    inference('sup-',[status(thm)],['7','39'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('41',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('42',plain,
    ( ~ ( r1_tarski @ ( sk_C_4 @ sk_A @ sk_C_6 ) @ sk_A )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

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
    inference(demod,[status(thm)],['35','36'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_6 )
      | ( r2_hidden @ sk_A @ ( sk_C_4 @ X0 @ sk_C_6 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('54',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ) ),
    inference(split,[status(esa)],['0'])).

thf('55',plain,
    ( ( r2_hidden @ sk_A @ ( sk_C_4 @ sk_B_3 @ sk_C_6 ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( sk_C_4 @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('57',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v2_wellord1 @ X33 )
      | ~ ( r2_hidden @ X34 @ X35 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_5 @ X35 @ X33 ) @ X34 ) @ X33 )
      | ( X35 = k1_xboole_0 )
      | ~ ( r1_tarski @ X35 @ ( k3_relat_1 @ X33 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( sk_C_4 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_5 @ ( sk_C_4 @ X1 @ X0 ) @ X0 ) @ X2 ) @ X0 )
      | ~ ( r2_hidden @ X2 @ ( sk_C_4 @ X1 @ X0 ) )
      | ~ ( v2_wellord1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v2_wellord1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( sk_C_4 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_5 @ ( sk_C_4 @ X1 @ X0 ) @ X0 ) @ X2 ) @ X0 )
      | ( ( sk_C_4 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_6 )
      | ( ( sk_C_4 @ sk_B_3 @ sk_C_6 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_5 @ ( sk_C_4 @ sk_B_3 @ sk_C_6 ) @ sk_C_6 ) @ sk_A ) @ sk_C_6 )
      | ~ ( v2_wellord1 @ sk_C_6 ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ) ),
    inference('sup-',[status(thm)],['55','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v2_wellord1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( ( sk_C_4 @ sk_B_3 @ sk_C_6 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_5 @ ( sk_C_4 @ sk_B_3 @ sk_C_6 ) @ sk_C_6 ) @ sk_A ) @ sk_C_6 ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ! [X29: $i,X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ~ ( r2_hidden @ ( k4_tarski @ X32 @ X31 ) @ X29 )
      | ~ ( r2_hidden @ X32 @ ( sk_C_4 @ X31 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[s1_xboole_0__e7_18__wellord1])).

thf('65',plain,
    ( ( ( ( sk_C_4 @ sk_B_3 @ sk_C_6 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_C_5 @ ( sk_C_4 @ sk_B_3 @ sk_C_6 ) @ sk_C_6 ) @ ( sk_C_4 @ sk_A @ sk_C_6 ) )
      | ~ ( v1_relat_1 @ sk_C_6 ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( ( ( sk_C_4 @ sk_B_3 @ sk_C_6 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_C_5 @ ( sk_C_4 @ sk_B_3 @ sk_C_6 ) @ sk_C_6 ) @ ( sk_C_4 @ sk_A @ sk_C_6 ) ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ~ ( r2_hidden @ ( sk_C_5 @ ( sk_C_4 @ sk_A @ sk_C_6 ) @ sk_C_6 ) @ ( sk_C_4 @ sk_A @ sk_C_6 ) )
      | ( ( sk_C_4 @ sk_B_3 @ sk_C_6 )
        = k1_xboole_0 ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ) ),
    inference('sup-',[status(thm)],['52','67'])).

thf('69',plain,
    ( ( sk_A = sk_B_3 )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('70',plain,
    ( ( ~ ( r2_hidden @ ( sk_C_5 @ ( sk_C_4 @ sk_A @ sk_C_6 ) @ sk_C_6 ) @ ( sk_C_4 @ sk_A @ sk_C_6 ) )
      | ( ( sk_C_4 @ sk_A @ sk_C_6 )
        = k1_xboole_0 ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_6 )
      | ( ( sk_C_4 @ sk_A @ sk_C_6 )
        = k1_xboole_0 )
      | ~ ( v2_wellord1 @ sk_C_6 )
      | ( ( sk_C_4 @ sk_A @ sk_C_6 )
        = k1_xboole_0 ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ) ),
    inference('sup-',[status(thm)],['51','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v2_wellord1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ( ( sk_C_4 @ sk_A @ sk_C_6 )
        = k1_xboole_0 )
      | ( ( sk_C_4 @ sk_A @ sk_C_6 )
        = k1_xboole_0 ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,
    ( ( ( sk_C_4 @ sk_A @ sk_C_6 )
      = k1_xboole_0 )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    v1_relat_1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('77',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('78',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('80',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X15
       != ( k1_wellord1 @ X14 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ X16 @ X13 ) @ X14 )
      | ~ ( r2_hidden @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('81',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k1_wellord1 @ X14 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ X16 @ X13 ) @ X14 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_wellord1 @ X1 @ X0 ) ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['79','81'])).

thf(t30_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )).

thf('83',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X9 )
      | ( r2_hidden @ X8 @ ( k3_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ ( k3_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_wellord1 @ X1 @ X0 ) ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['79','81'])).

thf('90',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X9 )
      | ( r2_hidden @ X7 @ ( k3_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ ( k3_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ! [X33: $i,X35: $i] :
      ( ~ ( v2_wellord1 @ X33 )
      | ( r2_hidden @ ( sk_C_5 @ X35 @ X33 ) @ X35 )
      | ( X35 = k1_xboole_0 )
      | ~ ( r1_tarski @ X35 @ ( k3_relat_1 @ X33 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord1])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_wellord1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_5 @ ( k1_wellord1 @ X0 @ X1 ) @ X0 ) @ ( k1_wellord1 @ X0 @ X1 ) )
      | ~ ( v2_wellord1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_wellord1 @ X0 )
      | ( r2_hidden @ ( sk_C_5 @ ( k1_wellord1 @ X0 @ X1 ) @ X0 ) @ ( k1_wellord1 @ X0 @ X1 ) )
      | ( ( k1_wellord1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_wellord1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_wellord1 @ X1 )
      | ~ ( r1_tarski @ ( k1_wellord1 @ X1 @ X0 ) @ ( sk_C_5 @ ( k1_wellord1 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_wellord1 @ X0 )
      | ( ( k1_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( ( k1_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','87'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_wellord1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_wellord1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v2_wellord1 @ sk_C_6 ) ) ),
    inference('sup-',[status(thm)],['76','105'])).

thf('107',plain,(
    v2_wellord1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
    | ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['42','75','108'])).

thf('110',plain,(
    ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','109'])).

thf('111',plain,(
    ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ),
    inference(simpl_trail,[status(thm)],['1','110'])).

thf('112',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ) ),
    inference(split,[status(esa)],['28'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_wellord1 @ X1 @ X0 ) ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['79','81'])).

thf(l2_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v8_relat_2 @ A )
      <=> ! [B: $i,C: $i,D: $i] :
            ( ( ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
              & ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) )
           => ( r2_hidden @ ( k4_tarski @ B @ D ) @ A ) ) ) ) )).

thf('114',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( v8_relat_2 @ X19 )
      | ~ ( r2_hidden @ ( k4_tarski @ X20 @ X21 ) @ X19 )
      | ~ ( r2_hidden @ ( k4_tarski @ X21 @ X22 ) @ X19 )
      | ( r2_hidden @ ( k4_tarski @ X20 @ X22 ) @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l2_wellord1])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) @ X3 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X3 ) @ X0 )
      | ~ ( v8_relat_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v8_relat_2 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X3 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) @ X3 ) @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_C_6 )
        | ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ X0 )
        | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_6 @ sk_A ) ) @ sk_B_3 ) @ sk_C_6 )
        | ~ ( v8_relat_2 @ sk_C_6 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ) ),
    inference('sup-',[status(thm)],['112','116'])).

thf('118',plain,(
    v1_relat_1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v1_relat_1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X18: $i] :
      ( ~ ( v2_wellord1 @ X18 )
      | ( v8_relat_2 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('121',plain,
    ( ( v8_relat_2 @ sk_C_6 )
    | ~ ( v2_wellord1 @ sk_C_6 ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v2_wellord1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v8_relat_2 @ sk_C_6 ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ X0 )
        | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_6 @ sk_A ) ) @ sk_B_3 ) @ sk_C_6 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ) ),
    inference(demod,[status(thm)],['117','118','123'])).

thf('125',plain,(
    ! [X13: $i,X14: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( X17 = X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X13 ) @ X14 )
      | ( r2_hidden @ X17 @ ( k1_wellord1 @ X14 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('126',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_6 @ sk_A ) ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) )
        | ( ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_6 @ sk_A ) )
          = sk_B_3 )
        | ~ ( v1_relat_1 @ sk_C_6 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    v1_relat_1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_6 @ sk_A ) ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) )
        | ( ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_6 @ sk_A ) )
          = sk_B_3 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ),
    inference(split,[status(esa)],['28'])).

thf('130',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ),
    inference('sat_resolution*',[status(thm)],['2','109','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_6 @ sk_A ) ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) )
      | ( ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_6 @ sk_A ) )
        = sk_B_3 ) ) ),
    inference(simpl_trail,[status(thm)],['128','130'])).

thf('132',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('133',plain,
    ( ( ( sk_C @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) @ ( k1_wellord1 @ sk_C_6 @ sk_A ) )
      = sk_B_3 )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) )
    | ( ( sk_C @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) @ ( k1_wellord1 @ sk_C_6 @ sk_A ) )
      = sk_B_3 ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ),
    inference(simpl_trail,[status(thm)],['1','110'])).

thf('136',plain,
    ( ( sk_C @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) @ ( k1_wellord1 @ sk_C_6 @ sk_A ) )
    = sk_B_3 ),
    inference(clc,[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_wellord1 @ X1 @ X0 ) ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['79','81'])).

thf(l3_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v4_relat_2 @ A )
      <=> ! [B: $i,C: $i] :
            ( ( ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
              & ( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) )
           => ( B = C ) ) ) ) )).

thf('138',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v4_relat_2 @ X23 )
      | ( X25 = X24 )
      | ~ ( r2_hidden @ ( k4_tarski @ X24 @ X25 ) @ X23 )
      | ~ ( r2_hidden @ ( k4_tarski @ X25 @ X24 ) @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l3_wellord1])).

thf('139',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) ) @ X0 )
      | ( X1
        = ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) )
      | ~ ( v4_relat_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v4_relat_2 @ X0 )
      | ( X1
        = ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) ) @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
    | ~ ( v1_relat_1 @ sk_C_6 )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) )
    | ( sk_A
      = ( sk_C @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) @ ( k1_wellord1 @ sk_C_6 @ sk_A ) ) )
    | ~ ( v4_relat_2 @ sk_C_6 ) ),
    inference('sup-',[status(thm)],['136','140'])).

thf('142',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ) ),
    inference(split,[status(esa)],['28'])).

thf('143',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ),
    inference('sat_resolution*',[status(thm)],['2','109','129'])).

thf('144',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_6 ),
    inference(simpl_trail,[status(thm)],['142','143'])).

thf('145',plain,(
    v1_relat_1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( sk_C @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) @ ( k1_wellord1 @ sk_C_6 @ sk_A ) )
    = sk_B_3 ),
    inference(clc,[status(thm)],['134','135'])).

thf('147',plain,(
    v1_relat_1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    ! [X18: $i] :
      ( ~ ( v2_wellord1 @ X18 )
      | ( v4_relat_2 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('149',plain,
    ( ( v4_relat_2 @ sk_C_6 )
    | ~ ( v2_wellord1 @ sk_C_6 ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    v2_wellord1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v4_relat_2 @ sk_C_6 ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) )
    | ( sk_A = sk_B_3 ) ),
    inference(demod,[status(thm)],['141','144','145','146','151'])).

thf('153',plain,(
    ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_3 ) ) ),
    inference(simpl_trail,[status(thm)],['1','110'])).

thf('154',plain,(
    sk_A = sk_B_3 ),
    inference(clc,[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('156',plain,(
    $false ),
    inference(demod,[status(thm)],['111','154','155'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fXRz2dMYOQ
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:50:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 4.70/4.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.70/4.89  % Solved by: fo/fo7.sh
% 4.70/4.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.70/4.89  % done 4644 iterations in 4.431s
% 4.70/4.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.70/4.89  % SZS output start Refutation
% 4.70/4.89  thf(v1_relat_2_type, type, v1_relat_2: $i > $o).
% 4.70/4.89  thf(sk_C_6_type, type, sk_C_6: $i).
% 4.70/4.89  thf(v8_relat_2_type, type, v8_relat_2: $i > $o).
% 4.70/4.89  thf(v4_relat_2_type, type, v4_relat_2: $i > $o).
% 4.70/4.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.70/4.89  thf(sk_C_5_type, type, sk_C_5: $i > $i > $i).
% 4.70/4.89  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.70/4.89  thf(sk_A_type, type, sk_A: $i).
% 4.70/4.89  thf(v6_relat_2_type, type, v6_relat_2: $i > $o).
% 4.70/4.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.70/4.89  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 4.70/4.89  thf(sk_B_3_type, type, sk_B_3: $i).
% 4.70/4.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.70/4.89  thf(v1_wellord1_type, type, v1_wellord1: $i > $o).
% 4.70/4.89  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 4.70/4.89  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.70/4.89  thf(sk_C_4_type, type, sk_C_4: $i > $i > $i).
% 4.70/4.89  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 4.70/4.89  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 4.70/4.89  thf(t37_wellord1, conjecture,
% 4.70/4.89    (![A:$i,B:$i,C:$i]:
% 4.70/4.89     ( ( v1_relat_1 @ C ) =>
% 4.70/4.89       ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 4.70/4.89           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) =>
% 4.70/4.89         ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 4.70/4.89           ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) ))).
% 4.70/4.89  thf(zf_stmt_0, negated_conjecture,
% 4.70/4.89    (~( ![A:$i,B:$i,C:$i]:
% 4.70/4.89        ( ( v1_relat_1 @ C ) =>
% 4.70/4.89          ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 4.70/4.89              ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) =>
% 4.70/4.89            ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 4.70/4.89              ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) ) )),
% 4.70/4.89    inference('cnf.neg', [status(esa)], [t37_wellord1])).
% 4.70/4.89  thf('0', plain,
% 4.70/4.89      ((~ (r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 4.70/4.89           (k1_wellord1 @ sk_C_6 @ sk_B_3))
% 4.70/4.89        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6))),
% 4.70/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.70/4.89  thf('1', plain,
% 4.70/4.89      ((~ (r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 4.70/4.89           (k1_wellord1 @ sk_C_6 @ sk_B_3)))
% 4.70/4.89         <= (~
% 4.70/4.89             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 4.70/4.89               (k1_wellord1 @ sk_C_6 @ sk_B_3))))),
% 4.70/4.89      inference('split', [status(esa)], ['0'])).
% 4.70/4.89  thf('2', plain,
% 4.70/4.89      (~
% 4.70/4.89       ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 4.70/4.89         (k1_wellord1 @ sk_C_6 @ sk_B_3))) | 
% 4.70/4.89       ~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6))),
% 4.70/4.89      inference('split', [status(esa)], ['0'])).
% 4.70/4.89  thf('3', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_6))),
% 4.70/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.70/4.89  thf(s1_xboole_0__e7_18__wellord1, axiom,
% 4.70/4.89    (![A:$i,B:$i]:
% 4.70/4.89     ( ( v1_relat_1 @ A ) =>
% 4.70/4.89       ( ?[C:$i]:
% 4.70/4.89         ( ![D:$i]:
% 4.70/4.89           ( ( r2_hidden @ D @ C ) <=>
% 4.70/4.89             ( ( r2_hidden @ D @ ( k3_relat_1 @ A ) ) & 
% 4.70/4.89               ( ~( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) ) ))).
% 4.70/4.89  thf('4', plain,
% 4.70/4.89      (![X29 : $i, X30 : $i, X31 : $i]:
% 4.70/4.89         (~ (v1_relat_1 @ X29)
% 4.70/4.89          | (r2_hidden @ X30 @ (sk_C_4 @ X31 @ X29))
% 4.70/4.89          | (r2_hidden @ (k4_tarski @ X30 @ X31) @ X29)
% 4.70/4.89          | ~ (r2_hidden @ X30 @ (k3_relat_1 @ X29)))),
% 4.70/4.89      inference('cnf', [status(esa)], [s1_xboole_0__e7_18__wellord1])).
% 4.70/4.89  thf('5', plain,
% 4.70/4.89      (![X0 : $i]:
% 4.70/4.89         ((r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_6)
% 4.70/4.89          | (r2_hidden @ sk_A @ (sk_C_4 @ X0 @ sk_C_6))
% 4.70/4.89          | ~ (v1_relat_1 @ sk_C_6))),
% 4.70/4.89      inference('sup-', [status(thm)], ['3', '4'])).
% 4.70/4.89  thf('6', plain, ((v1_relat_1 @ sk_C_6)),
% 4.70/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.70/4.89  thf('7', plain,
% 4.70/4.89      (![X0 : $i]:
% 4.70/4.89         ((r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_6)
% 4.70/4.89          | (r2_hidden @ sk_A @ (sk_C_4 @ X0 @ sk_C_6)))),
% 4.70/4.89      inference('demod', [status(thm)], ['5', '6'])).
% 4.70/4.89  thf('8', plain, ((r2_hidden @ sk_B_3 @ (k3_relat_1 @ sk_C_6))),
% 4.70/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.70/4.89  thf('9', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_6))),
% 4.70/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.70/4.89  thf(l4_wellord1, axiom,
% 4.70/4.89    (![A:$i]:
% 4.70/4.89     ( ( v1_relat_1 @ A ) =>
% 4.70/4.89       ( ( v6_relat_2 @ A ) <=>
% 4.70/4.89         ( ![B:$i,C:$i]:
% 4.70/4.89           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 4.70/4.89                ( r2_hidden @ C @ ( k3_relat_1 @ A ) ) & ( ( B ) != ( C ) ) & 
% 4.70/4.89                ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) & 
% 4.70/4.89                ( ~( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) ) ) ) ) ) ))).
% 4.70/4.89  thf('10', plain,
% 4.70/4.89      (![X26 : $i, X27 : $i, X28 : $i]:
% 4.70/4.89         (~ (v6_relat_2 @ X26)
% 4.70/4.89          | ~ (r2_hidden @ X27 @ (k3_relat_1 @ X26))
% 4.70/4.89          | (r2_hidden @ (k4_tarski @ X28 @ X27) @ X26)
% 4.70/4.89          | (r2_hidden @ (k4_tarski @ X27 @ X28) @ X26)
% 4.70/4.89          | ((X27) = (X28))
% 4.70/4.89          | ~ (r2_hidden @ X28 @ (k3_relat_1 @ X26))
% 4.70/4.89          | ~ (v1_relat_1 @ X26))),
% 4.70/4.89      inference('cnf', [status(esa)], [l4_wellord1])).
% 4.70/4.89  thf('11', plain,
% 4.70/4.89      (![X0 : $i]:
% 4.70/4.89         (~ (v1_relat_1 @ sk_C_6)
% 4.70/4.89          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C_6))
% 4.70/4.89          | ((sk_A) = (X0))
% 4.70/4.89          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_6)
% 4.70/4.89          | (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ sk_C_6)
% 4.70/4.89          | ~ (v6_relat_2 @ sk_C_6))),
% 4.70/4.89      inference('sup-', [status(thm)], ['9', '10'])).
% 4.70/4.89  thf('12', plain, ((v1_relat_1 @ sk_C_6)),
% 4.70/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.70/4.89  thf('13', plain, ((v1_relat_1 @ sk_C_6)),
% 4.70/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.70/4.89  thf(d4_wellord1, axiom,
% 4.70/4.89    (![A:$i]:
% 4.70/4.89     ( ( v1_relat_1 @ A ) =>
% 4.70/4.89       ( ( v2_wellord1 @ A ) <=>
% 4.70/4.89         ( ( v1_relat_2 @ A ) & ( v8_relat_2 @ A ) & ( v4_relat_2 @ A ) & 
% 4.70/4.89           ( v6_relat_2 @ A ) & ( v1_wellord1 @ A ) ) ) ))).
% 4.70/4.89  thf('14', plain,
% 4.70/4.89      (![X18 : $i]:
% 4.70/4.89         (~ (v2_wellord1 @ X18) | (v6_relat_2 @ X18) | ~ (v1_relat_1 @ X18))),
% 4.70/4.89      inference('cnf', [status(esa)], [d4_wellord1])).
% 4.70/4.89  thf('15', plain, (((v6_relat_2 @ sk_C_6) | ~ (v2_wellord1 @ sk_C_6))),
% 4.70/4.89      inference('sup-', [status(thm)], ['13', '14'])).
% 4.70/4.89  thf('16', plain, ((v2_wellord1 @ sk_C_6)),
% 4.70/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.70/4.89  thf('17', plain, ((v6_relat_2 @ sk_C_6)),
% 4.70/4.89      inference('demod', [status(thm)], ['15', '16'])).
% 4.70/4.89  thf('18', plain,
% 4.70/4.89      (![X0 : $i]:
% 4.70/4.89         (~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C_6))
% 4.70/4.89          | ((sk_A) = (X0))
% 4.70/4.89          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_6)
% 4.70/4.89          | (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ sk_C_6))),
% 4.70/4.89      inference('demod', [status(thm)], ['11', '12', '17'])).
% 4.70/4.89  thf('19', plain,
% 4.70/4.89      (((r2_hidden @ (k4_tarski @ sk_B_3 @ sk_A) @ sk_C_6)
% 4.70/4.89        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)
% 4.70/4.89        | ((sk_A) = (sk_B_3)))),
% 4.70/4.89      inference('sup-', [status(thm)], ['8', '18'])).
% 4.70/4.89  thf(d1_wellord1, axiom,
% 4.70/4.89    (![A:$i]:
% 4.70/4.89     ( ( v1_relat_1 @ A ) =>
% 4.70/4.89       ( ![B:$i,C:$i]:
% 4.70/4.89         ( ( ( C ) = ( k1_wellord1 @ A @ B ) ) <=>
% 4.70/4.89           ( ![D:$i]:
% 4.70/4.89             ( ( r2_hidden @ D @ C ) <=>
% 4.70/4.89               ( ( ( D ) != ( B ) ) & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) ) ))).
% 4.70/4.89  thf('20', plain,
% 4.70/4.89      (![X13 : $i, X14 : $i, X15 : $i, X17 : $i]:
% 4.70/4.89         (((X15) != (k1_wellord1 @ X14 @ X13))
% 4.70/4.89          | (r2_hidden @ X17 @ X15)
% 4.70/4.89          | ~ (r2_hidden @ (k4_tarski @ X17 @ X13) @ X14)
% 4.70/4.89          | ((X17) = (X13))
% 4.70/4.89          | ~ (v1_relat_1 @ X14))),
% 4.70/4.89      inference('cnf', [status(esa)], [d1_wellord1])).
% 4.70/4.89  thf('21', plain,
% 4.70/4.89      (![X13 : $i, X14 : $i, X17 : $i]:
% 4.70/4.89         (~ (v1_relat_1 @ X14)
% 4.70/4.89          | ((X17) = (X13))
% 4.70/4.89          | ~ (r2_hidden @ (k4_tarski @ X17 @ X13) @ X14)
% 4.70/4.89          | (r2_hidden @ X17 @ (k1_wellord1 @ X14 @ X13)))),
% 4.70/4.89      inference('simplify', [status(thm)], ['20'])).
% 4.70/4.89  thf('22', plain,
% 4.70/4.89      ((((sk_A) = (sk_B_3))
% 4.70/4.89        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)
% 4.70/4.89        | (r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_6 @ sk_A))
% 4.70/4.89        | ((sk_B_3) = (sk_A))
% 4.70/4.89        | ~ (v1_relat_1 @ sk_C_6))),
% 4.70/4.89      inference('sup-', [status(thm)], ['19', '21'])).
% 4.70/4.89  thf('23', plain, ((v1_relat_1 @ sk_C_6)),
% 4.70/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.70/4.89  thf('24', plain,
% 4.70/4.89      ((((sk_A) = (sk_B_3))
% 4.70/4.89        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)
% 4.70/4.89        | (r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_6 @ sk_A))
% 4.70/4.89        | ((sk_B_3) = (sk_A)))),
% 4.70/4.89      inference('demod', [status(thm)], ['22', '23'])).
% 4.70/4.89  thf('25', plain,
% 4.70/4.89      (((r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_6 @ sk_A))
% 4.70/4.89        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)
% 4.70/4.89        | ((sk_A) = (sk_B_3)))),
% 4.70/4.89      inference('simplify', [status(thm)], ['24'])).
% 4.70/4.89  thf('26', plain,
% 4.70/4.89      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6))
% 4.70/4.89         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)))),
% 4.70/4.89      inference('split', [status(esa)], ['0'])).
% 4.70/4.89  thf('27', plain,
% 4.70/4.89      (((((sk_A) = (sk_B_3))
% 4.70/4.89         | (r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_6 @ sk_A))))
% 4.70/4.89         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)))),
% 4.70/4.89      inference('sup-', [status(thm)], ['25', '26'])).
% 4.70/4.89  thf('28', plain,
% 4.70/4.89      (((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 4.70/4.89         (k1_wellord1 @ sk_C_6 @ sk_B_3))
% 4.70/4.89        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6))),
% 4.70/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.70/4.89  thf('29', plain,
% 4.70/4.89      (((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 4.70/4.89         (k1_wellord1 @ sk_C_6 @ sk_B_3)))
% 4.70/4.89         <= (((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 4.70/4.89               (k1_wellord1 @ sk_C_6 @ sk_B_3))))),
% 4.70/4.89      inference('split', [status(esa)], ['28'])).
% 4.70/4.89  thf(d3_tarski, axiom,
% 4.70/4.89    (![A:$i,B:$i]:
% 4.70/4.89     ( ( r1_tarski @ A @ B ) <=>
% 4.70/4.89       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 4.70/4.89  thf('30', plain,
% 4.70/4.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.70/4.89         (~ (r2_hidden @ X0 @ X1)
% 4.70/4.89          | (r2_hidden @ X0 @ X2)
% 4.70/4.89          | ~ (r1_tarski @ X1 @ X2))),
% 4.70/4.89      inference('cnf', [status(esa)], [d3_tarski])).
% 4.70/4.89  thf('31', plain,
% 4.70/4.89      ((![X0 : $i]:
% 4.70/4.89          ((r2_hidden @ X0 @ (k1_wellord1 @ sk_C_6 @ sk_B_3))
% 4.70/4.89           | ~ (r2_hidden @ X0 @ (k1_wellord1 @ sk_C_6 @ sk_A))))
% 4.70/4.89         <= (((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 4.70/4.89               (k1_wellord1 @ sk_C_6 @ sk_B_3))))),
% 4.70/4.89      inference('sup-', [status(thm)], ['29', '30'])).
% 4.70/4.89  thf('32', plain,
% 4.70/4.89      (((((sk_A) = (sk_B_3))
% 4.70/4.89         | (r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_6 @ sk_B_3))))
% 4.70/4.89         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)) & 
% 4.70/4.89             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 4.70/4.89               (k1_wellord1 @ sk_C_6 @ sk_B_3))))),
% 4.70/4.89      inference('sup-', [status(thm)], ['27', '31'])).
% 4.70/4.89  thf('33', plain,
% 4.70/4.89      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 4.70/4.89         (((X15) != (k1_wellord1 @ X14 @ X13))
% 4.70/4.89          | ((X16) != (X13))
% 4.70/4.89          | ~ (r2_hidden @ X16 @ X15)
% 4.70/4.89          | ~ (v1_relat_1 @ X14))),
% 4.70/4.89      inference('cnf', [status(esa)], [d1_wellord1])).
% 4.70/4.89  thf('34', plain,
% 4.70/4.89      (![X13 : $i, X14 : $i]:
% 4.70/4.89         (~ (v1_relat_1 @ X14)
% 4.70/4.89          | ~ (r2_hidden @ X13 @ (k1_wellord1 @ X14 @ X13)))),
% 4.70/4.89      inference('simplify', [status(thm)], ['33'])).
% 4.70/4.89  thf('35', plain,
% 4.70/4.89      (((((sk_A) = (sk_B_3)) | ~ (v1_relat_1 @ sk_C_6)))
% 4.70/4.89         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)) & 
% 4.70/4.89             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 4.70/4.89               (k1_wellord1 @ sk_C_6 @ sk_B_3))))),
% 4.70/4.89      inference('sup-', [status(thm)], ['32', '34'])).
% 4.70/4.89  thf('36', plain, ((v1_relat_1 @ sk_C_6)),
% 4.70/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.70/4.89  thf('37', plain,
% 4.70/4.89      ((((sk_A) = (sk_B_3)))
% 4.70/4.89         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)) & 
% 4.70/4.89             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 4.70/4.89               (k1_wellord1 @ sk_C_6 @ sk_B_3))))),
% 4.70/4.89      inference('demod', [status(thm)], ['35', '36'])).
% 4.70/4.89  thf('38', plain,
% 4.70/4.89      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6))
% 4.70/4.89         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)))),
% 4.70/4.89      inference('split', [status(esa)], ['0'])).
% 4.70/4.89  thf('39', plain,
% 4.70/4.89      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_A) @ sk_C_6))
% 4.70/4.89         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)) & 
% 4.70/4.89             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 4.70/4.89               (k1_wellord1 @ sk_C_6 @ sk_B_3))))),
% 4.70/4.89      inference('sup-', [status(thm)], ['37', '38'])).
% 4.70/4.89  thf('40', plain,
% 4.70/4.89      (((r2_hidden @ sk_A @ (sk_C_4 @ sk_A @ sk_C_6)))
% 4.70/4.89         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)) & 
% 4.70/4.89             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 4.70/4.89               (k1_wellord1 @ sk_C_6 @ sk_B_3))))),
% 4.70/4.89      inference('sup-', [status(thm)], ['7', '39'])).
% 4.70/4.89  thf(t7_ordinal1, axiom,
% 4.70/4.89    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.70/4.89  thf('41', plain,
% 4.70/4.89      (![X10 : $i, X11 : $i]:
% 4.70/4.89         (~ (r2_hidden @ X10 @ X11) | ~ (r1_tarski @ X11 @ X10))),
% 4.70/4.89      inference('cnf', [status(esa)], [t7_ordinal1])).
% 4.70/4.89  thf('42', plain,
% 4.70/4.89      ((~ (r1_tarski @ (sk_C_4 @ sk_A @ sk_C_6) @ sk_A))
% 4.70/4.89         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)) & 
% 4.70/4.89             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 4.70/4.89               (k1_wellord1 @ sk_C_6 @ sk_B_3))))),
% 4.70/4.89      inference('sup-', [status(thm)], ['40', '41'])).
% 4.70/4.89  thf('43', plain,
% 4.70/4.89      (![X1 : $i, X3 : $i]:
% 4.70/4.89         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 4.70/4.89      inference('cnf', [status(esa)], [d3_tarski])).
% 4.70/4.89  thf('44', plain,
% 4.70/4.89      (![X29 : $i, X31 : $i, X32 : $i]:
% 4.70/4.89         (~ (v1_relat_1 @ X29)
% 4.70/4.89          | (r2_hidden @ X32 @ (k3_relat_1 @ X29))
% 4.70/4.89          | ~ (r2_hidden @ X32 @ (sk_C_4 @ X31 @ X29)))),
% 4.70/4.89      inference('cnf', [status(esa)], [s1_xboole_0__e7_18__wellord1])).
% 4.70/4.89  thf('45', plain,
% 4.70/4.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.70/4.89         ((r1_tarski @ (sk_C_4 @ X1 @ X0) @ X2)
% 4.70/4.89          | (r2_hidden @ (sk_C @ X2 @ (sk_C_4 @ X1 @ X0)) @ (k3_relat_1 @ X0))
% 4.70/4.89          | ~ (v1_relat_1 @ X0))),
% 4.70/4.89      inference('sup-', [status(thm)], ['43', '44'])).
% 4.70/4.89  thf('46', plain,
% 4.70/4.89      (![X1 : $i, X3 : $i]:
% 4.70/4.89         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 4.70/4.89      inference('cnf', [status(esa)], [d3_tarski])).
% 4.70/4.89  thf('47', plain,
% 4.70/4.89      (![X0 : $i, X1 : $i]:
% 4.70/4.89         (~ (v1_relat_1 @ X0)
% 4.70/4.89          | (r1_tarski @ (sk_C_4 @ X1 @ X0) @ (k3_relat_1 @ X0))
% 4.70/4.89          | (r1_tarski @ (sk_C_4 @ X1 @ X0) @ (k3_relat_1 @ X0)))),
% 4.70/4.89      inference('sup-', [status(thm)], ['45', '46'])).
% 4.70/4.89  thf('48', plain,
% 4.70/4.89      (![X0 : $i, X1 : $i]:
% 4.70/4.89         ((r1_tarski @ (sk_C_4 @ X1 @ X0) @ (k3_relat_1 @ X0))
% 4.70/4.89          | ~ (v1_relat_1 @ X0))),
% 4.70/4.89      inference('simplify', [status(thm)], ['47'])).
% 4.70/4.89  thf(t10_wellord1, axiom,
% 4.70/4.89    (![A:$i]:
% 4.70/4.89     ( ( v1_relat_1 @ A ) =>
% 4.70/4.89       ( ( v2_wellord1 @ A ) =>
% 4.70/4.89         ( ![B:$i]:
% 4.70/4.89           ( ~( ( r1_tarski @ B @ ( k3_relat_1 @ A ) ) & 
% 4.70/4.89                ( ( B ) != ( k1_xboole_0 ) ) & 
% 4.70/4.89                ( ![C:$i]:
% 4.70/4.89                  ( ~( ( r2_hidden @ C @ B ) & 
% 4.70/4.89                       ( ![D:$i]:
% 4.70/4.89                         ( ( r2_hidden @ D @ B ) =>
% 4.70/4.89                           ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ) ) ) ) ) ) ))).
% 4.70/4.89  thf('49', plain,
% 4.70/4.89      (![X33 : $i, X35 : $i]:
% 4.70/4.89         (~ (v2_wellord1 @ X33)
% 4.70/4.89          | (r2_hidden @ (sk_C_5 @ X35 @ X33) @ X35)
% 4.70/4.89          | ((X35) = (k1_xboole_0))
% 4.70/4.89          | ~ (r1_tarski @ X35 @ (k3_relat_1 @ X33))
% 4.70/4.89          | ~ (v1_relat_1 @ X33))),
% 4.70/4.89      inference('cnf', [status(esa)], [t10_wellord1])).
% 4.70/4.89  thf('50', plain,
% 4.70/4.89      (![X0 : $i, X1 : $i]:
% 4.70/4.89         (~ (v1_relat_1 @ X0)
% 4.70/4.89          | ~ (v1_relat_1 @ X0)
% 4.70/4.89          | ((sk_C_4 @ X1 @ X0) = (k1_xboole_0))
% 4.70/4.89          | (r2_hidden @ (sk_C_5 @ (sk_C_4 @ X1 @ X0) @ X0) @ 
% 4.70/4.89             (sk_C_4 @ X1 @ X0))
% 4.70/4.89          | ~ (v2_wellord1 @ X0))),
% 4.70/4.89      inference('sup-', [status(thm)], ['48', '49'])).
% 4.70/4.89  thf('51', plain,
% 4.70/4.89      (![X0 : $i, X1 : $i]:
% 4.70/4.89         (~ (v2_wellord1 @ X0)
% 4.70/4.89          | (r2_hidden @ (sk_C_5 @ (sk_C_4 @ X1 @ X0) @ X0) @ 
% 4.70/4.89             (sk_C_4 @ X1 @ X0))
% 4.70/4.89          | ((sk_C_4 @ X1 @ X0) = (k1_xboole_0))
% 4.70/4.89          | ~ (v1_relat_1 @ X0))),
% 4.70/4.89      inference('simplify', [status(thm)], ['50'])).
% 4.70/4.89  thf('52', plain,
% 4.70/4.89      ((((sk_A) = (sk_B_3)))
% 4.70/4.89         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)) & 
% 4.70/4.89             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 4.70/4.89               (k1_wellord1 @ sk_C_6 @ sk_B_3))))),
% 4.70/4.89      inference('demod', [status(thm)], ['35', '36'])).
% 4.70/4.89  thf('53', plain,
% 4.70/4.89      (![X0 : $i]:
% 4.70/4.89         ((r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_6)
% 4.70/4.89          | (r2_hidden @ sk_A @ (sk_C_4 @ X0 @ sk_C_6)))),
% 4.70/4.89      inference('demod', [status(thm)], ['5', '6'])).
% 4.70/4.89  thf('54', plain,
% 4.70/4.89      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6))
% 4.70/4.89         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)))),
% 4.70/4.89      inference('split', [status(esa)], ['0'])).
% 4.70/4.89  thf('55', plain,
% 4.70/4.89      (((r2_hidden @ sk_A @ (sk_C_4 @ sk_B_3 @ sk_C_6)))
% 4.70/4.89         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)))),
% 4.70/4.89      inference('sup-', [status(thm)], ['53', '54'])).
% 4.70/4.89  thf('56', plain,
% 4.70/4.89      (![X0 : $i, X1 : $i]:
% 4.70/4.89         ((r1_tarski @ (sk_C_4 @ X1 @ X0) @ (k3_relat_1 @ X0))
% 4.70/4.89          | ~ (v1_relat_1 @ X0))),
% 4.70/4.89      inference('simplify', [status(thm)], ['47'])).
% 4.70/4.89  thf('57', plain,
% 4.70/4.89      (![X33 : $i, X34 : $i, X35 : $i]:
% 4.70/4.89         (~ (v2_wellord1 @ X33)
% 4.70/4.89          | ~ (r2_hidden @ X34 @ X35)
% 4.70/4.89          | (r2_hidden @ (k4_tarski @ (sk_C_5 @ X35 @ X33) @ X34) @ X33)
% 4.70/4.89          | ((X35) = (k1_xboole_0))
% 4.70/4.89          | ~ (r1_tarski @ X35 @ (k3_relat_1 @ X33))
% 4.70/4.89          | ~ (v1_relat_1 @ X33))),
% 4.70/4.89      inference('cnf', [status(esa)], [t10_wellord1])).
% 4.70/4.89  thf('58', plain,
% 4.70/4.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.70/4.89         (~ (v1_relat_1 @ X0)
% 4.70/4.89          | ~ (v1_relat_1 @ X0)
% 4.70/4.89          | ((sk_C_4 @ X1 @ X0) = (k1_xboole_0))
% 4.70/4.89          | (r2_hidden @ 
% 4.70/4.89             (k4_tarski @ (sk_C_5 @ (sk_C_4 @ X1 @ X0) @ X0) @ X2) @ X0)
% 4.70/4.89          | ~ (r2_hidden @ X2 @ (sk_C_4 @ X1 @ X0))
% 4.70/4.89          | ~ (v2_wellord1 @ X0))),
% 4.70/4.89      inference('sup-', [status(thm)], ['56', '57'])).
% 4.70/4.89  thf('59', plain,
% 4.70/4.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.70/4.89         (~ (v2_wellord1 @ X0)
% 4.70/4.89          | ~ (r2_hidden @ X2 @ (sk_C_4 @ X1 @ X0))
% 4.70/4.89          | (r2_hidden @ 
% 4.70/4.89             (k4_tarski @ (sk_C_5 @ (sk_C_4 @ X1 @ X0) @ X0) @ X2) @ X0)
% 4.70/4.89          | ((sk_C_4 @ X1 @ X0) = (k1_xboole_0))
% 4.70/4.89          | ~ (v1_relat_1 @ X0))),
% 4.70/4.89      inference('simplify', [status(thm)], ['58'])).
% 4.70/4.89  thf('60', plain,
% 4.70/4.89      (((~ (v1_relat_1 @ sk_C_6)
% 4.70/4.89         | ((sk_C_4 @ sk_B_3 @ sk_C_6) = (k1_xboole_0))
% 4.70/4.89         | (r2_hidden @ 
% 4.70/4.89            (k4_tarski @ (sk_C_5 @ (sk_C_4 @ sk_B_3 @ sk_C_6) @ sk_C_6) @ sk_A) @ 
% 4.70/4.89            sk_C_6)
% 4.70/4.89         | ~ (v2_wellord1 @ sk_C_6)))
% 4.70/4.89         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)))),
% 4.70/4.89      inference('sup-', [status(thm)], ['55', '59'])).
% 4.70/4.89  thf('61', plain, ((v1_relat_1 @ sk_C_6)),
% 4.70/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.70/4.89  thf('62', plain, ((v2_wellord1 @ sk_C_6)),
% 4.70/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.70/4.89  thf('63', plain,
% 4.70/4.89      (((((sk_C_4 @ sk_B_3 @ sk_C_6) = (k1_xboole_0))
% 4.70/4.89         | (r2_hidden @ 
% 4.70/4.89            (k4_tarski @ (sk_C_5 @ (sk_C_4 @ sk_B_3 @ sk_C_6) @ sk_C_6) @ sk_A) @ 
% 4.70/4.89            sk_C_6)))
% 4.70/4.89         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)))),
% 4.70/4.89      inference('demod', [status(thm)], ['60', '61', '62'])).
% 4.70/4.89  thf('64', plain,
% 4.70/4.89      (![X29 : $i, X31 : $i, X32 : $i]:
% 4.70/4.89         (~ (v1_relat_1 @ X29)
% 4.70/4.89          | ~ (r2_hidden @ (k4_tarski @ X32 @ X31) @ X29)
% 4.70/4.89          | ~ (r2_hidden @ X32 @ (sk_C_4 @ X31 @ X29)))),
% 4.70/4.89      inference('cnf', [status(esa)], [s1_xboole_0__e7_18__wellord1])).
% 4.70/4.89  thf('65', plain,
% 4.70/4.89      (((((sk_C_4 @ sk_B_3 @ sk_C_6) = (k1_xboole_0))
% 4.70/4.89         | ~ (r2_hidden @ (sk_C_5 @ (sk_C_4 @ sk_B_3 @ sk_C_6) @ sk_C_6) @ 
% 4.70/4.89              (sk_C_4 @ sk_A @ sk_C_6))
% 4.70/4.89         | ~ (v1_relat_1 @ sk_C_6)))
% 4.70/4.89         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)))),
% 4.70/4.89      inference('sup-', [status(thm)], ['63', '64'])).
% 4.70/4.89  thf('66', plain, ((v1_relat_1 @ sk_C_6)),
% 4.70/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.70/4.89  thf('67', plain,
% 4.70/4.89      (((((sk_C_4 @ sk_B_3 @ sk_C_6) = (k1_xboole_0))
% 4.70/4.89         | ~ (r2_hidden @ (sk_C_5 @ (sk_C_4 @ sk_B_3 @ sk_C_6) @ sk_C_6) @ 
% 4.70/4.89              (sk_C_4 @ sk_A @ sk_C_6))))
% 4.70/4.89         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)))),
% 4.70/4.89      inference('demod', [status(thm)], ['65', '66'])).
% 4.70/4.89  thf('68', plain,
% 4.70/4.89      (((~ (r2_hidden @ (sk_C_5 @ (sk_C_4 @ sk_A @ sk_C_6) @ sk_C_6) @ 
% 4.70/4.89            (sk_C_4 @ sk_A @ sk_C_6))
% 4.70/4.89         | ((sk_C_4 @ sk_B_3 @ sk_C_6) = (k1_xboole_0))))
% 4.70/4.89         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)) & 
% 4.70/4.89             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 4.70/4.89               (k1_wellord1 @ sk_C_6 @ sk_B_3))))),
% 4.70/4.89      inference('sup-', [status(thm)], ['52', '67'])).
% 4.70/4.89  thf('69', plain,
% 4.70/4.89      ((((sk_A) = (sk_B_3)))
% 4.70/4.89         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)) & 
% 4.70/4.89             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 4.70/4.89               (k1_wellord1 @ sk_C_6 @ sk_B_3))))),
% 4.70/4.89      inference('demod', [status(thm)], ['35', '36'])).
% 4.70/4.89  thf('70', plain,
% 4.70/4.89      (((~ (r2_hidden @ (sk_C_5 @ (sk_C_4 @ sk_A @ sk_C_6) @ sk_C_6) @ 
% 4.70/4.89            (sk_C_4 @ sk_A @ sk_C_6))
% 4.70/4.89         | ((sk_C_4 @ sk_A @ sk_C_6) = (k1_xboole_0))))
% 4.70/4.89         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)) & 
% 4.70/4.89             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 4.70/4.89               (k1_wellord1 @ sk_C_6 @ sk_B_3))))),
% 4.70/4.89      inference('demod', [status(thm)], ['68', '69'])).
% 4.70/4.89  thf('71', plain,
% 4.70/4.89      (((~ (v1_relat_1 @ sk_C_6)
% 4.70/4.89         | ((sk_C_4 @ sk_A @ sk_C_6) = (k1_xboole_0))
% 4.70/4.89         | ~ (v2_wellord1 @ sk_C_6)
% 4.70/4.89         | ((sk_C_4 @ sk_A @ sk_C_6) = (k1_xboole_0))))
% 4.70/4.89         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)) & 
% 4.70/4.89             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 4.70/4.89               (k1_wellord1 @ sk_C_6 @ sk_B_3))))),
% 4.70/4.89      inference('sup-', [status(thm)], ['51', '70'])).
% 4.70/4.89  thf('72', plain, ((v1_relat_1 @ sk_C_6)),
% 4.70/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.70/4.89  thf('73', plain, ((v2_wellord1 @ sk_C_6)),
% 4.70/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.70/4.89  thf('74', plain,
% 4.70/4.89      (((((sk_C_4 @ sk_A @ sk_C_6) = (k1_xboole_0))
% 4.70/4.89         | ((sk_C_4 @ sk_A @ sk_C_6) = (k1_xboole_0))))
% 4.70/4.89         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)) & 
% 4.70/4.89             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 4.70/4.89               (k1_wellord1 @ sk_C_6 @ sk_B_3))))),
% 4.70/4.89      inference('demod', [status(thm)], ['71', '72', '73'])).
% 4.70/4.89  thf('75', plain,
% 4.70/4.89      ((((sk_C_4 @ sk_A @ sk_C_6) = (k1_xboole_0)))
% 4.70/4.89         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)) & 
% 4.70/4.89             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 4.70/4.89               (k1_wellord1 @ sk_C_6 @ sk_B_3))))),
% 4.70/4.89      inference('simplify', [status(thm)], ['74'])).
% 4.70/4.89  thf('76', plain, ((v1_relat_1 @ sk_C_6)),
% 4.70/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.70/4.89  thf(d10_xboole_0, axiom,
% 4.70/4.89    (![A:$i,B:$i]:
% 4.70/4.89     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.70/4.89  thf('77', plain,
% 4.70/4.89      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 4.70/4.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.70/4.89  thf('78', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 4.70/4.89      inference('simplify', [status(thm)], ['77'])).
% 4.70/4.89  thf('79', plain,
% 4.70/4.89      (![X1 : $i, X3 : $i]:
% 4.70/4.89         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 4.70/4.89      inference('cnf', [status(esa)], [d3_tarski])).
% 4.70/4.89  thf('80', plain,
% 4.70/4.89      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 4.70/4.89         (((X15) != (k1_wellord1 @ X14 @ X13))
% 4.70/4.89          | (r2_hidden @ (k4_tarski @ X16 @ X13) @ X14)
% 4.70/4.89          | ~ (r2_hidden @ X16 @ X15)
% 4.70/4.89          | ~ (v1_relat_1 @ X14))),
% 4.70/4.89      inference('cnf', [status(esa)], [d1_wellord1])).
% 4.70/4.89  thf('81', plain,
% 4.70/4.89      (![X13 : $i, X14 : $i, X16 : $i]:
% 4.70/4.89         (~ (v1_relat_1 @ X14)
% 4.70/4.89          | ~ (r2_hidden @ X16 @ (k1_wellord1 @ X14 @ X13))
% 4.70/4.89          | (r2_hidden @ (k4_tarski @ X16 @ X13) @ X14))),
% 4.70/4.89      inference('simplify', [status(thm)], ['80'])).
% 4.70/4.89  thf('82', plain,
% 4.70/4.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.70/4.89         ((r1_tarski @ (k1_wellord1 @ X1 @ X0) @ X2)
% 4.70/4.89          | (r2_hidden @ 
% 4.70/4.89             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X1 @ X0)) @ X0) @ X1)
% 4.70/4.89          | ~ (v1_relat_1 @ X1))),
% 4.70/4.89      inference('sup-', [status(thm)], ['79', '81'])).
% 4.70/4.89  thf(t30_relat_1, axiom,
% 4.70/4.89    (![A:$i,B:$i,C:$i]:
% 4.70/4.89     ( ( v1_relat_1 @ C ) =>
% 4.70/4.89       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 4.70/4.89         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 4.70/4.89           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ))).
% 4.70/4.89  thf('83', plain,
% 4.70/4.89      (![X7 : $i, X8 : $i, X9 : $i]:
% 4.70/4.89         (~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ X9)
% 4.70/4.89          | (r2_hidden @ X8 @ (k3_relat_1 @ X9))
% 4.70/4.89          | ~ (v1_relat_1 @ X9))),
% 4.70/4.89      inference('cnf', [status(esa)], [t30_relat_1])).
% 4.70/4.89  thf('84', plain,
% 4.70/4.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.70/4.89         (~ (v1_relat_1 @ X0)
% 4.70/4.89          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 4.70/4.89          | ~ (v1_relat_1 @ X0)
% 4.70/4.89          | (r2_hidden @ X1 @ (k3_relat_1 @ X0)))),
% 4.70/4.89      inference('sup-', [status(thm)], ['82', '83'])).
% 4.70/4.89  thf('85', plain,
% 4.70/4.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.70/4.89         ((r2_hidden @ X1 @ (k3_relat_1 @ X0))
% 4.70/4.89          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 4.70/4.89          | ~ (v1_relat_1 @ X0))),
% 4.70/4.89      inference('simplify', [status(thm)], ['84'])).
% 4.70/4.89  thf('86', plain,
% 4.70/4.89      (![X10 : $i, X11 : $i]:
% 4.70/4.89         (~ (r2_hidden @ X10 @ X11) | ~ (r1_tarski @ X11 @ X10))),
% 4.70/4.89      inference('cnf', [status(esa)], [t7_ordinal1])).
% 4.70/4.89  thf('87', plain,
% 4.70/4.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.70/4.89         (~ (v1_relat_1 @ X0)
% 4.70/4.89          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 4.70/4.89          | ~ (r1_tarski @ (k3_relat_1 @ X0) @ X1))),
% 4.70/4.89      inference('sup-', [status(thm)], ['85', '86'])).
% 4.70/4.89  thf('88', plain,
% 4.70/4.89      (![X0 : $i, X1 : $i]:
% 4.70/4.89         ((r1_tarski @ (k1_wellord1 @ X0 @ (k3_relat_1 @ X0)) @ X1)
% 4.70/4.89          | ~ (v1_relat_1 @ X0))),
% 4.70/4.89      inference('sup-', [status(thm)], ['78', '87'])).
% 4.70/4.89  thf('89', plain,
% 4.70/4.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.70/4.89         ((r1_tarski @ (k1_wellord1 @ X1 @ X0) @ X2)
% 4.70/4.89          | (r2_hidden @ 
% 4.70/4.89             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X1 @ X0)) @ X0) @ X1)
% 4.70/4.89          | ~ (v1_relat_1 @ X1))),
% 4.70/4.89      inference('sup-', [status(thm)], ['79', '81'])).
% 4.70/4.89  thf('90', plain,
% 4.70/4.89      (![X7 : $i, X8 : $i, X9 : $i]:
% 4.70/4.89         (~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ X9)
% 4.70/4.89          | (r2_hidden @ X7 @ (k3_relat_1 @ X9))
% 4.70/4.89          | ~ (v1_relat_1 @ X9))),
% 4.70/4.89      inference('cnf', [status(esa)], [t30_relat_1])).
% 4.70/4.89  thf('91', plain,
% 4.70/4.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.70/4.89         (~ (v1_relat_1 @ X0)
% 4.70/4.89          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 4.70/4.89          | ~ (v1_relat_1 @ X0)
% 4.70/4.89          | (r2_hidden @ (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1)) @ 
% 4.70/4.89             (k3_relat_1 @ X0)))),
% 4.70/4.89      inference('sup-', [status(thm)], ['89', '90'])).
% 4.70/4.89  thf('92', plain,
% 4.70/4.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.70/4.89         ((r2_hidden @ (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1)) @ 
% 4.70/4.89           (k3_relat_1 @ X0))
% 4.70/4.89          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 4.70/4.89          | ~ (v1_relat_1 @ X0))),
% 4.70/4.89      inference('simplify', [status(thm)], ['91'])).
% 4.70/4.89  thf('93', plain,
% 4.70/4.89      (![X1 : $i, X3 : $i]:
% 4.70/4.89         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 4.70/4.89      inference('cnf', [status(esa)], [d3_tarski])).
% 4.70/4.89  thf('94', plain,
% 4.70/4.89      (![X0 : $i, X1 : $i]:
% 4.70/4.89         (~ (v1_relat_1 @ X0)
% 4.70/4.89          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ (k3_relat_1 @ X0))
% 4.70/4.89          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ (k3_relat_1 @ X0)))),
% 4.70/4.89      inference('sup-', [status(thm)], ['92', '93'])).
% 4.70/4.89  thf('95', plain,
% 4.70/4.89      (![X0 : $i, X1 : $i]:
% 4.70/4.89         ((r1_tarski @ (k1_wellord1 @ X0 @ X1) @ (k3_relat_1 @ X0))
% 4.70/4.89          | ~ (v1_relat_1 @ X0))),
% 4.70/4.89      inference('simplify', [status(thm)], ['94'])).
% 4.70/4.89  thf('96', plain,
% 4.70/4.89      (![X33 : $i, X35 : $i]:
% 4.70/4.89         (~ (v2_wellord1 @ X33)
% 4.70/4.89          | (r2_hidden @ (sk_C_5 @ X35 @ X33) @ X35)
% 4.70/4.89          | ((X35) = (k1_xboole_0))
% 4.70/4.89          | ~ (r1_tarski @ X35 @ (k3_relat_1 @ X33))
% 4.70/4.89          | ~ (v1_relat_1 @ X33))),
% 4.70/4.89      inference('cnf', [status(esa)], [t10_wellord1])).
% 4.70/4.89  thf('97', plain,
% 4.70/4.89      (![X0 : $i, X1 : $i]:
% 4.70/4.89         (~ (v1_relat_1 @ X0)
% 4.70/4.89          | ~ (v1_relat_1 @ X0)
% 4.70/4.89          | ((k1_wellord1 @ X0 @ X1) = (k1_xboole_0))
% 4.70/4.89          | (r2_hidden @ (sk_C_5 @ (k1_wellord1 @ X0 @ X1) @ X0) @ 
% 4.70/4.89             (k1_wellord1 @ X0 @ X1))
% 4.70/4.89          | ~ (v2_wellord1 @ X0))),
% 4.70/4.89      inference('sup-', [status(thm)], ['95', '96'])).
% 4.70/4.89  thf('98', plain,
% 4.70/4.89      (![X0 : $i, X1 : $i]:
% 4.70/4.89         (~ (v2_wellord1 @ X0)
% 4.70/4.89          | (r2_hidden @ (sk_C_5 @ (k1_wellord1 @ X0 @ X1) @ X0) @ 
% 4.70/4.89             (k1_wellord1 @ X0 @ X1))
% 4.70/4.89          | ((k1_wellord1 @ X0 @ X1) = (k1_xboole_0))
% 4.70/4.89          | ~ (v1_relat_1 @ X0))),
% 4.70/4.89      inference('simplify', [status(thm)], ['97'])).
% 4.70/4.89  thf('99', plain,
% 4.70/4.89      (![X10 : $i, X11 : $i]:
% 4.70/4.89         (~ (r2_hidden @ X10 @ X11) | ~ (r1_tarski @ X11 @ X10))),
% 4.70/4.89      inference('cnf', [status(esa)], [t7_ordinal1])).
% 4.70/4.89  thf('100', plain,
% 4.70/4.89      (![X0 : $i, X1 : $i]:
% 4.70/4.89         (~ (v1_relat_1 @ X1)
% 4.70/4.89          | ((k1_wellord1 @ X1 @ X0) = (k1_xboole_0))
% 4.70/4.89          | ~ (v2_wellord1 @ X1)
% 4.70/4.89          | ~ (r1_tarski @ (k1_wellord1 @ X1 @ X0) @ 
% 4.70/4.89               (sk_C_5 @ (k1_wellord1 @ X1 @ X0) @ X1)))),
% 4.70/4.89      inference('sup-', [status(thm)], ['98', '99'])).
% 4.70/4.89  thf('101', plain,
% 4.70/4.89      (![X0 : $i]:
% 4.70/4.89         (~ (v1_relat_1 @ X0)
% 4.70/4.89          | ~ (v2_wellord1 @ X0)
% 4.70/4.89          | ((k1_wellord1 @ X0 @ (k3_relat_1 @ X0)) = (k1_xboole_0))
% 4.70/4.89          | ~ (v1_relat_1 @ X0))),
% 4.70/4.89      inference('sup-', [status(thm)], ['88', '100'])).
% 4.70/4.89  thf('102', plain,
% 4.70/4.89      (![X0 : $i]:
% 4.70/4.89         (((k1_wellord1 @ X0 @ (k3_relat_1 @ X0)) = (k1_xboole_0))
% 4.70/4.89          | ~ (v2_wellord1 @ X0)
% 4.70/4.89          | ~ (v1_relat_1 @ X0))),
% 4.70/4.89      inference('simplify', [status(thm)], ['101'])).
% 4.70/4.89  thf('103', plain,
% 4.70/4.89      (![X0 : $i, X1 : $i]:
% 4.70/4.89         ((r1_tarski @ (k1_wellord1 @ X0 @ (k3_relat_1 @ X0)) @ X1)
% 4.70/4.89          | ~ (v1_relat_1 @ X0))),
% 4.70/4.89      inference('sup-', [status(thm)], ['78', '87'])).
% 4.70/4.89  thf('104', plain,
% 4.70/4.89      (![X0 : $i, X1 : $i]:
% 4.70/4.89         ((r1_tarski @ k1_xboole_0 @ X0)
% 4.70/4.89          | ~ (v1_relat_1 @ X1)
% 4.70/4.89          | ~ (v2_wellord1 @ X1)
% 4.70/4.89          | ~ (v1_relat_1 @ X1))),
% 4.70/4.89      inference('sup+', [status(thm)], ['102', '103'])).
% 4.70/4.89  thf('105', plain,
% 4.70/4.89      (![X0 : $i, X1 : $i]:
% 4.70/4.89         (~ (v2_wellord1 @ X1)
% 4.70/4.89          | ~ (v1_relat_1 @ X1)
% 4.70/4.89          | (r1_tarski @ k1_xboole_0 @ X0))),
% 4.70/4.89      inference('simplify', [status(thm)], ['104'])).
% 4.70/4.89  thf('106', plain,
% 4.70/4.89      (![X0 : $i]: ((r1_tarski @ k1_xboole_0 @ X0) | ~ (v2_wellord1 @ sk_C_6))),
% 4.70/4.89      inference('sup-', [status(thm)], ['76', '105'])).
% 4.70/4.89  thf('107', plain, ((v2_wellord1 @ sk_C_6)),
% 4.70/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.70/4.89  thf('108', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 4.70/4.89      inference('demod', [status(thm)], ['106', '107'])).
% 4.70/4.89  thf('109', plain,
% 4.70/4.89      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)) | 
% 4.70/4.89       ~
% 4.70/4.89       ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 4.70/4.89         (k1_wellord1 @ sk_C_6 @ sk_B_3)))),
% 4.70/4.89      inference('demod', [status(thm)], ['42', '75', '108'])).
% 4.70/4.89  thf('110', plain,
% 4.70/4.89      (~
% 4.70/4.89       ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 4.70/4.89         (k1_wellord1 @ sk_C_6 @ sk_B_3)))),
% 4.70/4.89      inference('sat_resolution*', [status(thm)], ['2', '109'])).
% 4.70/4.89  thf('111', plain,
% 4.70/4.89      (~ (r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 4.70/4.89          (k1_wellord1 @ sk_C_6 @ sk_B_3))),
% 4.70/4.89      inference('simpl_trail', [status(thm)], ['1', '110'])).
% 4.70/4.89  thf('112', plain,
% 4.70/4.89      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6))
% 4.70/4.89         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)))),
% 4.70/4.89      inference('split', [status(esa)], ['28'])).
% 4.70/4.89  thf('113', plain,
% 4.70/4.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.70/4.89         ((r1_tarski @ (k1_wellord1 @ X1 @ X0) @ X2)
% 4.70/4.89          | (r2_hidden @ 
% 4.70/4.89             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X1 @ X0)) @ X0) @ X1)
% 4.70/4.89          | ~ (v1_relat_1 @ X1))),
% 4.70/4.89      inference('sup-', [status(thm)], ['79', '81'])).
% 4.70/4.89  thf(l2_wellord1, axiom,
% 4.70/4.89    (![A:$i]:
% 4.70/4.89     ( ( v1_relat_1 @ A ) =>
% 4.70/4.89       ( ( v8_relat_2 @ A ) <=>
% 4.70/4.89         ( ![B:$i,C:$i,D:$i]:
% 4.70/4.89           ( ( ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) & 
% 4.70/4.89               ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) =>
% 4.70/4.89             ( r2_hidden @ ( k4_tarski @ B @ D ) @ A ) ) ) ) ))).
% 4.70/4.89  thf('114', plain,
% 4.70/4.89      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 4.70/4.89         (~ (v8_relat_2 @ X19)
% 4.70/4.89          | ~ (r2_hidden @ (k4_tarski @ X20 @ X21) @ X19)
% 4.70/4.89          | ~ (r2_hidden @ (k4_tarski @ X21 @ X22) @ X19)
% 4.70/4.89          | (r2_hidden @ (k4_tarski @ X20 @ X22) @ X19)
% 4.70/4.89          | ~ (v1_relat_1 @ X19))),
% 4.70/4.89      inference('cnf', [status(esa)], [l2_wellord1])).
% 4.70/4.89  thf('115', plain,
% 4.70/4.89      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.70/4.89         (~ (v1_relat_1 @ X0)
% 4.70/4.89          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 4.70/4.89          | ~ (v1_relat_1 @ X0)
% 4.70/4.89          | (r2_hidden @ 
% 4.70/4.89             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1)) @ X3) @ X0)
% 4.70/4.89          | ~ (r2_hidden @ (k4_tarski @ X1 @ X3) @ X0)
% 4.70/4.89          | ~ (v8_relat_2 @ X0))),
% 4.70/4.89      inference('sup-', [status(thm)], ['113', '114'])).
% 4.70/4.89  thf('116', plain,
% 4.70/4.89      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.70/4.89         (~ (v8_relat_2 @ X0)
% 4.70/4.89          | ~ (r2_hidden @ (k4_tarski @ X1 @ X3) @ X0)
% 4.70/4.89          | (r2_hidden @ 
% 4.70/4.89             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1)) @ X3) @ X0)
% 4.70/4.89          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 4.70/4.89          | ~ (v1_relat_1 @ X0))),
% 4.70/4.89      inference('simplify', [status(thm)], ['115'])).
% 4.70/4.89  thf('117', plain,
% 4.70/4.89      ((![X0 : $i]:
% 4.70/4.89          (~ (v1_relat_1 @ sk_C_6)
% 4.70/4.89           | (r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ X0)
% 4.70/4.89           | (r2_hidden @ 
% 4.70/4.89              (k4_tarski @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_6 @ sk_A)) @ sk_B_3) @ 
% 4.70/4.89              sk_C_6)
% 4.70/4.89           | ~ (v8_relat_2 @ sk_C_6)))
% 4.70/4.89         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)))),
% 4.70/4.89      inference('sup-', [status(thm)], ['112', '116'])).
% 4.70/4.89  thf('118', plain, ((v1_relat_1 @ sk_C_6)),
% 4.70/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.70/4.89  thf('119', plain, ((v1_relat_1 @ sk_C_6)),
% 4.70/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.70/4.89  thf('120', plain,
% 4.70/4.89      (![X18 : $i]:
% 4.70/4.89         (~ (v2_wellord1 @ X18) | (v8_relat_2 @ X18) | ~ (v1_relat_1 @ X18))),
% 4.70/4.89      inference('cnf', [status(esa)], [d4_wellord1])).
% 4.70/4.89  thf('121', plain, (((v8_relat_2 @ sk_C_6) | ~ (v2_wellord1 @ sk_C_6))),
% 4.70/4.89      inference('sup-', [status(thm)], ['119', '120'])).
% 4.70/4.89  thf('122', plain, ((v2_wellord1 @ sk_C_6)),
% 4.70/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.70/4.89  thf('123', plain, ((v8_relat_2 @ sk_C_6)),
% 4.70/4.89      inference('demod', [status(thm)], ['121', '122'])).
% 4.70/4.89  thf('124', plain,
% 4.70/4.89      ((![X0 : $i]:
% 4.70/4.89          ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ X0)
% 4.70/4.89           | (r2_hidden @ 
% 4.70/4.89              (k4_tarski @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_6 @ sk_A)) @ sk_B_3) @ 
% 4.70/4.89              sk_C_6)))
% 4.70/4.89         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)))),
% 4.70/4.89      inference('demod', [status(thm)], ['117', '118', '123'])).
% 4.70/4.89  thf('125', plain,
% 4.70/4.89      (![X13 : $i, X14 : $i, X17 : $i]:
% 4.70/4.89         (~ (v1_relat_1 @ X14)
% 4.70/4.89          | ((X17) = (X13))
% 4.70/4.89          | ~ (r2_hidden @ (k4_tarski @ X17 @ X13) @ X14)
% 4.70/4.89          | (r2_hidden @ X17 @ (k1_wellord1 @ X14 @ X13)))),
% 4.70/4.89      inference('simplify', [status(thm)], ['20'])).
% 4.70/4.89  thf('126', plain,
% 4.70/4.89      ((![X0 : $i]:
% 4.70/4.89          ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ X0)
% 4.70/4.89           | (r2_hidden @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_6 @ sk_A)) @ 
% 4.70/4.89              (k1_wellord1 @ sk_C_6 @ sk_B_3))
% 4.70/4.89           | ((sk_C @ X0 @ (k1_wellord1 @ sk_C_6 @ sk_A)) = (sk_B_3))
% 4.70/4.89           | ~ (v1_relat_1 @ sk_C_6)))
% 4.70/4.89         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)))),
% 4.70/4.89      inference('sup-', [status(thm)], ['124', '125'])).
% 4.70/4.89  thf('127', plain, ((v1_relat_1 @ sk_C_6)),
% 4.70/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.70/4.89  thf('128', plain,
% 4.70/4.89      ((![X0 : $i]:
% 4.70/4.89          ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ X0)
% 4.70/4.89           | (r2_hidden @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_6 @ sk_A)) @ 
% 4.70/4.89              (k1_wellord1 @ sk_C_6 @ sk_B_3))
% 4.70/4.89           | ((sk_C @ X0 @ (k1_wellord1 @ sk_C_6 @ sk_A)) = (sk_B_3))))
% 4.70/4.89         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)))),
% 4.70/4.89      inference('demod', [status(thm)], ['126', '127'])).
% 4.70/4.89  thf('129', plain,
% 4.70/4.89      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)) | 
% 4.70/4.89       ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 4.70/4.89         (k1_wellord1 @ sk_C_6 @ sk_B_3)))),
% 4.70/4.89      inference('split', [status(esa)], ['28'])).
% 4.70/4.89  thf('130', plain, (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6))),
% 4.70/4.89      inference('sat_resolution*', [status(thm)], ['2', '109', '129'])).
% 4.70/4.89  thf('131', plain,
% 4.70/4.89      (![X0 : $i]:
% 4.70/4.89         ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ X0)
% 4.70/4.89          | (r2_hidden @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_6 @ sk_A)) @ 
% 4.70/4.89             (k1_wellord1 @ sk_C_6 @ sk_B_3))
% 4.70/4.89          | ((sk_C @ X0 @ (k1_wellord1 @ sk_C_6 @ sk_A)) = (sk_B_3)))),
% 4.70/4.89      inference('simpl_trail', [status(thm)], ['128', '130'])).
% 4.70/4.89  thf('132', plain,
% 4.70/4.89      (![X1 : $i, X3 : $i]:
% 4.70/4.89         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 4.70/4.89      inference('cnf', [status(esa)], [d3_tarski])).
% 4.70/4.89  thf('133', plain,
% 4.70/4.89      ((((sk_C @ (k1_wellord1 @ sk_C_6 @ sk_B_3) @ 
% 4.70/4.89          (k1_wellord1 @ sk_C_6 @ sk_A)) = (sk_B_3))
% 4.70/4.89        | (r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 4.70/4.89           (k1_wellord1 @ sk_C_6 @ sk_B_3))
% 4.70/4.89        | (r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 4.70/4.89           (k1_wellord1 @ sk_C_6 @ sk_B_3)))),
% 4.70/4.89      inference('sup-', [status(thm)], ['131', '132'])).
% 4.70/4.89  thf('134', plain,
% 4.70/4.89      (((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 4.70/4.89         (k1_wellord1 @ sk_C_6 @ sk_B_3))
% 4.70/4.89        | ((sk_C @ (k1_wellord1 @ sk_C_6 @ sk_B_3) @ 
% 4.70/4.89            (k1_wellord1 @ sk_C_6 @ sk_A)) = (sk_B_3)))),
% 4.70/4.89      inference('simplify', [status(thm)], ['133'])).
% 4.70/4.89  thf('135', plain,
% 4.70/4.89      (~ (r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 4.70/4.89          (k1_wellord1 @ sk_C_6 @ sk_B_3))),
% 4.70/4.89      inference('simpl_trail', [status(thm)], ['1', '110'])).
% 4.70/4.89  thf('136', plain,
% 4.70/4.89      (((sk_C @ (k1_wellord1 @ sk_C_6 @ sk_B_3) @ (k1_wellord1 @ sk_C_6 @ sk_A))
% 4.70/4.89         = (sk_B_3))),
% 4.70/4.89      inference('clc', [status(thm)], ['134', '135'])).
% 4.70/4.89  thf('137', plain,
% 4.70/4.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.70/4.89         ((r1_tarski @ (k1_wellord1 @ X1 @ X0) @ X2)
% 4.70/4.89          | (r2_hidden @ 
% 4.70/4.89             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X1 @ X0)) @ X0) @ X1)
% 4.70/4.89          | ~ (v1_relat_1 @ X1))),
% 4.70/4.89      inference('sup-', [status(thm)], ['79', '81'])).
% 4.70/4.89  thf(l3_wellord1, axiom,
% 4.70/4.89    (![A:$i]:
% 4.70/4.89     ( ( v1_relat_1 @ A ) =>
% 4.70/4.89       ( ( v4_relat_2 @ A ) <=>
% 4.70/4.89         ( ![B:$i,C:$i]:
% 4.70/4.89           ( ( ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) & 
% 4.70/4.89               ( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) ) =>
% 4.70/4.89             ( ( B ) = ( C ) ) ) ) ) ))).
% 4.70/4.89  thf('138', plain,
% 4.70/4.89      (![X23 : $i, X24 : $i, X25 : $i]:
% 4.70/4.89         (~ (v4_relat_2 @ X23)
% 4.70/4.89          | ((X25) = (X24))
% 4.70/4.89          | ~ (r2_hidden @ (k4_tarski @ X24 @ X25) @ X23)
% 4.70/4.89          | ~ (r2_hidden @ (k4_tarski @ X25 @ X24) @ X23)
% 4.70/4.89          | ~ (v1_relat_1 @ X23))),
% 4.70/4.89      inference('cnf', [status(esa)], [l3_wellord1])).
% 4.70/4.89  thf('139', plain,
% 4.70/4.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.70/4.89         (~ (v1_relat_1 @ X0)
% 4.70/4.89          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 4.70/4.89          | ~ (v1_relat_1 @ X0)
% 4.70/4.89          | ~ (r2_hidden @ 
% 4.70/4.89               (k4_tarski @ X1 @ (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1))) @ X0)
% 4.70/4.89          | ((X1) = (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1)))
% 4.70/4.89          | ~ (v4_relat_2 @ X0))),
% 4.70/4.89      inference('sup-', [status(thm)], ['137', '138'])).
% 4.70/4.89  thf('140', plain,
% 4.70/4.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.70/4.89         (~ (v4_relat_2 @ X0)
% 4.70/4.89          | ((X1) = (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1)))
% 4.70/4.89          | ~ (r2_hidden @ 
% 4.70/4.89               (k4_tarski @ X1 @ (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1))) @ X0)
% 4.70/4.89          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 4.70/4.89          | ~ (v1_relat_1 @ X0))),
% 4.70/4.89      inference('simplify', [status(thm)], ['139'])).
% 4.70/4.89  thf('141', plain,
% 4.70/4.89      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)
% 4.70/4.89        | ~ (v1_relat_1 @ sk_C_6)
% 4.70/4.89        | (r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 4.70/4.89           (k1_wellord1 @ sk_C_6 @ sk_B_3))
% 4.70/4.89        | ((sk_A)
% 4.70/4.89            = (sk_C @ (k1_wellord1 @ sk_C_6 @ sk_B_3) @ 
% 4.70/4.89               (k1_wellord1 @ sk_C_6 @ sk_A)))
% 4.70/4.89        | ~ (v4_relat_2 @ sk_C_6))),
% 4.70/4.89      inference('sup-', [status(thm)], ['136', '140'])).
% 4.70/4.89  thf('142', plain,
% 4.70/4.89      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6))
% 4.70/4.89         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)))),
% 4.70/4.89      inference('split', [status(esa)], ['28'])).
% 4.70/4.89  thf('143', plain, (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6))),
% 4.70/4.89      inference('sat_resolution*', [status(thm)], ['2', '109', '129'])).
% 4.70/4.89  thf('144', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_6)),
% 4.70/4.89      inference('simpl_trail', [status(thm)], ['142', '143'])).
% 4.70/4.89  thf('145', plain, ((v1_relat_1 @ sk_C_6)),
% 4.70/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.70/4.89  thf('146', plain,
% 4.70/4.89      (((sk_C @ (k1_wellord1 @ sk_C_6 @ sk_B_3) @ (k1_wellord1 @ sk_C_6 @ sk_A))
% 4.70/4.89         = (sk_B_3))),
% 4.70/4.89      inference('clc', [status(thm)], ['134', '135'])).
% 4.70/4.89  thf('147', plain, ((v1_relat_1 @ sk_C_6)),
% 4.70/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.70/4.89  thf('148', plain,
% 4.70/4.89      (![X18 : $i]:
% 4.70/4.89         (~ (v2_wellord1 @ X18) | (v4_relat_2 @ X18) | ~ (v1_relat_1 @ X18))),
% 4.70/4.89      inference('cnf', [status(esa)], [d4_wellord1])).
% 4.70/4.89  thf('149', plain, (((v4_relat_2 @ sk_C_6) | ~ (v2_wellord1 @ sk_C_6))),
% 4.70/4.89      inference('sup-', [status(thm)], ['147', '148'])).
% 4.70/4.89  thf('150', plain, ((v2_wellord1 @ sk_C_6)),
% 4.70/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.70/4.89  thf('151', plain, ((v4_relat_2 @ sk_C_6)),
% 4.70/4.89      inference('demod', [status(thm)], ['149', '150'])).
% 4.70/4.89  thf('152', plain,
% 4.70/4.89      (((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 4.70/4.89         (k1_wellord1 @ sk_C_6 @ sk_B_3))
% 4.70/4.89        | ((sk_A) = (sk_B_3)))),
% 4.70/4.89      inference('demod', [status(thm)], ['141', '144', '145', '146', '151'])).
% 4.70/4.89  thf('153', plain,
% 4.70/4.89      (~ (r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 4.70/4.89          (k1_wellord1 @ sk_C_6 @ sk_B_3))),
% 4.70/4.89      inference('simpl_trail', [status(thm)], ['1', '110'])).
% 4.70/4.89  thf('154', plain, (((sk_A) = (sk_B_3))),
% 4.70/4.89      inference('clc', [status(thm)], ['152', '153'])).
% 4.70/4.89  thf('155', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 4.70/4.89      inference('simplify', [status(thm)], ['77'])).
% 4.70/4.89  thf('156', plain, ($false),
% 4.70/4.89      inference('demod', [status(thm)], ['111', '154', '155'])).
% 4.70/4.89  
% 4.70/4.89  % SZS output end Refutation
% 4.70/4.89  
% 4.70/4.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
