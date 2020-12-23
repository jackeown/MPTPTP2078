%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0611+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KYbJ1qnqoW

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:58 EST 2020

% Result     : Theorem 14.39s
% Output     : Refutation 14.39s
% Verified   : 
% Statistics : Number of formulae       :   55 (  65 expanded)
%              Number of leaves         :   23 (  29 expanded)
%              Depth                    :   12
%              Number of atoms          :  275 ( 377 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_6_type,type,(
    sk_A_6: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_15_type,type,(
    sk_B_15: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(t215_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_xboole_0 @ ( k2_relat_1 @ A @ ( k2_relat_1 @ B ) ) )
           => ( r1_xboole_0 @ ( A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_xboole_0 @ ( k2_relat_1 @ A @ ( k2_relat_1 @ B ) ) )
             => ( r1_xboole_0 @ ( A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t215_relat_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( sk_A_6 @ sk_B_15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ ( A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X2162: $i,X2163: $i] :
      ( ~ ( v1_relat_1 @ X2162 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ ( X2162 @ X2163 ) ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('2',plain,(
    r1_xboole_0 @ ( k2_relat_1 @ sk_A_6 @ ( k2_relat_1 @ sk_B_15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
    <=> ( ( k3_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('4',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('5',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_A_6 @ ( k2_relat_1 @ sk_B_15 ) ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t27_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ ( A @ B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ A @ ( k2_relat_1 @ B ) ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X2484: $i,X2485: $i] :
      ( ~ ( v1_relat_1 @ X2484 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ ( X2485 @ X2484 ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ X2485 @ ( k2_relat_1 @ X2484 ) ) ) ) )
      | ~ ( v1_relat_1 @ X2485 ) ) ),
    inference(cnf,[status(esa)],[t27_relat_1])).

thf('8',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ ( sk_A_6 @ sk_B_15 ) ) @ o_0_0_xboole_0 ) )
    | ~ ( v1_relat_1 @ sk_A_6 )
    | ~ ( v1_relat_1 @ sk_B_15 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_A_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_relat_1 @ sk_B_15 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ ( sk_A_6 @ sk_B_15 ) ) @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ ( A @ k1_xboole_0 ) )
     => ( A = k1_xboole_0 ) ) )).

thf('12',plain,(
    ! [X245: $i] :
      ( ( X245 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X245 @ k1_xboole_0 ) ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('13',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('14',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('15',plain,(
    ! [X245: $i] :
      ( ( X245 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X245 @ o_0_0_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,
    ( ( k2_relat_1 @ ( k3_xboole_0 @ ( sk_A_6 @ sk_B_15 ) ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['11','15'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X2182: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X2182 ) )
      | ~ ( v1_relat_1 @ X2182 )
      | ( v1_xboole_0 @ X2182 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('18',plain,
    ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
    | ( v1_xboole_0 @ ( k3_xboole_0 @ ( sk_A_6 @ sk_B_15 ) ) )
    | ~ ( v1_relat_1 @ ( k3_xboole_0 @ ( sk_A_6 @ sk_B_15 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('19',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( k3_xboole_0 @ ( sk_A_6 @ sk_B_15 ) ) )
    | ~ ( v1_relat_1 @ ( k3_xboole_0 @ ( sk_A_6 @ sk_B_15 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ sk_A_6 )
    | ( v1_xboole_0 @ ( k3_xboole_0 @ ( sk_A_6 @ sk_B_15 ) ) ) ),
    inference('sup-',[status(thm)],['1','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_A_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_xboole_0 @ ( k3_xboole_0 @ ( sk_A_6 @ sk_B_15 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ ( C @ B ) )
              & ( r2_hidden @ ( C @ A ) ) )
          & ( r1_xboole_0 @ ( A @ B ) ) )
      & ~ ( ~ ( r1_xboole_0 @ ( A @ B ) )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ ( C @ A ) )
                & ( r2_hidden @ ( C @ B ) ) ) ) ) )).

thf('24',plain,(
    ! [X58: $i,X59: $i] :
      ( ( r1_xboole_0 @ ( X58 @ X59 ) )
      | ( r2_hidden @ ( sk_C_2 @ ( X59 @ X58 ) @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ ( B @ A ) ) ) )).

thf('25',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ ( X10 @ X11 ) )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t75_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( r1_xboole_0 @ ( A @ B ) )
        & ( r1_xboole_0 @ ( k3_xboole_0 @ ( A @ B ) @ B ) ) ) )).

thf('27',plain,(
    ! [X348: $i,X349: $i] :
      ( ( r1_xboole_0 @ ( X348 @ X349 ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ ( X348 @ X349 ) @ X349 ) ) ) ),
    inference(cnf,[status(esa)],[t75_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ ( X1 @ X0 ) ) )
      | ( r1_xboole_0 @ ( X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r1_xboole_0 @ ( sk_A_6 @ sk_B_15 ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['0','29'])).

%------------------------------------------------------------------------------
