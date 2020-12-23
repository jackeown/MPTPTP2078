%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0616+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8r8iKxaBKJ

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:58 EST 2020

% Result     : Theorem 25.11s
% Output     : Refutation 25.11s
% Verified   : 
% Statistics : Number of formulae       :   49 (  86 expanded)
%              Number of leaves         :   13 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :  448 (1070 expanded)
%              Number of equality atoms :   25 (  60 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_16_type,type,(
    sk_B_16: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_7_type,type,(
    sk_A_7: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_37_type,type,(
    sk_C_37: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t8_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ ( A @ B ) @ C ) )
      <=> ( ( r2_hidden @ ( A @ ( k1_relat_1 @ C ) ) )
          & ( B
            = ( k1_funct_1 @ ( C @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ ( k4_tarski @ ( A @ B ) @ C ) )
        <=> ( ( r2_hidden @ ( A @ ( k1_relat_1 @ C ) ) )
            & ( B
              = ( k1_funct_1 @ ( C @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_funct_1])).

thf('0',plain,
    ( ( r2_hidden @ ( sk_A_7 @ ( k1_relat_1 @ sk_C_37 ) ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_A_7 @ sk_B_16 ) @ sk_C_37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( sk_A_7 @ ( k1_relat_1 @ sk_C_37 ) ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_A_7 @ sk_B_16 ) @ sk_C_37 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_B_16
     != ( k1_funct_1 @ ( sk_C_37 @ sk_A_7 ) ) )
    | ~ ( r2_hidden @ ( sk_A_7 @ ( k1_relat_1 @ sk_C_37 ) ) )
    | ~ ( r2_hidden @ ( k4_tarski @ ( sk_A_7 @ sk_B_16 ) @ sk_C_37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r2_hidden @ ( sk_A_7 @ ( k1_relat_1 @ sk_C_37 ) ) )
    | ( sk_B_16
     != ( k1_funct_1 @ ( sk_C_37 @ sk_A_7 ) ) )
    | ~ ( r2_hidden @ ( k4_tarski @ ( sk_A_7 @ sk_B_16 ) @ sk_C_37 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( sk_B_16
      = ( k1_funct_1 @ ( sk_C_37 @ sk_A_7 ) ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_A_7 @ sk_B_16 ) @ sk_C_37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( sk_B_16
      = ( k1_funct_1 @ ( sk_C_37 @ sk_A_7 ) ) )
   <= ( sk_B_16
      = ( k1_funct_1 @ ( sk_C_37 @ sk_A_7 ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( r2_hidden @ ( sk_A_7 @ ( k1_relat_1 @ sk_C_37 ) ) )
   <= ( r2_hidden @ ( sk_A_7 @ ( k1_relat_1 @ sk_C_37 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ ( B @ ( k1_relat_1 @ A ) ) )
           => ( ( C
                = ( k1_funct_1 @ ( A @ B ) ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ ( B @ ( k1_relat_1 @ A ) ) )
           => ( ( C
                = ( k1_funct_1 @ ( A @ B ) ) )
            <=> ( r2_hidden @ ( k4_tarski @ ( B @ C ) @ A ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X2617: $i,X2618: $i,X2620: $i] :
      ( ~ ( r2_hidden @ ( X2617 @ ( k1_relat_1 @ X2618 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( X2617 @ X2620 ) @ X2618 ) )
      | ( X2620
       != ( k1_funct_1 @ ( X2618 @ X2617 ) ) )
      | ~ ( v1_funct_1 @ X2618 )
      | ~ ( v1_relat_1 @ X2618 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('8',plain,(
    ! [X2617: $i,X2618: $i] :
      ( ~ ( v1_relat_1 @ X2618 )
      | ~ ( v1_funct_1 @ X2618 )
      | ( r2_hidden @ ( k4_tarski @ ( X2617 @ ( k1_funct_1 @ ( X2618 @ X2617 ) ) ) @ X2618 ) )
      | ~ ( r2_hidden @ ( X2617 @ ( k1_relat_1 @ X2618 ) ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_A_7 @ ( k1_funct_1 @ ( sk_C_37 @ sk_A_7 ) ) ) @ sk_C_37 ) )
      | ~ ( v1_funct_1 @ sk_C_37 )
      | ~ ( v1_relat_1 @ sk_C_37 ) )
   <= ( r2_hidden @ ( sk_A_7 @ ( k1_relat_1 @ sk_C_37 ) ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_C_37 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_relat_1 @ sk_C_37 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_A_7 @ ( k1_funct_1 @ ( sk_C_37 @ sk_A_7 ) ) ) @ sk_C_37 ) )
   <= ( r2_hidden @ ( sk_A_7 @ ( k1_relat_1 @ sk_C_37 ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_A_7 @ sk_B_16 ) @ sk_C_37 ) )
   <= ( ( r2_hidden @ ( sk_A_7 @ ( k1_relat_1 @ sk_C_37 ) ) )
      & ( sk_B_16
        = ( k1_funct_1 @ ( sk_C_37 @ sk_A_7 ) ) ) ) ),
    inference('sup+',[status(thm)],['5','12'])).

thf('14',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_A_7 @ sk_B_16 ) @ sk_C_37 ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ ( sk_A_7 @ sk_B_16 ) @ sk_C_37 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('15',plain,
    ( ~ ( r2_hidden @ ( sk_A_7 @ ( k1_relat_1 @ sk_C_37 ) ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_A_7 @ sk_B_16 ) @ sk_C_37 ) )
    | ( sk_B_16
     != ( k1_funct_1 @ ( sk_C_37 @ sk_A_7 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_A_7 @ sk_B_16 ) @ sk_C_37 ) )
    | ( sk_B_16
      = ( k1_funct_1 @ ( sk_C_37 @ sk_A_7 ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('17',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_A_7 @ sk_B_16 ) @ sk_C_37 ) )
   <= ( r2_hidden @ ( k4_tarski @ ( sk_A_7 @ sk_B_16 ) @ sk_C_37 ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ B ) )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ ( C @ D ) @ A ) ) ) ) )).

thf('18',plain,(
    ! [X2104: $i,X2105: $i,X2106: $i,X2107: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( X2104 @ X2105 ) @ X2106 ) )
      | ( r2_hidden @ ( X2104 @ X2107 ) )
      | ( X2107
       != ( k1_relat_1 @ X2106 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('19',plain,(
    ! [X2104: $i,X2105: $i,X2106: $i] :
      ( ( r2_hidden @ ( X2104 @ ( k1_relat_1 @ X2106 ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( X2104 @ X2105 ) @ X2106 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( r2_hidden @ ( sk_A_7 @ ( k1_relat_1 @ sk_C_37 ) ) )
   <= ( r2_hidden @ ( k4_tarski @ ( sk_A_7 @ sk_B_16 ) @ sk_C_37 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,
    ( ~ ( r2_hidden @ ( sk_A_7 @ ( k1_relat_1 @ sk_C_37 ) ) )
   <= ~ ( r2_hidden @ ( sk_A_7 @ ( k1_relat_1 @ sk_C_37 ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('22',plain,
    ( ( r2_hidden @ ( sk_A_7 @ ( k1_relat_1 @ sk_C_37 ) ) )
    | ~ ( r2_hidden @ ( k4_tarski @ ( sk_A_7 @ sk_B_16 ) @ sk_C_37 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_A_7 @ sk_B_16 ) @ sk_C_37 ) )
   <= ( r2_hidden @ ( k4_tarski @ ( sk_A_7 @ sk_B_16 ) @ sk_C_37 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,
    ( ( r2_hidden @ ( sk_A_7 @ ( k1_relat_1 @ sk_C_37 ) ) )
   <= ( r2_hidden @ ( sk_A_7 @ ( k1_relat_1 @ sk_C_37 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('25',plain,(
    ! [X2617: $i,X2618: $i,X2620: $i] :
      ( ~ ( r2_hidden @ ( X2617 @ ( k1_relat_1 @ X2618 ) ) )
      | ( X2620
        = ( k1_funct_1 @ ( X2618 @ X2617 ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( X2617 @ X2620 ) @ X2618 ) )
      | ~ ( v1_funct_1 @ X2618 )
      | ~ ( v1_relat_1 @ X2618 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_C_37 )
        | ~ ( v1_funct_1 @ sk_C_37 )
        | ~ ( r2_hidden @ ( k4_tarski @ ( sk_A_7 @ X0 ) @ sk_C_37 ) )
        | ( X0
          = ( k1_funct_1 @ ( sk_C_37 @ sk_A_7 ) ) ) )
   <= ( r2_hidden @ ( sk_A_7 @ ( k1_relat_1 @ sk_C_37 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C_37 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_C_37 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_A_7 @ X0 ) @ sk_C_37 ) )
        | ( X0
          = ( k1_funct_1 @ ( sk_C_37 @ sk_A_7 ) ) ) )
   <= ( r2_hidden @ ( sk_A_7 @ ( k1_relat_1 @ sk_C_37 ) ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ( sk_B_16
      = ( k1_funct_1 @ ( sk_C_37 @ sk_A_7 ) ) )
   <= ( ( r2_hidden @ ( k4_tarski @ ( sk_A_7 @ sk_B_16 ) @ sk_C_37 ) )
      & ( r2_hidden @ ( sk_A_7 @ ( k1_relat_1 @ sk_C_37 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','29'])).

thf('31',plain,
    ( ( sk_B_16
     != ( k1_funct_1 @ ( sk_C_37 @ sk_A_7 ) ) )
   <= ( sk_B_16
     != ( k1_funct_1 @ ( sk_C_37 @ sk_A_7 ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('32',plain,
    ( ( sk_B_16 != sk_B_16 )
   <= ( ( sk_B_16
       != ( k1_funct_1 @ ( sk_C_37 @ sk_A_7 ) ) )
      & ( r2_hidden @ ( k4_tarski @ ( sk_A_7 @ sk_B_16 ) @ sk_C_37 ) )
      & ( r2_hidden @ ( sk_A_7 @ ( k1_relat_1 @ sk_C_37 ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( r2_hidden @ ( sk_A_7 @ ( k1_relat_1 @ sk_C_37 ) ) )
    | ~ ( r2_hidden @ ( k4_tarski @ ( sk_A_7 @ sk_B_16 ) @ sk_C_37 ) )
    | ( sk_B_16
      = ( k1_funct_1 @ ( sk_C_37 @ sk_A_7 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','15','16','22','33'])).

%------------------------------------------------------------------------------
