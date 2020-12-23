%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0748+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y7pmcPqiXA

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:00 EST 2020

% Result     : Theorem 27.78s
% Output     : Refutation 27.78s
% Verified   : 
% Statistics : Number of formulae       :   22 (  29 expanded)
%              Number of leaves         :    8 (  12 expanded)
%              Depth                    :    6
%              Number of atoms          :   98 ( 145 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_B_32_type,type,(
    sk_B_32: $i > $i )).

thf(sk_A_14_type,type,(
    sk_A_14: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_37_type,type,(
    sk_B_37: $i > $i )).

thf(t38_ordinal1,conjecture,(
    ! [A: $i] :
      ~ ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( r2_hidden @ ( B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ~ ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( r2_hidden @ ( B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_ordinal1])).

thf('0',plain,(
    ! [X3133: $i] :
      ( ( r2_hidden @ ( X3133 @ sk_A_14 ) )
      | ~ ( v3_ordinal1 @ X3133 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(s1_xboole_0__e3_53__ordinal1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
    ! [C: $i] :
      ( ( r2_hidden @ ( C @ B ) )
    <=> ( ( r2_hidden @ ( C @ A ) )
        & ( v3_ordinal1 @ C ) ) ) )).

thf('1',plain,(
    ! [X3091: $i,X3092: $i] :
      ( ( r2_hidden @ ( X3092 @ ( sk_B_32 @ X3091 ) ) )
      | ~ ( v3_ordinal1 @ X3092 )
      | ~ ( r2_hidden @ ( X3092 @ X3091 ) ) ) ),
    inference(cnf,[status(esa)],[s1_xboole_0__e3_53__ordinal1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ ( X0 @ ( sk_B_32 @ sk_A_14 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( X0 @ ( sk_B_32 @ sk_A_14 ) ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t37_ordinal1,axiom,(
    ! [A: $i] :
      ~ ! [B: $i] :
          ( ( r2_hidden @ ( B @ A ) )
        <=> ( v3_ordinal1 @ B ) ) )).

thf('4',plain,(
    ! [X3132: $i] :
      ( ( v3_ordinal1 @ ( sk_B_37 @ X3132 ) )
      | ( r2_hidden @ ( sk_B_37 @ X3132 @ X3132 ) ) ) ),
    inference(cnf,[status(esa)],[t37_ordinal1])).

thf('5',plain,(
    ! [X3090: $i,X3091: $i] :
      ( ( v3_ordinal1 @ X3090 )
      | ~ ( r2_hidden @ ( X3090 @ ( sk_B_32 @ X3091 ) ) ) ) ),
    inference(cnf,[status(esa)],[s1_xboole_0__e3_53__ordinal1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v3_ordinal1 @ ( sk_B_37 @ ( sk_B_32 @ X0 ) ) )
      | ( v3_ordinal1 @ ( sk_B_37 @ ( sk_B_32 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( v3_ordinal1 @ ( sk_B_37 @ ( sk_B_32 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X3132: $i] :
      ( ~ ( v3_ordinal1 @ ( sk_B_37 @ X3132 ) )
      | ~ ( r2_hidden @ ( sk_B_37 @ X3132 @ X3132 ) ) ) ),
    inference(cnf,[status(esa)],[t37_ordinal1])).

thf('9',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ ( sk_B_37 @ ( sk_B_32 @ X0 ) @ ( sk_B_32 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v3_ordinal1 @ ( sk_B_37 @ ( sk_B_32 @ sk_A_14 ) ) ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( v3_ordinal1 @ ( sk_B_37 @ ( sk_B_32 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('12',plain,(
    $false ),
    inference(demod,[status(thm)],['10','11'])).

%------------------------------------------------------------------------------
