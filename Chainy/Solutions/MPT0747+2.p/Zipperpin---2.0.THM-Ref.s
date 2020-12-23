%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0747+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qUJhOwc1wL

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:00 EST 2020

% Result     : Theorem 1.81s
% Output     : Refutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   32 (  36 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :  120 ( 146 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_14_type,type,(
    sk_A_14: $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_40_type,type,(
    zip_tseitin_40: $i > $i > $o )).

thf(sk_B_35_type,type,(
    sk_B_35: $i > $i )).

thf(zip_tseitin_39_type,type,(
    zip_tseitin_39: $i > $i > $o )).

thf(sk_B_34_type,type,(
    sk_B_34: $i > $i )).

thf(t36_ordinal1,axiom,(
    ! [A: $i] :
      ~ ( ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ~ ( r1_tarski @ ( A @ B ) ) )
        & ! [B: $i] :
            ( ( r2_hidden @ ( B @ A ) )
           => ( v3_ordinal1 @ B ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( r2_hidden @ ( B @ A ) )
       => ( v3_ordinal1 @ B ) )
     => ( zip_tseitin_40 @ ( B @ A ) ) ) )).

thf('0',plain,(
    ! [X3126: $i,X3127: $i] :
      ( ( zip_tseitin_40 @ ( X3126 @ X3127 ) )
      | ( r2_hidden @ ( X3126 @ X3127 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t37_ordinal1,conjecture,(
    ! [A: $i] :
      ~ ! [B: $i] :
          ( ( r2_hidden @ ( B @ A ) )
        <=> ( v3_ordinal1 @ B ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i] :
        ~ ! [B: $i] :
            ( ( r2_hidden @ ( B @ A ) )
          <=> ( v3_ordinal1 @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t37_ordinal1])).

thf('1',plain,(
    ! [X3129: $i] :
      ( ( v3_ordinal1 @ X3129 )
      | ~ ( r2_hidden @ ( X3129 @ sk_A_14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_40 @ ( X0 @ sk_A_14 ) )
      | ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X3126: $i,X3127: $i] :
      ( ( zip_tseitin_40 @ ( X3126 @ X3127 ) )
      | ~ ( v3_ordinal1 @ X3126 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( zip_tseitin_40 @ ( X0 @ sk_A_14 ) ) ),
    inference(clc,[status(thm)],['2','3'])).

thf(zf_stmt_2,type,(
    zip_tseitin_40: $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_39: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( v3_ordinal1 @ B )
       => ~ ( r1_tarski @ ( A @ B ) ) )
     => ( zip_tseitin_39 @ ( B @ A ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i] :
      ~ ( ! [B: $i] :
            ( zip_tseitin_40 @ ( B @ A ) )
        & ! [B: $i] :
            ( zip_tseitin_39 @ ( B @ A ) ) ) )).

thf('5',plain,(
    ! [X3128: $i] :
      ( ~ ( zip_tseitin_40 @ ( sk_B_34 @ X3128 @ X3128 ) )
      | ~ ( zip_tseitin_39 @ ( sk_B_35 @ X3128 @ X3128 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,(
    ~ ( zip_tseitin_39 @ ( sk_B_35 @ sk_A_14 @ sk_A_14 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X3124: $i,X3125: $i] :
      ( ( zip_tseitin_39 @ ( X3124 @ X3125 ) )
      | ( r1_tarski @ ( X3125 @ X3124 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('8',plain,(
    ! [X3130: $i] :
      ( ( r2_hidden @ ( X3130 @ sk_A_14 ) )
      | ~ ( v3_ordinal1 @ X3130 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ ( A @ B ) )
        & ( r1_tarski @ ( B @ A ) ) ) )).

thf('9',plain,(
    ! [X3149: $i,X3150: $i] :
      ( ~ ( r2_hidden @ ( X3149 @ X3150 ) )
      | ~ ( r1_tarski @ ( X3150 @ X3149 ) ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ ( sk_A_14 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_39 @ ( X0 @ sk_A_14 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X3124: $i,X3125: $i] :
      ( ( zip_tseitin_39 @ ( X3124 @ X3125 ) )
      | ( v3_ordinal1 @ X3124 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('13',plain,(
    ! [X0: $i] :
      ( zip_tseitin_39 @ ( X0 @ sk_A_14 ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    $false ),
    inference(demod,[status(thm)],['6','13'])).

%------------------------------------------------------------------------------
