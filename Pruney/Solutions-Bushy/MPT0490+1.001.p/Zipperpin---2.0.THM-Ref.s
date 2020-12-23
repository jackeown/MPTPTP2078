%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0490+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xwzP1AIYHW

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:00 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   31 (  35 expanded)
%              Number of leaves         :   13 (  16 expanded)
%              Depth                    :   11
%              Number of atoms          :  272 ( 307 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X6 @ X7 ) @ ( sk_D_1 @ X6 @ X7 ) ) @ X7 )
      | ( r1_tarski @ X7 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf(d11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( C
              = ( k7_relat_1 @ A @ B ) )
          <=> ! [D: $i,E: $i] :
                ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
              <=> ( ( r2_hidden @ D @ B )
                  & ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
       != ( k7_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d11_relat_1])).

thf('3',plain,(
    ! [X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k7_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ X1 )
      | ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ X1 )
      | ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X6 @ X7 ) @ ( sk_D_1 @ X6 @ X7 ) ) @ X6 )
      | ( r1_tarski @ X7 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ X1 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(t88_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t88_relat_1])).

thf('13',plain,(
    ~ ( r1_tarski @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    $false ),
    inference(demod,[status(thm)],['14','15'])).


%------------------------------------------------------------------------------
