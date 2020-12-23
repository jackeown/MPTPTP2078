%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0457+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.B0xkNxsDBM

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:56 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :   38 (  44 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :   11
%              Number of atoms          :  399 ( 464 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :   21 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X8 @ X6 ) @ X8 ) @ X6 )
      | ( X7
       != ( k2_relat_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('3',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X8 @ X6 ) @ X8 ) @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k2_relat_1 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf(d8_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( C
                  = ( k5_relat_1 @ A @ B ) )
              <=> ! [D: $i,E: $i] :
                    ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
                  <=> ? [F: $i] :
                        ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B )
                        & ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( X13
       != ( k5_relat_1 @ X12 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X17 @ X14 @ X11 @ X12 ) @ X17 ) @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X17 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('6',plain,(
    ! [X11: $i,X12: $i,X14: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X17 ) @ ( k5_relat_1 @ X12 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X17 @ X14 @ X11 @ X12 ) @ X17 ) @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_C @ X2 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( sk_D_1 @ ( sk_C @ X2 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C @ X2 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_C @ X2 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( sk_D_1 @ ( sk_C @ X2 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C @ X2 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_C @ X2 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( sk_D_1 @ ( sk_C @ X2 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C @ X2 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ( X7
       != ( k2_relat_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('11',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ ( k2_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t45_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t45_relat_1])).

thf('16',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    $false ),
    inference(demod,[status(thm)],['17','18','19'])).


%------------------------------------------------------------------------------
