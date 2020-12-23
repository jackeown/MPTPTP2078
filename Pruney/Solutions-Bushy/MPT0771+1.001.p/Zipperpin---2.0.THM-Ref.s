%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0771+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.75at5iyU65

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:28 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   36 (  50 expanded)
%              Number of leaves         :   11 (  19 expanded)
%              Depth                    :   10
%              Number of atoms          :  276 ( 464 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t19_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k3_relat_1 @ ( k2_wellord1 @ C @ B ) ) )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_relat_1 @ ( k2_wellord1 @ X5 @ X6 ) ) )
      | ( r2_hidden @ X4 @ ( k3_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t19_wellord1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) ) @ ( k3_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t20_wellord1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ ( k3_relat_1 @ B ) )
        & ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ ( k3_relat_1 @ B ) )
          & ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_wellord1])).

thf('6',plain,
    ( ~ ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ sk_B @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ~ ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ sk_B @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) )
   <= ~ ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ sk_B @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_relat_1 @ ( k2_wellord1 @ X5 @ X6 ) ) )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t19_wellord1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ~ ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ sk_B @ sk_A ) ) @ sk_A )
   <= ~ ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_B )
   <= ~ ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ sk_B @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ sk_B @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('19',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ sk_B @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ sk_B @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['7','19'])).

thf('21',plain,(
    ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['21','22'])).


%------------------------------------------------------------------------------
