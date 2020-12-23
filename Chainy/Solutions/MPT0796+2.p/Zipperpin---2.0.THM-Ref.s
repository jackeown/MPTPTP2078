%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0796+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dYIkPuJIOk

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:01 EST 2020

% Result     : Theorem 28.97s
% Output     : Refutation 28.97s
% Verified   : 
% Statistics : Number of formulae       :   24 (  26 expanded)
%              Number of leaves         :   12 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :  110 ( 120 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_14_type,type,(
    sk_A_14: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(r3_wellord1_type,type,(
    r3_wellord1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r4_wellord1_type,type,(
    r4_wellord1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(t47_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r3_wellord1 @ ( A @ ( A @ ( k6_relat_1 @ ( k3_relat_1 @ A ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X3431: $i] :
      ( ( r3_wellord1 @ ( X3431 @ ( X3431 @ ( k6_relat_1 @ ( k3_relat_1 @ X3431 ) ) ) ) )
      | ~ ( v1_relat_1 @ X3431 ) ) ),
    inference(cnf,[status(esa)],[t47_wellord1])).

thf(d8_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r4_wellord1 @ ( A @ B ) )
          <=> ? [C: $i] :
                ( ( r3_wellord1 @ ( A @ ( B @ C ) ) )
                & ( v1_funct_1 @ C )
                & ( v1_relat_1 @ C ) ) ) ) ) )).

thf('1',plain,(
    ! [X3304: $i,X3305: $i,X3306: $i] :
      ( ~ ( v1_relat_1 @ X3304 )
      | ~ ( r3_wellord1 @ ( X3305 @ ( X3304 @ X3306 ) ) )
      | ~ ( v1_funct_1 @ X3306 )
      | ~ ( v1_relat_1 @ X3306 )
      | ( r4_wellord1 @ ( X3305 @ X3304 ) )
      | ~ ( v1_relat_1 @ X3305 ) ) ),
    inference(cnf,[status(esa)],[d8_wellord1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r4_wellord1 @ ( X0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X2135: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2135 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X2692: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X2692 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r4_wellord1 @ ( X0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r4_wellord1 @ ( X0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t48_wellord1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r4_wellord1 @ ( A @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( r4_wellord1 @ ( A @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_wellord1])).

thf('7',plain,(
    ~ ( r4_wellord1 @ ( sk_A_14 @ sk_A_14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ~ ( v1_relat_1 @ sk_A_14 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    $false ),
    inference(demod,[status(thm)],['8','9'])).

%------------------------------------------------------------------------------
