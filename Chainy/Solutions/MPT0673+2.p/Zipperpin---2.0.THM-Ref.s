%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0673+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hGdCKiiKFL

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:59 EST 2020

% Result     : Theorem 41.65s
% Output     : Refutation 41.65s
% Verified   : 
% Statistics : Number of formulae       :   29 (  35 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :  160 ( 220 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_24_type,type,(
    sk_B_24: $i )).

thf(sk_A_8_type,type,(
    sk_A_8: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ ( A @ B ) )
        = ( k5_relat_1 @ ( B @ ( k6_relat_1 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X2245: $i,X2246: $i] :
      ( ( ( k8_relat_1 @ ( X2246 @ X2245 ) )
        = ( k5_relat_1 @ ( X2245 @ ( k6_relat_1 @ X2246 ) ) ) )
      | ~ ( v1_relat_1 @ X2245 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(fc7_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A )
        & ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B )
        & ( v2_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k5_relat_1 @ ( A @ B ) ) )
        & ( v2_funct_1 @ ( k5_relat_1 @ ( A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X2654: $i,X2655: $i] :
      ( ~ ( v2_funct_1 @ X2654 )
      | ~ ( v1_funct_1 @ X2654 )
      | ~ ( v1_relat_1 @ X2654 )
      | ~ ( v1_relat_1 @ X2655 )
      | ~ ( v1_funct_1 @ X2655 )
      | ~ ( v2_funct_1 @ X2655 )
      | ( v2_funct_1 @ ( k5_relat_1 @ ( X2654 @ X2655 ) ) ) ) ),
    inference(cnf,[status(esa)],[fc7_funct_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_funct_1 @ ( k8_relat_1 @ ( X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X2651: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X2651 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X2649: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X2649 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X2135: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2135 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_funct_1 @ ( k8_relat_1 @ ( X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['2','3','4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_1 @ ( k8_relat_1 @ ( X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t99_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( v2_funct_1 @ ( k8_relat_1 @ ( A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( v2_funct_1 @ B )
         => ( v2_funct_1 @ ( k8_relat_1 @ ( A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t99_funct_1])).

thf('8',plain,(
    ~ ( v2_funct_1 @ ( k8_relat_1 @ ( sk_A_8 @ sk_B_24 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_B_24 )
    | ~ ( v1_funct_1 @ sk_B_24 )
    | ~ ( v2_funct_1 @ sk_B_24 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_B_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_B_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v2_funct_1 @ sk_B_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    $false ),
    inference(demod,[status(thm)],['9','10','11','12'])).

%------------------------------------------------------------------------------
