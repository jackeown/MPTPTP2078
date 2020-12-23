%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0672+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.y1BNzfvFuE

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   31 (  45 expanded)
%              Number of leaves         :   10 (  16 expanded)
%              Depth                    :   11
%              Number of atoms          :  288 ( 624 expanded)
%              Number of equality atoms :   27 (  55 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(t97_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r1_tarski @ A @ B )
       => ( ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) )
            = ( k8_relat_1 @ A @ C ) )
          & ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) )
            = ( k8_relat_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r1_tarski @ A @ B )
         => ( ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) )
              = ( k8_relat_1 @ A @ C ) )
            & ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) )
              = ( k8_relat_1 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t97_funct_1])).

thf('0',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t130_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) )
          = ( k8_relat_1 @ A @ C ) ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X5 )
      | ( ( k8_relat_1 @ X3 @ ( k8_relat_1 @ X4 @ X5 ) )
        = ( k8_relat_1 @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t130_relat_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ X0 ) )
        = ( k8_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
    | ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
   <= ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t129_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) )
          = ( k8_relat_1 @ A @ C ) ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ X2 ) )
        = ( k8_relat_1 @ X0 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t129_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ X0 ) )
        = ( k8_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
   <= ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('9',plain,
    ( ( ( ( k8_relat_1 @ sk_A @ sk_C )
       != ( k8_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k8_relat_1 @ sk_A @ sk_C )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
   <= ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
    = ( k8_relat_1 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
    | ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('14',plain,(
    ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C ) )
 != ( k8_relat_1 @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['12','13'])).

thf('15',plain,(
    ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C ) )
 != ( k8_relat_1 @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['4','14'])).

thf('16',plain,
    ( ( ( k8_relat_1 @ sk_A @ sk_C )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ( k8_relat_1 @ sk_A @ sk_C )
 != ( k8_relat_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    $false ),
    inference(simplify,[status(thm)],['18'])).


%------------------------------------------------------------------------------
