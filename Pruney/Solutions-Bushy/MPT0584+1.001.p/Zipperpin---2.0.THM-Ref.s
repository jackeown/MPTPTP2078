%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0584+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sgvJqVCc48

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:09 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   33 (  48 expanded)
%              Number of leaves         :   12 (  20 expanded)
%              Depth                    :   10
%              Number of atoms          :  225 ( 474 expanded)
%              Number of equality atoms :   23 (  47 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t188_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i,D: $i] :
              ( ( ( r1_tarski @ C @ D )
                & ( ( k7_relat_1 @ A @ D )
                  = ( k7_relat_1 @ B @ D ) ) )
             => ( ( k7_relat_1 @ A @ C )
                = ( k7_relat_1 @ B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ! [C: $i,D: $i] :
                ( ( ( r1_tarski @ C @ D )
                  & ( ( k7_relat_1 @ A @ D )
                    = ( k7_relat_1 @ B @ D ) ) )
               => ( ( k7_relat_1 @ A @ C )
                  = ( k7_relat_1 @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t188_relat_1])).

thf('0',plain,(
    r1_tarski @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('2',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = sk_C ),
    inference('sup-',[status(thm)],['0','1'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X3 ) @ X4 )
        = ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('5',plain,
    ( ( k7_relat_1 @ sk_A @ sk_D )
    = ( k7_relat_1 @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X3 ) @ X4 )
        = ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ sk_A @ sk_D ) @ X0 )
        = ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ sk_D @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ sk_A @ sk_D ) @ X0 )
      = ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ sk_D @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ sk_D @ X0 ) )
        = ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ sk_D @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ sk_D @ X0 ) )
      = ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ sk_D @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ sk_D @ X0 ) )
      = ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['3','12'])).

thf('14',plain,
    ( ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ sk_D @ sk_C ) )
    = ( k7_relat_1 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['2','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('16',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = sk_C ),
    inference('sup-',[status(thm)],['0','1'])).

thf('17',plain,
    ( ( k7_relat_1 @ sk_A @ sk_C )
    = ( k7_relat_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ( k7_relat_1 @ sk_A @ sk_C )
 != ( k7_relat_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).


%------------------------------------------------------------------------------
