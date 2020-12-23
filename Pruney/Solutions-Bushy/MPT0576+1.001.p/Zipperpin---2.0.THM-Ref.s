%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0576+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KdrMy9Vpf0

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   28 (  38 expanded)
%              Number of leaves         :   11 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :  177 ( 347 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(t180_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ! [D: $i] :
          ( ( v1_relat_1 @ D )
         => ( ( ( r1_tarski @ C @ D )
              & ( r1_tarski @ A @ B ) )
           => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ D @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ! [D: $i] :
            ( ( v1_relat_1 @ D )
           => ( ( ( r1_tarski @ C @ D )
                & ( r1_tarski @ A @ B ) )
             => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ D @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t180_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t178_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k10_relat_1 @ X2 @ X0 ) @ ( k10_relat_1 @ X2 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ sk_A ) @ ( k10_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t179_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( r1_tarski @ ( k10_relat_1 @ X4 @ X5 ) @ ( k10_relat_1 @ X3 @ X5 ) )
      | ~ ( r1_tarski @ X4 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t179_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k10_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_relat_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k10_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_C @ X0 ) @ X1 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    $false ),
    inference(demod,[status(thm)],['0','14'])).


%------------------------------------------------------------------------------
