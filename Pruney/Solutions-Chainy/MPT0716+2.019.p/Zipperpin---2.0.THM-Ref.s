%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pvXtZzCWEJ

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:21 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 452 expanded)
%              Number of leaves         :   25 ( 135 expanded)
%              Depth                    :   27
%              Number of atoms          : 1131 (6682 expanded)
%              Number of equality atoms :   34 (  91 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t171_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ! [C: $i] :
              ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) )
            <=> ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) )
                & ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ! [C: $i] :
                ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) )
              <=> ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) )
                  & ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t171_funct_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) ) @ ( k1_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('4',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('7',plain,
    ( ( ( k2_xboole_0 @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
      = ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('9',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) @ X0 )
        | ( r1_tarski @ sk_C @ X0 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('15',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k9_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(fc8_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('17',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t112_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) )).

thf('19',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) @ X11 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) @ X9 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t112_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('21',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('22',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X20 @ ( k1_relat_1 @ X21 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X21 @ X20 ) )
        = X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('23',plain,
    ( ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
        = sk_C ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
        = sk_C ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
      = sk_C )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
        = sk_C )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['19','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
      = sk_C )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf(t27_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k1_relat_1 @ B ) )
           => ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) )).

thf('32',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( r1_tarski @ ( k2_relat_1 @ X24 ) @ ( k1_relat_1 @ X25 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X24 @ X25 ) )
       != ( k1_relat_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t27_funct_1])).

thf('33',plain,
    ( ( ( sk_C
       != ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('35',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X20 @ ( k1_relat_1 @ X21 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X21 @ X20 ) )
        = X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('36',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
        = sk_C ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      = sk_C )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( sk_C != sk_C )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['33','38','39','40'])).

thf('42',plain,
    ( ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['18','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,
    ( ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['16','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('54',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['2','15','54'])).

thf('56',plain,(
    ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','55'])).

thf('57',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('58',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
    | ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['58'])).

thf('60',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
    | ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['58'])).

thf('61',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','15','54','60'])).

thf('62',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['59','61'])).

thf('63',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k9_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('64',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X17 @ X16 ) )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ ( k1_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('69',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X20 @ ( k1_relat_1 @ X21 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X21 @ X20 ) )
        = X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('70',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
        = sk_C ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      = sk_C )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('74',plain,(
    r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','15','54','73'])).

thf('75',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
    = sk_C ),
    inference(simpl_trail,[status(thm)],['72','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
      = sk_C )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['66','67','75','76'])).

thf('78',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['57','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('82',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) @ X11 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) @ X9 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t112_relat_1])).

thf(t89_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ) )).

thf('83',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) ) @ ( k1_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t89_relat_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['80','86'])).

thf('88',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    $false ),
    inference(demod,[status(thm)],['56','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pvXtZzCWEJ
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:45:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.42/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.62  % Solved by: fo/fo7.sh
% 0.42/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.62  % done 214 iterations in 0.158s
% 0.42/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.62  % SZS output start Refutation
% 0.42/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.42/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.42/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.42/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.42/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.62  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.42/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.42/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.42/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.62  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.42/0.62  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.42/0.62  thf(t171_funct_1, conjecture,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.42/0.62       ( ![B:$i]:
% 0.42/0.62         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.42/0.62           ( ![C:$i]:
% 0.42/0.62             ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 0.42/0.62               ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 0.42/0.62                 ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ))).
% 0.42/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.62    (~( ![A:$i]:
% 0.42/0.62        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.42/0.62          ( ![B:$i]:
% 0.42/0.62            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.42/0.62              ( ![C:$i]:
% 0.42/0.62                ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 0.42/0.62                  ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 0.42/0.62                    ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ) )),
% 0.42/0.62    inference('cnf.neg', [status(esa)], [t171_funct_1])).
% 0.42/0.62  thf('0', plain,
% 0.42/0.62      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))
% 0.42/0.62        | ~ (r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))
% 0.42/0.62        | ~ (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('1', plain,
% 0.42/0.62      ((~ (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.42/0.62         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.42/0.62      inference('split', [status(esa)], ['0'])).
% 0.42/0.62  thf('2', plain,
% 0.42/0.62      (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.42/0.62       ~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))) | 
% 0.42/0.62       ~ ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))),
% 0.42/0.62      inference('split', [status(esa)], ['0'])).
% 0.42/0.62  thf(t44_relat_1, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( v1_relat_1 @ A ) =>
% 0.42/0.62       ( ![B:$i]:
% 0.42/0.62         ( ( v1_relat_1 @ B ) =>
% 0.42/0.62           ( r1_tarski @
% 0.42/0.62             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.42/0.62  thf('3', plain,
% 0.42/0.62      (![X14 : $i, X15 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ X14)
% 0.42/0.62          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X15 @ X14)) @ 
% 0.42/0.62             (k1_relat_1 @ X15))
% 0.42/0.62          | ~ (v1_relat_1 @ X15))),
% 0.42/0.62      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.42/0.62  thf('4', plain,
% 0.42/0.62      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))
% 0.42/0.62        | (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('5', plain,
% 0.42/0.62      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.42/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.42/0.62      inference('split', [status(esa)], ['4'])).
% 0.42/0.62  thf(t12_xboole_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.42/0.62  thf('6', plain,
% 0.42/0.62      (![X3 : $i, X4 : $i]:
% 0.42/0.62         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.42/0.62      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.42/0.62  thf('7', plain,
% 0.42/0.62      ((((k2_xboole_0 @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))
% 0.42/0.62          = (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.42/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['5', '6'])).
% 0.42/0.62  thf(t11_xboole_1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i]:
% 0.42/0.62     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.42/0.62  thf('8', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 0.42/0.62      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.42/0.62  thf('9', plain,
% 0.42/0.62      ((![X0 : $i]:
% 0.42/0.62          (~ (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)) @ X0)
% 0.42/0.62           | (r1_tarski @ sk_C @ X0)))
% 0.42/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['7', '8'])).
% 0.42/0.62  thf('10', plain,
% 0.42/0.62      (((~ (v1_relat_1 @ sk_A)
% 0.42/0.62         | ~ (v1_relat_1 @ sk_B)
% 0.42/0.62         | (r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))
% 0.42/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['3', '9'])).
% 0.42/0.62  thf('11', plain, ((v1_relat_1 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('13', plain,
% 0.42/0.62      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 0.42/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.42/0.62      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.42/0.62  thf('14', plain,
% 0.42/0.62      ((~ (r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 0.42/0.62         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 0.42/0.62      inference('split', [status(esa)], ['0'])).
% 0.42/0.62  thf('15', plain,
% 0.42/0.62      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 0.42/0.62       ~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['13', '14'])).
% 0.42/0.62  thf(t148_relat_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( v1_relat_1 @ B ) =>
% 0.42/0.62       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.42/0.62  thf('16', plain,
% 0.42/0.62      (![X12 : $i, X13 : $i]:
% 0.42/0.62         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 0.42/0.62          | ~ (v1_relat_1 @ X12))),
% 0.42/0.62      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.42/0.62  thf(fc8_funct_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.42/0.62       ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) & 
% 0.42/0.62         ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 0.42/0.62  thf('17', plain,
% 0.42/0.62      (![X22 : $i, X23 : $i]:
% 0.42/0.62         (~ (v1_funct_1 @ X22)
% 0.42/0.62          | ~ (v1_relat_1 @ X22)
% 0.42/0.62          | (v1_funct_1 @ (k7_relat_1 @ X22 @ X23)))),
% 0.42/0.62      inference('cnf', [status(esa)], [fc8_funct_1])).
% 0.42/0.62  thf(dt_k7_relat_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.42/0.62  thf('18', plain,
% 0.42/0.62      (![X7 : $i, X8 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ X7) | (v1_relat_1 @ (k7_relat_1 @ X7 @ X8)))),
% 0.42/0.62      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.42/0.62  thf(t112_relat_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( v1_relat_1 @ B ) =>
% 0.42/0.62       ( ![C:$i]:
% 0.42/0.62         ( ( v1_relat_1 @ C ) =>
% 0.42/0.62           ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.42/0.62             ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) ))).
% 0.42/0.62  thf('19', plain,
% 0.42/0.62      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ X9)
% 0.42/0.62          | ((k7_relat_1 @ (k5_relat_1 @ X10 @ X9) @ X11)
% 0.42/0.62              = (k5_relat_1 @ (k7_relat_1 @ X10 @ X11) @ X9))
% 0.42/0.62          | ~ (v1_relat_1 @ X10))),
% 0.42/0.62      inference('cnf', [status(esa)], [t112_relat_1])).
% 0.42/0.62  thf(dt_k5_relat_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.42/0.62       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.42/0.62  thf('20', plain,
% 0.42/0.62      (![X5 : $i, X6 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ X5)
% 0.42/0.62          | ~ (v1_relat_1 @ X6)
% 0.42/0.62          | (v1_relat_1 @ (k5_relat_1 @ X5 @ X6)))),
% 0.42/0.62      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.42/0.62  thf('21', plain,
% 0.42/0.62      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.42/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.42/0.62      inference('split', [status(esa)], ['4'])).
% 0.42/0.62  thf(t91_relat_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( v1_relat_1 @ B ) =>
% 0.42/0.62       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.42/0.62         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.42/0.62  thf('22', plain,
% 0.42/0.62      (![X20 : $i, X21 : $i]:
% 0.42/0.62         (~ (r1_tarski @ X20 @ (k1_relat_1 @ X21))
% 0.42/0.62          | ((k1_relat_1 @ (k7_relat_1 @ X21 @ X20)) = (X20))
% 0.42/0.62          | ~ (v1_relat_1 @ X21))),
% 0.42/0.62      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.42/0.62  thf('23', plain,
% 0.42/0.62      (((~ (v1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 0.42/0.62         | ((k1_relat_1 @ (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C))
% 0.42/0.62             = (sk_C))))
% 0.42/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['21', '22'])).
% 0.42/0.62  thf('24', plain,
% 0.42/0.62      (((~ (v1_relat_1 @ sk_B)
% 0.42/0.62         | ~ (v1_relat_1 @ sk_A)
% 0.42/0.62         | ((k1_relat_1 @ (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C))
% 0.42/0.62             = (sk_C))))
% 0.42/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['20', '23'])).
% 0.42/0.62  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('26', plain, ((v1_relat_1 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('27', plain,
% 0.42/0.62      ((((k1_relat_1 @ (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C))
% 0.42/0.62          = (sk_C)))
% 0.42/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.42/0.62      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.42/0.62  thf('28', plain,
% 0.42/0.62      (((((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B))
% 0.42/0.62           = (sk_C))
% 0.42/0.62         | ~ (v1_relat_1 @ sk_A)
% 0.42/0.62         | ~ (v1_relat_1 @ sk_B)))
% 0.42/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.42/0.62      inference('sup+', [status(thm)], ['19', '27'])).
% 0.42/0.62  thf('29', plain, ((v1_relat_1 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('31', plain,
% 0.42/0.62      ((((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B))
% 0.42/0.62          = (sk_C)))
% 0.42/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.42/0.62      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.42/0.62  thf(t27_funct_1, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.42/0.62       ( ![B:$i]:
% 0.42/0.62         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.42/0.62           ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k1_relat_1 @ B ) ) =>
% 0.42/0.62             ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.42/0.62  thf('32', plain,
% 0.42/0.62      (![X24 : $i, X25 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ X24)
% 0.42/0.62          | ~ (v1_funct_1 @ X24)
% 0.42/0.62          | (r1_tarski @ (k2_relat_1 @ X24) @ (k1_relat_1 @ X25))
% 0.42/0.62          | ((k1_relat_1 @ (k5_relat_1 @ X24 @ X25)) != (k1_relat_1 @ X24))
% 0.42/0.62          | ~ (v1_funct_1 @ X25)
% 0.42/0.62          | ~ (v1_relat_1 @ X25))),
% 0.42/0.62      inference('cnf', [status(esa)], [t27_funct_1])).
% 0.42/0.62  thf('33', plain,
% 0.42/0.62      (((((sk_C) != (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)))
% 0.42/0.62         | ~ (v1_relat_1 @ sk_B)
% 0.42/0.62         | ~ (v1_funct_1 @ sk_B)
% 0.42/0.62         | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 0.42/0.62            (k1_relat_1 @ sk_B))
% 0.42/0.62         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C))
% 0.42/0.62         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))))
% 0.42/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['31', '32'])).
% 0.42/0.62  thf('34', plain,
% 0.42/0.62      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 0.42/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.42/0.62      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.42/0.62  thf('35', plain,
% 0.42/0.62      (![X20 : $i, X21 : $i]:
% 0.42/0.62         (~ (r1_tarski @ X20 @ (k1_relat_1 @ X21))
% 0.42/0.62          | ((k1_relat_1 @ (k7_relat_1 @ X21 @ X20)) = (X20))
% 0.42/0.62          | ~ (v1_relat_1 @ X21))),
% 0.42/0.62      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.42/0.62  thf('36', plain,
% 0.42/0.62      (((~ (v1_relat_1 @ sk_A)
% 0.42/0.62         | ((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) = (sk_C))))
% 0.42/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['34', '35'])).
% 0.42/0.62  thf('37', plain, ((v1_relat_1 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('38', plain,
% 0.42/0.62      ((((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) = (sk_C)))
% 0.42/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.42/0.62      inference('demod', [status(thm)], ['36', '37'])).
% 0.42/0.62  thf('39', plain, ((v1_relat_1 @ sk_B)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('40', plain, ((v1_funct_1 @ sk_B)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('41', plain,
% 0.42/0.62      (((((sk_C) != (sk_C))
% 0.42/0.62         | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 0.42/0.62            (k1_relat_1 @ sk_B))
% 0.42/0.62         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C))
% 0.42/0.62         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))))
% 0.42/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.42/0.62      inference('demod', [status(thm)], ['33', '38', '39', '40'])).
% 0.42/0.62  thf('42', plain,
% 0.42/0.62      (((~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))
% 0.42/0.62         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C))
% 0.42/0.62         | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 0.42/0.62            (k1_relat_1 @ sk_B))))
% 0.42/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.42/0.62      inference('simplify', [status(thm)], ['41'])).
% 0.42/0.62  thf('43', plain,
% 0.42/0.62      (((~ (v1_relat_1 @ sk_A)
% 0.42/0.62         | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 0.42/0.62            (k1_relat_1 @ sk_B))
% 0.42/0.62         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C))))
% 0.42/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['18', '42'])).
% 0.42/0.62  thf('44', plain, ((v1_relat_1 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('45', plain,
% 0.42/0.62      ((((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 0.42/0.62          (k1_relat_1 @ sk_B))
% 0.42/0.62         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C))))
% 0.42/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.42/0.62      inference('demod', [status(thm)], ['43', '44'])).
% 0.42/0.62  thf('46', plain,
% 0.42/0.62      (((~ (v1_relat_1 @ sk_A)
% 0.42/0.62         | ~ (v1_funct_1 @ sk_A)
% 0.42/0.62         | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 0.42/0.62            (k1_relat_1 @ sk_B))))
% 0.42/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['17', '45'])).
% 0.42/0.62  thf('47', plain, ((v1_relat_1 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('48', plain, ((v1_funct_1 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('49', plain,
% 0.42/0.62      (((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 0.42/0.62         (k1_relat_1 @ sk_B)))
% 0.42/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.42/0.62      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.42/0.62  thf('50', plain,
% 0.42/0.62      ((((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))
% 0.42/0.62         | ~ (v1_relat_1 @ sk_A)))
% 0.42/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.42/0.62      inference('sup+', [status(thm)], ['16', '49'])).
% 0.42/0.62  thf('51', plain, ((v1_relat_1 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('52', plain,
% 0.42/0.62      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 0.42/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.42/0.62      inference('demod', [status(thm)], ['50', '51'])).
% 0.42/0.62  thf('53', plain,
% 0.42/0.62      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 0.42/0.62         <= (~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))),
% 0.42/0.62      inference('split', [status(esa)], ['0'])).
% 0.42/0.62  thf('54', plain,
% 0.42/0.62      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))) | 
% 0.42/0.62       ~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['52', '53'])).
% 0.42/0.62  thf('55', plain,
% 0.42/0.62      (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.42/0.62      inference('sat_resolution*', [status(thm)], ['2', '15', '54'])).
% 0.42/0.62  thf('56', plain,
% 0.42/0.62      (~ (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))),
% 0.42/0.62      inference('simpl_trail', [status(thm)], ['1', '55'])).
% 0.42/0.62  thf('57', plain,
% 0.42/0.62      (![X7 : $i, X8 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ X7) | (v1_relat_1 @ (k7_relat_1 @ X7 @ X8)))),
% 0.42/0.62      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.42/0.62  thf('58', plain,
% 0.42/0.62      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))
% 0.42/0.62        | (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('59', plain,
% 0.42/0.62      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 0.42/0.62         <= (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))),
% 0.42/0.62      inference('split', [status(esa)], ['58'])).
% 0.42/0.62  thf('60', plain,
% 0.42/0.62      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))) | 
% 0.42/0.62       ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.42/0.62      inference('split', [status(esa)], ['58'])).
% 0.42/0.62  thf('61', plain,
% 0.42/0.62      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 0.42/0.62      inference('sat_resolution*', [status(thm)], ['2', '15', '54', '60'])).
% 0.42/0.62  thf('62', plain,
% 0.42/0.62      ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))),
% 0.42/0.62      inference('simpl_trail', [status(thm)], ['59', '61'])).
% 0.42/0.62  thf('63', plain,
% 0.42/0.62      (![X12 : $i, X13 : $i]:
% 0.42/0.62         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 0.42/0.62          | ~ (v1_relat_1 @ X12))),
% 0.42/0.62      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.42/0.62  thf(t46_relat_1, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( v1_relat_1 @ A ) =>
% 0.42/0.62       ( ![B:$i]:
% 0.42/0.62         ( ( v1_relat_1 @ B ) =>
% 0.42/0.62           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.42/0.62             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.42/0.62  thf('64', plain,
% 0.42/0.62      (![X16 : $i, X17 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ X16)
% 0.42/0.62          | ((k1_relat_1 @ (k5_relat_1 @ X17 @ X16)) = (k1_relat_1 @ X17))
% 0.42/0.62          | ~ (r1_tarski @ (k2_relat_1 @ X17) @ (k1_relat_1 @ X16))
% 0.42/0.62          | ~ (v1_relat_1 @ X17))),
% 0.42/0.62      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.42/0.62  thf('65', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         (~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k1_relat_1 @ X2))
% 0.42/0.62          | ~ (v1_relat_1 @ X1)
% 0.42/0.62          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.42/0.62          | ((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2))
% 0.42/0.62              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.42/0.62          | ~ (v1_relat_1 @ X2))),
% 0.42/0.62      inference('sup-', [status(thm)], ['63', '64'])).
% 0.42/0.62  thf('66', plain,
% 0.42/0.62      ((~ (v1_relat_1 @ sk_B)
% 0.42/0.62        | ((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B))
% 0.42/0.62            = (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)))
% 0.42/0.62        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))
% 0.42/0.62        | ~ (v1_relat_1 @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['62', '65'])).
% 0.42/0.62  thf('67', plain, ((v1_relat_1 @ sk_B)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('68', plain,
% 0.42/0.62      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 0.42/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 0.42/0.62      inference('split', [status(esa)], ['4'])).
% 0.42/0.62  thf('69', plain,
% 0.42/0.62      (![X20 : $i, X21 : $i]:
% 0.42/0.62         (~ (r1_tarski @ X20 @ (k1_relat_1 @ X21))
% 0.42/0.62          | ((k1_relat_1 @ (k7_relat_1 @ X21 @ X20)) = (X20))
% 0.42/0.62          | ~ (v1_relat_1 @ X21))),
% 0.42/0.62      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.42/0.62  thf('70', plain,
% 0.42/0.62      (((~ (v1_relat_1 @ sk_A)
% 0.42/0.62         | ((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) = (sk_C))))
% 0.42/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['68', '69'])).
% 0.42/0.62  thf('71', plain, ((v1_relat_1 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('72', plain,
% 0.42/0.62      ((((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) = (sk_C)))
% 0.42/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 0.42/0.62      inference('demod', [status(thm)], ['70', '71'])).
% 0.42/0.62  thf('73', plain,
% 0.42/0.62      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 0.42/0.62       ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.42/0.62      inference('split', [status(esa)], ['4'])).
% 0.42/0.62  thf('74', plain, (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))),
% 0.42/0.62      inference('sat_resolution*', [status(thm)], ['2', '15', '54', '73'])).
% 0.42/0.62  thf('75', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) = (sk_C))),
% 0.42/0.62      inference('simpl_trail', [status(thm)], ['72', '74'])).
% 0.42/0.62  thf('76', plain, ((v1_relat_1 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('77', plain,
% 0.42/0.62      ((((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B))
% 0.42/0.62          = (sk_C))
% 0.42/0.62        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)))),
% 0.42/0.62      inference('demod', [status(thm)], ['66', '67', '75', '76'])).
% 0.42/0.62  thf('78', plain,
% 0.42/0.62      ((~ (v1_relat_1 @ sk_A)
% 0.42/0.62        | ((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B))
% 0.42/0.62            = (sk_C)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['57', '77'])).
% 0.42/0.62  thf('79', plain, ((v1_relat_1 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('80', plain,
% 0.42/0.62      (((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B))
% 0.42/0.62         = (sk_C))),
% 0.42/0.62      inference('demod', [status(thm)], ['78', '79'])).
% 0.42/0.62  thf('81', plain,
% 0.42/0.62      (![X5 : $i, X6 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ X5)
% 0.42/0.62          | ~ (v1_relat_1 @ X6)
% 0.42/0.62          | (v1_relat_1 @ (k5_relat_1 @ X5 @ X6)))),
% 0.42/0.62      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.42/0.62  thf('82', plain,
% 0.42/0.62      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ X9)
% 0.42/0.62          | ((k7_relat_1 @ (k5_relat_1 @ X10 @ X9) @ X11)
% 0.42/0.62              = (k5_relat_1 @ (k7_relat_1 @ X10 @ X11) @ X9))
% 0.42/0.62          | ~ (v1_relat_1 @ X10))),
% 0.42/0.62      inference('cnf', [status(esa)], [t112_relat_1])).
% 0.42/0.62  thf(t89_relat_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( v1_relat_1 @ B ) =>
% 0.42/0.62       ( r1_tarski @
% 0.42/0.62         ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ))).
% 0.42/0.62  thf('83', plain,
% 0.42/0.62      (![X18 : $i, X19 : $i]:
% 0.42/0.62         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X18 @ X19)) @ 
% 0.42/0.62           (k1_relat_1 @ X18))
% 0.42/0.62          | ~ (v1_relat_1 @ X18))),
% 0.42/0.62      inference('cnf', [status(esa)], [t89_relat_1])).
% 0.42/0.62  thf('84', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         ((r1_tarski @ 
% 0.42/0.62           (k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)) @ 
% 0.42/0.62           (k1_relat_1 @ (k5_relat_1 @ X2 @ X0)))
% 0.42/0.62          | ~ (v1_relat_1 @ X2)
% 0.42/0.62          | ~ (v1_relat_1 @ X0)
% 0.42/0.62          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X0)))),
% 0.42/0.62      inference('sup+', [status(thm)], ['82', '83'])).
% 0.42/0.62  thf('85', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ X0)
% 0.42/0.62          | ~ (v1_relat_1 @ X1)
% 0.42/0.62          | ~ (v1_relat_1 @ X0)
% 0.42/0.62          | ~ (v1_relat_1 @ X1)
% 0.42/0.62          | (r1_tarski @ 
% 0.42/0.62             (k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0)) @ 
% 0.42/0.62             (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['81', '84'])).
% 0.42/0.62  thf('86', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         ((r1_tarski @ 
% 0.42/0.62           (k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0)) @ 
% 0.42/0.62           (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.42/0.62          | ~ (v1_relat_1 @ X1)
% 0.42/0.62          | ~ (v1_relat_1 @ X0))),
% 0.42/0.62      inference('simplify', [status(thm)], ['85'])).
% 0.42/0.62  thf('87', plain,
% 0.42/0.62      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))
% 0.42/0.62        | ~ (v1_relat_1 @ sk_B)
% 0.42/0.62        | ~ (v1_relat_1 @ sk_A))),
% 0.42/0.62      inference('sup+', [status(thm)], ['80', '86'])).
% 0.42/0.62  thf('88', plain, ((v1_relat_1 @ sk_B)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('89', plain, ((v1_relat_1 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('90', plain,
% 0.42/0.62      ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))),
% 0.42/0.62      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.42/0.62  thf('91', plain, ($false), inference('demod', [status(thm)], ['56', '90'])).
% 0.42/0.62  
% 0.42/0.62  % SZS output end Refutation
% 0.42/0.62  
% 0.47/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
