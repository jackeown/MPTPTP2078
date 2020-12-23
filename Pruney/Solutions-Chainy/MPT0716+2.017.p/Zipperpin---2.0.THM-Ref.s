%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sDMgkmXDbb

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:21 EST 2020

% Result     : Theorem 0.78s
% Output     : Refutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 480 expanded)
%              Number of leaves         :   28 ( 145 expanded)
%              Depth                    :   27
%              Number of atoms          : 1205 (6922 expanded)
%              Number of equality atoms :   36 (  97 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('17',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k7_relat_1 @ X23 @ X22 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X22 ) @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(fc2_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) )).

thf('18',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_funct_1 @ X25 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('20',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('21',plain,(
    ! [X27: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('24',plain,(
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

thf('25',plain,(
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

thf('26',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('27',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('28',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X20 @ ( k1_relat_1 @ X21 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X21 @ X20 ) )
        = X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('29',plain,
    ( ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
        = sk_C ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
        = sk_C ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
      = sk_C )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
        = sk_C )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['25','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
      = sk_C )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

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

thf('38',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ~ ( v1_funct_1 @ X28 )
      | ( r1_tarski @ ( k2_relat_1 @ X28 ) @ ( k1_relat_1 @ X29 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X28 @ X29 ) )
       != ( k1_relat_1 @ X28 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t27_funct_1])).

thf('39',plain,
    ( ( ( sk_C
       != ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('41',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X20 @ ( k1_relat_1 @ X21 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X21 @ X20 ) )
        = X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('42',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
        = sk_C ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      = sk_C )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( sk_C != sk_C )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['39','44','45','46'])).

thf('48',plain,
    ( ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['24','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['23','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,
    ( ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['16','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('60',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['2','15','60'])).

thf('62',plain,(
    ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','61'])).

thf('63',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('64',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
    | ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['64'])).

thf('66',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
    | ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['64'])).

thf('67',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','15','60','66'])).

thf('68',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['65','67'])).

thf('69',plain,(
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

thf('70',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X17 @ X16 ) )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ ( k1_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('75',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X20 @ ( k1_relat_1 @ X21 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X21 @ X20 ) )
        = X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('76',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
        = sk_C ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      = sk_C )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('80',plain,(
    r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','15','60','79'])).

thf('81',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
    = sk_C ),
    inference(simpl_trail,[status(thm)],['78','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
      = sk_C )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['72','73','81','82'])).

thf('84',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['63','83'])).

thf('85',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('88',plain,(
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

thf('89',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) ) @ ( k1_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t89_relat_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['87','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['86','92'])).

thf('94',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    $false ),
    inference(demod,[status(thm)],['62','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sDMgkmXDbb
% 0.13/0.37  % Computer   : n017.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 09:55:16 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.78/1.02  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.78/1.02  % Solved by: fo/fo7.sh
% 0.78/1.02  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.78/1.02  % done 594 iterations in 0.530s
% 0.78/1.02  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.78/1.02  % SZS output start Refutation
% 0.78/1.02  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.78/1.02  thf(sk_C_type, type, sk_C: $i).
% 0.78/1.02  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.78/1.02  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.78/1.02  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.78/1.02  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.78/1.02  thf(sk_B_type, type, sk_B: $i).
% 0.78/1.02  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.78/1.02  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.78/1.02  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.78/1.02  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.78/1.02  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.78/1.02  thf(sk_A_type, type, sk_A: $i).
% 0.78/1.02  thf(t171_funct_1, conjecture,
% 0.78/1.02    (![A:$i]:
% 0.78/1.02     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.78/1.02       ( ![B:$i]:
% 0.78/1.02         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.78/1.02           ( ![C:$i]:
% 0.78/1.02             ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 0.78/1.02               ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 0.78/1.02                 ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ))).
% 0.78/1.02  thf(zf_stmt_0, negated_conjecture,
% 0.78/1.02    (~( ![A:$i]:
% 0.78/1.02        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.78/1.02          ( ![B:$i]:
% 0.78/1.02            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.78/1.02              ( ![C:$i]:
% 0.78/1.02                ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 0.78/1.02                  ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 0.78/1.02                    ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ) )),
% 0.78/1.02    inference('cnf.neg', [status(esa)], [t171_funct_1])).
% 0.78/1.02  thf('0', plain,
% 0.78/1.02      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))
% 0.78/1.02        | ~ (r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))
% 0.78/1.02        | ~ (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.78/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.02  thf('1', plain,
% 0.78/1.02      ((~ (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.78/1.02         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.78/1.02      inference('split', [status(esa)], ['0'])).
% 0.78/1.02  thf('2', plain,
% 0.78/1.02      (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.78/1.02       ~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))) | 
% 0.78/1.02       ~ ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))),
% 0.78/1.02      inference('split', [status(esa)], ['0'])).
% 0.78/1.02  thf(t44_relat_1, axiom,
% 0.78/1.02    (![A:$i]:
% 0.78/1.02     ( ( v1_relat_1 @ A ) =>
% 0.78/1.02       ( ![B:$i]:
% 0.78/1.02         ( ( v1_relat_1 @ B ) =>
% 0.78/1.02           ( r1_tarski @
% 0.78/1.02             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.78/1.02  thf('3', plain,
% 0.78/1.02      (![X14 : $i, X15 : $i]:
% 0.78/1.02         (~ (v1_relat_1 @ X14)
% 0.78/1.02          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X15 @ X14)) @ 
% 0.78/1.02             (k1_relat_1 @ X15))
% 0.78/1.02          | ~ (v1_relat_1 @ X15))),
% 0.78/1.02      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.78/1.02  thf('4', plain,
% 0.78/1.02      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))
% 0.78/1.02        | (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.78/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.02  thf('5', plain,
% 0.78/1.02      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.78/1.02         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.78/1.02      inference('split', [status(esa)], ['4'])).
% 0.78/1.02  thf(t12_xboole_1, axiom,
% 0.78/1.02    (![A:$i,B:$i]:
% 0.78/1.02     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.78/1.02  thf('6', plain,
% 0.78/1.02      (![X3 : $i, X4 : $i]:
% 0.78/1.02         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.78/1.02      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.78/1.02  thf('7', plain,
% 0.78/1.02      ((((k2_xboole_0 @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))
% 0.78/1.02          = (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.78/1.02         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.78/1.02      inference('sup-', [status(thm)], ['5', '6'])).
% 0.78/1.02  thf(t11_xboole_1, axiom,
% 0.78/1.02    (![A:$i,B:$i,C:$i]:
% 0.78/1.02     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.78/1.02  thf('8', plain,
% 0.78/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/1.02         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 0.78/1.02      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.78/1.02  thf('9', plain,
% 0.78/1.02      ((![X0 : $i]:
% 0.78/1.02          (~ (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)) @ X0)
% 0.78/1.02           | (r1_tarski @ sk_C @ X0)))
% 0.78/1.02         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.78/1.02      inference('sup-', [status(thm)], ['7', '8'])).
% 0.78/1.02  thf('10', plain,
% 0.78/1.02      (((~ (v1_relat_1 @ sk_A)
% 0.78/1.02         | ~ (v1_relat_1 @ sk_B)
% 0.78/1.02         | (r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))
% 0.78/1.02         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.78/1.02      inference('sup-', [status(thm)], ['3', '9'])).
% 0.78/1.02  thf('11', plain, ((v1_relat_1 @ sk_A)),
% 0.78/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.02  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 0.78/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.02  thf('13', plain,
% 0.78/1.02      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 0.78/1.02         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.78/1.02      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.78/1.02  thf('14', plain,
% 0.78/1.02      ((~ (r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 0.78/1.02         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 0.78/1.02      inference('split', [status(esa)], ['0'])).
% 0.78/1.02  thf('15', plain,
% 0.78/1.02      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 0.78/1.02       ~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.78/1.02      inference('sup-', [status(thm)], ['13', '14'])).
% 0.78/1.02  thf(t148_relat_1, axiom,
% 0.78/1.02    (![A:$i,B:$i]:
% 0.78/1.02     ( ( v1_relat_1 @ B ) =>
% 0.78/1.02       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.78/1.02  thf('16', plain,
% 0.78/1.02      (![X12 : $i, X13 : $i]:
% 0.78/1.02         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 0.78/1.02          | ~ (v1_relat_1 @ X12))),
% 0.78/1.02      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.78/1.02  thf(t94_relat_1, axiom,
% 0.78/1.02    (![A:$i,B:$i]:
% 0.78/1.02     ( ( v1_relat_1 @ B ) =>
% 0.78/1.02       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.78/1.02  thf('17', plain,
% 0.78/1.02      (![X22 : $i, X23 : $i]:
% 0.78/1.02         (((k7_relat_1 @ X23 @ X22) = (k5_relat_1 @ (k6_relat_1 @ X22) @ X23))
% 0.78/1.02          | ~ (v1_relat_1 @ X23))),
% 0.78/1.02      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.78/1.02  thf(fc2_funct_1, axiom,
% 0.78/1.02    (![A:$i,B:$i]:
% 0.78/1.02     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v1_relat_1 @ B ) & 
% 0.78/1.02         ( v1_funct_1 @ B ) ) =>
% 0.78/1.02       ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) & 
% 0.78/1.02         ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ))).
% 0.78/1.02  thf('18', plain,
% 0.78/1.02      (![X24 : $i, X25 : $i]:
% 0.78/1.02         (~ (v1_funct_1 @ X24)
% 0.78/1.02          | ~ (v1_relat_1 @ X24)
% 0.78/1.02          | ~ (v1_relat_1 @ X25)
% 0.78/1.02          | ~ (v1_funct_1 @ X25)
% 0.78/1.02          | (v1_funct_1 @ (k5_relat_1 @ X24 @ X25)))),
% 0.78/1.02      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.78/1.02  thf('19', plain,
% 0.78/1.02      (![X0 : $i, X1 : $i]:
% 0.78/1.02         ((v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 0.78/1.02          | ~ (v1_relat_1 @ X1)
% 0.78/1.02          | ~ (v1_funct_1 @ X1)
% 0.78/1.02          | ~ (v1_relat_1 @ X1)
% 0.78/1.02          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.78/1.02          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 0.78/1.02      inference('sup+', [status(thm)], ['17', '18'])).
% 0.78/1.02  thf(fc3_funct_1, axiom,
% 0.78/1.02    (![A:$i]:
% 0.78/1.02     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.78/1.02       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.78/1.02  thf('20', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.78/1.02      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.78/1.02  thf('21', plain, (![X27 : $i]: (v1_funct_1 @ (k6_relat_1 @ X27))),
% 0.78/1.02      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.78/1.02  thf('22', plain,
% 0.78/1.02      (![X0 : $i, X1 : $i]:
% 0.78/1.02         ((v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 0.78/1.02          | ~ (v1_relat_1 @ X1)
% 0.78/1.02          | ~ (v1_funct_1 @ X1)
% 0.78/1.02          | ~ (v1_relat_1 @ X1))),
% 0.78/1.02      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.78/1.02  thf('23', plain,
% 0.78/1.02      (![X0 : $i, X1 : $i]:
% 0.78/1.02         (~ (v1_funct_1 @ X1)
% 0.78/1.02          | ~ (v1_relat_1 @ X1)
% 0.78/1.02          | (v1_funct_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.78/1.02      inference('simplify', [status(thm)], ['22'])).
% 0.78/1.02  thf(dt_k7_relat_1, axiom,
% 0.78/1.02    (![A:$i,B:$i]:
% 0.78/1.02     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.78/1.02  thf('24', plain,
% 0.78/1.02      (![X7 : $i, X8 : $i]:
% 0.78/1.02         (~ (v1_relat_1 @ X7) | (v1_relat_1 @ (k7_relat_1 @ X7 @ X8)))),
% 0.78/1.02      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.78/1.02  thf(t112_relat_1, axiom,
% 0.78/1.02    (![A:$i,B:$i]:
% 0.78/1.02     ( ( v1_relat_1 @ B ) =>
% 0.78/1.02       ( ![C:$i]:
% 0.78/1.02         ( ( v1_relat_1 @ C ) =>
% 0.78/1.02           ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.78/1.02             ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) ))).
% 0.78/1.02  thf('25', plain,
% 0.78/1.02      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.78/1.02         (~ (v1_relat_1 @ X9)
% 0.78/1.02          | ((k7_relat_1 @ (k5_relat_1 @ X10 @ X9) @ X11)
% 0.78/1.02              = (k5_relat_1 @ (k7_relat_1 @ X10 @ X11) @ X9))
% 0.78/1.02          | ~ (v1_relat_1 @ X10))),
% 0.78/1.02      inference('cnf', [status(esa)], [t112_relat_1])).
% 0.78/1.02  thf(dt_k5_relat_1, axiom,
% 0.78/1.02    (![A:$i,B:$i]:
% 0.78/1.02     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.78/1.02       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.78/1.02  thf('26', plain,
% 0.78/1.02      (![X5 : $i, X6 : $i]:
% 0.78/1.02         (~ (v1_relat_1 @ X5)
% 0.78/1.02          | ~ (v1_relat_1 @ X6)
% 0.78/1.02          | (v1_relat_1 @ (k5_relat_1 @ X5 @ X6)))),
% 0.78/1.02      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.78/1.02  thf('27', plain,
% 0.78/1.02      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.78/1.02         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.78/1.02      inference('split', [status(esa)], ['4'])).
% 0.78/1.02  thf(t91_relat_1, axiom,
% 0.78/1.02    (![A:$i,B:$i]:
% 0.78/1.02     ( ( v1_relat_1 @ B ) =>
% 0.78/1.02       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.78/1.02         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.78/1.02  thf('28', plain,
% 0.78/1.02      (![X20 : $i, X21 : $i]:
% 0.78/1.02         (~ (r1_tarski @ X20 @ (k1_relat_1 @ X21))
% 0.78/1.02          | ((k1_relat_1 @ (k7_relat_1 @ X21 @ X20)) = (X20))
% 0.78/1.02          | ~ (v1_relat_1 @ X21))),
% 0.78/1.02      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.78/1.02  thf('29', plain,
% 0.78/1.02      (((~ (v1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 0.78/1.02         | ((k1_relat_1 @ (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C))
% 0.78/1.02             = (sk_C))))
% 0.78/1.02         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.78/1.02      inference('sup-', [status(thm)], ['27', '28'])).
% 0.78/1.02  thf('30', plain,
% 0.78/1.02      (((~ (v1_relat_1 @ sk_B)
% 0.78/1.02         | ~ (v1_relat_1 @ sk_A)
% 0.78/1.02         | ((k1_relat_1 @ (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C))
% 0.78/1.02             = (sk_C))))
% 0.78/1.02         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.78/1.02      inference('sup-', [status(thm)], ['26', '29'])).
% 0.78/1.02  thf('31', plain, ((v1_relat_1 @ sk_B)),
% 0.78/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.02  thf('32', plain, ((v1_relat_1 @ sk_A)),
% 0.78/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.02  thf('33', plain,
% 0.78/1.02      ((((k1_relat_1 @ (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C))
% 0.78/1.02          = (sk_C)))
% 0.78/1.02         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.78/1.02      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.78/1.02  thf('34', plain,
% 0.78/1.02      (((((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B))
% 0.78/1.02           = (sk_C))
% 0.78/1.02         | ~ (v1_relat_1 @ sk_A)
% 0.78/1.02         | ~ (v1_relat_1 @ sk_B)))
% 0.78/1.02         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.78/1.02      inference('sup+', [status(thm)], ['25', '33'])).
% 0.78/1.02  thf('35', plain, ((v1_relat_1 @ sk_A)),
% 0.78/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.02  thf('36', plain, ((v1_relat_1 @ sk_B)),
% 0.78/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.02  thf('37', plain,
% 0.78/1.02      ((((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B))
% 0.78/1.02          = (sk_C)))
% 0.78/1.02         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.78/1.02      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.78/1.02  thf(t27_funct_1, axiom,
% 0.78/1.02    (![A:$i]:
% 0.78/1.02     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.78/1.02       ( ![B:$i]:
% 0.78/1.02         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.78/1.02           ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k1_relat_1 @ B ) ) =>
% 0.78/1.02             ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.78/1.02  thf('38', plain,
% 0.78/1.02      (![X28 : $i, X29 : $i]:
% 0.78/1.02         (~ (v1_relat_1 @ X28)
% 0.78/1.02          | ~ (v1_funct_1 @ X28)
% 0.78/1.02          | (r1_tarski @ (k2_relat_1 @ X28) @ (k1_relat_1 @ X29))
% 0.78/1.02          | ((k1_relat_1 @ (k5_relat_1 @ X28 @ X29)) != (k1_relat_1 @ X28))
% 0.78/1.02          | ~ (v1_funct_1 @ X29)
% 0.78/1.02          | ~ (v1_relat_1 @ X29))),
% 0.78/1.02      inference('cnf', [status(esa)], [t27_funct_1])).
% 0.78/1.02  thf('39', plain,
% 0.78/1.02      (((((sk_C) != (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)))
% 0.78/1.02         | ~ (v1_relat_1 @ sk_B)
% 0.78/1.02         | ~ (v1_funct_1 @ sk_B)
% 0.78/1.02         | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 0.78/1.02            (k1_relat_1 @ sk_B))
% 0.78/1.02         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C))
% 0.78/1.02         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))))
% 0.78/1.02         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.78/1.02      inference('sup-', [status(thm)], ['37', '38'])).
% 0.78/1.02  thf('40', plain,
% 0.78/1.02      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 0.78/1.02         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.78/1.02      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.78/1.02  thf('41', plain,
% 0.78/1.02      (![X20 : $i, X21 : $i]:
% 0.78/1.02         (~ (r1_tarski @ X20 @ (k1_relat_1 @ X21))
% 0.78/1.02          | ((k1_relat_1 @ (k7_relat_1 @ X21 @ X20)) = (X20))
% 0.78/1.02          | ~ (v1_relat_1 @ X21))),
% 0.78/1.02      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.78/1.02  thf('42', plain,
% 0.78/1.02      (((~ (v1_relat_1 @ sk_A)
% 0.78/1.02         | ((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) = (sk_C))))
% 0.78/1.02         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.78/1.02      inference('sup-', [status(thm)], ['40', '41'])).
% 0.78/1.02  thf('43', plain, ((v1_relat_1 @ sk_A)),
% 0.78/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.02  thf('44', plain,
% 0.78/1.02      ((((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) = (sk_C)))
% 0.78/1.02         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.78/1.02      inference('demod', [status(thm)], ['42', '43'])).
% 0.78/1.02  thf('45', plain, ((v1_relat_1 @ sk_B)),
% 0.78/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.02  thf('46', plain, ((v1_funct_1 @ sk_B)),
% 0.78/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.02  thf('47', plain,
% 0.78/1.02      (((((sk_C) != (sk_C))
% 0.78/1.02         | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 0.78/1.02            (k1_relat_1 @ sk_B))
% 0.78/1.02         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C))
% 0.78/1.02         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))))
% 0.78/1.02         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.78/1.02      inference('demod', [status(thm)], ['39', '44', '45', '46'])).
% 0.78/1.02  thf('48', plain,
% 0.78/1.02      (((~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))
% 0.78/1.02         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C))
% 0.78/1.02         | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 0.78/1.02            (k1_relat_1 @ sk_B))))
% 0.78/1.02         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.78/1.02      inference('simplify', [status(thm)], ['47'])).
% 0.78/1.02  thf('49', plain,
% 0.78/1.02      (((~ (v1_relat_1 @ sk_A)
% 0.78/1.02         | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 0.78/1.02            (k1_relat_1 @ sk_B))
% 0.78/1.02         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C))))
% 0.78/1.02         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.78/1.02      inference('sup-', [status(thm)], ['24', '48'])).
% 0.78/1.02  thf('50', plain, ((v1_relat_1 @ sk_A)),
% 0.78/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.02  thf('51', plain,
% 0.78/1.02      ((((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 0.78/1.02          (k1_relat_1 @ sk_B))
% 0.78/1.02         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C))))
% 0.78/1.02         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.78/1.02      inference('demod', [status(thm)], ['49', '50'])).
% 0.78/1.02  thf('52', plain,
% 0.78/1.02      (((~ (v1_relat_1 @ sk_A)
% 0.78/1.02         | ~ (v1_funct_1 @ sk_A)
% 0.78/1.02         | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 0.78/1.02            (k1_relat_1 @ sk_B))))
% 0.78/1.02         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.78/1.02      inference('sup-', [status(thm)], ['23', '51'])).
% 0.78/1.02  thf('53', plain, ((v1_relat_1 @ sk_A)),
% 0.78/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.02  thf('54', plain, ((v1_funct_1 @ sk_A)),
% 0.78/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.02  thf('55', plain,
% 0.78/1.02      (((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 0.78/1.02         (k1_relat_1 @ sk_B)))
% 0.78/1.02         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.78/1.02      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.78/1.02  thf('56', plain,
% 0.78/1.02      ((((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))
% 0.78/1.02         | ~ (v1_relat_1 @ sk_A)))
% 0.78/1.02         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.78/1.02      inference('sup+', [status(thm)], ['16', '55'])).
% 0.78/1.02  thf('57', plain, ((v1_relat_1 @ sk_A)),
% 0.78/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.02  thf('58', plain,
% 0.78/1.02      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 0.78/1.02         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.78/1.02      inference('demod', [status(thm)], ['56', '57'])).
% 0.78/1.02  thf('59', plain,
% 0.78/1.02      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 0.78/1.02         <= (~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))),
% 0.78/1.02      inference('split', [status(esa)], ['0'])).
% 0.78/1.02  thf('60', plain,
% 0.78/1.02      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))) | 
% 0.78/1.02       ~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.78/1.02      inference('sup-', [status(thm)], ['58', '59'])).
% 0.78/1.02  thf('61', plain,
% 0.78/1.02      (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.78/1.02      inference('sat_resolution*', [status(thm)], ['2', '15', '60'])).
% 0.78/1.02  thf('62', plain,
% 0.78/1.02      (~ (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))),
% 0.78/1.02      inference('simpl_trail', [status(thm)], ['1', '61'])).
% 0.78/1.02  thf('63', plain,
% 0.78/1.02      (![X7 : $i, X8 : $i]:
% 0.78/1.02         (~ (v1_relat_1 @ X7) | (v1_relat_1 @ (k7_relat_1 @ X7 @ X8)))),
% 0.78/1.02      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.78/1.02  thf('64', plain,
% 0.78/1.02      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))
% 0.78/1.02        | (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.78/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.02  thf('65', plain,
% 0.78/1.02      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 0.78/1.02         <= (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))),
% 0.78/1.02      inference('split', [status(esa)], ['64'])).
% 0.78/1.02  thf('66', plain,
% 0.78/1.02      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))) | 
% 0.78/1.02       ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.78/1.02      inference('split', [status(esa)], ['64'])).
% 0.78/1.02  thf('67', plain,
% 0.78/1.02      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 0.78/1.02      inference('sat_resolution*', [status(thm)], ['2', '15', '60', '66'])).
% 0.78/1.02  thf('68', plain,
% 0.78/1.02      ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))),
% 0.78/1.02      inference('simpl_trail', [status(thm)], ['65', '67'])).
% 0.78/1.02  thf('69', plain,
% 0.78/1.02      (![X12 : $i, X13 : $i]:
% 0.78/1.02         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 0.78/1.02          | ~ (v1_relat_1 @ X12))),
% 0.78/1.02      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.78/1.02  thf(t46_relat_1, axiom,
% 0.78/1.02    (![A:$i]:
% 0.78/1.02     ( ( v1_relat_1 @ A ) =>
% 0.78/1.02       ( ![B:$i]:
% 0.78/1.02         ( ( v1_relat_1 @ B ) =>
% 0.78/1.02           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.78/1.02             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.78/1.02  thf('70', plain,
% 0.78/1.02      (![X16 : $i, X17 : $i]:
% 0.78/1.02         (~ (v1_relat_1 @ X16)
% 0.78/1.02          | ((k1_relat_1 @ (k5_relat_1 @ X17 @ X16)) = (k1_relat_1 @ X17))
% 0.78/1.02          | ~ (r1_tarski @ (k2_relat_1 @ X17) @ (k1_relat_1 @ X16))
% 0.78/1.02          | ~ (v1_relat_1 @ X17))),
% 0.78/1.02      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.78/1.02  thf('71', plain,
% 0.78/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/1.02         (~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k1_relat_1 @ X2))
% 0.78/1.02          | ~ (v1_relat_1 @ X1)
% 0.78/1.02          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.78/1.02          | ((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2))
% 0.78/1.02              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.78/1.02          | ~ (v1_relat_1 @ X2))),
% 0.78/1.02      inference('sup-', [status(thm)], ['69', '70'])).
% 0.78/1.02  thf('72', plain,
% 0.78/1.02      ((~ (v1_relat_1 @ sk_B)
% 0.78/1.02        | ((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B))
% 0.78/1.02            = (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)))
% 0.78/1.02        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))
% 0.78/1.02        | ~ (v1_relat_1 @ sk_A))),
% 0.78/1.02      inference('sup-', [status(thm)], ['68', '71'])).
% 0.78/1.02  thf('73', plain, ((v1_relat_1 @ sk_B)),
% 0.78/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.02  thf('74', plain,
% 0.78/1.02      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 0.78/1.02         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 0.78/1.02      inference('split', [status(esa)], ['4'])).
% 0.78/1.02  thf('75', plain,
% 0.78/1.02      (![X20 : $i, X21 : $i]:
% 0.78/1.02         (~ (r1_tarski @ X20 @ (k1_relat_1 @ X21))
% 0.78/1.02          | ((k1_relat_1 @ (k7_relat_1 @ X21 @ X20)) = (X20))
% 0.78/1.02          | ~ (v1_relat_1 @ X21))),
% 0.78/1.02      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.78/1.02  thf('76', plain,
% 0.78/1.02      (((~ (v1_relat_1 @ sk_A)
% 0.78/1.02         | ((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) = (sk_C))))
% 0.78/1.02         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 0.78/1.02      inference('sup-', [status(thm)], ['74', '75'])).
% 0.78/1.02  thf('77', plain, ((v1_relat_1 @ sk_A)),
% 0.78/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.02  thf('78', plain,
% 0.78/1.02      ((((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) = (sk_C)))
% 0.78/1.02         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 0.78/1.02      inference('demod', [status(thm)], ['76', '77'])).
% 0.78/1.02  thf('79', plain,
% 0.78/1.02      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 0.78/1.02       ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.78/1.02      inference('split', [status(esa)], ['4'])).
% 0.78/1.02  thf('80', plain, (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))),
% 0.78/1.02      inference('sat_resolution*', [status(thm)], ['2', '15', '60', '79'])).
% 0.78/1.02  thf('81', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) = (sk_C))),
% 0.78/1.02      inference('simpl_trail', [status(thm)], ['78', '80'])).
% 0.78/1.02  thf('82', plain, ((v1_relat_1 @ sk_A)),
% 0.78/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.02  thf('83', plain,
% 0.78/1.02      ((((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B))
% 0.78/1.02          = (sk_C))
% 0.78/1.02        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)))),
% 0.78/1.02      inference('demod', [status(thm)], ['72', '73', '81', '82'])).
% 0.78/1.02  thf('84', plain,
% 0.78/1.02      ((~ (v1_relat_1 @ sk_A)
% 0.78/1.02        | ((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B))
% 0.78/1.02            = (sk_C)))),
% 0.78/1.02      inference('sup-', [status(thm)], ['63', '83'])).
% 0.78/1.02  thf('85', plain, ((v1_relat_1 @ sk_A)),
% 0.78/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.02  thf('86', plain,
% 0.78/1.02      (((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B))
% 0.78/1.02         = (sk_C))),
% 0.78/1.02      inference('demod', [status(thm)], ['84', '85'])).
% 0.78/1.02  thf('87', plain,
% 0.78/1.02      (![X5 : $i, X6 : $i]:
% 0.78/1.02         (~ (v1_relat_1 @ X5)
% 0.78/1.02          | ~ (v1_relat_1 @ X6)
% 0.78/1.02          | (v1_relat_1 @ (k5_relat_1 @ X5 @ X6)))),
% 0.78/1.02      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.78/1.02  thf('88', plain,
% 0.78/1.02      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.78/1.02         (~ (v1_relat_1 @ X9)
% 0.78/1.02          | ((k7_relat_1 @ (k5_relat_1 @ X10 @ X9) @ X11)
% 0.78/1.02              = (k5_relat_1 @ (k7_relat_1 @ X10 @ X11) @ X9))
% 0.78/1.02          | ~ (v1_relat_1 @ X10))),
% 0.78/1.02      inference('cnf', [status(esa)], [t112_relat_1])).
% 0.78/1.02  thf(t89_relat_1, axiom,
% 0.78/1.02    (![A:$i,B:$i]:
% 0.78/1.02     ( ( v1_relat_1 @ B ) =>
% 0.78/1.02       ( r1_tarski @
% 0.78/1.02         ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ))).
% 0.78/1.02  thf('89', plain,
% 0.78/1.02      (![X18 : $i, X19 : $i]:
% 0.78/1.02         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X18 @ X19)) @ 
% 0.78/1.02           (k1_relat_1 @ X18))
% 0.78/1.02          | ~ (v1_relat_1 @ X18))),
% 0.78/1.02      inference('cnf', [status(esa)], [t89_relat_1])).
% 0.78/1.02  thf('90', plain,
% 0.78/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/1.02         ((r1_tarski @ 
% 0.78/1.02           (k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)) @ 
% 0.78/1.02           (k1_relat_1 @ (k5_relat_1 @ X2 @ X0)))
% 0.78/1.02          | ~ (v1_relat_1 @ X2)
% 0.78/1.02          | ~ (v1_relat_1 @ X0)
% 0.78/1.02          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X0)))),
% 0.78/1.02      inference('sup+', [status(thm)], ['88', '89'])).
% 0.78/1.02  thf('91', plain,
% 0.78/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/1.02         (~ (v1_relat_1 @ X0)
% 0.78/1.02          | ~ (v1_relat_1 @ X1)
% 0.78/1.02          | ~ (v1_relat_1 @ X0)
% 0.78/1.02          | ~ (v1_relat_1 @ X1)
% 0.78/1.02          | (r1_tarski @ 
% 0.78/1.02             (k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0)) @ 
% 0.78/1.02             (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 0.78/1.02      inference('sup-', [status(thm)], ['87', '90'])).
% 0.78/1.02  thf('92', plain,
% 0.78/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/1.02         ((r1_tarski @ 
% 0.78/1.02           (k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0)) @ 
% 0.78/1.02           (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.78/1.02          | ~ (v1_relat_1 @ X1)
% 0.78/1.02          | ~ (v1_relat_1 @ X0))),
% 0.78/1.02      inference('simplify', [status(thm)], ['91'])).
% 0.78/1.02  thf('93', plain,
% 0.78/1.02      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))
% 0.78/1.02        | ~ (v1_relat_1 @ sk_B)
% 0.78/1.02        | ~ (v1_relat_1 @ sk_A))),
% 0.78/1.02      inference('sup+', [status(thm)], ['86', '92'])).
% 0.78/1.02  thf('94', plain, ((v1_relat_1 @ sk_B)),
% 0.78/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.02  thf('95', plain, ((v1_relat_1 @ sk_A)),
% 0.78/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.02  thf('96', plain,
% 0.78/1.02      ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))),
% 0.78/1.02      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.78/1.02  thf('97', plain, ($false), inference('demod', [status(thm)], ['62', '96'])).
% 0.78/1.02  
% 0.78/1.02  % SZS output end Refutation
% 0.78/1.02  
% 0.85/1.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
