%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0628+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KgXirO2V7f

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:13 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 192 expanded)
%              Number of leaves         :   16 (  59 expanded)
%              Depth                    :   18
%              Number of atoms          :  964 (3377 expanded)
%              Number of equality atoms :   52 ( 170 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t23_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A )
              = ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v1_funct_1 @ C ) )
           => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
             => ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A )
                = ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_funct_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc2_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( X2
        = ( k1_funct_1 @ X1 @ X0 ) )
      | ( X2 != k1_xboole_0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( k1_xboole_0
        = ( k1_funct_1 @ X1 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t21_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
          <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
              & ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( r2_hidden @ X7 @ ( k1_relat_1 @ ( k5_relat_1 @ X6 @ X8 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X6 @ X7 ) @ ( k1_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X1 @ X2 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( k1_funct_1 @ X1 @ X2 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( k1_xboole_0
        = ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X1 @ X2 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( k1_funct_1 @ X1 @ X2 ) @ ( k1_relat_1 @ X0 ) )
      | ( k1_xboole_0
        = ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X1 @ X2 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( r2_hidden @ X7 @ ( k1_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X6 @ X7 ) @ ( k1_relat_1 @ X8 ) )
      | ( r2_hidden @ X7 @ ( k1_relat_1 @ ( k5_relat_1 @ X6 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( k1_xboole_0
        = ( k1_funct_1 @ ( k5_relat_1 @ X2 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X2 ) )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) ) )
      | ( k1_xboole_0
        = ( k1_funct_1 @ ( k5_relat_1 @ X2 @ X0 ) @ X1 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( k1_xboole_0
        = ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ X0 ) @ sk_A ) )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ X0 ) @ sk_A ) )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf(t22_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A )
              = ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) )).

thf('18',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X9 @ X10 ) @ X11 )
        = ( k1_funct_1 @ X10 @ ( k1_funct_1 @ X9 @ X11 ) ) )
      | ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ ( k5_relat_1 @ X9 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ X0 ) @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ X0 ) @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ X0 ) @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C ) @ sk_A )
 != ( k1_funct_1 @ sk_C @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( k1_xboole_0
        = ( k1_funct_1 @ X1 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('27',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( r2_hidden @ X7 @ ( k1_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X6 @ X7 ) @ ( k1_relat_1 @ X8 ) )
      | ( r2_hidden @ X7 @ ( k1_relat_1 @ ( k5_relat_1 @ X6 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X2 ) )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( k1_xboole_0
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X2 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X9 @ X10 ) @ X11 )
        = ( k1_funct_1 @ X10 @ ( k1_funct_1 @ X9 @ X11 ) ) )
      | ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ ( k5_relat_1 @ X9 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( k1_xboole_0
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( k1_xboole_0
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C ) @ sk_A )
 != ( k1_funct_1 @ sk_C @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( k1_funct_1 @ sk_C @ ( k1_funct_1 @ sk_B @ sk_A ) )
     != ( k1_funct_1 @ sk_C @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( k1_xboole_0
      = ( k1_funct_1 @ sk_C @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( ( k1_funct_1 @ sk_C @ ( k1_funct_1 @ sk_B @ sk_A ) )
     != ( k1_funct_1 @ sk_C @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ( k1_xboole_0
      = ( k1_funct_1 @ sk_C @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( k1_xboole_0
    = ( k1_funct_1 @ sk_C @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C ) @ sk_A )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['24','45'])).

thf('47',plain,
    ( ( ( k1_funct_1 @ sk_C @ ( k1_funct_1 @ sk_B @ sk_A ) )
     != k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['23','46'])).

thf('48',plain,
    ( k1_xboole_0
    = ( k1_funct_1 @ sk_C @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('49',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('52',plain,
    ( k1_xboole_0
    = ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C ) @ sk_A )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['24','45'])).

thf('54',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['52','53'])).


%------------------------------------------------------------------------------
