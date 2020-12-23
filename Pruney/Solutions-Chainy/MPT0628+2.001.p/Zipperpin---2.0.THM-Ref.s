%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1yyDIV2dBI

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:47 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 442 expanded)
%              Number of leaves         :   18 ( 122 expanded)
%              Depth                    :   27
%              Number of atoms          : 1631 (8206 expanded)
%              Number of equality atoms :  101 ( 469 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(fc2_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X14 @ X15 ) ) ) ),
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

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X10 @ ( k1_relat_1 @ X11 ) )
      | ( X12
        = ( k1_funct_1 @ X11 @ X10 ) )
      | ( X12 != k1_xboole_0 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( k1_xboole_0
        = ( k1_funct_1 @ X11 @ X10 ) )
      | ( r2_hidden @ X10 @ ( k1_relat_1 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

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

thf('4',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X16 @ X17 ) @ X18 )
        = ( k1_funct_1 @ X17 @ ( k1_funct_1 @ X16 @ X18 ) ) )
      | ~ ( r2_hidden @ X18 @ ( k1_relat_1 @ ( k5_relat_1 @ X16 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( k1_xboole_0
        = ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ X2 ) ) )
      | ( k1_xboole_0
        = ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

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

thf('10',plain,(
    ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C ) @ sk_A )
 != ( k1_funct_1 @ sk_C @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C ) @ sk_A )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_B )
    | ( k1_xboole_0
      = ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C ) @ sk_A )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C ) @ sk_A ) )
    | ( k1_xboole_0
      = ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12','13','14','15'])).

thf('17',plain,
    ( k1_xboole_0
    = ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('19',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('20',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ X10 @ X13 ) @ X11 )
      | ( X13
       != ( k1_funct_1 @ X11 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('22',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ X10 @ ( k1_funct_1 @ X11 @ X10 ) ) @ X11 )
      | ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( k1_xboole_0
        = ( k1_funct_1 @ X11 @ X10 ) )
      | ( r2_hidden @ X10 @ ( k1_relat_1 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('28',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ X10 @ ( k1_funct_1 @ X11 @ X10 ) ) @ X11 )
      | ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k1_funct_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_funct_1 @ X0 @ X1 ) ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_funct_1 @ X0 @ X1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( k1_xboole_0
        = ( k1_funct_1 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

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

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X2
       != ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X4 ) @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X4 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X2 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_xboole_0
        = ( k1_funct_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( k1_funct_1 @ X0 @ X1 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X1 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( k1_funct_1 @ X0 @ X1 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( k1_xboole_0
        = ( k1_funct_1 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) @ ( k5_relat_1 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) @ ( k5_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('41',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X19 @ X21 ) @ X20 )
      | ( r2_hidden @ X19 @ ( k1_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( k1_xboole_0
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B @ X0 ) )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B @ X0 ) )
      | ( k1_xboole_0
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B @ X0 ) )
      | ( k1_xboole_0
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ( k1_xboole_0
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B @ X0 ) )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ X0 ) ) )
      | ( k1_xboole_0
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ X0 ) ) )
      | ( k1_xboole_0
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('53',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_funct_1 @ X0 @ X1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( k1_xboole_0
        = ( k1_funct_1 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X1 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( k1_funct_1 @ X0 @ X1 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( k1_xboole_0
        = ( k1_funct_1 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k1_funct_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k1_funct_1 @ X2 @ ( k1_funct_1 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_funct_1 @ X2 @ ( k1_funct_1 @ X0 @ X1 ) ) ) @ ( k5_relat_1 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_funct_1 @ X2 @ ( k1_funct_1 @ X0 @ X1 ) ) ) @ ( k5_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( k1_xboole_0
        = ( k1_funct_1 @ X2 @ ( k1_funct_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( k1_xboole_0
        = ( k1_funct_1 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X19 @ X21 ) @ X20 )
      | ( X21
        = ( k1_funct_1 @ X20 @ X19 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k1_funct_1 @ X1 @ X2 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ X2 ) )
        = ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ X2 ) )
        = ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( k1_xboole_0
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( k1_xboole_0
        = ( k1_funct_1 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['53','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k1_funct_1 @ X1 @ X2 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ( k1_xboole_0
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ X2 ) )
        = ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ X2 ) )
        = ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( k1_xboole_0
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ( k1_xboole_0
        = ( k1_funct_1 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['52','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k1_funct_1 @ X1 @ X2 ) )
      | ( k1_xboole_0
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ X2 ) ) )
      | ( ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ X2 ) )
        = ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C ) @ sk_A )
 != ( k1_funct_1 @ sk_C @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C ) @ sk_A )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C ) @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( k1_xboole_0
      = ( k1_funct_1 @ sk_C @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ( k1_xboole_0
      = ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C ) @ sk_A )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C ) @ sk_A ) )
    | ( k1_xboole_0
      = ( k1_funct_1 @ sk_C @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ( k1_xboole_0
      = ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66','67','68','69'])).

thf('71',plain,
    ( ( k1_xboole_0
      = ( k1_funct_1 @ sk_B @ sk_A ) )
    | ( k1_xboole_0
      = ( k1_funct_1 @ sk_C @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C ) @ sk_A )
 != ( k1_funct_1 @ sk_C @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C ) @ sk_A )
     != k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( k1_xboole_0
    = ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(simplify,[status(thm)],['16'])).

thf('75',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( k1_xboole_0
    = ( k1_funct_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_funct_1 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','76'])).

thf('78',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X16 @ X17 ) @ X18 )
        = ( k1_funct_1 @ X17 @ ( k1_funct_1 @ X16 @ X18 ) ) )
      | ~ ( r2_hidden @ X18 @ ( k1_relat_1 @ ( k5_relat_1 @ X16 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k1_funct_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( k1_xboole_0
    = ( k1_funct_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['75'])).

thf('81',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k1_funct_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k1_funct_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ( k1_xboole_0
      = ( k1_funct_1 @ sk_C @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( k1_xboole_0
      = ( k1_funct_1 @ sk_C @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['17','84'])).

thf('86',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( k1_xboole_0
      = ( k1_funct_1 @ sk_C @ k1_xboole_0 ) )
    | ( k1_xboole_0
      = ( k1_funct_1 @ sk_C @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,
    ( k1_xboole_0
    = ( k1_funct_1 @ sk_C @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C ) @ sk_A )
 != ( k1_funct_1 @ sk_C @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( k1_xboole_0
    = ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(simplify,[status(thm)],['16'])).

thf('92',plain,(
    k1_xboole_0
 != ( k1_funct_1 @ sk_C @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( k1_xboole_0
    = ( k1_funct_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['75'])).

thf('94',plain,(
    k1_xboole_0
 != ( k1_funct_1 @ sk_C @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['89','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1yyDIV2dBI
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:48:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.61  % Solved by: fo/fo7.sh
% 0.35/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.61  % done 79 iterations in 0.130s
% 0.35/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.61  % SZS output start Refutation
% 0.35/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.35/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.61  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.35/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.61  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.35/0.61  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.35/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.61  thf(dt_k5_relat_1, axiom,
% 0.35/0.61    (![A:$i,B:$i]:
% 0.35/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.35/0.61       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.35/0.61  thf('0', plain,
% 0.35/0.61      (![X8 : $i, X9 : $i]:
% 0.35/0.61         (~ (v1_relat_1 @ X8)
% 0.35/0.61          | ~ (v1_relat_1 @ X9)
% 0.35/0.61          | (v1_relat_1 @ (k5_relat_1 @ X8 @ X9)))),
% 0.35/0.61      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.35/0.61  thf(fc2_funct_1, axiom,
% 0.35/0.61    (![A:$i,B:$i]:
% 0.35/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v1_relat_1 @ B ) & 
% 0.35/0.61         ( v1_funct_1 @ B ) ) =>
% 0.35/0.61       ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) & 
% 0.35/0.61         ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ))).
% 0.35/0.61  thf('1', plain,
% 0.35/0.61      (![X14 : $i, X15 : $i]:
% 0.35/0.61         (~ (v1_funct_1 @ X14)
% 0.35/0.61          | ~ (v1_relat_1 @ X14)
% 0.35/0.61          | ~ (v1_relat_1 @ X15)
% 0.35/0.61          | ~ (v1_funct_1 @ X15)
% 0.35/0.61          | (v1_funct_1 @ (k5_relat_1 @ X14 @ X15)))),
% 0.35/0.61      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.35/0.61  thf(d4_funct_1, axiom,
% 0.35/0.61    (![A:$i]:
% 0.35/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.35/0.61       ( ![B:$i,C:$i]:
% 0.35/0.61         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.35/0.61             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.35/0.61               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.35/0.61           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.35/0.61             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.35/0.61               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.35/0.61  thf('2', plain,
% 0.35/0.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.35/0.61         ((r2_hidden @ X10 @ (k1_relat_1 @ X11))
% 0.35/0.61          | ((X12) = (k1_funct_1 @ X11 @ X10))
% 0.35/0.61          | ((X12) != (k1_xboole_0))
% 0.35/0.61          | ~ (v1_funct_1 @ X11)
% 0.35/0.61          | ~ (v1_relat_1 @ X11))),
% 0.35/0.61      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.35/0.61  thf('3', plain,
% 0.35/0.61      (![X10 : $i, X11 : $i]:
% 0.35/0.61         (~ (v1_relat_1 @ X11)
% 0.35/0.61          | ~ (v1_funct_1 @ X11)
% 0.35/0.61          | ((k1_xboole_0) = (k1_funct_1 @ X11 @ X10))
% 0.35/0.61          | (r2_hidden @ X10 @ (k1_relat_1 @ X11)))),
% 0.35/0.61      inference('simplify', [status(thm)], ['2'])).
% 0.35/0.61  thf(t22_funct_1, axiom,
% 0.35/0.61    (![A:$i,B:$i]:
% 0.35/0.61     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.35/0.61       ( ![C:$i]:
% 0.35/0.61         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.35/0.61           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) =>
% 0.35/0.61             ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A ) =
% 0.35/0.61               ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) ))).
% 0.35/0.61  thf('4', plain,
% 0.35/0.61      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.35/0.61         (~ (v1_relat_1 @ X16)
% 0.35/0.61          | ~ (v1_funct_1 @ X16)
% 0.35/0.61          | ((k1_funct_1 @ (k5_relat_1 @ X16 @ X17) @ X18)
% 0.35/0.61              = (k1_funct_1 @ X17 @ (k1_funct_1 @ X16 @ X18)))
% 0.35/0.61          | ~ (r2_hidden @ X18 @ (k1_relat_1 @ (k5_relat_1 @ X16 @ X17)))
% 0.35/0.61          | ~ (v1_funct_1 @ X17)
% 0.35/0.61          | ~ (v1_relat_1 @ X17))),
% 0.35/0.61      inference('cnf', [status(esa)], [t22_funct_1])).
% 0.35/0.61  thf('5', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.61         (((k1_xboole_0) = (k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2))
% 0.35/0.61          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.35/0.61          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.35/0.61          | ~ (v1_relat_1 @ X0)
% 0.35/0.61          | ~ (v1_funct_1 @ X0)
% 0.35/0.61          | ((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.35/0.61              = (k1_funct_1 @ X0 @ (k1_funct_1 @ X1 @ X2)))
% 0.35/0.61          | ~ (v1_funct_1 @ X1)
% 0.35/0.61          | ~ (v1_relat_1 @ X1))),
% 0.35/0.61      inference('sup-', [status(thm)], ['3', '4'])).
% 0.35/0.61  thf('6', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.61         (~ (v1_funct_1 @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ X1)
% 0.35/0.61          | ~ (v1_funct_1 @ X1)
% 0.35/0.61          | ~ (v1_relat_1 @ X1)
% 0.35/0.61          | ~ (v1_funct_1 @ X1)
% 0.35/0.61          | ((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.35/0.61              = (k1_funct_1 @ X0 @ (k1_funct_1 @ X1 @ X2)))
% 0.35/0.61          | ~ (v1_funct_1 @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.35/0.61          | ((k1_xboole_0) = (k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['1', '5'])).
% 0.35/0.61  thf('7', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.61         (((k1_xboole_0) = (k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2))
% 0.35/0.61          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.35/0.61          | ((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.35/0.61              = (k1_funct_1 @ X0 @ (k1_funct_1 @ X1 @ X2)))
% 0.35/0.61          | ~ (v1_funct_1 @ X1)
% 0.35/0.61          | ~ (v1_relat_1 @ X1)
% 0.35/0.61          | ~ (v1_relat_1 @ X0)
% 0.35/0.61          | ~ (v1_funct_1 @ X0))),
% 0.35/0.61      inference('simplify', [status(thm)], ['6'])).
% 0.35/0.61  thf('8', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.61         (~ (v1_relat_1 @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ X1)
% 0.35/0.61          | ~ (v1_funct_1 @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ X1)
% 0.35/0.61          | ~ (v1_funct_1 @ X1)
% 0.35/0.61          | ((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.35/0.61              = (k1_funct_1 @ X0 @ (k1_funct_1 @ X1 @ X2)))
% 0.35/0.61          | ((k1_xboole_0) = (k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['0', '7'])).
% 0.35/0.61  thf('9', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.61         (((k1_xboole_0) = (k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2))
% 0.35/0.61          | ((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.35/0.61              = (k1_funct_1 @ X0 @ (k1_funct_1 @ X1 @ X2)))
% 0.35/0.61          | ~ (v1_funct_1 @ X1)
% 0.35/0.61          | ~ (v1_funct_1 @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ X1)
% 0.35/0.61          | ~ (v1_relat_1 @ X0))),
% 0.35/0.61      inference('simplify', [status(thm)], ['8'])).
% 0.35/0.61  thf(t23_funct_1, conjecture,
% 0.35/0.61    (![A:$i,B:$i]:
% 0.35/0.61     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.35/0.61       ( ![C:$i]:
% 0.35/0.61         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.35/0.61           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.35/0.61             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.35/0.61               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 0.35/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.61    (~( ![A:$i,B:$i]:
% 0.35/0.61        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.35/0.61          ( ![C:$i]:
% 0.35/0.61            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.35/0.61              ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.35/0.61                ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.35/0.61                  ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ) )),
% 0.35/0.61    inference('cnf.neg', [status(esa)], [t23_funct_1])).
% 0.35/0.61  thf('10', plain,
% 0.35/0.61      (((k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C) @ sk_A)
% 0.35/0.61         != (k1_funct_1 @ sk_C @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('11', plain,
% 0.35/0.61      ((((k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C) @ sk_A)
% 0.35/0.61          != (k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C) @ sk_A))
% 0.35/0.61        | ~ (v1_relat_1 @ sk_C)
% 0.35/0.61        | ~ (v1_relat_1 @ sk_B)
% 0.35/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.35/0.61        | ~ (v1_funct_1 @ sk_B)
% 0.35/0.61        | ((k1_xboole_0) = (k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C) @ sk_A)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['9', '10'])).
% 0.35/0.61  thf('12', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('13', plain, ((v1_relat_1 @ sk_B)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('14', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('15', plain, ((v1_funct_1 @ sk_B)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('16', plain,
% 0.35/0.61      ((((k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C) @ sk_A)
% 0.35/0.61          != (k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C) @ sk_A))
% 0.35/0.61        | ((k1_xboole_0) = (k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C) @ sk_A)))),
% 0.35/0.61      inference('demod', [status(thm)], ['11', '12', '13', '14', '15'])).
% 0.35/0.61  thf('17', plain,
% 0.35/0.61      (((k1_xboole_0) = (k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C) @ sk_A))),
% 0.35/0.61      inference('simplify', [status(thm)], ['16'])).
% 0.35/0.61  thf('18', plain,
% 0.35/0.61      (![X14 : $i, X15 : $i]:
% 0.35/0.61         (~ (v1_funct_1 @ X14)
% 0.35/0.61          | ~ (v1_relat_1 @ X14)
% 0.35/0.61          | ~ (v1_relat_1 @ X15)
% 0.35/0.61          | ~ (v1_funct_1 @ X15)
% 0.35/0.61          | (v1_funct_1 @ (k5_relat_1 @ X14 @ X15)))),
% 0.35/0.61      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.35/0.61  thf('19', plain,
% 0.35/0.61      (![X8 : $i, X9 : $i]:
% 0.35/0.61         (~ (v1_relat_1 @ X8)
% 0.35/0.61          | ~ (v1_relat_1 @ X9)
% 0.35/0.61          | (v1_relat_1 @ (k5_relat_1 @ X8 @ X9)))),
% 0.35/0.61      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.35/0.61  thf('20', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('21', plain,
% 0.35/0.61      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.35/0.61         (~ (r2_hidden @ X10 @ (k1_relat_1 @ X11))
% 0.35/0.61          | (r2_hidden @ (k4_tarski @ X10 @ X13) @ X11)
% 0.35/0.61          | ((X13) != (k1_funct_1 @ X11 @ X10))
% 0.35/0.61          | ~ (v1_funct_1 @ X11)
% 0.35/0.61          | ~ (v1_relat_1 @ X11))),
% 0.35/0.61      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.35/0.61  thf('22', plain,
% 0.35/0.61      (![X10 : $i, X11 : $i]:
% 0.35/0.61         (~ (v1_relat_1 @ X11)
% 0.35/0.61          | ~ (v1_funct_1 @ X11)
% 0.35/0.61          | (r2_hidden @ (k4_tarski @ X10 @ (k1_funct_1 @ X11 @ X10)) @ X11)
% 0.35/0.61          | ~ (r2_hidden @ X10 @ (k1_relat_1 @ X11)))),
% 0.35/0.61      inference('simplify', [status(thm)], ['21'])).
% 0.35/0.61  thf('23', plain,
% 0.35/0.61      (((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)
% 0.35/0.61        | ~ (v1_funct_1 @ sk_B)
% 0.35/0.61        | ~ (v1_relat_1 @ sk_B))),
% 0.35/0.61      inference('sup-', [status(thm)], ['20', '22'])).
% 0.35/0.61  thf('24', plain, ((v1_funct_1 @ sk_B)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('26', plain,
% 0.35/0.61      ((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)),
% 0.35/0.61      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.35/0.61  thf('27', plain,
% 0.35/0.61      (![X10 : $i, X11 : $i]:
% 0.35/0.61         (~ (v1_relat_1 @ X11)
% 0.35/0.61          | ~ (v1_funct_1 @ X11)
% 0.35/0.61          | ((k1_xboole_0) = (k1_funct_1 @ X11 @ X10))
% 0.35/0.61          | (r2_hidden @ X10 @ (k1_relat_1 @ X11)))),
% 0.35/0.61      inference('simplify', [status(thm)], ['2'])).
% 0.35/0.61  thf('28', plain,
% 0.35/0.61      (![X10 : $i, X11 : $i]:
% 0.35/0.61         (~ (v1_relat_1 @ X11)
% 0.35/0.61          | ~ (v1_funct_1 @ X11)
% 0.35/0.61          | (r2_hidden @ (k4_tarski @ X10 @ (k1_funct_1 @ X11 @ X10)) @ X11)
% 0.35/0.61          | ~ (r2_hidden @ X10 @ (k1_relat_1 @ X11)))),
% 0.35/0.61      inference('simplify', [status(thm)], ['21'])).
% 0.35/0.61  thf('29', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         (((k1_xboole_0) = (k1_funct_1 @ X0 @ X1))
% 0.35/0.61          | ~ (v1_funct_1 @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ X0)
% 0.35/0.61          | (r2_hidden @ (k4_tarski @ X1 @ (k1_funct_1 @ X0 @ X1)) @ X0)
% 0.35/0.61          | ~ (v1_funct_1 @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ X0))),
% 0.35/0.61      inference('sup-', [status(thm)], ['27', '28'])).
% 0.35/0.61  thf('30', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         ((r2_hidden @ (k4_tarski @ X1 @ (k1_funct_1 @ X0 @ X1)) @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ X0)
% 0.35/0.61          | ~ (v1_funct_1 @ X0)
% 0.35/0.61          | ((k1_xboole_0) = (k1_funct_1 @ X0 @ X1)))),
% 0.35/0.61      inference('simplify', [status(thm)], ['29'])).
% 0.35/0.61  thf('31', plain,
% 0.35/0.61      (![X8 : $i, X9 : $i]:
% 0.35/0.61         (~ (v1_relat_1 @ X8)
% 0.35/0.61          | ~ (v1_relat_1 @ X9)
% 0.35/0.61          | (v1_relat_1 @ (k5_relat_1 @ X8 @ X9)))),
% 0.35/0.61      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.35/0.61  thf(d8_relat_1, axiom,
% 0.35/0.61    (![A:$i]:
% 0.35/0.61     ( ( v1_relat_1 @ A ) =>
% 0.35/0.61       ( ![B:$i]:
% 0.35/0.61         ( ( v1_relat_1 @ B ) =>
% 0.35/0.61           ( ![C:$i]:
% 0.35/0.61             ( ( v1_relat_1 @ C ) =>
% 0.35/0.61               ( ( ( C ) = ( k5_relat_1 @ A @ B ) ) <=>
% 0.35/0.61                 ( ![D:$i,E:$i]:
% 0.35/0.61                   ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 0.35/0.61                     ( ?[F:$i]:
% 0.35/0.61                       ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B ) & 
% 0.35/0.61                         ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.35/0.61  thf('32', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.35/0.61         (~ (v1_relat_1 @ X0)
% 0.35/0.61          | ((X2) != (k5_relat_1 @ X1 @ X0))
% 0.35/0.61          | (r2_hidden @ (k4_tarski @ X3 @ X4) @ X2)
% 0.35/0.61          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ X1)
% 0.35/0.61          | ~ (r2_hidden @ (k4_tarski @ X5 @ X4) @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ X2)
% 0.35/0.61          | ~ (v1_relat_1 @ X1))),
% 0.35/0.61      inference('cnf', [status(esa)], [d8_relat_1])).
% 0.35/0.61  thf('33', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.35/0.61         (~ (v1_relat_1 @ X1)
% 0.35/0.61          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.35/0.61          | ~ (r2_hidden @ (k4_tarski @ X5 @ X4) @ X0)
% 0.35/0.61          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ X1)
% 0.35/0.61          | (r2_hidden @ (k4_tarski @ X3 @ X4) @ (k5_relat_1 @ X1 @ X0))
% 0.35/0.61          | ~ (v1_relat_1 @ X0))),
% 0.35/0.61      inference('simplify', [status(thm)], ['32'])).
% 0.35/0.61  thf('34', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.35/0.61         (~ (v1_relat_1 @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ X1)
% 0.35/0.61          | ~ (v1_relat_1 @ X0)
% 0.35/0.61          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k5_relat_1 @ X1 @ X0))
% 0.35/0.61          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X1)
% 0.35/0.61          | ~ (r2_hidden @ (k4_tarski @ X4 @ X2) @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ X1))),
% 0.35/0.61      inference('sup-', [status(thm)], ['31', '33'])).
% 0.35/0.61  thf('35', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.35/0.61         (~ (r2_hidden @ (k4_tarski @ X4 @ X2) @ X0)
% 0.35/0.61          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X1)
% 0.35/0.61          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k5_relat_1 @ X1 @ X0))
% 0.35/0.61          | ~ (v1_relat_1 @ X1)
% 0.35/0.61          | ~ (v1_relat_1 @ X0))),
% 0.35/0.61      inference('simplify', [status(thm)], ['34'])).
% 0.35/0.61  thf('36', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.35/0.61         (((k1_xboole_0) = (k1_funct_1 @ X0 @ X1))
% 0.35/0.61          | ~ (v1_funct_1 @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ X2)
% 0.35/0.61          | (r2_hidden @ (k4_tarski @ X3 @ (k1_funct_1 @ X0 @ X1)) @ 
% 0.35/0.61             (k5_relat_1 @ X2 @ X0))
% 0.35/0.61          | ~ (r2_hidden @ (k4_tarski @ X3 @ X1) @ X2))),
% 0.35/0.61      inference('sup-', [status(thm)], ['30', '35'])).
% 0.35/0.61  thf('37', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.35/0.61         (~ (r2_hidden @ (k4_tarski @ X3 @ X1) @ X2)
% 0.35/0.61          | (r2_hidden @ (k4_tarski @ X3 @ (k1_funct_1 @ X0 @ X1)) @ 
% 0.35/0.61             (k5_relat_1 @ X2 @ X0))
% 0.35/0.61          | ~ (v1_relat_1 @ X2)
% 0.35/0.61          | ~ (v1_relat_1 @ X0)
% 0.35/0.61          | ~ (v1_funct_1 @ X0)
% 0.35/0.61          | ((k1_xboole_0) = (k1_funct_1 @ X0 @ X1)))),
% 0.35/0.61      inference('simplify', [status(thm)], ['36'])).
% 0.35/0.61  thf('38', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         (((k1_xboole_0) = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.35/0.61          | ~ (v1_funct_1 @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ sk_B)
% 0.35/0.61          | (r2_hidden @ 
% 0.35/0.61             (k4_tarski @ sk_A @ (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_B @ sk_A))) @ 
% 0.35/0.61             (k5_relat_1 @ sk_B @ X0)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['26', '37'])).
% 0.35/0.61  thf('39', plain, ((v1_relat_1 @ sk_B)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('40', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         (((k1_xboole_0) = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.35/0.61          | ~ (v1_funct_1 @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ X0)
% 0.35/0.61          | (r2_hidden @ 
% 0.35/0.61             (k4_tarski @ sk_A @ (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_B @ sk_A))) @ 
% 0.35/0.61             (k5_relat_1 @ sk_B @ X0)))),
% 0.35/0.61      inference('demod', [status(thm)], ['38', '39'])).
% 0.35/0.61  thf(t8_funct_1, axiom,
% 0.35/0.61    (![A:$i,B:$i,C:$i]:
% 0.35/0.61     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.35/0.61       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.35/0.61         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.35/0.61           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.35/0.61  thf('41', plain,
% 0.35/0.61      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.35/0.61         (~ (r2_hidden @ (k4_tarski @ X19 @ X21) @ X20)
% 0.35/0.61          | (r2_hidden @ X19 @ (k1_relat_1 @ X20))
% 0.35/0.61          | ~ (v1_funct_1 @ X20)
% 0.35/0.61          | ~ (v1_relat_1 @ X20))),
% 0.35/0.61      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.35/0.61  thf('42', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         (~ (v1_relat_1 @ X0)
% 0.35/0.61          | ~ (v1_funct_1 @ X0)
% 0.35/0.61          | ((k1_xboole_0) = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.35/0.61          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B @ X0))
% 0.35/0.61          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B @ X0))
% 0.35/0.61          | (r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_B @ X0))))),
% 0.35/0.61      inference('sup-', [status(thm)], ['40', '41'])).
% 0.35/0.61  thf('43', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         (~ (v1_relat_1 @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ sk_B)
% 0.35/0.61          | (r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_B @ X0)))
% 0.35/0.61          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B @ X0))
% 0.35/0.61          | ((k1_xboole_0) = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.35/0.61          | ~ (v1_funct_1 @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ X0))),
% 0.35/0.61      inference('sup-', [status(thm)], ['19', '42'])).
% 0.35/0.61  thf('44', plain, ((v1_relat_1 @ sk_B)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('45', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         (~ (v1_relat_1 @ X0)
% 0.35/0.61          | (r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_B @ X0)))
% 0.35/0.61          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B @ X0))
% 0.35/0.61          | ((k1_xboole_0) = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.35/0.61          | ~ (v1_funct_1 @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ X0))),
% 0.35/0.61      inference('demod', [status(thm)], ['43', '44'])).
% 0.35/0.61  thf('46', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         (~ (v1_funct_1 @ X0)
% 0.35/0.61          | ((k1_xboole_0) = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.35/0.61          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B @ X0))
% 0.35/0.61          | (r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_B @ X0)))
% 0.35/0.61          | ~ (v1_relat_1 @ X0))),
% 0.35/0.61      inference('simplify', [status(thm)], ['45'])).
% 0.35/0.61  thf('47', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         (~ (v1_funct_1 @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ sk_B)
% 0.35/0.61          | ~ (v1_funct_1 @ sk_B)
% 0.35/0.61          | ~ (v1_relat_1 @ X0)
% 0.35/0.61          | (r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_B @ X0)))
% 0.35/0.61          | ((k1_xboole_0) = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.35/0.61          | ~ (v1_funct_1 @ X0))),
% 0.35/0.61      inference('sup-', [status(thm)], ['18', '46'])).
% 0.35/0.61  thf('48', plain, ((v1_relat_1 @ sk_B)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('49', plain, ((v1_funct_1 @ sk_B)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('50', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         (~ (v1_funct_1 @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ X0)
% 0.35/0.61          | (r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_B @ X0)))
% 0.35/0.61          | ((k1_xboole_0) = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.35/0.61          | ~ (v1_funct_1 @ X0))),
% 0.35/0.61      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.35/0.61  thf('51', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         (((k1_xboole_0) = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.35/0.61          | (r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_B @ X0)))
% 0.35/0.61          | ~ (v1_relat_1 @ X0)
% 0.35/0.61          | ~ (v1_funct_1 @ X0))),
% 0.35/0.61      inference('simplify', [status(thm)], ['50'])).
% 0.35/0.61  thf('52', plain,
% 0.35/0.61      (![X14 : $i, X15 : $i]:
% 0.35/0.61         (~ (v1_funct_1 @ X14)
% 0.35/0.61          | ~ (v1_relat_1 @ X14)
% 0.35/0.61          | ~ (v1_relat_1 @ X15)
% 0.35/0.61          | ~ (v1_funct_1 @ X15)
% 0.35/0.61          | (v1_funct_1 @ (k5_relat_1 @ X14 @ X15)))),
% 0.35/0.61      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.35/0.61  thf('53', plain,
% 0.35/0.61      (![X8 : $i, X9 : $i]:
% 0.35/0.61         (~ (v1_relat_1 @ X8)
% 0.35/0.61          | ~ (v1_relat_1 @ X9)
% 0.35/0.61          | (v1_relat_1 @ (k5_relat_1 @ X8 @ X9)))),
% 0.35/0.61      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.35/0.61  thf('54', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         ((r2_hidden @ (k4_tarski @ X1 @ (k1_funct_1 @ X0 @ X1)) @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ X0)
% 0.35/0.61          | ~ (v1_funct_1 @ X0)
% 0.35/0.61          | ((k1_xboole_0) = (k1_funct_1 @ X0 @ X1)))),
% 0.35/0.61      inference('simplify', [status(thm)], ['29'])).
% 0.35/0.61  thf('55', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.35/0.61         (~ (r2_hidden @ (k4_tarski @ X3 @ X1) @ X2)
% 0.35/0.61          | (r2_hidden @ (k4_tarski @ X3 @ (k1_funct_1 @ X0 @ X1)) @ 
% 0.35/0.61             (k5_relat_1 @ X2 @ X0))
% 0.35/0.61          | ~ (v1_relat_1 @ X2)
% 0.35/0.61          | ~ (v1_relat_1 @ X0)
% 0.35/0.61          | ~ (v1_funct_1 @ X0)
% 0.35/0.61          | ((k1_xboole_0) = (k1_funct_1 @ X0 @ X1)))),
% 0.35/0.61      inference('simplify', [status(thm)], ['36'])).
% 0.35/0.61  thf('56', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.61         (((k1_xboole_0) = (k1_funct_1 @ X0 @ X1))
% 0.35/0.61          | ~ (v1_funct_1 @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ X0)
% 0.35/0.61          | ((k1_xboole_0) = (k1_funct_1 @ X2 @ (k1_funct_1 @ X0 @ X1)))
% 0.35/0.61          | ~ (v1_funct_1 @ X2)
% 0.35/0.61          | ~ (v1_relat_1 @ X2)
% 0.35/0.61          | ~ (v1_relat_1 @ X0)
% 0.35/0.61          | (r2_hidden @ 
% 0.35/0.61             (k4_tarski @ X1 @ (k1_funct_1 @ X2 @ (k1_funct_1 @ X0 @ X1))) @ 
% 0.35/0.61             (k5_relat_1 @ X0 @ X2)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['54', '55'])).
% 0.35/0.61  thf('57', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.61         ((r2_hidden @ 
% 0.35/0.61           (k4_tarski @ X1 @ (k1_funct_1 @ X2 @ (k1_funct_1 @ X0 @ X1))) @ 
% 0.35/0.61           (k5_relat_1 @ X0 @ X2))
% 0.35/0.61          | ~ (v1_relat_1 @ X2)
% 0.35/0.61          | ~ (v1_funct_1 @ X2)
% 0.35/0.61          | ((k1_xboole_0) = (k1_funct_1 @ X2 @ (k1_funct_1 @ X0 @ X1)))
% 0.35/0.61          | ~ (v1_relat_1 @ X0)
% 0.35/0.61          | ~ (v1_funct_1 @ X0)
% 0.35/0.61          | ((k1_xboole_0) = (k1_funct_1 @ X0 @ X1)))),
% 0.35/0.61      inference('simplify', [status(thm)], ['56'])).
% 0.35/0.61  thf('58', plain,
% 0.35/0.61      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.35/0.61         (~ (r2_hidden @ (k4_tarski @ X19 @ X21) @ X20)
% 0.35/0.61          | ((X21) = (k1_funct_1 @ X20 @ X19))
% 0.35/0.61          | ~ (v1_funct_1 @ X20)
% 0.35/0.61          | ~ (v1_relat_1 @ X20))),
% 0.35/0.61      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.35/0.61  thf('59', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.61         (((k1_xboole_0) = (k1_funct_1 @ X1 @ X2))
% 0.35/0.61          | ~ (v1_funct_1 @ X1)
% 0.35/0.61          | ~ (v1_relat_1 @ X1)
% 0.35/0.61          | ((k1_xboole_0) = (k1_funct_1 @ X0 @ (k1_funct_1 @ X1 @ X2)))
% 0.35/0.61          | ~ (v1_funct_1 @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.35/0.61          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.35/0.61          | ((k1_funct_1 @ X0 @ (k1_funct_1 @ X1 @ X2))
% 0.35/0.61              = (k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['57', '58'])).
% 0.35/0.61  thf('60', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.61         (~ (v1_relat_1 @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ X1)
% 0.35/0.61          | ((k1_funct_1 @ X0 @ (k1_funct_1 @ X1 @ X2))
% 0.35/0.61              = (k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2))
% 0.35/0.61          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.35/0.61          | ~ (v1_relat_1 @ X0)
% 0.35/0.61          | ~ (v1_funct_1 @ X0)
% 0.35/0.61          | ((k1_xboole_0) = (k1_funct_1 @ X0 @ (k1_funct_1 @ X1 @ X2)))
% 0.35/0.61          | ~ (v1_relat_1 @ X1)
% 0.35/0.61          | ~ (v1_funct_1 @ X1)
% 0.35/0.61          | ((k1_xboole_0) = (k1_funct_1 @ X1 @ X2)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['53', '59'])).
% 0.35/0.61  thf('61', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.61         (((k1_xboole_0) = (k1_funct_1 @ X1 @ X2))
% 0.35/0.61          | ~ (v1_funct_1 @ X1)
% 0.35/0.61          | ((k1_xboole_0) = (k1_funct_1 @ X0 @ (k1_funct_1 @ X1 @ X2)))
% 0.35/0.61          | ~ (v1_funct_1 @ X0)
% 0.35/0.61          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.35/0.61          | ((k1_funct_1 @ X0 @ (k1_funct_1 @ X1 @ X2))
% 0.35/0.61              = (k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2))
% 0.35/0.61          | ~ (v1_relat_1 @ X1)
% 0.35/0.61          | ~ (v1_relat_1 @ X0))),
% 0.35/0.61      inference('simplify', [status(thm)], ['60'])).
% 0.35/0.61  thf('62', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.61         (~ (v1_funct_1 @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ X1)
% 0.35/0.61          | ~ (v1_funct_1 @ X1)
% 0.35/0.61          | ~ (v1_relat_1 @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ X1)
% 0.35/0.61          | ((k1_funct_1 @ X0 @ (k1_funct_1 @ X1 @ X2))
% 0.35/0.61              = (k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2))
% 0.35/0.61          | ~ (v1_funct_1 @ X0)
% 0.35/0.61          | ((k1_xboole_0) = (k1_funct_1 @ X0 @ (k1_funct_1 @ X1 @ X2)))
% 0.35/0.61          | ~ (v1_funct_1 @ X1)
% 0.35/0.61          | ((k1_xboole_0) = (k1_funct_1 @ X1 @ X2)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['52', '61'])).
% 0.35/0.61  thf('63', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.61         (((k1_xboole_0) = (k1_funct_1 @ X1 @ X2))
% 0.35/0.61          | ((k1_xboole_0) = (k1_funct_1 @ X0 @ (k1_funct_1 @ X1 @ X2)))
% 0.35/0.61          | ((k1_funct_1 @ X0 @ (k1_funct_1 @ X1 @ X2))
% 0.35/0.61              = (k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2))
% 0.35/0.61          | ~ (v1_funct_1 @ X1)
% 0.35/0.61          | ~ (v1_relat_1 @ X1)
% 0.35/0.61          | ~ (v1_relat_1 @ X0)
% 0.35/0.61          | ~ (v1_funct_1 @ X0))),
% 0.35/0.61      inference('simplify', [status(thm)], ['62'])).
% 0.35/0.61  thf('64', plain,
% 0.35/0.61      (((k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C) @ sk_A)
% 0.35/0.61         != (k1_funct_1 @ sk_C @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('65', plain,
% 0.35/0.61      ((((k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C) @ sk_A)
% 0.35/0.61          != (k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C) @ sk_A))
% 0.35/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.35/0.61        | ~ (v1_relat_1 @ sk_C)
% 0.35/0.61        | ~ (v1_relat_1 @ sk_B)
% 0.35/0.61        | ~ (v1_funct_1 @ sk_B)
% 0.35/0.61        | ((k1_xboole_0) = (k1_funct_1 @ sk_C @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.35/0.61        | ((k1_xboole_0) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['63', '64'])).
% 0.35/0.61  thf('66', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('67', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('68', plain, ((v1_relat_1 @ sk_B)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('69', plain, ((v1_funct_1 @ sk_B)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('70', plain,
% 0.35/0.61      ((((k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C) @ sk_A)
% 0.35/0.61          != (k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C) @ sk_A))
% 0.35/0.61        | ((k1_xboole_0) = (k1_funct_1 @ sk_C @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.35/0.61        | ((k1_xboole_0) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.35/0.61      inference('demod', [status(thm)], ['65', '66', '67', '68', '69'])).
% 0.35/0.61  thf('71', plain,
% 0.35/0.61      ((((k1_xboole_0) = (k1_funct_1 @ sk_B @ sk_A))
% 0.35/0.61        | ((k1_xboole_0) = (k1_funct_1 @ sk_C @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.35/0.61      inference('simplify', [status(thm)], ['70'])).
% 0.35/0.61  thf('72', plain,
% 0.35/0.61      (((k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C) @ sk_A)
% 0.35/0.61         != (k1_funct_1 @ sk_C @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('73', plain,
% 0.35/0.61      ((((k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C) @ sk_A) != (k1_xboole_0))
% 0.35/0.61        | ((k1_xboole_0) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['71', '72'])).
% 0.35/0.61  thf('74', plain,
% 0.35/0.61      (((k1_xboole_0) = (k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C) @ sk_A))),
% 0.35/0.61      inference('simplify', [status(thm)], ['16'])).
% 0.35/0.61  thf('75', plain,
% 0.35/0.61      ((((k1_xboole_0) != (k1_xboole_0))
% 0.35/0.61        | ((k1_xboole_0) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.35/0.61      inference('demod', [status(thm)], ['73', '74'])).
% 0.35/0.61  thf('76', plain, (((k1_xboole_0) = (k1_funct_1 @ sk_B @ sk_A))),
% 0.35/0.61      inference('simplify', [status(thm)], ['75'])).
% 0.35/0.61  thf('77', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         (((k1_xboole_0) = (k1_funct_1 @ X0 @ k1_xboole_0))
% 0.35/0.61          | (r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_B @ X0)))
% 0.35/0.61          | ~ (v1_relat_1 @ X0)
% 0.35/0.61          | ~ (v1_funct_1 @ X0))),
% 0.35/0.61      inference('demod', [status(thm)], ['51', '76'])).
% 0.35/0.61  thf('78', plain,
% 0.35/0.61      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.35/0.61         (~ (v1_relat_1 @ X16)
% 0.35/0.61          | ~ (v1_funct_1 @ X16)
% 0.35/0.61          | ((k1_funct_1 @ (k5_relat_1 @ X16 @ X17) @ X18)
% 0.35/0.61              = (k1_funct_1 @ X17 @ (k1_funct_1 @ X16 @ X18)))
% 0.35/0.61          | ~ (r2_hidden @ X18 @ (k1_relat_1 @ (k5_relat_1 @ X16 @ X17)))
% 0.35/0.61          | ~ (v1_funct_1 @ X17)
% 0.35/0.61          | ~ (v1_relat_1 @ X17))),
% 0.35/0.61      inference('cnf', [status(esa)], [t22_funct_1])).
% 0.35/0.61  thf('79', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         (~ (v1_funct_1 @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ X0)
% 0.35/0.61          | ((k1_xboole_0) = (k1_funct_1 @ X0 @ k1_xboole_0))
% 0.35/0.61          | ~ (v1_relat_1 @ X0)
% 0.35/0.61          | ~ (v1_funct_1 @ X0)
% 0.35/0.61          | ((k1_funct_1 @ (k5_relat_1 @ sk_B @ X0) @ sk_A)
% 0.35/0.61              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.35/0.61          | ~ (v1_funct_1 @ sk_B)
% 0.35/0.61          | ~ (v1_relat_1 @ sk_B))),
% 0.35/0.61      inference('sup-', [status(thm)], ['77', '78'])).
% 0.35/0.61  thf('80', plain, (((k1_xboole_0) = (k1_funct_1 @ sk_B @ sk_A))),
% 0.35/0.61      inference('simplify', [status(thm)], ['75'])).
% 0.35/0.61  thf('81', plain, ((v1_funct_1 @ sk_B)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('82', plain, ((v1_relat_1 @ sk_B)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('83', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         (~ (v1_funct_1 @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ X0)
% 0.35/0.61          | ((k1_xboole_0) = (k1_funct_1 @ X0 @ k1_xboole_0))
% 0.35/0.61          | ~ (v1_relat_1 @ X0)
% 0.35/0.61          | ~ (v1_funct_1 @ X0)
% 0.35/0.61          | ((k1_funct_1 @ (k5_relat_1 @ sk_B @ X0) @ sk_A)
% 0.35/0.61              = (k1_funct_1 @ X0 @ k1_xboole_0)))),
% 0.35/0.61      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 0.35/0.61  thf('84', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         (((k1_funct_1 @ (k5_relat_1 @ sk_B @ X0) @ sk_A)
% 0.35/0.61            = (k1_funct_1 @ X0 @ k1_xboole_0))
% 0.35/0.61          | ((k1_xboole_0) = (k1_funct_1 @ X0 @ k1_xboole_0))
% 0.35/0.61          | ~ (v1_relat_1 @ X0)
% 0.35/0.61          | ~ (v1_funct_1 @ X0))),
% 0.35/0.61      inference('simplify', [status(thm)], ['83'])).
% 0.35/0.61  thf('85', plain,
% 0.35/0.61      ((((k1_xboole_0) = (k1_funct_1 @ sk_C @ k1_xboole_0))
% 0.35/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.35/0.61        | ~ (v1_relat_1 @ sk_C)
% 0.35/0.61        | ((k1_xboole_0) = (k1_funct_1 @ sk_C @ k1_xboole_0)))),
% 0.35/0.61      inference('sup+', [status(thm)], ['17', '84'])).
% 0.35/0.61  thf('86', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('87', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('88', plain,
% 0.35/0.61      ((((k1_xboole_0) = (k1_funct_1 @ sk_C @ k1_xboole_0))
% 0.35/0.61        | ((k1_xboole_0) = (k1_funct_1 @ sk_C @ k1_xboole_0)))),
% 0.35/0.61      inference('demod', [status(thm)], ['85', '86', '87'])).
% 0.35/0.61  thf('89', plain, (((k1_xboole_0) = (k1_funct_1 @ sk_C @ k1_xboole_0))),
% 0.35/0.61      inference('simplify', [status(thm)], ['88'])).
% 0.35/0.61  thf('90', plain,
% 0.35/0.61      (((k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C) @ sk_A)
% 0.35/0.61         != (k1_funct_1 @ sk_C @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('91', plain,
% 0.35/0.61      (((k1_xboole_0) = (k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C) @ sk_A))),
% 0.35/0.61      inference('simplify', [status(thm)], ['16'])).
% 0.35/0.61  thf('92', plain,
% 0.35/0.61      (((k1_xboole_0) != (k1_funct_1 @ sk_C @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.35/0.61      inference('demod', [status(thm)], ['90', '91'])).
% 0.35/0.61  thf('93', plain, (((k1_xboole_0) = (k1_funct_1 @ sk_B @ sk_A))),
% 0.35/0.61      inference('simplify', [status(thm)], ['75'])).
% 0.35/0.61  thf('94', plain, (((k1_xboole_0) != (k1_funct_1 @ sk_C @ k1_xboole_0))),
% 0.35/0.61      inference('demod', [status(thm)], ['92', '93'])).
% 0.35/0.61  thf('95', plain, ($false),
% 0.35/0.61      inference('simplify_reflect-', [status(thm)], ['89', '94'])).
% 0.35/0.61  
% 0.35/0.61  % SZS output end Refutation
% 0.35/0.61  
% 0.35/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
