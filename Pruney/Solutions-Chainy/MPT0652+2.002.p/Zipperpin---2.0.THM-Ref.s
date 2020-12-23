%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XHAX4ZAb3u

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 119 expanded)
%              Number of leaves         :   19 (  41 expanded)
%              Depth                    :   23
%              Number of atoms          :  685 (1520 expanded)
%              Number of equality atoms :   64 ( 142 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( ( ( k2_relat_1 @ X7 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X7: $i] :
      ( ( ( k1_relat_1 @ X7 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X9 ) @ ( k1_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) )
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X0 ) )
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X0 ) )
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X0 ) )
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('10',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ X10 )
        = ( k4_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf(t59_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
            = ( k2_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
            = ( k2_relat_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v2_funct_1 @ A )
         => ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
              = ( k2_relat_1 @ A ) )
            & ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t59_funct_1])).

thf('11',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,
    ( ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ sk_A ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('18',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('19',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ X10 )
        = ( k4_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('20',plain,(
    ! [X4: $i] :
      ( ( ( k9_relat_1 @ X4 @ ( k1_relat_1 @ X4 ) )
        = ( k2_relat_1 @ X4 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('21',plain,(
    ! [X7: $i] :
      ( ( ( k1_relat_1 @ X7 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('22',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ X10 )
        = ( k4_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('23',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) )
        = ( k9_relat_1 @ X5 @ ( k2_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('24',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['11'])).

thf('25',plain,
    ( ( ( ( k9_relat_1 @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( ( ( k9_relat_1 @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( ( k9_relat_1 @ sk_A @ ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( ( k9_relat_1 @ sk_A @ ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf('33',plain,
    ( ( ( ( k9_relat_1 @ sk_A @ ( k1_relat_1 @ sk_A ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( ( k9_relat_1 @ sk_A @ ( k1_relat_1 @ sk_A ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( ( k2_relat_1 @ sk_A )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( ( ( k2_relat_1 @ sk_A )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41','42','43'])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_A )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
    = ( k2_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['11'])).

thf('49',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
 != ( k2_relat_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['47','48'])).

thf('50',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ sk_A ) )
 != ( k2_relat_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['17','49'])).

thf('51',plain,
    ( ( ( k1_relat_1 @ ( k4_relat_1 @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ( k1_relat_1 @ ( k4_relat_1 @ sk_A ) )
 != ( k2_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ( k2_relat_1 @ sk_A )
 != ( k2_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    $false ),
    inference(simplify,[status(thm)],['56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XHAX4ZAb3u
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:10:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 38 iterations in 0.044s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.21/0.52  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.52  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.52  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.52  thf(t37_relat_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ A ) =>
% 0.21/0.52       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.21/0.52         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (![X7 : $i]:
% 0.21/0.52         (((k2_relat_1 @ X7) = (k1_relat_1 @ (k4_relat_1 @ X7)))
% 0.21/0.52          | ~ (v1_relat_1 @ X7))),
% 0.21/0.52      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.21/0.52  thf(d10_xboole_0, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.52  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.52      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X7 : $i]:
% 0.21/0.52         (((k1_relat_1 @ X7) = (k2_relat_1 @ (k4_relat_1 @ X7)))
% 0.21/0.52          | ~ (v1_relat_1 @ X7))),
% 0.21/0.52      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.21/0.52  thf(t46_relat_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( v1_relat_1 @ B ) =>
% 0.21/0.52           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.52             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X8 : $i, X9 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X8)
% 0.21/0.52          | ((k1_relat_1 @ (k5_relat_1 @ X9 @ X8)) = (k1_relat_1 @ X9))
% 0.21/0.52          | ~ (r1_tarski @ (k2_relat_1 @ X9) @ (k1_relat_1 @ X8))
% 0.21/0.52          | ~ (v1_relat_1 @ X9))),
% 0.21/0.52      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (r1_tarski @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X1))
% 0.21/0.52          | ~ (v1_relat_1 @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.21/0.52          | ((k1_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X1))
% 0.21/0.52              = (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.21/0.52          | ~ (v1_relat_1 @ X1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X0)
% 0.21/0.52          | ((k1_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0))
% 0.21/0.52              = (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.21/0.52          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.21/0.52          | ~ (v1_relat_1 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '5'])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.21/0.52          | ((k1_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0))
% 0.21/0.52              = (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.21/0.52          | ~ (v1_relat_1 @ X0))),
% 0.21/0.52      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.52  thf(dt_k4_relat_1, axiom,
% 0.21/0.52    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X3 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X3)) | ~ (v1_relat_1 @ X3))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X0)
% 0.21/0.52          | ((k1_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0))
% 0.21/0.52              = (k1_relat_1 @ (k4_relat_1 @ X0))))),
% 0.21/0.52      inference('clc', [status(thm)], ['7', '8'])).
% 0.21/0.52  thf(d9_funct_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.52       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (![X10 : $i]:
% 0.21/0.52         (~ (v2_funct_1 @ X10)
% 0.21/0.52          | ((k2_funct_1 @ X10) = (k4_relat_1 @ X10))
% 0.21/0.52          | ~ (v1_funct_1 @ X10)
% 0.21/0.52          | ~ (v1_relat_1 @ X10))),
% 0.21/0.52      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.21/0.52  thf(t59_funct_1, conjecture,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.52       ( ( v2_funct_1 @ A ) =>
% 0.21/0.52         ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.21/0.52             ( k2_relat_1 @ A ) ) & 
% 0.21/0.52           ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.21/0.52             ( k2_relat_1 @ A ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i]:
% 0.21/0.52        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.52          ( ( v2_funct_1 @ A ) =>
% 0.21/0.52            ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.21/0.52                ( k2_relat_1 @ A ) ) & 
% 0.21/0.52              ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.21/0.52                ( k2_relat_1 @ A ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t59_funct_1])).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      ((((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.52          != (k2_relat_1 @ sk_A))
% 0.21/0.52        | ((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.52            != (k2_relat_1 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      ((((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.52          != (k2_relat_1 @ sk_A)))
% 0.21/0.52         <= (~
% 0.21/0.52             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.52                = (k2_relat_1 @ sk_A))))),
% 0.21/0.52      inference('split', [status(esa)], ['11'])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (((((k1_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_A) @ sk_A))
% 0.21/0.52           != (k2_relat_1 @ sk_A))
% 0.21/0.52         | ~ (v1_relat_1 @ sk_A)
% 0.21/0.52         | ~ (v1_funct_1 @ sk_A)
% 0.21/0.52         | ~ (v2_funct_1 @ sk_A)))
% 0.21/0.52         <= (~
% 0.21/0.52             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.52                = (k2_relat_1 @ sk_A))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['10', '12'])).
% 0.21/0.52  thf('14', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('15', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('16', plain, ((v2_funct_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      ((((k1_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_A) @ sk_A))
% 0.21/0.52          != (k2_relat_1 @ sk_A)))
% 0.21/0.52         <= (~
% 0.21/0.52             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.52                = (k2_relat_1 @ sk_A))))),
% 0.21/0.52      inference('demod', [status(thm)], ['13', '14', '15', '16'])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (![X3 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X3)) | ~ (v1_relat_1 @ X3))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X10 : $i]:
% 0.21/0.52         (~ (v2_funct_1 @ X10)
% 0.21/0.52          | ((k2_funct_1 @ X10) = (k4_relat_1 @ X10))
% 0.21/0.52          | ~ (v1_funct_1 @ X10)
% 0.21/0.52          | ~ (v1_relat_1 @ X10))),
% 0.21/0.52      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.21/0.52  thf(t146_relat_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ A ) =>
% 0.21/0.52       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X4 : $i]:
% 0.21/0.52         (((k9_relat_1 @ X4 @ (k1_relat_1 @ X4)) = (k2_relat_1 @ X4))
% 0.21/0.52          | ~ (v1_relat_1 @ X4))),
% 0.21/0.52      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (![X7 : $i]:
% 0.21/0.52         (((k1_relat_1 @ X7) = (k2_relat_1 @ (k4_relat_1 @ X7)))
% 0.21/0.52          | ~ (v1_relat_1 @ X7))),
% 0.21/0.52      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (![X10 : $i]:
% 0.21/0.52         (~ (v2_funct_1 @ X10)
% 0.21/0.52          | ((k2_funct_1 @ X10) = (k4_relat_1 @ X10))
% 0.21/0.52          | ~ (v1_funct_1 @ X10)
% 0.21/0.52          | ~ (v1_relat_1 @ X10))),
% 0.21/0.52      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.21/0.52  thf(t160_relat_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( v1_relat_1 @ B ) =>
% 0.21/0.52           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.21/0.52             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      (![X5 : $i, X6 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X5)
% 0.21/0.52          | ((k2_relat_1 @ (k5_relat_1 @ X6 @ X5))
% 0.21/0.52              = (k9_relat_1 @ X5 @ (k2_relat_1 @ X6)))
% 0.21/0.52          | ~ (v1_relat_1 @ X6))),
% 0.21/0.52      inference('cnf', [status(esa)], [t160_relat_1])).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      ((((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.52          != (k2_relat_1 @ sk_A)))
% 0.21/0.52         <= (~
% 0.21/0.52             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.52                = (k2_relat_1 @ sk_A))))),
% 0.21/0.52      inference('split', [status(esa)], ['11'])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      (((((k9_relat_1 @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.21/0.52           != (k2_relat_1 @ sk_A))
% 0.21/0.52         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.21/0.52         | ~ (v1_relat_1 @ sk_A)))
% 0.21/0.52         <= (~
% 0.21/0.52             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.52                = (k2_relat_1 @ sk_A))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.52  thf('26', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (((((k9_relat_1 @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.21/0.52           != (k2_relat_1 @ sk_A))
% 0.21/0.52         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.21/0.52         <= (~
% 0.21/0.52             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.52                = (k2_relat_1 @ sk_A))))),
% 0.21/0.52      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      (((((k9_relat_1 @ sk_A @ (k2_relat_1 @ (k4_relat_1 @ sk_A)))
% 0.21/0.52           != (k2_relat_1 @ sk_A))
% 0.21/0.52         | ~ (v1_relat_1 @ sk_A)
% 0.21/0.52         | ~ (v1_funct_1 @ sk_A)
% 0.21/0.52         | ~ (v2_funct_1 @ sk_A)
% 0.21/0.52         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.21/0.52         <= (~
% 0.21/0.52             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.52                = (k2_relat_1 @ sk_A))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['22', '27'])).
% 0.21/0.52  thf('29', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('30', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('31', plain, ((v2_funct_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      (((((k9_relat_1 @ sk_A @ (k2_relat_1 @ (k4_relat_1 @ sk_A)))
% 0.21/0.52           != (k2_relat_1 @ sk_A))
% 0.21/0.52         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.21/0.52         <= (~
% 0.21/0.52             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.52                = (k2_relat_1 @ sk_A))))),
% 0.21/0.52      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      (((((k9_relat_1 @ sk_A @ (k1_relat_1 @ sk_A)) != (k2_relat_1 @ sk_A))
% 0.21/0.52         | ~ (v1_relat_1 @ sk_A)
% 0.21/0.52         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.21/0.52         <= (~
% 0.21/0.52             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.52                = (k2_relat_1 @ sk_A))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['21', '32'])).
% 0.21/0.52  thf('34', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      (((((k9_relat_1 @ sk_A @ (k1_relat_1 @ sk_A)) != (k2_relat_1 @ sk_A))
% 0.21/0.52         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.21/0.52         <= (~
% 0.21/0.52             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.52                = (k2_relat_1 @ sk_A))))),
% 0.21/0.52      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      (((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))
% 0.21/0.52         | ~ (v1_relat_1 @ sk_A)
% 0.21/0.52         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.21/0.52         <= (~
% 0.21/0.52             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.52                = (k2_relat_1 @ sk_A))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['20', '35'])).
% 0.21/0.52  thf('37', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      (((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))
% 0.21/0.52         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.21/0.52         <= (~
% 0.21/0.52             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.52                = (k2_relat_1 @ sk_A))))),
% 0.21/0.52      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.21/0.52         <= (~
% 0.21/0.52             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.52                = (k2_relat_1 @ sk_A))))),
% 0.21/0.52      inference('simplify', [status(thm)], ['38'])).
% 0.21/0.52  thf('40', plain,
% 0.21/0.52      (((~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.21/0.52         | ~ (v1_relat_1 @ sk_A)
% 0.21/0.52         | ~ (v1_funct_1 @ sk_A)
% 0.21/0.52         | ~ (v2_funct_1 @ sk_A)))
% 0.21/0.52         <= (~
% 0.21/0.52             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.52                = (k2_relat_1 @ sk_A))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['19', '39'])).
% 0.21/0.52  thf('41', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('42', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('43', plain, ((v2_funct_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('44', plain,
% 0.21/0.52      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_A)))
% 0.21/0.52         <= (~
% 0.21/0.52             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.52                = (k2_relat_1 @ sk_A))))),
% 0.21/0.52      inference('demod', [status(thm)], ['40', '41', '42', '43'])).
% 0.21/0.52  thf('45', plain,
% 0.21/0.52      ((~ (v1_relat_1 @ sk_A))
% 0.21/0.52         <= (~
% 0.21/0.52             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.52                = (k2_relat_1 @ sk_A))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['18', '44'])).
% 0.21/0.52  thf('46', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('47', plain,
% 0.21/0.52      ((((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.52          = (k2_relat_1 @ sk_A)))),
% 0.21/0.52      inference('demod', [status(thm)], ['45', '46'])).
% 0.21/0.52  thf('48', plain,
% 0.21/0.52      (~
% 0.21/0.52       (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.52          = (k2_relat_1 @ sk_A))) | 
% 0.21/0.52       ~
% 0.21/0.52       (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.52          = (k2_relat_1 @ sk_A)))),
% 0.21/0.52      inference('split', [status(esa)], ['11'])).
% 0.21/0.52  thf('49', plain,
% 0.21/0.52      (~
% 0.21/0.52       (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.52          = (k2_relat_1 @ sk_A)))),
% 0.21/0.52      inference('sat_resolution*', [status(thm)], ['47', '48'])).
% 0.21/0.52  thf('50', plain,
% 0.21/0.52      (((k1_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_A) @ sk_A))
% 0.21/0.52         != (k2_relat_1 @ sk_A))),
% 0.21/0.52      inference('simpl_trail', [status(thm)], ['17', '49'])).
% 0.21/0.52  thf('51', plain,
% 0.21/0.52      ((((k1_relat_1 @ (k4_relat_1 @ sk_A)) != (k2_relat_1 @ sk_A))
% 0.21/0.52        | ~ (v1_relat_1 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['9', '50'])).
% 0.21/0.52  thf('52', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('53', plain,
% 0.21/0.52      (((k1_relat_1 @ (k4_relat_1 @ sk_A)) != (k2_relat_1 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['51', '52'])).
% 0.21/0.52  thf('54', plain,
% 0.21/0.52      ((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A)) | ~ (v1_relat_1 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['0', '53'])).
% 0.21/0.52  thf('55', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('56', plain, (((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['54', '55'])).
% 0.21/0.52  thf('57', plain, ($false), inference('simplify', [status(thm)], ['56'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.35/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
