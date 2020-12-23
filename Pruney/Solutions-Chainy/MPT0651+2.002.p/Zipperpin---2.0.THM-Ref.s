%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QIGrARkY0i

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 118 expanded)
%              Number of leaves         :   19 (  41 expanded)
%              Depth                    :   21
%              Number of atoms          :  708 (1504 expanded)
%              Number of equality atoms :   68 ( 142 expanded)
%              Maximal formula depth    :   11 (   6 average)

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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X7: $i] :
      ( ( ( k2_relat_1 @ X7 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X7 ) ) )
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

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X9 ) @ ( k1_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ X10 )
        = ( k4_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf(t58_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v2_funct_1 @ A )
         => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
              = ( k1_relat_1 @ A ) )
            & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
              = ( k1_relat_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t58_funct_1])).

thf('10',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k4_relat_1 @ sk_A ) ) )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k4_relat_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('17',plain,(
    ! [X7: $i] :
      ( ( ( k1_relat_1 @ X7 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

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

thf('20',plain,(
    ! [X7: $i] :
      ( ( ( k2_relat_1 @ X7 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('21',plain,(
    ! [X4: $i] :
      ( ( ( k9_relat_1 @ X4 @ ( k1_relat_1 @ X4 ) )
        = ( k2_relat_1 @ X4 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
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

thf('26',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) )
        = ( k9_relat_1 @ X5 @ ( k2_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('27',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['10'])).

thf('28',plain,
    ( ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( ( k9_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( ( k9_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('36',plain,
    ( ( ( ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( ( ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) )
       != ( k1_relat_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) )
       != ( k1_relat_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) )
       != ( k1_relat_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) )
     != ( k1_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( ( k1_relat_1 @ sk_A )
       != ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != ( k1_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
    = ( k1_relat_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['10'])).

thf('52',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
 != ( k1_relat_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['50','51'])).

thf('53',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k4_relat_1 @ sk_A ) ) )
 != ( k1_relat_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['16','52'])).

thf('54',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ( k1_relat_1 @ sk_A )
 != ( k1_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    $false ),
    inference(simplify,[status(thm)],['56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QIGrARkY0i
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:47:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 34 iterations in 0.026s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.20/0.48  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.48  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.48  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.48  thf(d10_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.48  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.48      inference('simplify', [status(thm)], ['0'])).
% 0.20/0.48  thf(t37_relat_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.20/0.48         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X7 : $i]:
% 0.20/0.48         (((k2_relat_1 @ X7) = (k1_relat_1 @ (k4_relat_1 @ X7)))
% 0.20/0.48          | ~ (v1_relat_1 @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.20/0.48  thf(t46_relat_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( v1_relat_1 @ B ) =>
% 0.20/0.48           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.48             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X8 : $i, X9 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X8)
% 0.20/0.48          | ((k1_relat_1 @ (k5_relat_1 @ X9 @ X8)) = (k1_relat_1 @ X9))
% 0.20/0.48          | ~ (r1_tarski @ (k2_relat_1 @ X9) @ (k1_relat_1 @ X8))
% 0.20/0.48          | ~ (v1_relat_1 @ X9))),
% 0.20/0.48      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (r1_tarski @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0))
% 0.20/0.48          | ~ (v1_relat_1 @ X0)
% 0.20/0.48          | ~ (v1_relat_1 @ X1)
% 0.20/0.48          | ((k1_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0)))
% 0.20/0.48              = (k1_relat_1 @ X1))
% 0.20/0.48          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.20/0.48          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ X0)))
% 0.20/0.48              = (k1_relat_1 @ X0))
% 0.20/0.48          | ~ (v1_relat_1 @ X0)
% 0.20/0.48          | ~ (v1_relat_1 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '4'])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X0)
% 0.20/0.48          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ X0)))
% 0.20/0.48              = (k1_relat_1 @ X0))
% 0.20/0.48          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.48  thf(dt_k4_relat_1, axiom,
% 0.20/0.48    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X3 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X3)) | ~ (v1_relat_1 @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k1_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ X0)))
% 0.20/0.48            = (k1_relat_1 @ X0))
% 0.20/0.48          | ~ (v1_relat_1 @ X0))),
% 0.20/0.48      inference('clc', [status(thm)], ['6', '7'])).
% 0.20/0.48  thf(d9_funct_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.48       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X10 : $i]:
% 0.20/0.48         (~ (v2_funct_1 @ X10)
% 0.20/0.48          | ((k2_funct_1 @ X10) = (k4_relat_1 @ X10))
% 0.20/0.48          | ~ (v1_funct_1 @ X10)
% 0.20/0.48          | ~ (v1_relat_1 @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.20/0.48  thf(t58_funct_1, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.48       ( ( v2_funct_1 @ A ) =>
% 0.20/0.48         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.20/0.48             ( k1_relat_1 @ A ) ) & 
% 0.20/0.48           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.20/0.48             ( k1_relat_1 @ A ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.48          ( ( v2_funct_1 @ A ) =>
% 0.20/0.48            ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.20/0.48                ( k1_relat_1 @ A ) ) & 
% 0.20/0.48              ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.20/0.48                ( k1_relat_1 @ A ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t58_funct_1])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      ((((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.48          != (k1_relat_1 @ sk_A))
% 0.20/0.48        | ((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.48            != (k1_relat_1 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      ((((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.48          != (k1_relat_1 @ sk_A)))
% 0.20/0.48         <= (~
% 0.20/0.48             (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.48                = (k1_relat_1 @ sk_A))))),
% 0.20/0.48      inference('split', [status(esa)], ['10'])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (((((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k4_relat_1 @ sk_A)))
% 0.20/0.48           != (k1_relat_1 @ sk_A))
% 0.20/0.48         | ~ (v1_relat_1 @ sk_A)
% 0.20/0.48         | ~ (v1_funct_1 @ sk_A)
% 0.20/0.48         | ~ (v2_funct_1 @ sk_A)))
% 0.20/0.48         <= (~
% 0.20/0.48             (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.48                = (k1_relat_1 @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['9', '11'])).
% 0.20/0.48  thf('13', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('14', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('15', plain, ((v2_funct_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      ((((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k4_relat_1 @ sk_A)))
% 0.20/0.48          != (k1_relat_1 @ sk_A)))
% 0.20/0.48         <= (~
% 0.20/0.48             (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.48                = (k1_relat_1 @ sk_A))))),
% 0.20/0.48      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X7 : $i]:
% 0.20/0.48         (((k1_relat_1 @ X7) = (k2_relat_1 @ (k4_relat_1 @ X7)))
% 0.20/0.48          | ~ (v1_relat_1 @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X3 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X3)) | ~ (v1_relat_1 @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X10 : $i]:
% 0.20/0.48         (~ (v2_funct_1 @ X10)
% 0.20/0.48          | ((k2_funct_1 @ X10) = (k4_relat_1 @ X10))
% 0.20/0.48          | ~ (v1_funct_1 @ X10)
% 0.20/0.48          | ~ (v1_relat_1 @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X7 : $i]:
% 0.20/0.48         (((k2_relat_1 @ X7) = (k1_relat_1 @ (k4_relat_1 @ X7)))
% 0.20/0.48          | ~ (v1_relat_1 @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.20/0.48  thf(t146_relat_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (![X4 : $i]:
% 0.20/0.48         (((k9_relat_1 @ X4 @ (k1_relat_1 @ X4)) = (k2_relat_1 @ X4))
% 0.20/0.48          | ~ (v1_relat_1 @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k9_relat_1 @ (k4_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.20/0.48            = (k2_relat_1 @ (k4_relat_1 @ X0)))
% 0.20/0.48          | ~ (v1_relat_1 @ X0)
% 0.20/0.48          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['20', '21'])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (![X3 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X3)) | ~ (v1_relat_1 @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X0)
% 0.20/0.48          | ((k9_relat_1 @ (k4_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.20/0.48              = (k2_relat_1 @ (k4_relat_1 @ X0))))),
% 0.20/0.48      inference('clc', [status(thm)], ['22', '23'])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (![X10 : $i]:
% 0.20/0.48         (~ (v2_funct_1 @ X10)
% 0.20/0.48          | ((k2_funct_1 @ X10) = (k4_relat_1 @ X10))
% 0.20/0.48          | ~ (v1_funct_1 @ X10)
% 0.20/0.48          | ~ (v1_relat_1 @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.20/0.48  thf(t160_relat_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( v1_relat_1 @ B ) =>
% 0.20/0.48           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.20/0.48             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X5)
% 0.20/0.48          | ((k2_relat_1 @ (k5_relat_1 @ X6 @ X5))
% 0.20/0.48              = (k9_relat_1 @ X5 @ (k2_relat_1 @ X6)))
% 0.20/0.48          | ~ (v1_relat_1 @ X6))),
% 0.20/0.48      inference('cnf', [status(esa)], [t160_relat_1])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      ((((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.48          != (k1_relat_1 @ sk_A)))
% 0.20/0.48         <= (~
% 0.20/0.48             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.48                = (k1_relat_1 @ sk_A))))),
% 0.20/0.48      inference('split', [status(esa)], ['10'])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      (((((k9_relat_1 @ (k2_funct_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.20/0.48           != (k1_relat_1 @ sk_A))
% 0.20/0.48         | ~ (v1_relat_1 @ sk_A)
% 0.20/0.48         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.20/0.48         <= (~
% 0.20/0.48             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.48                = (k1_relat_1 @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.48  thf('29', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      (((((k9_relat_1 @ (k2_funct_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.20/0.48           != (k1_relat_1 @ sk_A))
% 0.20/0.48         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.20/0.48         <= (~
% 0.20/0.48             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.48                = (k1_relat_1 @ sk_A))))),
% 0.20/0.48      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      (((((k9_relat_1 @ (k4_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.20/0.48           != (k1_relat_1 @ sk_A))
% 0.20/0.48         | ~ (v1_relat_1 @ sk_A)
% 0.20/0.48         | ~ (v1_funct_1 @ sk_A)
% 0.20/0.48         | ~ (v2_funct_1 @ sk_A)
% 0.20/0.48         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.20/0.48         <= (~
% 0.20/0.48             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.48                = (k1_relat_1 @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['25', '30'])).
% 0.20/0.48  thf('32', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('33', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('34', plain, ((v2_funct_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      (((((k9_relat_1 @ (k4_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.20/0.48           != (k1_relat_1 @ sk_A))
% 0.20/0.48         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.20/0.48         <= (~
% 0.20/0.48             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.48                = (k1_relat_1 @ sk_A))))),
% 0.20/0.48      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      (((((k2_relat_1 @ (k4_relat_1 @ sk_A)) != (k1_relat_1 @ sk_A))
% 0.20/0.48         | ~ (v1_relat_1 @ sk_A)
% 0.20/0.48         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.20/0.48         <= (~
% 0.20/0.48             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.48                = (k1_relat_1 @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['24', '35'])).
% 0.20/0.48  thf('37', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      (((((k2_relat_1 @ (k4_relat_1 @ sk_A)) != (k1_relat_1 @ sk_A))
% 0.20/0.48         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.20/0.48         <= (~
% 0.20/0.48             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.48                = (k1_relat_1 @ sk_A))))),
% 0.20/0.48      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      (((~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.20/0.48         | ~ (v1_relat_1 @ sk_A)
% 0.20/0.48         | ~ (v1_funct_1 @ sk_A)
% 0.20/0.48         | ~ (v2_funct_1 @ sk_A)
% 0.20/0.48         | ((k2_relat_1 @ (k4_relat_1 @ sk_A)) != (k1_relat_1 @ sk_A))))
% 0.20/0.48         <= (~
% 0.20/0.48             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.48                = (k1_relat_1 @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['19', '38'])).
% 0.20/0.48  thf('40', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('41', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('42', plain, ((v2_funct_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('43', plain,
% 0.20/0.48      (((~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.20/0.48         | ((k2_relat_1 @ (k4_relat_1 @ sk_A)) != (k1_relat_1 @ sk_A))))
% 0.20/0.48         <= (~
% 0.20/0.48             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.48                = (k1_relat_1 @ sk_A))))),
% 0.20/0.48      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 0.20/0.48  thf('44', plain,
% 0.20/0.48      (((~ (v1_relat_1 @ sk_A)
% 0.20/0.48         | ((k2_relat_1 @ (k4_relat_1 @ sk_A)) != (k1_relat_1 @ sk_A))))
% 0.20/0.48         <= (~
% 0.20/0.48             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.48                = (k1_relat_1 @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['18', '43'])).
% 0.20/0.48  thf('45', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('46', plain,
% 0.20/0.48      ((((k2_relat_1 @ (k4_relat_1 @ sk_A)) != (k1_relat_1 @ sk_A)))
% 0.20/0.48         <= (~
% 0.20/0.48             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.48                = (k1_relat_1 @ sk_A))))),
% 0.20/0.48      inference('demod', [status(thm)], ['44', '45'])).
% 0.20/0.48  thf('47', plain,
% 0.20/0.48      (((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A)) | ~ (v1_relat_1 @ sk_A)))
% 0.20/0.48         <= (~
% 0.20/0.48             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.48                = (k1_relat_1 @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['17', '46'])).
% 0.20/0.48  thf('48', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('49', plain,
% 0.20/0.48      ((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A)))
% 0.20/0.48         <= (~
% 0.20/0.48             (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.48                = (k1_relat_1 @ sk_A))))),
% 0.20/0.48      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.48  thf('50', plain,
% 0.20/0.48      ((((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.48          = (k1_relat_1 @ sk_A)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['49'])).
% 0.20/0.48  thf('51', plain,
% 0.20/0.48      (~
% 0.20/0.48       (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.48          = (k1_relat_1 @ sk_A))) | 
% 0.20/0.48       ~
% 0.20/0.48       (((k2_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.48          = (k1_relat_1 @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['10'])).
% 0.20/0.48  thf('52', plain,
% 0.20/0.48      (~
% 0.20/0.48       (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 0.20/0.48          = (k1_relat_1 @ sk_A)))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['50', '51'])).
% 0.20/0.48  thf('53', plain,
% 0.20/0.48      (((k1_relat_1 @ (k5_relat_1 @ sk_A @ (k4_relat_1 @ sk_A)))
% 0.20/0.48         != (k1_relat_1 @ sk_A))),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['16', '52'])).
% 0.20/0.48  thf('54', plain,
% 0.20/0.48      ((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A)) | ~ (v1_relat_1 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['8', '53'])).
% 0.20/0.48  thf('55', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('56', plain, (((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['54', '55'])).
% 0.20/0.48  thf('57', plain, ($false), inference('simplify', [status(thm)], ['56'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
