%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H9Hrsb5dkR

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:44 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 173 expanded)
%              Number of leaves         :   30 (  66 expanded)
%              Depth                    :   18
%              Number of atoms          :  624 (1147 expanded)
%              Number of equality atoms :   55 ( 110 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v1_relat_1 @ X42 )
      | ~ ( v1_relat_1 @ X43 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X42 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t47_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v1_relat_1 @ X48 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X48 @ X49 ) )
        = ( k2_relat_1 @ X49 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X49 ) @ ( k2_relat_1 @ X48 ) )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('4',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('5',plain,(
    ! [X39: $i] :
      ( ( v1_relat_1 @ X39 )
      | ( r2_hidden @ ( sk_B @ X39 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X35 @ X36 ) )
      = ( k3_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('8',plain,(
    ! [X5: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X5 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('9',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X1 @ X4 ) )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('10',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X35 @ X36 ) )
      = ( k3_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('11',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X4 ) ) )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('13',plain,(
    ! [X7: $i] :
      ( r1_xboole_0 @ X7 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('14',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','14'])).

thf('16',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4','15','16'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('18',plain,(
    ! [X45: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X45 ) )
      | ~ ( v1_relat_1 @ X45 )
      | ( v1_xboole_0 @ X45 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('20',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','21'])).

thf('23',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','14'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('26',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t62_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
          = k1_xboole_0 )
        & ( ( k5_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
            = k1_xboole_0 )
          & ( ( k5_relat_1 @ A @ k1_xboole_0 )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_relat_1])).

thf('29',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v1_relat_1 @ X42 )
      | ~ ( v1_relat_1 @ X43 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X42 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('33',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('34',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( v1_relat_1 @ X46 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X47 @ X46 ) )
        = ( k1_relat_1 @ X47 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X47 ) @ ( k1_relat_1 @ X46 ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('37',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','14'])).

thf('38',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('40',plain,(
    ! [X44: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X44 ) )
      | ~ ( v1_relat_1 @ X44 )
      | ( v1_xboole_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','43'])).

thf('45',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','14'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('52',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['29'])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('57',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('61',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['29'])).

thf('63',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['31','63'])).

thf('65',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('68',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    $false ),
    inference(simplify,[status(thm)],['68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H9Hrsb5dkR
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:02:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.42/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.62  % Solved by: fo/fo7.sh
% 0.42/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.62  % done 227 iterations in 0.159s
% 0.42/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.62  % SZS output start Refutation
% 0.42/0.62  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.42/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.62  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.42/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.42/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.42/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.62  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.42/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.42/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.42/0.62  thf(sk_B_type, type, sk_B: $i > $i).
% 0.42/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.42/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.42/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.62  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.42/0.62  thf(dt_k5_relat_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.42/0.62       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.42/0.62  thf('0', plain,
% 0.42/0.62      (![X42 : $i, X43 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ X42)
% 0.42/0.62          | ~ (v1_relat_1 @ X43)
% 0.42/0.62          | (v1_relat_1 @ (k5_relat_1 @ X42 @ X43)))),
% 0.42/0.62      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.42/0.62  thf(t60_relat_1, axiom,
% 0.42/0.62    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.42/0.62     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.42/0.62  thf('1', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.62      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.42/0.62  thf(t47_relat_1, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( v1_relat_1 @ A ) =>
% 0.42/0.62       ( ![B:$i]:
% 0.42/0.62         ( ( v1_relat_1 @ B ) =>
% 0.42/0.62           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.42/0.62             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.42/0.62  thf('2', plain,
% 0.42/0.62      (![X48 : $i, X49 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ X48)
% 0.42/0.62          | ((k2_relat_1 @ (k5_relat_1 @ X48 @ X49)) = (k2_relat_1 @ X49))
% 0.42/0.62          | ~ (r1_tarski @ (k1_relat_1 @ X49) @ (k2_relat_1 @ X48))
% 0.42/0.62          | ~ (v1_relat_1 @ X49))),
% 0.42/0.62      inference('cnf', [status(esa)], [t47_relat_1])).
% 0.42/0.62  thf('3', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (r1_tarski @ k1_xboole_0 @ (k2_relat_1 @ X0))
% 0.42/0.62          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.42/0.62          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.42/0.62              = (k2_relat_1 @ k1_xboole_0))
% 0.42/0.62          | ~ (v1_relat_1 @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.42/0.62  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.42/0.62  thf('4', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.42/0.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.42/0.62  thf(d1_relat_1, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( v1_relat_1 @ A ) <=>
% 0.42/0.62       ( ![B:$i]:
% 0.42/0.62         ( ~( ( r2_hidden @ B @ A ) & 
% 0.42/0.62              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.42/0.62  thf('5', plain,
% 0.42/0.62      (![X39 : $i]: ((v1_relat_1 @ X39) | (r2_hidden @ (sk_B @ X39) @ X39))),
% 0.42/0.62      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.42/0.62  thf(t2_boole, axiom,
% 0.42/0.62    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.42/0.62  thf('6', plain,
% 0.42/0.62      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.62      inference('cnf', [status(esa)], [t2_boole])).
% 0.42/0.62  thf(t12_setfam_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.42/0.62  thf('7', plain,
% 0.42/0.62      (![X35 : $i, X36 : $i]:
% 0.42/0.62         ((k1_setfam_1 @ (k2_tarski @ X35 @ X36)) = (k3_xboole_0 @ X35 @ X36))),
% 0.42/0.62      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.42/0.62  thf('8', plain,
% 0.42/0.62      (![X5 : $i]:
% 0.42/0.62         ((k1_setfam_1 @ (k2_tarski @ X5 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.42/0.62      inference('demod', [status(thm)], ['6', '7'])).
% 0.42/0.62  thf(t4_xboole_0, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.42/0.62            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.42/0.62       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.42/0.62            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.42/0.62  thf('9', plain,
% 0.42/0.62      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X1 @ X4))
% 0.42/0.62          | ~ (r1_xboole_0 @ X1 @ X4))),
% 0.42/0.62      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.42/0.62  thf('10', plain,
% 0.42/0.62      (![X35 : $i, X36 : $i]:
% 0.42/0.62         ((k1_setfam_1 @ (k2_tarski @ X35 @ X36)) = (k3_xboole_0 @ X35 @ X36))),
% 0.42/0.62      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.42/0.62  thf('11', plain,
% 0.42/0.62      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X3 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X4)))
% 0.42/0.62          | ~ (r1_xboole_0 @ X1 @ X4))),
% 0.42/0.62      inference('demod', [status(thm)], ['9', '10'])).
% 0.42/0.62  thf('12', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['8', '11'])).
% 0.42/0.62  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.42/0.62  thf('13', plain, (![X7 : $i]: (r1_xboole_0 @ X7 @ k1_xboole_0)),
% 0.42/0.62      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.42/0.62  thf('14', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.42/0.62      inference('demod', [status(thm)], ['12', '13'])).
% 0.42/0.62  thf('15', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.42/0.62      inference('sup-', [status(thm)], ['5', '14'])).
% 0.42/0.62  thf('16', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.62      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.42/0.62  thf('17', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.42/0.62          | ~ (v1_relat_1 @ X0))),
% 0.42/0.62      inference('demod', [status(thm)], ['3', '4', '15', '16'])).
% 0.42/0.62  thf(fc9_relat_1, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.42/0.62       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.42/0.62  thf('18', plain,
% 0.42/0.62      (![X45 : $i]:
% 0.42/0.62         (~ (v1_xboole_0 @ (k2_relat_1 @ X45))
% 0.42/0.62          | ~ (v1_relat_1 @ X45)
% 0.42/0.62          | (v1_xboole_0 @ X45))),
% 0.42/0.62      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.42/0.62  thf('19', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.42/0.62          | ~ (v1_relat_1 @ X0)
% 0.42/0.62          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.42/0.62          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['17', '18'])).
% 0.42/0.62  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.42/0.63  thf('20', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.42/0.63      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.42/0.63  thf('21', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         (~ (v1_relat_1 @ X0)
% 0.42/0.63          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.42/0.63          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.42/0.63      inference('demod', [status(thm)], ['19', '20'])).
% 0.42/0.63  thf('22', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         (~ (v1_relat_1 @ k1_xboole_0)
% 0.42/0.63          | ~ (v1_relat_1 @ X0)
% 0.42/0.63          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.42/0.63          | ~ (v1_relat_1 @ X0))),
% 0.42/0.63      inference('sup-', [status(thm)], ['0', '21'])).
% 0.42/0.63  thf('23', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.42/0.63      inference('sup-', [status(thm)], ['5', '14'])).
% 0.42/0.63  thf('24', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         (~ (v1_relat_1 @ X0)
% 0.42/0.63          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.42/0.63          | ~ (v1_relat_1 @ X0))),
% 0.42/0.63      inference('demod', [status(thm)], ['22', '23'])).
% 0.42/0.63  thf('25', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         ((v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)) | ~ (v1_relat_1 @ X0))),
% 0.42/0.63      inference('simplify', [status(thm)], ['24'])).
% 0.42/0.63  thf(l13_xboole_0, axiom,
% 0.42/0.63    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.42/0.63  thf('26', plain,
% 0.42/0.63      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.42/0.63      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.42/0.63  thf('27', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         (~ (v1_relat_1 @ X0)
% 0.42/0.63          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.42/0.63      inference('sup-', [status(thm)], ['25', '26'])).
% 0.42/0.63  thf('28', plain,
% 0.42/0.63      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.42/0.63      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.42/0.63  thf(t62_relat_1, conjecture,
% 0.42/0.63    (![A:$i]:
% 0.42/0.63     ( ( v1_relat_1 @ A ) =>
% 0.42/0.63       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.42/0.63         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.42/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.63    (~( ![A:$i]:
% 0.42/0.63        ( ( v1_relat_1 @ A ) =>
% 0.42/0.63          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.42/0.63            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.42/0.63    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.42/0.63  thf('29', plain,
% 0.42/0.63      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.42/0.63        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('30', plain,
% 0.42/0.63      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.42/0.63         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.42/0.63      inference('split', [status(esa)], ['29'])).
% 0.42/0.63  thf('31', plain,
% 0.42/0.63      ((![X0 : $i]:
% 0.42/0.63          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.42/0.63         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.42/0.63      inference('sup-', [status(thm)], ['28', '30'])).
% 0.42/0.63  thf('32', plain,
% 0.42/0.63      (![X42 : $i, X43 : $i]:
% 0.42/0.63         (~ (v1_relat_1 @ X42)
% 0.42/0.63          | ~ (v1_relat_1 @ X43)
% 0.42/0.63          | (v1_relat_1 @ (k5_relat_1 @ X42 @ X43)))),
% 0.42/0.63      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.42/0.63  thf('33', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.63      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.42/0.63  thf(t46_relat_1, axiom,
% 0.42/0.63    (![A:$i]:
% 0.42/0.63     ( ( v1_relat_1 @ A ) =>
% 0.42/0.63       ( ![B:$i]:
% 0.42/0.63         ( ( v1_relat_1 @ B ) =>
% 0.42/0.63           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.42/0.63             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.42/0.63  thf('34', plain,
% 0.42/0.63      (![X46 : $i, X47 : $i]:
% 0.42/0.63         (~ (v1_relat_1 @ X46)
% 0.42/0.63          | ((k1_relat_1 @ (k5_relat_1 @ X47 @ X46)) = (k1_relat_1 @ X47))
% 0.42/0.63          | ~ (r1_tarski @ (k2_relat_1 @ X47) @ (k1_relat_1 @ X46))
% 0.42/0.63          | ~ (v1_relat_1 @ X47))),
% 0.42/0.63      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.42/0.63  thf('35', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.42/0.63          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.42/0.63          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.42/0.63              = (k1_relat_1 @ k1_xboole_0))
% 0.42/0.63          | ~ (v1_relat_1 @ X0))),
% 0.42/0.63      inference('sup-', [status(thm)], ['33', '34'])).
% 0.42/0.63  thf('36', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.42/0.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.42/0.63  thf('37', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.42/0.63      inference('sup-', [status(thm)], ['5', '14'])).
% 0.42/0.63  thf('38', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.63      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.42/0.63  thf('39', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         (((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.42/0.63          | ~ (v1_relat_1 @ X0))),
% 0.42/0.63      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 0.42/0.63  thf(fc8_relat_1, axiom,
% 0.42/0.63    (![A:$i]:
% 0.42/0.63     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.42/0.63       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.42/0.63  thf('40', plain,
% 0.42/0.63      (![X44 : $i]:
% 0.42/0.63         (~ (v1_xboole_0 @ (k1_relat_1 @ X44))
% 0.42/0.63          | ~ (v1_relat_1 @ X44)
% 0.42/0.63          | (v1_xboole_0 @ X44))),
% 0.42/0.63      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.42/0.63  thf('41', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.42/0.63          | ~ (v1_relat_1 @ X0)
% 0.42/0.63          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.42/0.63          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.42/0.63      inference('sup-', [status(thm)], ['39', '40'])).
% 0.42/0.63  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.42/0.63      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.42/0.63  thf('43', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         (~ (v1_relat_1 @ X0)
% 0.42/0.63          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.42/0.63          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.42/0.63      inference('demod', [status(thm)], ['41', '42'])).
% 0.42/0.63  thf('44', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         (~ (v1_relat_1 @ X0)
% 0.42/0.63          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.42/0.63          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.42/0.63          | ~ (v1_relat_1 @ X0))),
% 0.42/0.63      inference('sup-', [status(thm)], ['32', '43'])).
% 0.42/0.63  thf('45', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.42/0.63      inference('sup-', [status(thm)], ['5', '14'])).
% 0.42/0.63  thf('46', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         (~ (v1_relat_1 @ X0)
% 0.42/0.63          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.42/0.63          | ~ (v1_relat_1 @ X0))),
% 0.42/0.63      inference('demod', [status(thm)], ['44', '45'])).
% 0.42/0.63  thf('47', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.42/0.63      inference('simplify', [status(thm)], ['46'])).
% 0.42/0.63  thf('48', plain,
% 0.42/0.63      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.42/0.63      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.42/0.63  thf('49', plain,
% 0.42/0.63      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.42/0.63      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.42/0.63  thf('50', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]:
% 0.42/0.63         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.42/0.63      inference('sup+', [status(thm)], ['48', '49'])).
% 0.42/0.63  thf('51', plain,
% 0.42/0.63      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.42/0.63      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.42/0.63  thf('52', plain,
% 0.42/0.63      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.42/0.63         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.42/0.63      inference('split', [status(esa)], ['29'])).
% 0.42/0.63  thf('53', plain,
% 0.42/0.63      ((![X0 : $i]:
% 0.42/0.63          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.42/0.63         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.42/0.63      inference('sup-', [status(thm)], ['51', '52'])).
% 0.42/0.63  thf('54', plain,
% 0.42/0.63      ((![X0 : $i, X1 : $i]:
% 0.42/0.63          (((X0) != (k1_xboole_0))
% 0.42/0.63           | ~ (v1_xboole_0 @ X0)
% 0.42/0.63           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.42/0.63           | ~ (v1_xboole_0 @ X1)))
% 0.42/0.63         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.42/0.63      inference('sup-', [status(thm)], ['50', '53'])).
% 0.42/0.63  thf('55', plain,
% 0.42/0.63      ((![X1 : $i]:
% 0.42/0.63          (~ (v1_xboole_0 @ X1)
% 0.42/0.63           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.42/0.63           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.42/0.63         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.42/0.63      inference('simplify', [status(thm)], ['54'])).
% 0.42/0.63  thf('56', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.42/0.63      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.42/0.63  thf('57', plain,
% 0.42/0.63      ((![X1 : $i]:
% 0.42/0.63          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))))
% 0.42/0.63         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.42/0.63      inference('simplify_reflect+', [status(thm)], ['55', '56'])).
% 0.42/0.63  thf('58', plain,
% 0.42/0.63      (((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.42/0.63         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.42/0.63      inference('sup-', [status(thm)], ['47', '57'])).
% 0.42/0.63  thf('59', plain, ((v1_relat_1 @ sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('60', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.42/0.63      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.42/0.63  thf('61', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.42/0.63      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.42/0.63  thf('62', plain,
% 0.42/0.63      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.42/0.63       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.42/0.63      inference('split', [status(esa)], ['29'])).
% 0.42/0.63  thf('63', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.42/0.63      inference('sat_resolution*', [status(thm)], ['61', '62'])).
% 0.42/0.63  thf('64', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.42/0.63      inference('simpl_trail', [status(thm)], ['31', '63'])).
% 0.42/0.63  thf('65', plain,
% 0.42/0.63      ((((k1_xboole_0) != (k1_xboole_0))
% 0.42/0.63        | ~ (v1_relat_1 @ sk_A)
% 0.42/0.63        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.42/0.63      inference('sup-', [status(thm)], ['27', '64'])).
% 0.42/0.63  thf('66', plain, ((v1_relat_1 @ sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('67', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.42/0.63      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.42/0.63  thf('68', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.42/0.63      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.42/0.63  thf('69', plain, ($false), inference('simplify', [status(thm)], ['68'])).
% 0.42/0.63  
% 0.42/0.63  % SZS output end Refutation
% 0.42/0.63  
% 0.47/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
