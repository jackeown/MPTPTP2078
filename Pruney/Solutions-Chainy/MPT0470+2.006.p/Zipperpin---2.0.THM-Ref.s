%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CE4xaiMgQe

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:26 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 308 expanded)
%              Number of leaves         :   30 ( 107 expanded)
%              Depth                    :   29
%              Number of atoms          :  832 (2066 expanded)
%              Number of equality atoms :   67 ( 163 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v1_relat_1 @ X37 )
      | ~ ( v1_relat_1 @ X38 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('2',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( v1_relat_1 @ X41 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X42 @ X41 ) ) @ ( k2_relat_1 @ X41 ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X11: $i,X13: $i] :
      ( ( X11 = X13 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('6',plain,(
    ! [X14: $i] :
      ( r1_tarski @ k1_xboole_0 @ X14 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('7',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

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

thf('8',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('9',plain,(
    ! [X36: $i] :
      ( ( v1_relat_1 @ X36 )
      | ~ ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('10',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v1_relat_1 @ X37 )
      | ~ ( v1_relat_1 @ X38 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('11',plain,(
    ! [X36: $i] :
      ( ( v1_relat_1 @ X36 )
      | ~ ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('12',plain,
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

thf('13',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X44 @ X43 ) )
        = ( k1_relat_1 @ X44 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X44 ) @ ( k1_relat_1 @ X43 ) )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X14: $i] :
      ( r1_tarski @ k1_xboole_0 @ X14 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('16',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('19',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('21',plain,(
    ! [X39: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X39 ) )
      | ~ ( v1_relat_1 @ X39 )
      | ( v1_xboole_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','26'])).

thf('28',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X36: $i] :
      ( ( v1_relat_1 @ X36 )
      | ~ ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('31',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('33',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v1_relat_1 @ X37 )
      | ~ ( v1_relat_1 @ X38 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['41'])).

thf('43',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6','7','43'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('45',plain,(
    ! [X40: $i] :
      ( ( r1_tarski @ X40 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X40 ) @ ( k2_relat_1 @ X40 ) ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('46',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('47',plain,(
    ! [X14: $i] :
      ( r1_tarski @ k1_xboole_0 @ X14 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('48',plain,(
    ! [X11: $i,X13: $i] :
      ( ( X11 = X13 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['45','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['44','51'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('53',plain,(
    ! [X15: $i] :
      ( r1_xboole_0 @ X15 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t127_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ B )
        | ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('54',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X30 @ X31 ) @ ( k2_zfmisc_1 @ X32 @ X33 ) )
      | ~ ( r1_xboole_0 @ X31 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('56',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('57',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('58',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X7 @ X10 ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','60'])).

thf('62',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['52','63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','65'])).

thf('67',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','42'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('71',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['71'])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('75',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('76',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('79',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['71'])).

thf('80',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('84',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','84'])).

thf('86',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('88',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['71'])).

thf('90',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['73','90'])).

thf('92',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','91'])).

thf('93',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('95',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,(
    $false ),
    inference(simplify,[status(thm)],['95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CE4xaiMgQe
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:11:00 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.75/0.96  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.75/0.96  % Solved by: fo/fo7.sh
% 0.75/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.96  % done 1302 iterations in 0.556s
% 0.75/0.96  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.75/0.96  % SZS output start Refutation
% 0.75/0.96  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.75/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.96  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/0.96  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.75/0.96  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.75/0.96  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.75/0.96  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.75/0.96  thf(sk_B_type, type, sk_B: $i > $i).
% 0.75/0.96  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/0.96  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.75/0.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.96  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.75/0.96  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.75/0.96  thf(dt_k5_relat_1, axiom,
% 0.75/0.96    (![A:$i,B:$i]:
% 0.75/0.96     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.75/0.96       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.75/0.96  thf('0', plain,
% 0.75/0.96      (![X37 : $i, X38 : $i]:
% 0.75/0.96         (~ (v1_relat_1 @ X37)
% 0.75/0.96          | ~ (v1_relat_1 @ X38)
% 0.75/0.96          | (v1_relat_1 @ (k5_relat_1 @ X37 @ X38)))),
% 0.75/0.96      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.75/0.96  thf(t60_relat_1, axiom,
% 0.75/0.96    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.75/0.96     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.75/0.96  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.96      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.75/0.96  thf(t45_relat_1, axiom,
% 0.75/0.96    (![A:$i]:
% 0.75/0.96     ( ( v1_relat_1 @ A ) =>
% 0.75/0.96       ( ![B:$i]:
% 0.75/0.96         ( ( v1_relat_1 @ B ) =>
% 0.75/0.96           ( r1_tarski @
% 0.75/0.96             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.75/0.96  thf('2', plain,
% 0.75/0.96      (![X41 : $i, X42 : $i]:
% 0.75/0.96         (~ (v1_relat_1 @ X41)
% 0.75/0.96          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X42 @ X41)) @ 
% 0.75/0.96             (k2_relat_1 @ X41))
% 0.75/0.96          | ~ (v1_relat_1 @ X42))),
% 0.75/0.96      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.75/0.96  thf(d10_xboole_0, axiom,
% 0.75/0.96    (![A:$i,B:$i]:
% 0.75/0.96     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.75/0.96  thf('3', plain,
% 0.75/0.96      (![X11 : $i, X13 : $i]:
% 0.75/0.96         (((X11) = (X13))
% 0.75/0.96          | ~ (r1_tarski @ X13 @ X11)
% 0.75/0.96          | ~ (r1_tarski @ X11 @ X13))),
% 0.75/0.96      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.75/0.96  thf('4', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]:
% 0.75/0.96         (~ (v1_relat_1 @ X1)
% 0.75/0.96          | ~ (v1_relat_1 @ X0)
% 0.75/0.96          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 0.75/0.96               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.75/0.96          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 0.75/0.96      inference('sup-', [status(thm)], ['2', '3'])).
% 0.75/0.96  thf('5', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         (~ (r1_tarski @ k1_xboole_0 @ 
% 0.75/0.96             (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))
% 0.75/0.96          | ((k2_relat_1 @ k1_xboole_0)
% 0.75/0.96              = (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))
% 0.75/0.96          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.75/0.96          | ~ (v1_relat_1 @ X0))),
% 0.75/0.96      inference('sup-', [status(thm)], ['1', '4'])).
% 0.75/0.96  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.75/0.96  thf('6', plain, (![X14 : $i]: (r1_tarski @ k1_xboole_0 @ X14)),
% 0.75/0.96      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.75/0.96  thf('7', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.96      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.75/0.96  thf(t62_relat_1, conjecture,
% 0.75/0.96    (![A:$i]:
% 0.75/0.96     ( ( v1_relat_1 @ A ) =>
% 0.75/0.96       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.75/0.96         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.75/0.96  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.96    (~( ![A:$i]:
% 0.75/0.96        ( ( v1_relat_1 @ A ) =>
% 0.75/0.96          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.75/0.96            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.75/0.96    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.75/0.96  thf('8', plain, ((v1_relat_1 @ sk_A)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf(cc1_relat_1, axiom,
% 0.75/0.96    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.75/0.96  thf('9', plain, (![X36 : $i]: ((v1_relat_1 @ X36) | ~ (v1_xboole_0 @ X36))),
% 0.75/0.96      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.75/0.96  thf('10', plain,
% 0.75/0.96      (![X37 : $i, X38 : $i]:
% 0.75/0.96         (~ (v1_relat_1 @ X37)
% 0.75/0.96          | ~ (v1_relat_1 @ X38)
% 0.75/0.96          | (v1_relat_1 @ (k5_relat_1 @ X37 @ X38)))),
% 0.75/0.96      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.75/0.96  thf('11', plain, (![X36 : $i]: ((v1_relat_1 @ X36) | ~ (v1_xboole_0 @ X36))),
% 0.75/0.96      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.75/0.96  thf('12', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.96      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.75/0.96  thf(t46_relat_1, axiom,
% 0.75/0.96    (![A:$i]:
% 0.75/0.96     ( ( v1_relat_1 @ A ) =>
% 0.75/0.96       ( ![B:$i]:
% 0.75/0.96         ( ( v1_relat_1 @ B ) =>
% 0.75/0.96           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.75/0.96             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.75/0.96  thf('13', plain,
% 0.75/0.96      (![X43 : $i, X44 : $i]:
% 0.75/0.96         (~ (v1_relat_1 @ X43)
% 0.75/0.96          | ((k1_relat_1 @ (k5_relat_1 @ X44 @ X43)) = (k1_relat_1 @ X44))
% 0.75/0.96          | ~ (r1_tarski @ (k2_relat_1 @ X44) @ (k1_relat_1 @ X43))
% 0.75/0.96          | ~ (v1_relat_1 @ X44))),
% 0.75/0.96      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.75/0.96  thf('14', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.75/0.96          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.75/0.96          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.75/0.96              = (k1_relat_1 @ k1_xboole_0))
% 0.75/0.96          | ~ (v1_relat_1 @ X0))),
% 0.75/0.96      inference('sup-', [status(thm)], ['12', '13'])).
% 0.75/0.96  thf('15', plain, (![X14 : $i]: (r1_tarski @ k1_xboole_0 @ X14)),
% 0.75/0.96      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.75/0.96  thf('16', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.96      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.75/0.96  thf('17', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         (~ (v1_relat_1 @ k1_xboole_0)
% 0.75/0.96          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.75/0.96          | ~ (v1_relat_1 @ X0))),
% 0.75/0.96      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.75/0.96  thf('18', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.75/0.96          | ~ (v1_relat_1 @ X0)
% 0.75/0.96          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['11', '17'])).
% 0.75/0.96  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.75/0.96  thf('19', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.75/0.96      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.75/0.96  thf('20', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         (~ (v1_relat_1 @ X0)
% 0.75/0.96          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.75/0.96      inference('demod', [status(thm)], ['18', '19'])).
% 0.75/0.96  thf(fc8_relat_1, axiom,
% 0.75/0.96    (![A:$i]:
% 0.75/0.96     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.75/0.96       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.75/0.96  thf('21', plain,
% 0.75/0.96      (![X39 : $i]:
% 0.75/0.96         (~ (v1_xboole_0 @ (k1_relat_1 @ X39))
% 0.75/0.96          | ~ (v1_relat_1 @ X39)
% 0.75/0.96          | (v1_xboole_0 @ X39))),
% 0.75/0.96      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.75/0.96  thf('22', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.75/0.96          | ~ (v1_relat_1 @ X0)
% 0.75/0.96          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.75/0.96          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['20', '21'])).
% 0.75/0.96  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.75/0.96      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.75/0.96  thf('24', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         (~ (v1_relat_1 @ X0)
% 0.75/0.96          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.75/0.96          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.75/0.96      inference('demod', [status(thm)], ['22', '23'])).
% 0.75/0.96  thf('25', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         (~ (v1_relat_1 @ X0)
% 0.75/0.96          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.75/0.96          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.75/0.96          | ~ (v1_relat_1 @ X0))),
% 0.75/0.96      inference('sup-', [status(thm)], ['10', '24'])).
% 0.75/0.96  thf('26', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.75/0.96          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.75/0.96          | ~ (v1_relat_1 @ X0))),
% 0.75/0.96      inference('simplify', [status(thm)], ['25'])).
% 0.75/0.96  thf('27', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.75/0.96          | ~ (v1_relat_1 @ X0)
% 0.75/0.96          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['9', '26'])).
% 0.75/0.96  thf('28', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.75/0.96      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.75/0.96  thf('29', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.75/0.96      inference('demod', [status(thm)], ['27', '28'])).
% 0.75/0.96  thf('30', plain, (![X36 : $i]: ((v1_relat_1 @ X36) | ~ (v1_xboole_0 @ X36))),
% 0.75/0.96      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.75/0.96  thf(l13_xboole_0, axiom,
% 0.75/0.96    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.75/0.96  thf('31', plain,
% 0.75/0.96      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.75/0.96      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.75/0.96  thf('32', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.75/0.96      inference('demod', [status(thm)], ['27', '28'])).
% 0.75/0.96  thf('33', plain,
% 0.75/0.96      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.75/0.96      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.75/0.96  thf('34', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         (~ (v1_relat_1 @ X0)
% 0.75/0.96          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['32', '33'])).
% 0.75/0.96  thf('35', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]:
% 0.75/0.96         (((k5_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.75/0.96          | ~ (v1_xboole_0 @ X0)
% 0.75/0.96          | ~ (v1_relat_1 @ X1))),
% 0.75/0.96      inference('sup+', [status(thm)], ['31', '34'])).
% 0.75/0.96  thf('36', plain,
% 0.75/0.96      (![X37 : $i, X38 : $i]:
% 0.75/0.96         (~ (v1_relat_1 @ X37)
% 0.75/0.96          | ~ (v1_relat_1 @ X38)
% 0.75/0.96          | (v1_relat_1 @ (k5_relat_1 @ X37 @ X38)))),
% 0.75/0.96      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.75/0.96  thf('37', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]:
% 0.75/0.96         ((v1_relat_1 @ k1_xboole_0)
% 0.75/0.96          | ~ (v1_relat_1 @ X0)
% 0.75/0.96          | ~ (v1_xboole_0 @ X1)
% 0.75/0.96          | ~ (v1_relat_1 @ X0)
% 0.75/0.96          | ~ (v1_relat_1 @ X1))),
% 0.75/0.96      inference('sup+', [status(thm)], ['35', '36'])).
% 0.75/0.96  thf('38', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]:
% 0.75/0.96         (~ (v1_relat_1 @ X1)
% 0.75/0.96          | ~ (v1_xboole_0 @ X1)
% 0.75/0.96          | ~ (v1_relat_1 @ X0)
% 0.75/0.96          | (v1_relat_1 @ k1_xboole_0))),
% 0.75/0.96      inference('simplify', [status(thm)], ['37'])).
% 0.75/0.96  thf('39', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]:
% 0.75/0.96         (~ (v1_xboole_0 @ X0)
% 0.75/0.96          | (v1_relat_1 @ k1_xboole_0)
% 0.75/0.96          | ~ (v1_relat_1 @ X1)
% 0.75/0.96          | ~ (v1_xboole_0 @ X0))),
% 0.75/0.96      inference('sup-', [status(thm)], ['30', '38'])).
% 0.75/0.96  thf('40', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]:
% 0.75/0.96         (~ (v1_relat_1 @ X1)
% 0.75/0.96          | (v1_relat_1 @ k1_xboole_0)
% 0.75/0.96          | ~ (v1_xboole_0 @ X0))),
% 0.75/0.96      inference('simplify', [status(thm)], ['39'])).
% 0.75/0.96  thf('41', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]:
% 0.75/0.96         (~ (v1_relat_1 @ X0)
% 0.75/0.96          | (v1_relat_1 @ k1_xboole_0)
% 0.75/0.96          | ~ (v1_relat_1 @ X1))),
% 0.75/0.96      inference('sup-', [status(thm)], ['29', '40'])).
% 0.75/0.96  thf('42', plain,
% 0.75/0.96      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.75/0.96      inference('condensation', [status(thm)], ['41'])).
% 0.75/0.96  thf('43', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.75/0.96      inference('sup-', [status(thm)], ['8', '42'])).
% 0.75/0.96  thf('44', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         (((k1_xboole_0) = (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))
% 0.75/0.96          | ~ (v1_relat_1 @ X0))),
% 0.75/0.96      inference('demod', [status(thm)], ['5', '6', '7', '43'])).
% 0.75/0.96  thf(t21_relat_1, axiom,
% 0.75/0.96    (![A:$i]:
% 0.75/0.96     ( ( v1_relat_1 @ A ) =>
% 0.75/0.96       ( r1_tarski @
% 0.75/0.96         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.75/0.96  thf('45', plain,
% 0.75/0.96      (![X40 : $i]:
% 0.75/0.96         ((r1_tarski @ X40 @ 
% 0.75/0.96           (k2_zfmisc_1 @ (k1_relat_1 @ X40) @ (k2_relat_1 @ X40)))
% 0.75/0.96          | ~ (v1_relat_1 @ X40))),
% 0.75/0.96      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.75/0.96  thf('46', plain,
% 0.75/0.96      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.75/0.96      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.75/0.96  thf('47', plain, (![X14 : $i]: (r1_tarski @ k1_xboole_0 @ X14)),
% 0.75/0.96      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.75/0.96  thf('48', plain,
% 0.75/0.96      (![X11 : $i, X13 : $i]:
% 0.75/0.96         (((X11) = (X13))
% 0.75/0.96          | ~ (r1_tarski @ X13 @ X11)
% 0.75/0.96          | ~ (r1_tarski @ X11 @ X13))),
% 0.75/0.96      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.75/0.96  thf('49', plain,
% 0.75/0.96      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['47', '48'])).
% 0.75/0.96  thf('50', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]:
% 0.75/0.96         (~ (r1_tarski @ X1 @ X0)
% 0.75/0.96          | ~ (v1_xboole_0 @ X0)
% 0.75/0.96          | ((X1) = (k1_xboole_0)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['46', '49'])).
% 0.75/0.96  thf('51', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         (~ (v1_relat_1 @ X0)
% 0.75/0.96          | ((X0) = (k1_xboole_0))
% 0.75/0.96          | ~ (v1_xboole_0 @ 
% 0.75/0.96               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 0.75/0.96      inference('sup-', [status(thm)], ['45', '50'])).
% 0.75/0.96  thf('52', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         (~ (v1_xboole_0 @ 
% 0.75/0.96             (k2_zfmisc_1 @ (k1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.75/0.96              k1_xboole_0))
% 0.75/0.96          | ~ (v1_relat_1 @ X0)
% 0.75/0.96          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.75/0.96          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['44', '51'])).
% 0.75/0.96  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.75/0.96  thf('53', plain, (![X15 : $i]: (r1_xboole_0 @ X15 @ k1_xboole_0)),
% 0.75/0.96      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.75/0.96  thf(t127_zfmisc_1, axiom,
% 0.75/0.96    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.96     ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.75/0.96       ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.75/0.96  thf('54', plain,
% 0.75/0.96      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.75/0.96         ((r1_xboole_0 @ (k2_zfmisc_1 @ X30 @ X31) @ (k2_zfmisc_1 @ X32 @ X33))
% 0.75/0.96          | ~ (r1_xboole_0 @ X31 @ X33))),
% 0.75/0.96      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.75/0.96  thf('55', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.96         (r1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ 
% 0.75/0.96          (k2_zfmisc_1 @ X1 @ k1_xboole_0))),
% 0.75/0.96      inference('sup-', [status(thm)], ['53', '54'])).
% 0.75/0.96  thf(d1_xboole_0, axiom,
% 0.75/0.96    (![A:$i]:
% 0.75/0.96     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.75/0.96  thf('56', plain,
% 0.75/0.96      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.75/0.96      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.75/0.96  thf(idempotence_k3_xboole_0, axiom,
% 0.75/0.96    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.75/0.96  thf('57', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.75/0.96      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.75/0.96  thf(t4_xboole_0, axiom,
% 0.75/0.96    (![A:$i,B:$i]:
% 0.75/0.96     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.75/0.96            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.75/0.96       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.75/0.96            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.75/0.96  thf('58', plain,
% 0.75/0.96      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.75/0.96         (~ (r2_hidden @ X9 @ (k3_xboole_0 @ X7 @ X10))
% 0.75/0.96          | ~ (r1_xboole_0 @ X7 @ X10))),
% 0.75/0.96      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.75/0.96  thf('59', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]:
% 0.75/0.96         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.75/0.96      inference('sup-', [status(thm)], ['57', '58'])).
% 0.75/0.96  thf('60', plain,
% 0.75/0.96      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.75/0.96      inference('sup-', [status(thm)], ['56', '59'])).
% 0.75/0.96  thf('61', plain,
% 0.75/0.96      (![X0 : $i]: (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0))),
% 0.75/0.96      inference('sup-', [status(thm)], ['55', '60'])).
% 0.75/0.96  thf('62', plain,
% 0.75/0.96      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.75/0.96      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.75/0.96  thf('63', plain,
% 0.75/0.97      (![X0 : $i]: ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.97      inference('sup-', [status(thm)], ['61', '62'])).
% 0.75/0.97  thf('64', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.75/0.97      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.75/0.97  thf('65', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         (~ (v1_relat_1 @ X0)
% 0.75/0.97          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.75/0.97          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.75/0.97      inference('demod', [status(thm)], ['52', '63', '64'])).
% 0.75/0.97  thf('66', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         (~ (v1_relat_1 @ k1_xboole_0)
% 0.75/0.97          | ~ (v1_relat_1 @ X0)
% 0.75/0.97          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.75/0.97          | ~ (v1_relat_1 @ X0))),
% 0.75/0.97      inference('sup-', [status(thm)], ['0', '65'])).
% 0.75/0.97  thf('67', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.75/0.97      inference('sup-', [status(thm)], ['8', '42'])).
% 0.75/0.97  thf('68', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         (~ (v1_relat_1 @ X0)
% 0.75/0.97          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.75/0.97          | ~ (v1_relat_1 @ X0))),
% 0.75/0.97      inference('demod', [status(thm)], ['66', '67'])).
% 0.75/0.97  thf('69', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         (((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.75/0.97          | ~ (v1_relat_1 @ X0))),
% 0.75/0.97      inference('simplify', [status(thm)], ['68'])).
% 0.75/0.97  thf('70', plain,
% 0.75/0.97      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.75/0.97      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.75/0.97  thf('71', plain,
% 0.75/0.97      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.75/0.97        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('72', plain,
% 0.75/0.97      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.75/0.97         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.75/0.97      inference('split', [status(esa)], ['71'])).
% 0.75/0.97  thf('73', plain,
% 0.75/0.97      ((![X0 : $i]:
% 0.75/0.97          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.75/0.97         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.75/0.97      inference('sup-', [status(thm)], ['70', '72'])).
% 0.75/0.97  thf('74', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.75/0.97      inference('demod', [status(thm)], ['27', '28'])).
% 0.75/0.97  thf('75', plain,
% 0.75/0.97      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.75/0.97      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.75/0.97  thf('76', plain,
% 0.75/0.97      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.75/0.97      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.75/0.97  thf('77', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.75/0.97      inference('sup+', [status(thm)], ['75', '76'])).
% 0.75/0.97  thf('78', plain,
% 0.75/0.97      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.75/0.97      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.75/0.97  thf('79', plain,
% 0.75/0.97      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.75/0.97         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.75/0.97      inference('split', [status(esa)], ['71'])).
% 0.75/0.97  thf('80', plain,
% 0.75/0.97      ((![X0 : $i]:
% 0.75/0.97          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.75/0.97         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.75/0.97      inference('sup-', [status(thm)], ['78', '79'])).
% 0.75/0.97  thf('81', plain,
% 0.75/0.97      ((![X0 : $i, X1 : $i]:
% 0.75/0.97          (((X0) != (k1_xboole_0))
% 0.75/0.97           | ~ (v1_xboole_0 @ X0)
% 0.75/0.97           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.75/0.97           | ~ (v1_xboole_0 @ X1)))
% 0.75/0.97         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.75/0.97      inference('sup-', [status(thm)], ['77', '80'])).
% 0.75/0.97  thf('82', plain,
% 0.75/0.97      ((![X1 : $i]:
% 0.75/0.97          (~ (v1_xboole_0 @ X1)
% 0.75/0.97           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.75/0.97           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.75/0.97         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.75/0.97      inference('simplify', [status(thm)], ['81'])).
% 0.75/0.97  thf('83', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.75/0.97      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.75/0.97  thf('84', plain,
% 0.75/0.97      ((![X1 : $i]:
% 0.75/0.97          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))))
% 0.75/0.97         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.75/0.97      inference('simplify_reflect+', [status(thm)], ['82', '83'])).
% 0.75/0.97  thf('85', plain,
% 0.75/0.97      (((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.75/0.97         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.75/0.97      inference('sup-', [status(thm)], ['74', '84'])).
% 0.75/0.97  thf('86', plain, ((v1_relat_1 @ sk_A)),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('87', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.75/0.97      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.75/0.97  thf('88', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.75/0.97      inference('demod', [status(thm)], ['85', '86', '87'])).
% 0.75/0.97  thf('89', plain,
% 0.75/0.97      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.75/0.97       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.75/0.97      inference('split', [status(esa)], ['71'])).
% 0.75/0.97  thf('90', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.75/0.97      inference('sat_resolution*', [status(thm)], ['88', '89'])).
% 0.75/0.97  thf('91', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.75/0.97      inference('simpl_trail', [status(thm)], ['73', '90'])).
% 0.75/0.97  thf('92', plain,
% 0.75/0.97      ((((k1_xboole_0) != (k1_xboole_0))
% 0.75/0.97        | ~ (v1_relat_1 @ sk_A)
% 0.75/0.97        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.75/0.97      inference('sup-', [status(thm)], ['69', '91'])).
% 0.75/0.97  thf('93', plain, ((v1_relat_1 @ sk_A)),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('94', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.75/0.97      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.75/0.97  thf('95', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.75/0.97      inference('demod', [status(thm)], ['92', '93', '94'])).
% 0.75/0.97  thf('96', plain, ($false), inference('simplify', [status(thm)], ['95'])).
% 0.75/0.97  
% 0.75/0.97  % SZS output end Refutation
% 0.75/0.97  
% 0.75/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
