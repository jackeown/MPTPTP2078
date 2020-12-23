%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.V8aBuwFnwb

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 128 expanded)
%              Number of leaves         :   23 (  47 expanded)
%              Depth                    :   19
%              Number of atoms          :  652 ( 860 expanded)
%              Number of equality atoms :   72 ( 103 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('0',plain,(
    ! [X23: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_relat_1 @ X25 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('2',plain,(
    ! [X23: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('3',plain,
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

thf('4',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X29 @ X30 ) )
        = ( k2_relat_1 @ X30 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X30 ) @ ( k2_relat_1 @ X29 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('6',plain,(
    ! [X2: $i] :
      ( r1_tarski @ k1_xboole_0 @ X2 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('7',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('10',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(fc3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ B )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X17 @ X18 ) )
      | ~ ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('15',plain,(
    ! [X26: $i] :
      ( ( ( k3_xboole_0 @ X26 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X26 ) @ ( k2_relat_1 @ X26 ) ) )
        = X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
        = X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('17',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','23'])).

thf('25',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
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

thf('28',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X23: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('32',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_relat_1 @ X25 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('33',plain,(
    ! [X23: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('34',plain,
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

thf('35',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X28 @ X27 ) )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X28 ) @ ( k1_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X2: $i] :
      ( r1_tarski @ k1_xboole_0 @ X2 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('38',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('43',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_xboole_0 @ X19 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X26: $i] :
      ( ( ( k3_xboole_0 @ X26 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X26 ) @ ( k2_relat_1 @ X26 ) ) )
        = X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
        = X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','49'])).

thf('51',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','54'])).

thf('56',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('59',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('64',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('67',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['30','67'])).

thf('69',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('72',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    $false ),
    inference(simplify,[status(thm)],['72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.V8aBuwFnwb
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:10:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.58  % Solved by: fo/fo7.sh
% 0.21/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.58  % done 206 iterations in 0.124s
% 0.21/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.58  % SZS output start Refutation
% 0.21/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.58  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.58  thf(cc1_relat_1, axiom,
% 0.21/0.58    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.21/0.58  thf('0', plain, (![X23 : $i]: ((v1_relat_1 @ X23) | ~ (v1_xboole_0 @ X23))),
% 0.21/0.58      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.21/0.58  thf(dt_k5_relat_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.21/0.58       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.21/0.58  thf('1', plain,
% 0.21/0.58      (![X24 : $i, X25 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ X24)
% 0.21/0.58          | ~ (v1_relat_1 @ X25)
% 0.21/0.58          | (v1_relat_1 @ (k5_relat_1 @ X24 @ X25)))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.21/0.58  thf('2', plain, (![X23 : $i]: ((v1_relat_1 @ X23) | ~ (v1_xboole_0 @ X23))),
% 0.21/0.58      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.21/0.58  thf(t60_relat_1, axiom,
% 0.21/0.58    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.58     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.58  thf('3', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.58      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.58  thf(t47_relat_1, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( v1_relat_1 @ A ) =>
% 0.21/0.58       ( ![B:$i]:
% 0.21/0.58         ( ( v1_relat_1 @ B ) =>
% 0.21/0.58           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.21/0.58             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.21/0.58  thf('4', plain,
% 0.21/0.58      (![X29 : $i, X30 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ X29)
% 0.21/0.58          | ((k2_relat_1 @ (k5_relat_1 @ X29 @ X30)) = (k2_relat_1 @ X30))
% 0.21/0.58          | ~ (r1_tarski @ (k1_relat_1 @ X30) @ (k2_relat_1 @ X29))
% 0.21/0.58          | ~ (v1_relat_1 @ X30))),
% 0.21/0.58      inference('cnf', [status(esa)], [t47_relat_1])).
% 0.21/0.58  thf('5', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (r1_tarski @ k1_xboole_0 @ (k2_relat_1 @ X0))
% 0.21/0.58          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.58          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.21/0.58              = (k2_relat_1 @ k1_xboole_0))
% 0.21/0.58          | ~ (v1_relat_1 @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.58  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.58  thf('6', plain, (![X2 : $i]: (r1_tarski @ k1_xboole_0 @ X2)),
% 0.21/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.58  thf('7', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.58      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.58  thf('8', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.58          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.21/0.58          | ~ (v1_relat_1 @ X0))),
% 0.21/0.58      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.21/0.58  thf('9', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.58          | ~ (v1_relat_1 @ X0)
% 0.21/0.58          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['2', '8'])).
% 0.21/0.58  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.58  thf('10', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.58  thf('11', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ X0)
% 0.21/0.58          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.21/0.58      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.58  thf(fc3_zfmisc_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( v1_xboole_0 @ B ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.21/0.58  thf('12', plain,
% 0.21/0.58      (![X17 : $i, X18 : $i]:
% 0.21/0.58         ((v1_xboole_0 @ (k2_zfmisc_1 @ X17 @ X18)) | ~ (v1_xboole_0 @ X18))),
% 0.21/0.58      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 0.21/0.58  thf(l13_xboole_0, axiom,
% 0.21/0.58    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.58  thf('13', plain,
% 0.21/0.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.58  thf('14', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (~ (v1_xboole_0 @ X0) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.58  thf(t22_relat_1, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( v1_relat_1 @ A ) =>
% 0.21/0.58       ( ( k3_xboole_0 @
% 0.21/0.58           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.21/0.58         ( A ) ) ))).
% 0.21/0.58  thf('15', plain,
% 0.21/0.58      (![X26 : $i]:
% 0.21/0.58         (((k3_xboole_0 @ X26 @ 
% 0.21/0.58            (k2_zfmisc_1 @ (k1_relat_1 @ X26) @ (k2_relat_1 @ X26))) = (
% 0.21/0.58            X26))
% 0.21/0.58          | ~ (v1_relat_1 @ X26))),
% 0.21/0.58      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.21/0.58  thf('16', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (((k3_xboole_0 @ X0 @ k1_xboole_0) = (X0))
% 0.21/0.58          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.21/0.58          | ~ (v1_relat_1 @ X0))),
% 0.21/0.58      inference('sup+', [status(thm)], ['14', '15'])).
% 0.21/0.58  thf(t2_boole, axiom,
% 0.21/0.58    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.58  thf('17', plain,
% 0.21/0.58      (![X1 : $i]: ((k3_xboole_0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.58      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.58  thf('18', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (((k1_xboole_0) = (X0))
% 0.21/0.58          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.21/0.58          | ~ (v1_relat_1 @ X0))),
% 0.21/0.58      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.58  thf('19', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.58          | ~ (v1_relat_1 @ X0)
% 0.21/0.58          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.21/0.58          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['11', '18'])).
% 0.21/0.58  thf('20', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.58  thf('21', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ X0)
% 0.21/0.58          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.21/0.58          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.21/0.58      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.58  thf('22', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.58          | ~ (v1_relat_1 @ X0)
% 0.21/0.58          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.21/0.58          | ~ (v1_relat_1 @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['1', '21'])).
% 0.21/0.58  thf('23', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.21/0.58          | ~ (v1_relat_1 @ X0)
% 0.21/0.58          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.58      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.58  thf('24', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.58          | ~ (v1_relat_1 @ X0)
% 0.21/0.58          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['0', '23'])).
% 0.21/0.58  thf('25', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.58  thf('26', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ X0)
% 0.21/0.58          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.21/0.58      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.58  thf('27', plain,
% 0.21/0.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.58  thf(t62_relat_1, conjecture,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( v1_relat_1 @ A ) =>
% 0.21/0.58       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.21/0.58         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.58    (~( ![A:$i]:
% 0.21/0.58        ( ( v1_relat_1 @ A ) =>
% 0.21/0.58          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.21/0.58            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.21/0.58    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.21/0.58  thf('28', plain,
% 0.21/0.58      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.21/0.58        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('29', plain,
% 0.21/0.58      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.58         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.58      inference('split', [status(esa)], ['28'])).
% 0.21/0.58  thf('30', plain,
% 0.21/0.58      ((![X0 : $i]:
% 0.21/0.58          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.21/0.58         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['27', '29'])).
% 0.21/0.58  thf('31', plain, (![X23 : $i]: ((v1_relat_1 @ X23) | ~ (v1_xboole_0 @ X23))),
% 0.21/0.58      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.21/0.58  thf('32', plain,
% 0.21/0.58      (![X24 : $i, X25 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ X24)
% 0.21/0.58          | ~ (v1_relat_1 @ X25)
% 0.21/0.58          | (v1_relat_1 @ (k5_relat_1 @ X24 @ X25)))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.21/0.58  thf('33', plain, (![X23 : $i]: ((v1_relat_1 @ X23) | ~ (v1_xboole_0 @ X23))),
% 0.21/0.58      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.21/0.58  thf('34', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.58      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.58  thf(t46_relat_1, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( v1_relat_1 @ A ) =>
% 0.21/0.58       ( ![B:$i]:
% 0.21/0.58         ( ( v1_relat_1 @ B ) =>
% 0.21/0.58           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.58             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.21/0.58  thf('35', plain,
% 0.21/0.58      (![X27 : $i, X28 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ X27)
% 0.21/0.58          | ((k1_relat_1 @ (k5_relat_1 @ X28 @ X27)) = (k1_relat_1 @ X28))
% 0.21/0.58          | ~ (r1_tarski @ (k2_relat_1 @ X28) @ (k1_relat_1 @ X27))
% 0.21/0.58          | ~ (v1_relat_1 @ X28))),
% 0.21/0.58      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.21/0.58  thf('36', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.21/0.58          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.58          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.21/0.58              = (k1_relat_1 @ k1_xboole_0))
% 0.21/0.58          | ~ (v1_relat_1 @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.58  thf('37', plain, (![X2 : $i]: (r1_tarski @ k1_xboole_0 @ X2)),
% 0.21/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.58  thf('38', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.58      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.58  thf('39', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.58          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.21/0.58          | ~ (v1_relat_1 @ X0))),
% 0.21/0.58      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.21/0.58  thf('40', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.58          | ~ (v1_relat_1 @ X0)
% 0.21/0.58          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['33', '39'])).
% 0.21/0.58  thf('41', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.58  thf('42', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ X0)
% 0.21/0.58          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.21/0.58      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.58  thf(fc4_zfmisc_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.21/0.58  thf('43', plain,
% 0.21/0.58      (![X19 : $i, X20 : $i]:
% 0.21/0.58         (~ (v1_xboole_0 @ X19) | (v1_xboole_0 @ (k2_zfmisc_1 @ X19 @ X20)))),
% 0.21/0.58      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 0.21/0.58  thf('44', plain,
% 0.21/0.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.58  thf('45', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (~ (v1_xboole_0 @ X1) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.58  thf('46', plain,
% 0.21/0.58      (![X26 : $i]:
% 0.21/0.58         (((k3_xboole_0 @ X26 @ 
% 0.21/0.58            (k2_zfmisc_1 @ (k1_relat_1 @ X26) @ (k2_relat_1 @ X26))) = (
% 0.21/0.58            X26))
% 0.21/0.58          | ~ (v1_relat_1 @ X26))),
% 0.21/0.58      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.21/0.58  thf('47', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (((k3_xboole_0 @ X0 @ k1_xboole_0) = (X0))
% 0.21/0.58          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.21/0.58          | ~ (v1_relat_1 @ X0))),
% 0.21/0.58      inference('sup+', [status(thm)], ['45', '46'])).
% 0.21/0.58  thf('48', plain,
% 0.21/0.58      (![X1 : $i]: ((k3_xboole_0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.58      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.58  thf('49', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (((k1_xboole_0) = (X0))
% 0.21/0.58          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.21/0.58          | ~ (v1_relat_1 @ X0))),
% 0.21/0.58      inference('demod', [status(thm)], ['47', '48'])).
% 0.21/0.58  thf('50', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.58          | ~ (v1_relat_1 @ X0)
% 0.21/0.58          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.21/0.58          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['42', '49'])).
% 0.21/0.58  thf('51', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.58  thf('52', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ X0)
% 0.21/0.58          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.21/0.58          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.21/0.58      inference('demod', [status(thm)], ['50', '51'])).
% 0.21/0.58  thf('53', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ X0)
% 0.21/0.58          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.58          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.21/0.58          | ~ (v1_relat_1 @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['32', '52'])).
% 0.21/0.58  thf('54', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.21/0.58          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.58          | ~ (v1_relat_1 @ X0))),
% 0.21/0.58      inference('simplify', [status(thm)], ['53'])).
% 0.21/0.58  thf('55', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.58          | ~ (v1_relat_1 @ X0)
% 0.21/0.58          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['31', '54'])).
% 0.21/0.58  thf('56', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.58  thf('57', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ X0)
% 0.21/0.58          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.21/0.58      inference('demod', [status(thm)], ['55', '56'])).
% 0.21/0.58  thf('58', plain,
% 0.21/0.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.58  thf('59', plain,
% 0.21/0.58      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.21/0.58         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.58      inference('split', [status(esa)], ['28'])).
% 0.21/0.58  thf('60', plain,
% 0.21/0.58      ((![X0 : $i]:
% 0.21/0.58          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.21/0.58         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['58', '59'])).
% 0.21/0.58  thf('61', plain,
% 0.21/0.58      (((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.58         | ~ (v1_relat_1 @ sk_A)
% 0.21/0.58         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.21/0.58         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['57', '60'])).
% 0.21/0.58  thf('62', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('63', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.58  thf('64', plain,
% 0.21/0.58      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.58         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.58      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.21/0.58  thf('65', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['64'])).
% 0.21/0.58  thf('66', plain,
% 0.21/0.58      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.21/0.58       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.58      inference('split', [status(esa)], ['28'])).
% 0.21/0.58  thf('67', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.58      inference('sat_resolution*', [status(thm)], ['65', '66'])).
% 0.21/0.58  thf('68', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.58      inference('simpl_trail', [status(thm)], ['30', '67'])).
% 0.21/0.58  thf('69', plain,
% 0.21/0.58      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.58        | ~ (v1_relat_1 @ sk_A)
% 0.21/0.58        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['26', '68'])).
% 0.21/0.58  thf('70', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('71', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.58  thf('72', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.58      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.21/0.58  thf('73', plain, ($false), inference('simplify', [status(thm)], ['72'])).
% 0.21/0.58  
% 0.21/0.58  % SZS output end Refutation
% 0.21/0.58  
% 0.21/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
