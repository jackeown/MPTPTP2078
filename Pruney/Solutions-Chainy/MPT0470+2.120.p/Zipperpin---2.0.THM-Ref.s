%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uiugo7tyti

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:44 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 143 expanded)
%              Number of leaves         :   30 (  56 expanded)
%              Depth                    :   17
%              Number of atoms          :  613 ( 918 expanded)
%              Number of equality atoms :   67 ( 101 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v1_relat_1 @ X32 )
      | ~ ( v1_relat_1 @ X33 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X32 @ X33 ) ) ) ),
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
    ! [X37: $i,X38: $i] :
      ( ~ ( v1_relat_1 @ X37 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X37 @ X38 ) )
        = ( k2_relat_1 @ X38 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X38 ) @ ( k2_relat_1 @ X37 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
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
    ! [X2: $i] :
      ( r1_tarski @ k1_xboole_0 @ X2 ) ),
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
    ! [X29: $i] :
      ( ( v1_relat_1 @ X29 )
      | ( r2_hidden @ ( sk_B @ X29 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('6',plain,(
    ! [X3: $i] :
      ( r1_xboole_0 @ X3 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('7',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X23 ) @ X24 )
      | ~ ( r2_hidden @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4','9','10'])).

thf(fc3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ B )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X19 @ X20 ) )
      | ~ ( v1_xboole_0 @ X20 ) ) ),
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
    ! [X34: $i] :
      ( ( ( k3_xboole_0 @ X34 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X34 ) @ ( k2_relat_1 @ X34 ) ) )
        = X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
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

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

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
    inference('sup-',[status(thm)],['0','21'])).

thf('23',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','8'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
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

thf('27',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['27'])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v1_relat_1 @ X32 )
      | ~ ( v1_relat_1 @ X33 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('31',plain,
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

thf('32',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v1_relat_1 @ X35 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X36 @ X35 ) )
        = ( k1_relat_1 @ X36 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X36 ) @ ( k1_relat_1 @ X35 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X2: $i] :
      ( r1_tarski @ k1_xboole_0 @ X2 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('35',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','8'])).

thf('36',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34','35','36'])).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('38',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_xboole_0 @ X21 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X34: $i] :
      ( ( ( k3_xboole_0 @ X34 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X34 ) @ ( k2_relat_1 @ X34 ) ) )
        = X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
        = X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','44'])).

thf('46',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','47'])).

thf('49',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','8'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('53',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['27'])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('58',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['27'])).

thf('61',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['29','61'])).

thf('63',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('66',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    $false ),
    inference(simplify,[status(thm)],['66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uiugo7tyti
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:02:29 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.40/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.58  % Solved by: fo/fo7.sh
% 0.40/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.58  % done 198 iterations in 0.113s
% 0.40/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.58  % SZS output start Refutation
% 0.40/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.40/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.58  thf(sk_B_type, type, sk_B: $i > $i).
% 0.40/0.58  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.40/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.40/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.58  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.40/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.58  thf(dt_k5_relat_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.40/0.58       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.40/0.58  thf('0', plain,
% 0.40/0.58      (![X32 : $i, X33 : $i]:
% 0.40/0.58         (~ (v1_relat_1 @ X32)
% 0.40/0.58          | ~ (v1_relat_1 @ X33)
% 0.40/0.58          | (v1_relat_1 @ (k5_relat_1 @ X32 @ X33)))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.40/0.58  thf(t60_relat_1, axiom,
% 0.40/0.58    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.40/0.58     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.40/0.58  thf('1', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.58      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.40/0.58  thf(t47_relat_1, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( v1_relat_1 @ A ) =>
% 0.40/0.58       ( ![B:$i]:
% 0.40/0.58         ( ( v1_relat_1 @ B ) =>
% 0.40/0.58           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.40/0.58             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.40/0.58  thf('2', plain,
% 0.40/0.58      (![X37 : $i, X38 : $i]:
% 0.40/0.58         (~ (v1_relat_1 @ X37)
% 0.40/0.58          | ((k2_relat_1 @ (k5_relat_1 @ X37 @ X38)) = (k2_relat_1 @ X38))
% 0.40/0.58          | ~ (r1_tarski @ (k1_relat_1 @ X38) @ (k2_relat_1 @ X37))
% 0.40/0.58          | ~ (v1_relat_1 @ X38))),
% 0.40/0.58      inference('cnf', [status(esa)], [t47_relat_1])).
% 0.40/0.58  thf('3', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (r1_tarski @ k1_xboole_0 @ (k2_relat_1 @ X0))
% 0.40/0.58          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.40/0.58          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.40/0.58              = (k2_relat_1 @ k1_xboole_0))
% 0.40/0.58          | ~ (v1_relat_1 @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.58  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.40/0.58  thf('4', plain, (![X2 : $i]: (r1_tarski @ k1_xboole_0 @ X2)),
% 0.40/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.40/0.58  thf(d1_relat_1, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( v1_relat_1 @ A ) <=>
% 0.40/0.58       ( ![B:$i]:
% 0.40/0.58         ( ~( ( r2_hidden @ B @ A ) & 
% 0.40/0.58              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.40/0.58  thf('5', plain,
% 0.40/0.58      (![X29 : $i]: ((v1_relat_1 @ X29) | (r2_hidden @ (sk_B @ X29) @ X29))),
% 0.40/0.58      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.40/0.58  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.40/0.58  thf('6', plain, (![X3 : $i]: (r1_xboole_0 @ X3 @ k1_xboole_0)),
% 0.40/0.58      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.40/0.58  thf(l24_zfmisc_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.40/0.58  thf('7', plain,
% 0.40/0.58      (![X23 : $i, X24 : $i]:
% 0.40/0.58         (~ (r1_xboole_0 @ (k1_tarski @ X23) @ X24) | ~ (r2_hidden @ X23 @ X24))),
% 0.40/0.58      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.40/0.58  thf('8', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.40/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.40/0.58  thf('9', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.40/0.58      inference('sup-', [status(thm)], ['5', '8'])).
% 0.40/0.58  thf('10', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.58      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.40/0.58  thf('11', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.40/0.58          | ~ (v1_relat_1 @ X0))),
% 0.40/0.58      inference('demod', [status(thm)], ['3', '4', '9', '10'])).
% 0.40/0.58  thf(fc3_zfmisc_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( v1_xboole_0 @ B ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.40/0.58  thf('12', plain,
% 0.40/0.58      (![X19 : $i, X20 : $i]:
% 0.40/0.58         ((v1_xboole_0 @ (k2_zfmisc_1 @ X19 @ X20)) | ~ (v1_xboole_0 @ X20))),
% 0.40/0.58      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 0.40/0.58  thf(l13_xboole_0, axiom,
% 0.40/0.58    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.40/0.58  thf('13', plain,
% 0.40/0.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.40/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.40/0.58  thf('14', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (~ (v1_xboole_0 @ X0) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.40/0.58  thf(t22_relat_1, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( v1_relat_1 @ A ) =>
% 0.40/0.58       ( ( k3_xboole_0 @
% 0.40/0.58           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.40/0.58         ( A ) ) ))).
% 0.40/0.58  thf('15', plain,
% 0.40/0.58      (![X34 : $i]:
% 0.40/0.58         (((k3_xboole_0 @ X34 @ 
% 0.40/0.58            (k2_zfmisc_1 @ (k1_relat_1 @ X34) @ (k2_relat_1 @ X34))) = (
% 0.40/0.58            X34))
% 0.40/0.58          | ~ (v1_relat_1 @ X34))),
% 0.40/0.58      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.40/0.58  thf('16', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (((k3_xboole_0 @ X0 @ k1_xboole_0) = (X0))
% 0.40/0.58          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.40/0.58          | ~ (v1_relat_1 @ X0))),
% 0.40/0.58      inference('sup+', [status(thm)], ['14', '15'])).
% 0.40/0.58  thf(t2_boole, axiom,
% 0.40/0.58    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.40/0.58  thf('17', plain,
% 0.40/0.58      (![X1 : $i]: ((k3_xboole_0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.58      inference('cnf', [status(esa)], [t2_boole])).
% 0.40/0.58  thf('18', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (((k1_xboole_0) = (X0))
% 0.40/0.58          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.40/0.58          | ~ (v1_relat_1 @ X0))),
% 0.40/0.58      inference('demod', [status(thm)], ['16', '17'])).
% 0.40/0.58  thf('19', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.40/0.58          | ~ (v1_relat_1 @ X0)
% 0.40/0.58          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.40/0.58          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['11', '18'])).
% 0.40/0.58  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.40/0.58  thf('20', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.40/0.58  thf('21', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (v1_relat_1 @ X0)
% 0.40/0.58          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.40/0.58          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.40/0.58      inference('demod', [status(thm)], ['19', '20'])).
% 0.40/0.58  thf('22', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (v1_relat_1 @ k1_xboole_0)
% 0.40/0.58          | ~ (v1_relat_1 @ X0)
% 0.40/0.58          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.40/0.58          | ~ (v1_relat_1 @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['0', '21'])).
% 0.40/0.58  thf('23', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.40/0.58      inference('sup-', [status(thm)], ['5', '8'])).
% 0.40/0.58  thf('24', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (v1_relat_1 @ X0)
% 0.40/0.58          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.40/0.58          | ~ (v1_relat_1 @ X0))),
% 0.40/0.58      inference('demod', [status(thm)], ['22', '23'])).
% 0.40/0.58  thf('25', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.40/0.58          | ~ (v1_relat_1 @ X0))),
% 0.40/0.58      inference('simplify', [status(thm)], ['24'])).
% 0.40/0.58  thf('26', plain,
% 0.40/0.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.40/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.40/0.58  thf(t62_relat_1, conjecture,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( v1_relat_1 @ A ) =>
% 0.40/0.58       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.40/0.58         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.40/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.58    (~( ![A:$i]:
% 0.40/0.58        ( ( v1_relat_1 @ A ) =>
% 0.40/0.58          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.40/0.58            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.40/0.58    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.40/0.58  thf('27', plain,
% 0.40/0.58      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.40/0.58        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('28', plain,
% 0.40/0.58      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.40/0.58         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.40/0.58      inference('split', [status(esa)], ['27'])).
% 0.40/0.58  thf('29', plain,
% 0.40/0.58      ((![X0 : $i]:
% 0.40/0.58          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.40/0.58         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['26', '28'])).
% 0.40/0.58  thf('30', plain,
% 0.40/0.58      (![X32 : $i, X33 : $i]:
% 0.40/0.58         (~ (v1_relat_1 @ X32)
% 0.40/0.58          | ~ (v1_relat_1 @ X33)
% 0.40/0.58          | (v1_relat_1 @ (k5_relat_1 @ X32 @ X33)))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.40/0.58  thf('31', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.58      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.40/0.58  thf(t46_relat_1, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( v1_relat_1 @ A ) =>
% 0.40/0.58       ( ![B:$i]:
% 0.40/0.58         ( ( v1_relat_1 @ B ) =>
% 0.40/0.58           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.40/0.58             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.40/0.58  thf('32', plain,
% 0.40/0.58      (![X35 : $i, X36 : $i]:
% 0.40/0.58         (~ (v1_relat_1 @ X35)
% 0.40/0.58          | ((k1_relat_1 @ (k5_relat_1 @ X36 @ X35)) = (k1_relat_1 @ X36))
% 0.40/0.58          | ~ (r1_tarski @ (k2_relat_1 @ X36) @ (k1_relat_1 @ X35))
% 0.40/0.58          | ~ (v1_relat_1 @ X36))),
% 0.40/0.58      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.40/0.58  thf('33', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.40/0.58          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.40/0.58          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.40/0.58              = (k1_relat_1 @ k1_xboole_0))
% 0.40/0.58          | ~ (v1_relat_1 @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['31', '32'])).
% 0.40/0.58  thf('34', plain, (![X2 : $i]: (r1_tarski @ k1_xboole_0 @ X2)),
% 0.40/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.40/0.58  thf('35', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.40/0.58      inference('sup-', [status(thm)], ['5', '8'])).
% 0.40/0.58  thf('36', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.58      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.40/0.58  thf('37', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.40/0.58          | ~ (v1_relat_1 @ X0))),
% 0.40/0.58      inference('demod', [status(thm)], ['33', '34', '35', '36'])).
% 0.40/0.58  thf(fc4_zfmisc_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.40/0.58  thf('38', plain,
% 0.40/0.58      (![X21 : $i, X22 : $i]:
% 0.40/0.58         (~ (v1_xboole_0 @ X21) | (v1_xboole_0 @ (k2_zfmisc_1 @ X21 @ X22)))),
% 0.40/0.58      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 0.40/0.58  thf('39', plain,
% 0.40/0.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.40/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.40/0.58  thf('40', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (~ (v1_xboole_0 @ X1) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['38', '39'])).
% 0.40/0.58  thf('41', plain,
% 0.40/0.58      (![X34 : $i]:
% 0.40/0.58         (((k3_xboole_0 @ X34 @ 
% 0.40/0.58            (k2_zfmisc_1 @ (k1_relat_1 @ X34) @ (k2_relat_1 @ X34))) = (
% 0.40/0.58            X34))
% 0.40/0.58          | ~ (v1_relat_1 @ X34))),
% 0.40/0.58      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.40/0.58  thf('42', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (((k3_xboole_0 @ X0 @ k1_xboole_0) = (X0))
% 0.40/0.58          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.40/0.58          | ~ (v1_relat_1 @ X0))),
% 0.40/0.58      inference('sup+', [status(thm)], ['40', '41'])).
% 0.40/0.58  thf('43', plain,
% 0.40/0.58      (![X1 : $i]: ((k3_xboole_0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.58      inference('cnf', [status(esa)], [t2_boole])).
% 0.40/0.58  thf('44', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (((k1_xboole_0) = (X0))
% 0.40/0.58          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.40/0.58          | ~ (v1_relat_1 @ X0))),
% 0.40/0.58      inference('demod', [status(thm)], ['42', '43'])).
% 0.40/0.58  thf('45', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.40/0.58          | ~ (v1_relat_1 @ X0)
% 0.40/0.58          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.40/0.58          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['37', '44'])).
% 0.40/0.58  thf('46', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.40/0.58  thf('47', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (v1_relat_1 @ X0)
% 0.40/0.58          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.40/0.58          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.40/0.58      inference('demod', [status(thm)], ['45', '46'])).
% 0.40/0.58  thf('48', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (v1_relat_1 @ X0)
% 0.40/0.58          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.40/0.58          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.40/0.58          | ~ (v1_relat_1 @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['30', '47'])).
% 0.40/0.58  thf('49', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.40/0.58      inference('sup-', [status(thm)], ['5', '8'])).
% 0.40/0.58  thf('50', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (v1_relat_1 @ X0)
% 0.40/0.58          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.40/0.58          | ~ (v1_relat_1 @ X0))),
% 0.40/0.58      inference('demod', [status(thm)], ['48', '49'])).
% 0.40/0.58  thf('51', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.40/0.58          | ~ (v1_relat_1 @ X0))),
% 0.40/0.58      inference('simplify', [status(thm)], ['50'])).
% 0.40/0.58  thf('52', plain,
% 0.40/0.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.40/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.40/0.58  thf('53', plain,
% 0.40/0.58      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.40/0.58         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.40/0.58      inference('split', [status(esa)], ['27'])).
% 0.40/0.58  thf('54', plain,
% 0.40/0.58      ((![X0 : $i]:
% 0.40/0.58          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.40/0.58         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['52', '53'])).
% 0.40/0.58  thf('55', plain,
% 0.40/0.58      (((((k1_xboole_0) != (k1_xboole_0))
% 0.40/0.58         | ~ (v1_relat_1 @ sk_A)
% 0.40/0.58         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.40/0.58         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['51', '54'])).
% 0.40/0.58  thf('56', plain, ((v1_relat_1 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('57', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.40/0.58  thf('58', plain,
% 0.40/0.58      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.40/0.58         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.40/0.58      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.40/0.58  thf('59', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.40/0.58      inference('simplify', [status(thm)], ['58'])).
% 0.40/0.58  thf('60', plain,
% 0.40/0.58      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.40/0.58       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.40/0.58      inference('split', [status(esa)], ['27'])).
% 0.40/0.58  thf('61', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.40/0.58      inference('sat_resolution*', [status(thm)], ['59', '60'])).
% 0.40/0.58  thf('62', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.40/0.58      inference('simpl_trail', [status(thm)], ['29', '61'])).
% 0.40/0.58  thf('63', plain,
% 0.40/0.58      ((((k1_xboole_0) != (k1_xboole_0))
% 0.40/0.58        | ~ (v1_relat_1 @ sk_A)
% 0.40/0.58        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['25', '62'])).
% 0.40/0.58  thf('64', plain, ((v1_relat_1 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('65', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.40/0.58  thf('66', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.40/0.58      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.40/0.58  thf('67', plain, ($false), inference('simplify', [status(thm)], ['66'])).
% 0.40/0.58  
% 0.40/0.58  % SZS output end Refutation
% 0.40/0.58  
% 0.40/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
