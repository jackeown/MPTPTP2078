%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GKdjQvUlbO

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:41 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 145 expanded)
%              Number of leaves         :   31 (  56 expanded)
%              Depth                    :   17
%              Number of atoms          :  628 ( 931 expanded)
%              Number of equality atoms :   66 (  98 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v1_relat_1 @ X35 )
      | ~ ( v1_relat_1 @ X36 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X35 @ X36 ) ) ) ),
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
    ! [X38: $i,X39: $i] :
      ( ~ ( v1_relat_1 @ X38 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X39 @ X38 ) ) @ ( k2_relat_1 @ X38 ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('4',plain,(
    ! [X32: $i] :
      ( ( v1_relat_1 @ X32 )
      | ( r2_hidden @ ( sk_B @ X32 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('5',plain,(
    ! [X6: $i] :
      ( r1_xboole_0 @ X6 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t55_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf('6',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X25 @ X26 ) @ X27 )
      | ~ ( r2_hidden @ X25 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('7',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','8'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('10',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(fc3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ B )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X21 @ X22 ) )
      | ~ ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('17',plain,(
    ! [X37: $i] :
      ( ( ( k3_xboole_0 @ X37 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X37 ) @ ( k2_relat_1 @ X37 ) ) )
        = X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
        = X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('19',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['13','20'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('22',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','23'])).

thf('25',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','7'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

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
    ! [X35: $i,X36: $i] :
      ( ~ ( v1_relat_1 @ X35 )
      | ~ ( v1_relat_1 @ X36 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X35 @ X36 ) ) ) ),
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
    ! [X40: $i,X41: $i] :
      ( ~ ( v1_relat_1 @ X40 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X41 @ X40 ) )
        = ( k1_relat_1 @ X41 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X41 ) @ ( k1_relat_1 @ X40 ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
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
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('37',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','7'])).

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

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('40',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_xboole_0 @ X23 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X37: $i] :
      ( ( ( k3_xboole_0 @ X37 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X37 ) @ ( k2_relat_1 @ X37 ) ) )
        = X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
        = X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','46'])).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','49'])).

thf('51',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','7'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('55',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['29'])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('60',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['60'])).

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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GKdjQvUlbO
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:05:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.52/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.71  % Solved by: fo/fo7.sh
% 0.52/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.71  % done 281 iterations in 0.256s
% 0.52/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.71  % SZS output start Refutation
% 0.52/0.71  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.52/0.71  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.52/0.71  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.52/0.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.52/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.71  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.52/0.71  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.52/0.71  thf(sk_B_type, type, sk_B: $i > $i).
% 0.52/0.71  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.52/0.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.52/0.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.52/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.71  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.52/0.71  thf(dt_k5_relat_1, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.52/0.71       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.52/0.71  thf('0', plain,
% 0.52/0.71      (![X35 : $i, X36 : $i]:
% 0.52/0.71         (~ (v1_relat_1 @ X35)
% 0.52/0.71          | ~ (v1_relat_1 @ X36)
% 0.52/0.71          | (v1_relat_1 @ (k5_relat_1 @ X35 @ X36)))),
% 0.52/0.71      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.52/0.71  thf(t60_relat_1, axiom,
% 0.52/0.71    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.52/0.71     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.52/0.71  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.71      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.52/0.71  thf(t45_relat_1, axiom,
% 0.52/0.71    (![A:$i]:
% 0.52/0.71     ( ( v1_relat_1 @ A ) =>
% 0.52/0.71       ( ![B:$i]:
% 0.52/0.71         ( ( v1_relat_1 @ B ) =>
% 0.52/0.71           ( r1_tarski @
% 0.52/0.71             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.52/0.71  thf('2', plain,
% 0.52/0.71      (![X38 : $i, X39 : $i]:
% 0.52/0.71         (~ (v1_relat_1 @ X38)
% 0.52/0.71          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X39 @ X38)) @ 
% 0.52/0.71             (k2_relat_1 @ X38))
% 0.52/0.71          | ~ (v1_relat_1 @ X39))),
% 0.52/0.71      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.52/0.71  thf('3', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.52/0.71           k1_xboole_0)
% 0.52/0.71          | ~ (v1_relat_1 @ X0)
% 0.52/0.71          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.52/0.71      inference('sup+', [status(thm)], ['1', '2'])).
% 0.52/0.71  thf(d1_relat_1, axiom,
% 0.52/0.71    (![A:$i]:
% 0.52/0.71     ( ( v1_relat_1 @ A ) <=>
% 0.52/0.71       ( ![B:$i]:
% 0.52/0.71         ( ~( ( r2_hidden @ B @ A ) & 
% 0.52/0.71              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.52/0.71  thf('4', plain,
% 0.52/0.71      (![X32 : $i]: ((v1_relat_1 @ X32) | (r2_hidden @ (sk_B @ X32) @ X32))),
% 0.52/0.71      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.52/0.71  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.52/0.71  thf('5', plain, (![X6 : $i]: (r1_xboole_0 @ X6 @ k1_xboole_0)),
% 0.52/0.71      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.52/0.71  thf(t55_zfmisc_1, axiom,
% 0.52/0.71    (![A:$i,B:$i,C:$i]:
% 0.52/0.71     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 0.52/0.71  thf('6', plain,
% 0.52/0.71      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.52/0.71         (~ (r1_xboole_0 @ (k2_tarski @ X25 @ X26) @ X27)
% 0.52/0.71          | ~ (r2_hidden @ X25 @ X27))),
% 0.52/0.71      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.52/0.71  thf('7', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.52/0.71      inference('sup-', [status(thm)], ['5', '6'])).
% 0.52/0.71  thf('8', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.52/0.71      inference('sup-', [status(thm)], ['4', '7'])).
% 0.52/0.71  thf('9', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.52/0.71           k1_xboole_0)
% 0.52/0.71          | ~ (v1_relat_1 @ X0))),
% 0.52/0.71      inference('demod', [status(thm)], ['3', '8'])).
% 0.52/0.71  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.52/0.71  thf('10', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.52/0.71      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.52/0.71  thf(d10_xboole_0, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.52/0.71  thf('11', plain,
% 0.52/0.71      (![X1 : $i, X3 : $i]:
% 0.52/0.71         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.52/0.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.52/0.71  thf('12', plain,
% 0.52/0.71      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['10', '11'])).
% 0.52/0.71  thf('13', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (~ (v1_relat_1 @ X0)
% 0.52/0.71          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['9', '12'])).
% 0.52/0.71  thf(fc3_zfmisc_1, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( v1_xboole_0 @ B ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.52/0.71  thf('14', plain,
% 0.52/0.71      (![X21 : $i, X22 : $i]:
% 0.52/0.71         ((v1_xboole_0 @ (k2_zfmisc_1 @ X21 @ X22)) | ~ (v1_xboole_0 @ X22))),
% 0.52/0.71      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 0.52/0.71  thf(l13_xboole_0, axiom,
% 0.52/0.71    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.52/0.71  thf('15', plain,
% 0.52/0.71      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.71      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.52/0.71  thf('16', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         (~ (v1_xboole_0 @ X0) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['14', '15'])).
% 0.52/0.71  thf(t22_relat_1, axiom,
% 0.52/0.71    (![A:$i]:
% 0.52/0.71     ( ( v1_relat_1 @ A ) =>
% 0.52/0.71       ( ( k3_xboole_0 @
% 0.52/0.71           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.52/0.71         ( A ) ) ))).
% 0.52/0.71  thf('17', plain,
% 0.52/0.71      (![X37 : $i]:
% 0.52/0.71         (((k3_xboole_0 @ X37 @ 
% 0.52/0.71            (k2_zfmisc_1 @ (k1_relat_1 @ X37) @ (k2_relat_1 @ X37))) = (
% 0.52/0.71            X37))
% 0.52/0.71          | ~ (v1_relat_1 @ X37))),
% 0.52/0.71      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.52/0.71  thf('18', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (((k3_xboole_0 @ X0 @ k1_xboole_0) = (X0))
% 0.52/0.71          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.52/0.71          | ~ (v1_relat_1 @ X0))),
% 0.52/0.71      inference('sup+', [status(thm)], ['16', '17'])).
% 0.52/0.71  thf(t2_boole, axiom,
% 0.52/0.71    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.52/0.71  thf('19', plain,
% 0.52/0.71      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.71      inference('cnf', [status(esa)], [t2_boole])).
% 0.52/0.71  thf('20', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (((k1_xboole_0) = (X0))
% 0.52/0.71          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.52/0.71          | ~ (v1_relat_1 @ X0))),
% 0.52/0.71      inference('demod', [status(thm)], ['18', '19'])).
% 0.52/0.71  thf('21', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.52/0.71          | ~ (v1_relat_1 @ X0)
% 0.52/0.71          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.52/0.71          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['13', '20'])).
% 0.52/0.71  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.52/0.71  thf('22', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.52/0.71  thf('23', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (~ (v1_relat_1 @ X0)
% 0.52/0.71          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.52/0.71          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.52/0.71      inference('demod', [status(thm)], ['21', '22'])).
% 0.52/0.71  thf('24', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (~ (v1_relat_1 @ k1_xboole_0)
% 0.52/0.71          | ~ (v1_relat_1 @ X0)
% 0.52/0.71          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.52/0.71          | ~ (v1_relat_1 @ X0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['0', '23'])).
% 0.52/0.71  thf('25', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.52/0.71      inference('sup-', [status(thm)], ['4', '7'])).
% 0.52/0.71  thf('26', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (~ (v1_relat_1 @ X0)
% 0.52/0.71          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.52/0.71          | ~ (v1_relat_1 @ X0))),
% 0.52/0.71      inference('demod', [status(thm)], ['24', '25'])).
% 0.52/0.71  thf('27', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.52/0.71          | ~ (v1_relat_1 @ X0))),
% 0.52/0.71      inference('simplify', [status(thm)], ['26'])).
% 0.52/0.71  thf('28', plain,
% 0.52/0.71      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.71      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.52/0.71  thf(t62_relat_1, conjecture,
% 0.52/0.71    (![A:$i]:
% 0.52/0.71     ( ( v1_relat_1 @ A ) =>
% 0.52/0.71       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.52/0.71         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.52/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.71    (~( ![A:$i]:
% 0.52/0.71        ( ( v1_relat_1 @ A ) =>
% 0.52/0.71          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.52/0.71            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.52/0.71    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.52/0.71  thf('29', plain,
% 0.52/0.71      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.52/0.71        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('30', plain,
% 0.52/0.71      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.52/0.71         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.52/0.71      inference('split', [status(esa)], ['29'])).
% 0.52/0.71  thf('31', plain,
% 0.52/0.71      ((![X0 : $i]:
% 0.52/0.71          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.52/0.71         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['28', '30'])).
% 0.52/0.71  thf('32', plain,
% 0.52/0.71      (![X35 : $i, X36 : $i]:
% 0.52/0.71         (~ (v1_relat_1 @ X35)
% 0.52/0.71          | ~ (v1_relat_1 @ X36)
% 0.52/0.71          | (v1_relat_1 @ (k5_relat_1 @ X35 @ X36)))),
% 0.52/0.71      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.52/0.71  thf('33', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.71      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.52/0.71  thf(t46_relat_1, axiom,
% 0.52/0.71    (![A:$i]:
% 0.52/0.71     ( ( v1_relat_1 @ A ) =>
% 0.52/0.71       ( ![B:$i]:
% 0.52/0.71         ( ( v1_relat_1 @ B ) =>
% 0.52/0.71           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.52/0.71             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.52/0.71  thf('34', plain,
% 0.52/0.71      (![X40 : $i, X41 : $i]:
% 0.52/0.71         (~ (v1_relat_1 @ X40)
% 0.52/0.71          | ((k1_relat_1 @ (k5_relat_1 @ X41 @ X40)) = (k1_relat_1 @ X41))
% 0.52/0.71          | ~ (r1_tarski @ (k2_relat_1 @ X41) @ (k1_relat_1 @ X40))
% 0.52/0.71          | ~ (v1_relat_1 @ X41))),
% 0.52/0.71      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.52/0.71  thf('35', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.52/0.71          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.52/0.71          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.52/0.71              = (k1_relat_1 @ k1_xboole_0))
% 0.52/0.71          | ~ (v1_relat_1 @ X0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['33', '34'])).
% 0.52/0.71  thf('36', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.52/0.71      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.52/0.71  thf('37', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.52/0.71      inference('sup-', [status(thm)], ['4', '7'])).
% 0.52/0.71  thf('38', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.71      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.52/0.71  thf('39', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.52/0.71          | ~ (v1_relat_1 @ X0))),
% 0.52/0.71      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 0.52/0.71  thf(fc4_zfmisc_1, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.52/0.71  thf('40', plain,
% 0.52/0.71      (![X23 : $i, X24 : $i]:
% 0.52/0.71         (~ (v1_xboole_0 @ X23) | (v1_xboole_0 @ (k2_zfmisc_1 @ X23 @ X24)))),
% 0.52/0.71      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 0.52/0.71  thf('41', plain,
% 0.52/0.71      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.71      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.52/0.71  thf('42', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         (~ (v1_xboole_0 @ X1) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['40', '41'])).
% 0.52/0.71  thf('43', plain,
% 0.52/0.71      (![X37 : $i]:
% 0.52/0.71         (((k3_xboole_0 @ X37 @ 
% 0.52/0.71            (k2_zfmisc_1 @ (k1_relat_1 @ X37) @ (k2_relat_1 @ X37))) = (
% 0.52/0.71            X37))
% 0.52/0.71          | ~ (v1_relat_1 @ X37))),
% 0.52/0.71      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.52/0.71  thf('44', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (((k3_xboole_0 @ X0 @ k1_xboole_0) = (X0))
% 0.52/0.71          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.52/0.71          | ~ (v1_relat_1 @ X0))),
% 0.52/0.71      inference('sup+', [status(thm)], ['42', '43'])).
% 0.52/0.71  thf('45', plain,
% 0.52/0.71      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.71      inference('cnf', [status(esa)], [t2_boole])).
% 0.52/0.71  thf('46', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (((k1_xboole_0) = (X0))
% 0.52/0.71          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.52/0.71          | ~ (v1_relat_1 @ X0))),
% 0.52/0.71      inference('demod', [status(thm)], ['44', '45'])).
% 0.52/0.71  thf('47', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.52/0.71          | ~ (v1_relat_1 @ X0)
% 0.52/0.71          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.52/0.71          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['39', '46'])).
% 0.52/0.71  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.52/0.71  thf('49', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (~ (v1_relat_1 @ X0)
% 0.52/0.71          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.52/0.71          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.52/0.71      inference('demod', [status(thm)], ['47', '48'])).
% 0.52/0.71  thf('50', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (~ (v1_relat_1 @ X0)
% 0.52/0.71          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.52/0.71          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.52/0.71          | ~ (v1_relat_1 @ X0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['32', '49'])).
% 0.52/0.71  thf('51', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.52/0.71      inference('sup-', [status(thm)], ['4', '7'])).
% 0.52/0.71  thf('52', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (~ (v1_relat_1 @ X0)
% 0.52/0.71          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.52/0.71          | ~ (v1_relat_1 @ X0))),
% 0.52/0.71      inference('demod', [status(thm)], ['50', '51'])).
% 0.52/0.71  thf('53', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.52/0.71          | ~ (v1_relat_1 @ X0))),
% 0.52/0.71      inference('simplify', [status(thm)], ['52'])).
% 0.52/0.71  thf('54', plain,
% 0.52/0.71      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.71      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.52/0.71  thf('55', plain,
% 0.52/0.71      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.52/0.71         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.71      inference('split', [status(esa)], ['29'])).
% 0.52/0.71  thf('56', plain,
% 0.52/0.71      ((![X0 : $i]:
% 0.52/0.71          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.52/0.71         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['54', '55'])).
% 0.52/0.71  thf('57', plain,
% 0.52/0.71      (((((k1_xboole_0) != (k1_xboole_0))
% 0.52/0.71         | ~ (v1_relat_1 @ sk_A)
% 0.52/0.71         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.52/0.71         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['53', '56'])).
% 0.52/0.71  thf('58', plain, ((v1_relat_1 @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('59', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.52/0.71  thf('60', plain,
% 0.52/0.71      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.52/0.71         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.71      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.52/0.71  thf('61', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.52/0.71      inference('simplify', [status(thm)], ['60'])).
% 0.52/0.71  thf('62', plain,
% 0.52/0.71      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.52/0.71       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.52/0.71      inference('split', [status(esa)], ['29'])).
% 0.52/0.71  thf('63', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.52/0.71      inference('sat_resolution*', [status(thm)], ['61', '62'])).
% 0.52/0.71  thf('64', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.71      inference('simpl_trail', [status(thm)], ['31', '63'])).
% 0.52/0.71  thf('65', plain,
% 0.52/0.71      ((((k1_xboole_0) != (k1_xboole_0))
% 0.52/0.71        | ~ (v1_relat_1 @ sk_A)
% 0.52/0.71        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['27', '64'])).
% 0.52/0.71  thf('66', plain, ((v1_relat_1 @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('67', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.52/0.71  thf('68', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.52/0.71      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.52/0.71  thf('69', plain, ($false), inference('simplify', [status(thm)], ['68'])).
% 0.52/0.71  
% 0.52/0.71  % SZS output end Refutation
% 0.52/0.71  
% 0.52/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
