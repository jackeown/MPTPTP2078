%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nhCiP6iINr

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:17 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 520 expanded)
%              Number of leaves         :   34 ( 177 expanded)
%              Depth                    :   23
%              Number of atoms          :  785 (3563 expanded)
%              Number of equality atoms :  115 ( 483 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('0',plain,(
    ! [X20: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('1',plain,(
    ! [X20: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X8: $i] :
      ( ( k2_tarski @ X8 @ X8 )
      = ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t24_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( v1_relat_1 @ E )
     => ( ( E
          = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ C @ D ) ) )
       => ( ( ( k1_relat_1 @ E )
            = ( k2_tarski @ A @ C ) )
          & ( ( k2_relat_1 @ E )
            = ( k2_tarski @ B @ D ) ) ) ) ) )).

thf('3',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( X33
       != ( k2_tarski @ ( k4_tarski @ X29 @ X30 ) @ ( k4_tarski @ X31 @ X32 ) ) )
      | ( ( k1_relat_1 @ X33 )
        = ( k2_tarski @ X29 @ X31 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t24_relat_1])).

thf('4',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X29 @ X30 ) @ ( k4_tarski @ X31 @ X32 ) ) )
      | ( ( k1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X29 @ X30 ) @ ( k4_tarski @ X31 @ X32 ) ) )
        = ( k2_tarski @ X29 @ X31 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(fc7_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ C @ D ) ) ) )).

thf('5',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X22 @ X23 ) @ ( k4_tarski @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[fc7_relat_1])).

thf('6',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X29 @ X30 ) @ ( k4_tarski @ X31 @ X32 ) ) )
      = ( k2_tarski @ X29 @ X31 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      = ( k2_tarski @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','6'])).

thf('8',plain,(
    ! [X8: $i] :
      ( ( k2_tarski @ X8 @ X8 )
      = ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      = ( k1_tarski @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X20: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('12',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('13',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ o_0_0_xboole_0 )
      = X3 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t13_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k2_xboole_0 @ A @ B ) )
            = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('14',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ( ( k1_relat_1 @ ( k2_xboole_0 @ X27 @ X26 ) )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X27 ) @ ( k1_relat_1 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t13_relat_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('17',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
        = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k1_relat_1 @ o_0_0_xboole_0 ) @ ( k1_relat_1 @ X0 ) )
        = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_relat_1 @ o_0_0_xboole_0 ) @ ( k1_relat_1 @ X0 ) )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','21'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('23',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('24',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('25',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_relat_1 @ o_0_0_xboole_0 ) @ ( k1_relat_1 @ X0 ) )
        = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_relat_1 @ o_0_0_xboole_0 ) @ ( k1_tarski @ X0 ) )
        = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['9','26'])).

thf('28',plain,(
    ! [X8: $i] :
      ( ( k2_tarski @ X8 @ X8 )
      = ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('29',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X22 @ X23 ) @ ( k4_tarski @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[fc7_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_relat_1 @ o_0_0_xboole_0 ) @ ( k1_tarski @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['27','30'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('32',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('33',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('34',plain,(
    ! [X2: $i] :
      ( ( X2 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('35',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ( r2_hidden @ X14 @ ( k4_xboole_0 @ X15 @ ( k1_tarski @ X17 ) ) )
      | ( X14 = X17 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ( ( sk_B @ X0 )
        = X1 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ ( k1_relat_1 @ o_0_0_xboole_0 ) ) @ o_0_0_xboole_0 )
      | ( ( sk_B @ ( k1_relat_1 @ o_0_0_xboole_0 ) )
        = X0 )
      | ( ( k1_relat_1 @ o_0_0_xboole_0 )
        = o_0_0_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ o_0_0_xboole_0 )
      = X3 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('39',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X14 != X16 )
      | ~ ( r2_hidden @ X14 @ ( k4_xboole_0 @ X15 @ ( k1_tarski @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('42',plain,(
    ! [X15: $i,X16: $i] :
      ~ ( r2_hidden @ X16 @ ( k4_xboole_0 @ X15 @ ( k1_tarski @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ o_0_0_xboole_0 )
        = o_0_0_xboole_0 )
      | ( ( sk_B @ ( k1_relat_1 @ o_0_0_xboole_0 ) )
        = X0 ) ) ),
    inference(clc,[status(thm)],['37','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ o_0_0_xboole_0 )
        = o_0_0_xboole_0 )
      | ( ( sk_B @ ( k1_relat_1 @ o_0_0_xboole_0 ) )
        = X0 ) ) ),
    inference(clc,[status(thm)],['37','43'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( ( k1_relat_1 @ o_0_0_xboole_0 )
        = o_0_0_xboole_0 )
      | ( ( k1_relat_1 @ o_0_0_xboole_0 )
        = o_0_0_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ o_0_0_xboole_0 )
        = o_0_0_xboole_0 )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( k1_relat_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(condensation,[status(thm)],['47'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('49',plain,(
    ! [X34: $i] :
      ( ( ( k1_relat_1 @ X34 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X34 ) ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('50',plain,(
    ! [X28: $i] :
      ( ( ( k3_xboole_0 @ X28 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X28 ) @ ( k2_relat_1 @ X28 ) ) )
        = X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k4_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) )
        = ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('52',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k4_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) )
        = ( k4_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k3_xboole_0 @ ( k4_relat_1 @ o_0_0_xboole_0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k4_relat_1 @ o_0_0_xboole_0 ) ) @ o_0_0_xboole_0 ) )
      = ( k4_relat_1 @ o_0_0_xboole_0 ) )
    | ~ ( v1_relat_1 @ o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','53'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('55',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_zfmisc_1 @ X10 @ X11 )
        = k1_xboole_0 )
      | ( X11 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('56',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('58',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('59',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ X10 @ o_0_0_xboole_0 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('60',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('61',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('62',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('63',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ o_0_0_xboole_0 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ( o_0_0_xboole_0
      = ( k4_relat_1 @ o_0_0_xboole_0 ) )
    | ~ ( v1_relat_1 @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['54','59','63'])).

thf('65',plain,
    ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
    | ( o_0_0_xboole_0
      = ( k4_relat_1 @ o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','64'])).

thf('66',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['23','24'])).

thf('67',plain,
    ( o_0_0_xboole_0
    = ( k4_relat_1 @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X34: $i] :
      ( ( ( k2_relat_1 @ X34 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X34 ) ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('69',plain,
    ( ( ( k2_relat_1 @ o_0_0_xboole_0 )
      = ( k1_relat_1 @ o_0_0_xboole_0 ) )
    | ~ ( v1_relat_1 @ o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k1_relat_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(condensation,[status(thm)],['47'])).

thf('71',plain,
    ( ( ( k2_relat_1 @ o_0_0_xboole_0 )
      = o_0_0_xboole_0 )
    | ~ ( v1_relat_1 @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf(t60_relat_1,conjecture,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      & ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t60_relat_1])).

thf('72',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['72'])).

thf('74',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('75',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('76',plain,
    ( ( ( k2_relat_1 @ o_0_0_xboole_0 )
     != o_0_0_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,
    ( ( k1_relat_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(condensation,[status(thm)],['47'])).

thf('78',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('79',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['72'])).

thf('80',plain,
    ( ( ( k1_relat_1 @ o_0_0_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('82',plain,
    ( ( ( k1_relat_1 @ o_0_0_xboole_0 )
     != o_0_0_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','82'])).

thf('84',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['72'])).

thf('86',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['84','85'])).

thf('87',plain,(
    ( k2_relat_1 @ o_0_0_xboole_0 )
 != o_0_0_xboole_0 ),
    inference(simpl_trail,[status(thm)],['76','86'])).

thf('88',plain,(
    ~ ( v1_relat_1 @ o_0_0_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['71','87'])).

thf('89',plain,(
    ~ ( v1_xboole_0 @ o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','88'])).

thf('90',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['23','24'])).

thf('91',plain,(
    $false ),
    inference(demod,[status(thm)],['89','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nhCiP6iINr
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:03:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.56  % Solved by: fo/fo7.sh
% 0.20/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.56  % done 190 iterations in 0.108s
% 0.20/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.56  % SZS output start Refutation
% 0.20/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.56  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.20/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.56  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.20/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.56  thf(cc1_relat_1, axiom,
% 0.20/0.56    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.20/0.56  thf('0', plain, (![X20 : $i]: ((v1_relat_1 @ X20) | ~ (v1_xboole_0 @ X20))),
% 0.20/0.56      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.20/0.56  thf('1', plain, (![X20 : $i]: ((v1_relat_1 @ X20) | ~ (v1_xboole_0 @ X20))),
% 0.20/0.56      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.20/0.56  thf(t69_enumset1, axiom,
% 0.20/0.56    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.56  thf('2', plain, (![X8 : $i]: ((k2_tarski @ X8 @ X8) = (k1_tarski @ X8))),
% 0.20/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.56  thf(t24_relat_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.56     ( ( v1_relat_1 @ E ) =>
% 0.20/0.56       ( ( ( E ) =
% 0.20/0.56           ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ C @ D ) ) ) =>
% 0.20/0.56         ( ( ( k1_relat_1 @ E ) = ( k2_tarski @ A @ C ) ) & 
% 0.20/0.56           ( ( k2_relat_1 @ E ) = ( k2_tarski @ B @ D ) ) ) ) ))).
% 0.20/0.56  thf('3', plain,
% 0.20/0.56      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.20/0.56         (((X33)
% 0.20/0.56            != (k2_tarski @ (k4_tarski @ X29 @ X30) @ (k4_tarski @ X31 @ X32)))
% 0.20/0.56          | ((k1_relat_1 @ X33) = (k2_tarski @ X29 @ X31))
% 0.20/0.56          | ~ (v1_relat_1 @ X33))),
% 0.20/0.56      inference('cnf', [status(esa)], [t24_relat_1])).
% 0.20/0.56  thf('4', plain,
% 0.20/0.56      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.56         (~ (v1_relat_1 @ 
% 0.20/0.56             (k2_tarski @ (k4_tarski @ X29 @ X30) @ (k4_tarski @ X31 @ X32)))
% 0.20/0.56          | ((k1_relat_1 @ 
% 0.20/0.56              (k2_tarski @ (k4_tarski @ X29 @ X30) @ (k4_tarski @ X31 @ X32)))
% 0.20/0.56              = (k2_tarski @ X29 @ X31)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.56  thf(fc7_relat_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.56     ( v1_relat_1 @
% 0.20/0.56       ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ C @ D ) ) ))).
% 0.20/0.56  thf('5', plain,
% 0.20/0.56      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.56         (v1_relat_1 @ 
% 0.20/0.56          (k2_tarski @ (k4_tarski @ X22 @ X23) @ (k4_tarski @ X24 @ X25)))),
% 0.20/0.56      inference('cnf', [status(esa)], [fc7_relat_1])).
% 0.20/0.56  thf('6', plain,
% 0.20/0.56      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.56         ((k1_relat_1 @ 
% 0.20/0.56           (k2_tarski @ (k4_tarski @ X29 @ X30) @ (k4_tarski @ X31 @ X32)))
% 0.20/0.56           = (k2_tarski @ X29 @ X31))),
% 0.20/0.56      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.56  thf('7', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.20/0.56           = (k2_tarski @ X1 @ X1))),
% 0.20/0.56      inference('sup+', [status(thm)], ['2', '6'])).
% 0.20/0.56  thf('8', plain, (![X8 : $i]: ((k2_tarski @ X8 @ X8) = (k1_tarski @ X8))),
% 0.20/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.56  thf('9', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) = (k1_tarski @ X1))),
% 0.20/0.56      inference('sup+', [status(thm)], ['7', '8'])).
% 0.20/0.56  thf('10', plain, (![X20 : $i]: ((v1_relat_1 @ X20) | ~ (v1_xboole_0 @ X20))),
% 0.20/0.56      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.20/0.56  thf(t1_boole, axiom,
% 0.20/0.56    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.56  thf('11', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.20/0.56      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.56  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.20/0.56  thf('12', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.56  thf('13', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ o_0_0_xboole_0) = (X3))),
% 0.20/0.56      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.56  thf(t13_relat_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( v1_relat_1 @ A ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( v1_relat_1 @ B ) =>
% 0.20/0.56           ( ( k1_relat_1 @ ( k2_xboole_0 @ A @ B ) ) =
% 0.20/0.56             ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.20/0.56  thf('14', plain,
% 0.20/0.56      (![X26 : $i, X27 : $i]:
% 0.20/0.56         (~ (v1_relat_1 @ X26)
% 0.20/0.56          | ((k1_relat_1 @ (k2_xboole_0 @ X27 @ X26))
% 0.20/0.56              = (k2_xboole_0 @ (k1_relat_1 @ X27) @ (k1_relat_1 @ X26)))
% 0.20/0.56          | ~ (v1_relat_1 @ X27))),
% 0.20/0.56      inference('cnf', [status(esa)], [t13_relat_1])).
% 0.20/0.56  thf(commutativity_k2_xboole_0, axiom,
% 0.20/0.56    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.20/0.56  thf('15', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.56      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.56  thf(t46_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.20/0.56  thf('16', plain,
% 0.20/0.56      (![X5 : $i, X6 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ X5 @ (k2_xboole_0 @ X5 @ X6)) = (k1_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.20/0.56  thf('17', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.56  thf('18', plain,
% 0.20/0.56      (![X5 : $i, X6 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ X5 @ (k2_xboole_0 @ X5 @ X6)) = (o_0_0_xboole_0))),
% 0.20/0.56      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.56  thf('19', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (o_0_0_xboole_0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['15', '18'])).
% 0.20/0.56  thf('20', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (((k4_xboole_0 @ (k1_relat_1 @ X0) @ 
% 0.20/0.56            (k1_relat_1 @ (k2_xboole_0 @ X1 @ X0))) = (o_0_0_xboole_0))
% 0.20/0.56          | ~ (v1_relat_1 @ X1)
% 0.20/0.56          | ~ (v1_relat_1 @ X0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['14', '19'])).
% 0.20/0.56  thf('21', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (((k4_xboole_0 @ (k1_relat_1 @ o_0_0_xboole_0) @ (k1_relat_1 @ X0))
% 0.20/0.56            = (o_0_0_xboole_0))
% 0.20/0.56          | ~ (v1_relat_1 @ o_0_0_xboole_0)
% 0.20/0.56          | ~ (v1_relat_1 @ X0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['13', '20'])).
% 0.20/0.56  thf('22', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (v1_xboole_0 @ o_0_0_xboole_0)
% 0.20/0.56          | ~ (v1_relat_1 @ X0)
% 0.20/0.56          | ((k4_xboole_0 @ (k1_relat_1 @ o_0_0_xboole_0) @ (k1_relat_1 @ X0))
% 0.20/0.56              = (o_0_0_xboole_0)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['10', '21'])).
% 0.20/0.56  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.56  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.56  thf('24', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.56  thf('25', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.20/0.56      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.56  thf('26', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (v1_relat_1 @ X0)
% 0.20/0.56          | ((k4_xboole_0 @ (k1_relat_1 @ o_0_0_xboole_0) @ (k1_relat_1 @ X0))
% 0.20/0.56              = (o_0_0_xboole_0)))),
% 0.20/0.56      inference('demod', [status(thm)], ['22', '25'])).
% 0.20/0.56  thf('27', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (((k4_xboole_0 @ (k1_relat_1 @ o_0_0_xboole_0) @ (k1_tarski @ X0))
% 0.20/0.56            = (o_0_0_xboole_0))
% 0.20/0.56          | ~ (v1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))),
% 0.20/0.56      inference('sup+', [status(thm)], ['9', '26'])).
% 0.20/0.56  thf('28', plain, (![X8 : $i]: ((k2_tarski @ X8 @ X8) = (k1_tarski @ X8))),
% 0.20/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.56  thf('29', plain,
% 0.20/0.56      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.56         (v1_relat_1 @ 
% 0.20/0.56          (k2_tarski @ (k4_tarski @ X22 @ X23) @ (k4_tarski @ X24 @ X25)))),
% 0.20/0.56      inference('cnf', [status(esa)], [fc7_relat_1])).
% 0.20/0.56  thf('30', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.20/0.56      inference('sup+', [status(thm)], ['28', '29'])).
% 0.20/0.56  thf('31', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ (k1_relat_1 @ o_0_0_xboole_0) @ (k1_tarski @ X0))
% 0.20/0.56           = (o_0_0_xboole_0))),
% 0.20/0.56      inference('demod', [status(thm)], ['27', '30'])).
% 0.20/0.56  thf(t7_xboole_0, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.56          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.56  thf('32', plain,
% 0.20/0.56      (![X2 : $i]: (((X2) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.56      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.56  thf('33', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.56  thf('34', plain,
% 0.20/0.56      (![X2 : $i]: (((X2) = (o_0_0_xboole_0)) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.56      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.56  thf(t64_zfmisc_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.20/0.56       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.20/0.56  thf('35', plain,
% 0.20/0.56      (![X14 : $i, X15 : $i, X17 : $i]:
% 0.20/0.56         ((r2_hidden @ X14 @ (k4_xboole_0 @ X15 @ (k1_tarski @ X17)))
% 0.20/0.56          | ((X14) = (X17))
% 0.20/0.56          | ~ (r2_hidden @ X14 @ X15))),
% 0.20/0.56      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.20/0.56  thf('36', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (((X0) = (o_0_0_xboole_0))
% 0.20/0.56          | ((sk_B @ X0) = (X1))
% 0.20/0.56          | (r2_hidden @ (sk_B @ X0) @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.56  thf('37', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((r2_hidden @ (sk_B @ (k1_relat_1 @ o_0_0_xboole_0)) @ o_0_0_xboole_0)
% 0.20/0.56          | ((sk_B @ (k1_relat_1 @ o_0_0_xboole_0)) = (X0))
% 0.20/0.56          | ((k1_relat_1 @ o_0_0_xboole_0) = (o_0_0_xboole_0)))),
% 0.20/0.56      inference('sup+', [status(thm)], ['31', '36'])).
% 0.20/0.56  thf('38', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ o_0_0_xboole_0) = (X3))),
% 0.20/0.56      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.56  thf('39', plain,
% 0.20/0.56      (![X5 : $i, X6 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ X5 @ (k2_xboole_0 @ X5 @ X6)) = (o_0_0_xboole_0))),
% 0.20/0.56      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.56  thf('40', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (o_0_0_xboole_0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['38', '39'])).
% 0.20/0.56  thf('41', plain,
% 0.20/0.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.56         (((X14) != (X16))
% 0.20/0.56          | ~ (r2_hidden @ X14 @ (k4_xboole_0 @ X15 @ (k1_tarski @ X16))))),
% 0.20/0.56      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.20/0.56  thf('42', plain,
% 0.20/0.56      (![X15 : $i, X16 : $i]:
% 0.20/0.56         ~ (r2_hidden @ X16 @ (k4_xboole_0 @ X15 @ (k1_tarski @ X16)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['41'])).
% 0.20/0.56  thf('43', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ o_0_0_xboole_0)),
% 0.20/0.56      inference('sup-', [status(thm)], ['40', '42'])).
% 0.20/0.56  thf('44', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (((k1_relat_1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))
% 0.20/0.56          | ((sk_B @ (k1_relat_1 @ o_0_0_xboole_0)) = (X0)))),
% 0.20/0.56      inference('clc', [status(thm)], ['37', '43'])).
% 0.20/0.56  thf('45', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (((k1_relat_1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))
% 0.20/0.56          | ((sk_B @ (k1_relat_1 @ o_0_0_xboole_0)) = (X0)))),
% 0.20/0.56      inference('clc', [status(thm)], ['37', '43'])).
% 0.20/0.56  thf('46', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (((X0) = (X1))
% 0.20/0.56          | ((k1_relat_1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))
% 0.20/0.56          | ((k1_relat_1 @ o_0_0_xboole_0) = (o_0_0_xboole_0)))),
% 0.20/0.56      inference('sup+', [status(thm)], ['44', '45'])).
% 0.20/0.56  thf('47', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (((k1_relat_1 @ o_0_0_xboole_0) = (o_0_0_xboole_0)) | ((X0) = (X1)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['46'])).
% 0.20/0.56  thf('48', plain, (((k1_relat_1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.56      inference('condensation', [status(thm)], ['47'])).
% 0.20/0.56  thf(t37_relat_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( v1_relat_1 @ A ) =>
% 0.20/0.56       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.20/0.56         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.20/0.56  thf('49', plain,
% 0.20/0.56      (![X34 : $i]:
% 0.20/0.56         (((k1_relat_1 @ X34) = (k2_relat_1 @ (k4_relat_1 @ X34)))
% 0.20/0.56          | ~ (v1_relat_1 @ X34))),
% 0.20/0.56      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.20/0.56  thf(t22_relat_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( v1_relat_1 @ A ) =>
% 0.20/0.56       ( ( k3_xboole_0 @
% 0.20/0.56           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.20/0.56         ( A ) ) ))).
% 0.20/0.56  thf('50', plain,
% 0.20/0.56      (![X28 : $i]:
% 0.20/0.56         (((k3_xboole_0 @ X28 @ 
% 0.20/0.56            (k2_zfmisc_1 @ (k1_relat_1 @ X28) @ (k2_relat_1 @ X28))) = (
% 0.20/0.56            X28))
% 0.20/0.56          | ~ (v1_relat_1 @ X28))),
% 0.20/0.56      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.20/0.56  thf('51', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (((k3_xboole_0 @ (k4_relat_1 @ X0) @ 
% 0.20/0.56            (k2_zfmisc_1 @ (k1_relat_1 @ (k4_relat_1 @ X0)) @ (k1_relat_1 @ X0)))
% 0.20/0.56            = (k4_relat_1 @ X0))
% 0.20/0.56          | ~ (v1_relat_1 @ X0)
% 0.20/0.56          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.20/0.56      inference('sup+', [status(thm)], ['49', '50'])).
% 0.20/0.56  thf(dt_k4_relat_1, axiom,
% 0.20/0.56    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.20/0.56  thf('52', plain,
% 0.20/0.56      (![X21 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X21)) | ~ (v1_relat_1 @ X21))),
% 0.20/0.56      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.20/0.56  thf('53', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (v1_relat_1 @ X0)
% 0.20/0.56          | ((k3_xboole_0 @ (k4_relat_1 @ X0) @ 
% 0.20/0.56              (k2_zfmisc_1 @ (k1_relat_1 @ (k4_relat_1 @ X0)) @ 
% 0.20/0.56               (k1_relat_1 @ X0)))
% 0.20/0.56              = (k4_relat_1 @ X0)))),
% 0.20/0.56      inference('clc', [status(thm)], ['51', '52'])).
% 0.20/0.56  thf('54', plain,
% 0.20/0.56      ((((k3_xboole_0 @ (k4_relat_1 @ o_0_0_xboole_0) @ 
% 0.20/0.56          (k2_zfmisc_1 @ (k1_relat_1 @ (k4_relat_1 @ o_0_0_xboole_0)) @ 
% 0.20/0.56           o_0_0_xboole_0))
% 0.20/0.56          = (k4_relat_1 @ o_0_0_xboole_0))
% 0.20/0.56        | ~ (v1_relat_1 @ o_0_0_xboole_0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['48', '53'])).
% 0.20/0.56  thf(t113_zfmisc_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.56       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.56  thf('55', plain,
% 0.20/0.56      (![X10 : $i, X11 : $i]:
% 0.20/0.56         (((k2_zfmisc_1 @ X10 @ X11) = (k1_xboole_0))
% 0.20/0.56          | ((X11) != (k1_xboole_0)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.56  thf('56', plain,
% 0.20/0.56      (![X10 : $i]: ((k2_zfmisc_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.56      inference('simplify', [status(thm)], ['55'])).
% 0.20/0.56  thf('57', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.56  thf('58', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.56  thf('59', plain,
% 0.20/0.56      (![X10 : $i]: ((k2_zfmisc_1 @ X10 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.56      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.20/0.56  thf(t2_boole, axiom,
% 0.20/0.56    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.56  thf('60', plain,
% 0.20/0.56      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.56  thf('61', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.56  thf('62', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.56  thf('63', plain,
% 0.20/0.56      (![X4 : $i]: ((k3_xboole_0 @ X4 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.56      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.20/0.56  thf('64', plain,
% 0.20/0.56      ((((o_0_0_xboole_0) = (k4_relat_1 @ o_0_0_xboole_0))
% 0.20/0.56        | ~ (v1_relat_1 @ o_0_0_xboole_0))),
% 0.20/0.56      inference('demod', [status(thm)], ['54', '59', '63'])).
% 0.20/0.56  thf('65', plain,
% 0.20/0.56      ((~ (v1_xboole_0 @ o_0_0_xboole_0)
% 0.20/0.56        | ((o_0_0_xboole_0) = (k4_relat_1 @ o_0_0_xboole_0)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['1', '64'])).
% 0.20/0.56  thf('66', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.20/0.56      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.56  thf('67', plain, (((o_0_0_xboole_0) = (k4_relat_1 @ o_0_0_xboole_0))),
% 0.20/0.56      inference('demod', [status(thm)], ['65', '66'])).
% 0.20/0.56  thf('68', plain,
% 0.20/0.56      (![X34 : $i]:
% 0.20/0.56         (((k2_relat_1 @ X34) = (k1_relat_1 @ (k4_relat_1 @ X34)))
% 0.20/0.56          | ~ (v1_relat_1 @ X34))),
% 0.20/0.56      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.20/0.56  thf('69', plain,
% 0.20/0.56      ((((k2_relat_1 @ o_0_0_xboole_0) = (k1_relat_1 @ o_0_0_xboole_0))
% 0.20/0.56        | ~ (v1_relat_1 @ o_0_0_xboole_0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['67', '68'])).
% 0.20/0.56  thf('70', plain, (((k1_relat_1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.56      inference('condensation', [status(thm)], ['47'])).
% 0.20/0.56  thf('71', plain,
% 0.20/0.56      ((((k2_relat_1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))
% 0.20/0.56        | ~ (v1_relat_1 @ o_0_0_xboole_0))),
% 0.20/0.56      inference('demod', [status(thm)], ['69', '70'])).
% 0.20/0.56  thf(t60_relat_1, conjecture,
% 0.20/0.56    (( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.56     ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.56    (~( ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.56        ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.20/0.56    inference('cnf.neg', [status(esa)], [t60_relat_1])).
% 0.20/0.56  thf('72', plain,
% 0.20/0.56      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.20/0.56        | ((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('73', plain,
% 0.20/0.56      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.56         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.56      inference('split', [status(esa)], ['72'])).
% 0.20/0.56  thf('74', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.56  thf('75', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.56  thf('76', plain,
% 0.20/0.56      ((((k2_relat_1 @ o_0_0_xboole_0) != (o_0_0_xboole_0)))
% 0.20/0.56         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.56      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.20/0.56  thf('77', plain, (((k1_relat_1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.56      inference('condensation', [status(thm)], ['47'])).
% 0.20/0.56  thf('78', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.56  thf('79', plain,
% 0.20/0.56      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.56         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.56      inference('split', [status(esa)], ['72'])).
% 0.20/0.56  thf('80', plain,
% 0.20/0.56      ((((k1_relat_1 @ o_0_0_xboole_0) != (k1_xboole_0)))
% 0.20/0.56         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['78', '79'])).
% 0.20/0.56  thf('81', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.56  thf('82', plain,
% 0.20/0.56      ((((k1_relat_1 @ o_0_0_xboole_0) != (o_0_0_xboole_0)))
% 0.20/0.56         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.56      inference('demod', [status(thm)], ['80', '81'])).
% 0.20/0.56  thf('83', plain,
% 0.20/0.56      ((((o_0_0_xboole_0) != (o_0_0_xboole_0)))
% 0.20/0.56         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['77', '82'])).
% 0.20/0.56  thf('84', plain, ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['83'])).
% 0.20/0.56  thf('85', plain,
% 0.20/0.56      (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.20/0.56       ~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.56      inference('split', [status(esa)], ['72'])).
% 0.20/0.56  thf('86', plain, (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.56      inference('sat_resolution*', [status(thm)], ['84', '85'])).
% 0.20/0.56  thf('87', plain, (((k2_relat_1 @ o_0_0_xboole_0) != (o_0_0_xboole_0))),
% 0.20/0.56      inference('simpl_trail', [status(thm)], ['76', '86'])).
% 0.20/0.56  thf('88', plain, (~ (v1_relat_1 @ o_0_0_xboole_0)),
% 0.20/0.56      inference('simplify_reflect-', [status(thm)], ['71', '87'])).
% 0.20/0.56  thf('89', plain, (~ (v1_xboole_0 @ o_0_0_xboole_0)),
% 0.20/0.56      inference('sup-', [status(thm)], ['0', '88'])).
% 0.20/0.56  thf('90', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.20/0.56      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.56  thf('91', plain, ($false), inference('demod', [status(thm)], ['89', '90'])).
% 0.20/0.56  
% 0.20/0.56  % SZS output end Refutation
% 0.20/0.56  
% 0.20/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
