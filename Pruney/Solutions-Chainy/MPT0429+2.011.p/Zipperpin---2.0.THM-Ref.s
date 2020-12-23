%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Xteencm1DQ

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:31 EST 2020

% Result     : Theorem 2.17s
% Output     : Refutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 254 expanded)
%              Number of leaves         :   37 (  93 expanded)
%              Depth                    :   16
%              Number of atoms          :  690 (1711 expanded)
%              Number of equality atoms :   47 ( 125 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X49: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('1',plain,(
    ! [X49: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('2',plain,(
    ! [X49: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t57_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ A )
         => ! [D: $i] :
              ( ( m1_subset_1 @ D @ A )
             => ( ( A != k1_xboole_0 )
               => ( m1_subset_1 @ ( k1_enumset1 @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X50 @ X51 )
      | ( X51 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k1_enumset1 @ X52 @ X50 @ X53 ) @ ( k1_zfmisc_1 @ X51 ) )
      | ~ ( m1_subset_1 @ X53 @ X51 )
      | ~ ( m1_subset_1 @ X52 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t57_subset_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ ( k1_enumset1 @ X1 @ k1_xboole_0 @ X2 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( ( k1_zfmisc_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_zfmisc_1 @ X0 )
        = k1_xboole_0 )
      | ( m1_subset_1 @ ( k1_enumset1 @ k1_xboole_0 @ k1_xboole_0 @ X1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_enumset1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( ( k1_zfmisc_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf(t91_enumset1,axiom,(
    ! [A: $i] :
      ( ( k4_enumset1 @ A @ A @ A @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('7',plain,(
    ! [X25: $i] :
      ( ( k4_enumset1 @ X25 @ X25 @ X25 @ X25 @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t91_enumset1])).

thf(t82_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_enumset1 @ A @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X24: $i] :
      ( ( k2_enumset1 @ X24 @ X24 @ X24 @ X24 )
      = ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[t82_enumset1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k4_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t93_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k6_enumset1 @ A @ A @ A @ A @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('10',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k6_enumset1 @ X26 @ X26 @ X26 @ X26 @ X26 @ X26 @ X27 @ X28 )
      = ( k1_enumset1 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t93_enumset1])).

thf(t81_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k6_enumset1 @ A @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('11',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k6_enumset1 @ X18 @ X18 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 )
      = ( k4_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t81_enumset1])).

thf('12',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k4_enumset1 @ X26 @ X26 @ X26 @ X26 @ X27 @ X28 )
      = ( k1_enumset1 @ X26 @ X27 @ X28 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X24: $i] :
      ( ( k2_enumset1 @ X24 @ X24 @ X24 @ X24 )
      = ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[t82_enumset1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( ( k1_zfmisc_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['6','15'])).

thf(t61_setfam_1,conjecture,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_setfam_1])).

thf('17',plain,(
    ~ ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k1_zfmisc_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('19',plain,(
    ! [X3: $i] :
      ( ( r1_xboole_0 @ X3 @ X3 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('20',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['19'])).

thf(t127_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ B )
        | ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('21',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X37 @ X38 ) @ ( k2_zfmisc_1 @ X39 @ X40 ) )
      | ~ ( r1_xboole_0 @ X38 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(fc13_subset_1,axiom,(
    ! [A: $i] :
      ( v1_xboole_0 @ ( k1_subset_1 @ A ) ) )).

thf('25',plain,(
    ! [X46: $i] :
      ( v1_xboole_0 @ ( k1_subset_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[fc13_subset_1])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('26',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('27',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_xboole_0 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ( X7 = X8 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( o_0_0_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( o_0_0_xboole_0
      = ( k1_subset_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( o_0_0_xboole_0
      = ( k1_subset_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf(t38_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf('31',plain,(
    ! [X47: $i,X48: $i] :
      ( ( X48
       != ( k1_subset_1 @ X47 ) )
      | ( r1_tarski @ X48 @ ( k3_subset_1 @ X47 @ X48 ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t38_subset_1])).

thf('32',plain,(
    ! [X47: $i] :
      ( ~ ( m1_subset_1 @ ( k1_subset_1 @ X47 ) @ ( k1_zfmisc_1 @ X47 ) )
      | ( r1_tarski @ ( k1_subset_1 @ X47 ) @ ( k3_subset_1 @ X47 @ ( k1_subset_1 @ X47 ) ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf(dt_k1_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('33',plain,(
    ! [X45: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ X45 ) @ ( k1_zfmisc_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_subset_1])).

thf('34',plain,(
    ! [X47: $i] :
      ( r1_tarski @ ( k1_subset_1 @ X47 ) @ ( k3_subset_1 @ X47 @ ( k1_subset_1 @ X47 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ o_0_0_xboole_0 @ ( k3_subset_1 @ X0 @ ( k1_subset_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ o_0_0_xboole_0 @ ( k3_subset_1 @ X0 @ o_0_0_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','35'])).

thf(t118_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )).

thf('37',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ X34 @ X35 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X34 @ X36 ) @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ o_0_0_xboole_0 @ X1 ) @ ( k2_zfmisc_1 @ ( k3_subset_1 @ X0 @ o_0_0_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k2_zfmisc_1 @ ( k3_subset_1 @ X0 @ o_0_0_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['24','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('41',plain,(
    r1_tarski @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['39','40'])).

thf(t82_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) )).

thf('42',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ ( k4_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t82_xboole_1])).

thf('43',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ k1_xboole_0 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('48',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ X29 @ X30 )
      | ( r2_hidden @ X29 @ X31 )
      | ( X31
       != ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('49',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r2_hidden @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( r1_tarski @ X29 @ X30 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    ! [X46: $i] :
      ( v1_xboole_0 @ ( k1_subset_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[fc13_subset_1])).

thf('52',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_xboole_0 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ( X7 = X8 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_subset_1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('55',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( r1_tarski @ X48 @ ( k3_subset_1 @ X47 @ X48 ) )
      | ( X48
        = ( k1_subset_1 @ X47 ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t38_subset_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( k1_xboole_0
        = ( k1_subset_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X49: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k1_subset_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X1: $i] :
      ( ( k1_xboole_0 = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['53','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('61',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( X41 != X43 )
      | ~ ( r2_hidden @ X41 @ ( k4_xboole_0 @ X42 @ ( k1_tarski @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('62',plain,(
    ! [X42: $i,X43: $i] :
      ~ ( r2_hidden @ X43 @ ( k4_xboole_0 @ X42 @ ( k1_tarski @ X43 ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','64'])).

thf('66',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','65'])).

thf('67',plain,(
    ! [X46: $i] :
      ( v1_xboole_0 @ ( k1_subset_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[fc13_subset_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k1_subset_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('69',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['66','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Xteencm1DQ
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:41:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.17/2.37  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.17/2.37  % Solved by: fo/fo7.sh
% 2.17/2.37  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.17/2.37  % done 4275 iterations in 1.905s
% 2.17/2.37  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.17/2.37  % SZS output start Refutation
% 2.17/2.37  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 2.17/2.37  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.17/2.37  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 2.17/2.37  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.17/2.37  thf(sk_A_type, type, sk_A: $i).
% 2.17/2.37  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.17/2.37  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.17/2.37  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 2.17/2.37  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.17/2.37  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 2.17/2.37  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 2.17/2.37  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 2.17/2.37                                           $i > $i).
% 2.17/2.37  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.17/2.37  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.17/2.37  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.17/2.37  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.17/2.37  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.17/2.37  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 2.17/2.37  thf(t4_subset_1, axiom,
% 2.17/2.37    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 2.17/2.37  thf('0', plain,
% 2.17/2.37      (![X49 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X49))),
% 2.17/2.37      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.17/2.37  thf('1', plain,
% 2.17/2.37      (![X49 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X49))),
% 2.17/2.37      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.17/2.37  thf('2', plain,
% 2.17/2.37      (![X49 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X49))),
% 2.17/2.37      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.17/2.37  thf(t57_subset_1, axiom,
% 2.17/2.37    (![A:$i,B:$i]:
% 2.17/2.37     ( ( m1_subset_1 @ B @ A ) =>
% 2.17/2.37       ( ![C:$i]:
% 2.17/2.37         ( ( m1_subset_1 @ C @ A ) =>
% 2.17/2.37           ( ![D:$i]:
% 2.17/2.37             ( ( m1_subset_1 @ D @ A ) =>
% 2.17/2.37               ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 2.17/2.37                 ( m1_subset_1 @
% 2.17/2.37                   ( k1_enumset1 @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) ) ) ) ) ))).
% 2.17/2.37  thf('3', plain,
% 2.17/2.37      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 2.17/2.37         (~ (m1_subset_1 @ X50 @ X51)
% 2.17/2.37          | ((X51) = (k1_xboole_0))
% 2.17/2.37          | (m1_subset_1 @ (k1_enumset1 @ X52 @ X50 @ X53) @ 
% 2.17/2.37             (k1_zfmisc_1 @ X51))
% 2.17/2.37          | ~ (m1_subset_1 @ X53 @ X51)
% 2.17/2.37          | ~ (m1_subset_1 @ X52 @ X51))),
% 2.17/2.37      inference('cnf', [status(esa)], [t57_subset_1])).
% 2.17/2.37  thf('4', plain,
% 2.17/2.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.17/2.37         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 2.17/2.37          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0))
% 2.17/2.37          | (m1_subset_1 @ (k1_enumset1 @ X1 @ k1_xboole_0 @ X2) @ 
% 2.17/2.37             (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))
% 2.17/2.37          | ((k1_zfmisc_1 @ X0) = (k1_xboole_0)))),
% 2.17/2.37      inference('sup-', [status(thm)], ['2', '3'])).
% 2.17/2.37  thf('5', plain,
% 2.17/2.37      (![X0 : $i, X1 : $i]:
% 2.17/2.37         (((k1_zfmisc_1 @ X0) = (k1_xboole_0))
% 2.17/2.37          | (m1_subset_1 @ (k1_enumset1 @ k1_xboole_0 @ k1_xboole_0 @ X1) @ 
% 2.17/2.37             (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))
% 2.17/2.37          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 2.17/2.37      inference('sup-', [status(thm)], ['1', '4'])).
% 2.17/2.37  thf('6', plain,
% 2.17/2.37      (![X0 : $i]:
% 2.17/2.37         ((m1_subset_1 @ 
% 2.17/2.37           (k1_enumset1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ 
% 2.17/2.37           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))
% 2.17/2.37          | ((k1_zfmisc_1 @ X0) = (k1_xboole_0)))),
% 2.17/2.37      inference('sup-', [status(thm)], ['0', '5'])).
% 2.17/2.37  thf(t91_enumset1, axiom,
% 2.17/2.37    (![A:$i]: ( ( k4_enumset1 @ A @ A @ A @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 2.17/2.37  thf('7', plain,
% 2.17/2.37      (![X25 : $i]:
% 2.17/2.37         ((k4_enumset1 @ X25 @ X25 @ X25 @ X25 @ X25 @ X25) = (k1_tarski @ X25))),
% 2.17/2.37      inference('cnf', [status(esa)], [t91_enumset1])).
% 2.17/2.37  thf(t82_enumset1, axiom,
% 2.17/2.37    (![A:$i]: ( ( k2_enumset1 @ A @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 2.17/2.37  thf('8', plain,
% 2.17/2.37      (![X24 : $i]: ((k2_enumset1 @ X24 @ X24 @ X24 @ X24) = (k1_tarski @ X24))),
% 2.17/2.37      inference('cnf', [status(esa)], [t82_enumset1])).
% 2.17/2.37  thf('9', plain,
% 2.17/2.37      (![X0 : $i]:
% 2.17/2.37         ((k2_enumset1 @ X0 @ X0 @ X0 @ X0)
% 2.17/2.37           = (k4_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0))),
% 2.17/2.37      inference('sup+', [status(thm)], ['7', '8'])).
% 2.17/2.37  thf(t93_enumset1, axiom,
% 2.17/2.37    (![A:$i,B:$i,C:$i]:
% 2.17/2.37     ( ( k6_enumset1 @ A @ A @ A @ A @ A @ A @ B @ C ) =
% 2.17/2.37       ( k1_enumset1 @ A @ B @ C ) ))).
% 2.17/2.37  thf('10', plain,
% 2.17/2.37      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.17/2.37         ((k6_enumset1 @ X26 @ X26 @ X26 @ X26 @ X26 @ X26 @ X27 @ X28)
% 2.17/2.37           = (k1_enumset1 @ X26 @ X27 @ X28))),
% 2.17/2.37      inference('cnf', [status(esa)], [t93_enumset1])).
% 2.17/2.37  thf(t81_enumset1, axiom,
% 2.17/2.37    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.17/2.37     ( ( k6_enumset1 @ A @ A @ A @ B @ C @ D @ E @ F ) =
% 2.17/2.37       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 2.17/2.37  thf('11', plain,
% 2.17/2.37      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 2.17/2.37         ((k6_enumset1 @ X18 @ X18 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23)
% 2.17/2.37           = (k4_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23))),
% 2.17/2.37      inference('cnf', [status(esa)], [t81_enumset1])).
% 2.17/2.37  thf('12', plain,
% 2.17/2.37      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.17/2.37         ((k4_enumset1 @ X26 @ X26 @ X26 @ X26 @ X27 @ X28)
% 2.17/2.37           = (k1_enumset1 @ X26 @ X27 @ X28))),
% 2.17/2.37      inference('demod', [status(thm)], ['10', '11'])).
% 2.17/2.37  thf('13', plain,
% 2.17/2.37      (![X0 : $i]:
% 2.17/2.37         ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_enumset1 @ X0 @ X0 @ X0))),
% 2.17/2.37      inference('demod', [status(thm)], ['9', '12'])).
% 2.17/2.37  thf('14', plain,
% 2.17/2.37      (![X24 : $i]: ((k2_enumset1 @ X24 @ X24 @ X24 @ X24) = (k1_tarski @ X24))),
% 2.17/2.37      inference('cnf', [status(esa)], [t82_enumset1])).
% 2.17/2.37  thf('15', plain,
% 2.17/2.37      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 2.17/2.37      inference('sup+', [status(thm)], ['13', '14'])).
% 2.17/2.37  thf('16', plain,
% 2.17/2.37      (![X0 : $i]:
% 2.17/2.37         ((m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 2.17/2.37           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))
% 2.17/2.37          | ((k1_zfmisc_1 @ X0) = (k1_xboole_0)))),
% 2.17/2.37      inference('demod', [status(thm)], ['6', '15'])).
% 2.17/2.37  thf(t61_setfam_1, conjecture,
% 2.17/2.37    (![A:$i]:
% 2.17/2.37     ( m1_subset_1 @
% 2.17/2.37       ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.17/2.37  thf(zf_stmt_0, negated_conjecture,
% 2.17/2.37    (~( ![A:$i]:
% 2.17/2.37        ( m1_subset_1 @
% 2.17/2.37          ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )),
% 2.17/2.37    inference('cnf.neg', [status(esa)], [t61_setfam_1])).
% 2.17/2.37  thf('17', plain,
% 2.17/2.37      (~ (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 2.17/2.37          (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf('18', plain, (((k1_zfmisc_1 @ sk_A) = (k1_xboole_0))),
% 2.17/2.37      inference('sup-', [status(thm)], ['16', '17'])).
% 2.17/2.37  thf(t66_xboole_1, axiom,
% 2.17/2.37    (![A:$i]:
% 2.17/2.37     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 2.17/2.37       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 2.17/2.37  thf('19', plain,
% 2.17/2.37      (![X3 : $i]: ((r1_xboole_0 @ X3 @ X3) | ((X3) != (k1_xboole_0)))),
% 2.17/2.37      inference('cnf', [status(esa)], [t66_xboole_1])).
% 2.17/2.37  thf('20', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 2.17/2.37      inference('simplify', [status(thm)], ['19'])).
% 2.17/2.37  thf(t127_zfmisc_1, axiom,
% 2.17/2.37    (![A:$i,B:$i,C:$i,D:$i]:
% 2.17/2.37     ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 2.17/2.37       ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 2.17/2.37  thf('21', plain,
% 2.17/2.37      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 2.17/2.37         ((r1_xboole_0 @ (k2_zfmisc_1 @ X37 @ X38) @ (k2_zfmisc_1 @ X39 @ X40))
% 2.17/2.37          | ~ (r1_xboole_0 @ X38 @ X40))),
% 2.17/2.37      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 2.17/2.37  thf('22', plain,
% 2.17/2.37      (![X0 : $i, X1 : $i]:
% 2.17/2.37         (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ k1_xboole_0) @ 
% 2.17/2.37          (k2_zfmisc_1 @ X0 @ k1_xboole_0))),
% 2.17/2.37      inference('sup-', [status(thm)], ['20', '21'])).
% 2.17/2.37  thf('23', plain,
% 2.17/2.37      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X4))),
% 2.17/2.37      inference('cnf', [status(esa)], [t66_xboole_1])).
% 2.17/2.37  thf('24', plain,
% 2.17/2.37      (![X0 : $i]: ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 2.17/2.37      inference('sup-', [status(thm)], ['22', '23'])).
% 2.17/2.37  thf(fc13_subset_1, axiom, (![A:$i]: ( v1_xboole_0 @ ( k1_subset_1 @ A ) ))).
% 2.17/2.37  thf('25', plain, (![X46 : $i]: (v1_xboole_0 @ (k1_subset_1 @ X46))),
% 2.17/2.37      inference('cnf', [status(esa)], [fc13_subset_1])).
% 2.17/2.37  thf(dt_o_0_0_xboole_0, axiom, (v1_xboole_0 @ o_0_0_xboole_0)).
% 2.17/2.37  thf('26', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 2.17/2.37      inference('cnf', [status(esa)], [dt_o_0_0_xboole_0])).
% 2.17/2.37  thf(t8_boole, axiom,
% 2.17/2.37    (![A:$i,B:$i]:
% 2.17/2.37     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 2.17/2.37  thf('27', plain,
% 2.17/2.37      (![X7 : $i, X8 : $i]:
% 2.17/2.37         (~ (v1_xboole_0 @ X7) | ~ (v1_xboole_0 @ X8) | ((X7) = (X8)))),
% 2.17/2.37      inference('cnf', [status(esa)], [t8_boole])).
% 2.17/2.37  thf('28', plain,
% 2.17/2.37      (![X0 : $i]: (((o_0_0_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 2.17/2.37      inference('sup-', [status(thm)], ['26', '27'])).
% 2.17/2.37  thf('29', plain, (![X0 : $i]: ((o_0_0_xboole_0) = (k1_subset_1 @ X0))),
% 2.17/2.37      inference('sup-', [status(thm)], ['25', '28'])).
% 2.17/2.37  thf('30', plain, (![X0 : $i]: ((o_0_0_xboole_0) = (k1_subset_1 @ X0))),
% 2.17/2.37      inference('sup-', [status(thm)], ['25', '28'])).
% 2.17/2.37  thf(t38_subset_1, axiom,
% 2.17/2.37    (![A:$i,B:$i]:
% 2.17/2.37     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.17/2.37       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 2.17/2.37         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 2.17/2.37  thf('31', plain,
% 2.17/2.37      (![X47 : $i, X48 : $i]:
% 2.17/2.37         (((X48) != (k1_subset_1 @ X47))
% 2.17/2.37          | (r1_tarski @ X48 @ (k3_subset_1 @ X47 @ X48))
% 2.17/2.37          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X47)))),
% 2.17/2.37      inference('cnf', [status(esa)], [t38_subset_1])).
% 2.17/2.37  thf('32', plain,
% 2.17/2.37      (![X47 : $i]:
% 2.17/2.37         (~ (m1_subset_1 @ (k1_subset_1 @ X47) @ (k1_zfmisc_1 @ X47))
% 2.17/2.37          | (r1_tarski @ (k1_subset_1 @ X47) @ 
% 2.17/2.37             (k3_subset_1 @ X47 @ (k1_subset_1 @ X47))))),
% 2.17/2.37      inference('simplify', [status(thm)], ['31'])).
% 2.17/2.37  thf(dt_k1_subset_1, axiom,
% 2.17/2.37    (![A:$i]: ( m1_subset_1 @ ( k1_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 2.17/2.37  thf('33', plain,
% 2.17/2.37      (![X45 : $i]: (m1_subset_1 @ (k1_subset_1 @ X45) @ (k1_zfmisc_1 @ X45))),
% 2.17/2.37      inference('cnf', [status(esa)], [dt_k1_subset_1])).
% 2.17/2.37  thf('34', plain,
% 2.17/2.37      (![X47 : $i]:
% 2.17/2.37         (r1_tarski @ (k1_subset_1 @ X47) @ 
% 2.17/2.37          (k3_subset_1 @ X47 @ (k1_subset_1 @ X47)))),
% 2.17/2.37      inference('demod', [status(thm)], ['32', '33'])).
% 2.17/2.37  thf('35', plain,
% 2.17/2.37      (![X0 : $i]:
% 2.17/2.37         (r1_tarski @ o_0_0_xboole_0 @ (k3_subset_1 @ X0 @ (k1_subset_1 @ X0)))),
% 2.17/2.37      inference('sup+', [status(thm)], ['30', '34'])).
% 2.17/2.37  thf('36', plain,
% 2.17/2.37      (![X0 : $i]:
% 2.17/2.37         (r1_tarski @ o_0_0_xboole_0 @ (k3_subset_1 @ X0 @ o_0_0_xboole_0))),
% 2.17/2.37      inference('sup+', [status(thm)], ['29', '35'])).
% 2.17/2.37  thf(t118_zfmisc_1, axiom,
% 2.17/2.37    (![A:$i,B:$i,C:$i]:
% 2.17/2.37     ( ( r1_tarski @ A @ B ) =>
% 2.17/2.37       ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 2.17/2.37         ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 2.17/2.37  thf('37', plain,
% 2.17/2.37      (![X34 : $i, X35 : $i, X36 : $i]:
% 2.17/2.37         (~ (r1_tarski @ X34 @ X35)
% 2.17/2.37          | (r1_tarski @ (k2_zfmisc_1 @ X34 @ X36) @ (k2_zfmisc_1 @ X35 @ X36)))),
% 2.17/2.37      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 2.17/2.37  thf('38', plain,
% 2.17/2.37      (![X0 : $i, X1 : $i]:
% 2.17/2.37         (r1_tarski @ (k2_zfmisc_1 @ o_0_0_xboole_0 @ X1) @ 
% 2.17/2.37          (k2_zfmisc_1 @ (k3_subset_1 @ X0 @ o_0_0_xboole_0) @ X1))),
% 2.17/2.37      inference('sup-', [status(thm)], ['36', '37'])).
% 2.17/2.37  thf('39', plain,
% 2.17/2.37      (![X0 : $i]:
% 2.17/2.37         (r1_tarski @ k1_xboole_0 @ 
% 2.17/2.37          (k2_zfmisc_1 @ (k3_subset_1 @ X0 @ o_0_0_xboole_0) @ k1_xboole_0))),
% 2.17/2.37      inference('sup+', [status(thm)], ['24', '38'])).
% 2.17/2.37  thf('40', plain,
% 2.17/2.37      (![X0 : $i]: ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 2.17/2.37      inference('sup-', [status(thm)], ['22', '23'])).
% 2.17/2.37  thf('41', plain, ((r1_tarski @ k1_xboole_0 @ k1_xboole_0)),
% 2.17/2.37      inference('demod', [status(thm)], ['39', '40'])).
% 2.17/2.37  thf(t82_xboole_1, axiom,
% 2.17/2.37    (![A:$i,B:$i]:
% 2.17/2.37     ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ))).
% 2.17/2.37  thf('42', plain,
% 2.17/2.37      (![X5 : $i, X6 : $i]:
% 2.17/2.37         (r1_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ (k4_xboole_0 @ X6 @ X5))),
% 2.17/2.37      inference('cnf', [status(esa)], [t82_xboole_1])).
% 2.17/2.37  thf('43', plain,
% 2.17/2.37      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X4))),
% 2.17/2.37      inference('cnf', [status(esa)], [t66_xboole_1])).
% 2.17/2.37  thf('44', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.17/2.37      inference('sup-', [status(thm)], ['42', '43'])).
% 2.17/2.37  thf(t106_xboole_1, axiom,
% 2.17/2.37    (![A:$i,B:$i,C:$i]:
% 2.17/2.37     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 2.17/2.37       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 2.17/2.37  thf('45', plain,
% 2.17/2.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.17/2.37         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ X0 @ (k4_xboole_0 @ X1 @ X2)))),
% 2.17/2.37      inference('cnf', [status(esa)], [t106_xboole_1])).
% 2.17/2.37  thf('46', plain,
% 2.17/2.37      (![X0 : $i, X1 : $i]:
% 2.17/2.37         (~ (r1_tarski @ X1 @ k1_xboole_0) | (r1_tarski @ X1 @ X0))),
% 2.17/2.37      inference('sup-', [status(thm)], ['44', '45'])).
% 2.17/2.37  thf('47', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 2.17/2.37      inference('sup-', [status(thm)], ['41', '46'])).
% 2.17/2.37  thf(d1_zfmisc_1, axiom,
% 2.17/2.37    (![A:$i,B:$i]:
% 2.17/2.37     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 2.17/2.37       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 2.17/2.37  thf('48', plain,
% 2.17/2.37      (![X29 : $i, X30 : $i, X31 : $i]:
% 2.17/2.37         (~ (r1_tarski @ X29 @ X30)
% 2.17/2.37          | (r2_hidden @ X29 @ X31)
% 2.17/2.37          | ((X31) != (k1_zfmisc_1 @ X30)))),
% 2.17/2.37      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 2.17/2.37  thf('49', plain,
% 2.17/2.37      (![X29 : $i, X30 : $i]:
% 2.17/2.37         ((r2_hidden @ X29 @ (k1_zfmisc_1 @ X30)) | ~ (r1_tarski @ X29 @ X30))),
% 2.17/2.37      inference('simplify', [status(thm)], ['48'])).
% 2.17/2.37  thf('50', plain,
% 2.17/2.37      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 2.17/2.37      inference('sup-', [status(thm)], ['47', '49'])).
% 2.17/2.37  thf('51', plain, (![X46 : $i]: (v1_xboole_0 @ (k1_subset_1 @ X46))),
% 2.17/2.37      inference('cnf', [status(esa)], [fc13_subset_1])).
% 2.17/2.37  thf('52', plain,
% 2.17/2.37      (![X7 : $i, X8 : $i]:
% 2.17/2.37         (~ (v1_xboole_0 @ X7) | ~ (v1_xboole_0 @ X8) | ((X7) = (X8)))),
% 2.17/2.37      inference('cnf', [status(esa)], [t8_boole])).
% 2.17/2.37  thf('53', plain,
% 2.17/2.37      (![X0 : $i, X1 : $i]:
% 2.17/2.37         (((k1_subset_1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X1))),
% 2.17/2.37      inference('sup-', [status(thm)], ['51', '52'])).
% 2.17/2.37  thf('54', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 2.17/2.37      inference('sup-', [status(thm)], ['41', '46'])).
% 2.17/2.37  thf('55', plain,
% 2.17/2.37      (![X47 : $i, X48 : $i]:
% 2.17/2.37         (~ (r1_tarski @ X48 @ (k3_subset_1 @ X47 @ X48))
% 2.17/2.37          | ((X48) = (k1_subset_1 @ X47))
% 2.17/2.37          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X47)))),
% 2.17/2.37      inference('cnf', [status(esa)], [t38_subset_1])).
% 2.17/2.37  thf('56', plain,
% 2.17/2.37      (![X0 : $i]:
% 2.17/2.37         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 2.17/2.37          | ((k1_xboole_0) = (k1_subset_1 @ X0)))),
% 2.17/2.37      inference('sup-', [status(thm)], ['54', '55'])).
% 2.17/2.37  thf('57', plain,
% 2.17/2.37      (![X49 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X49))),
% 2.17/2.37      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.17/2.37  thf('58', plain, (![X0 : $i]: ((k1_xboole_0) = (k1_subset_1 @ X0))),
% 2.17/2.37      inference('demod', [status(thm)], ['56', '57'])).
% 2.17/2.37  thf('59', plain,
% 2.17/2.37      (![X1 : $i]: (((k1_xboole_0) = (X1)) | ~ (v1_xboole_0 @ X1))),
% 2.17/2.37      inference('demod', [status(thm)], ['53', '58'])).
% 2.17/2.37  thf('60', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.17/2.37      inference('sup-', [status(thm)], ['42', '43'])).
% 2.17/2.37  thf(t64_zfmisc_1, axiom,
% 2.17/2.37    (![A:$i,B:$i,C:$i]:
% 2.17/2.37     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 2.17/2.37       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 2.17/2.37  thf('61', plain,
% 2.17/2.37      (![X41 : $i, X42 : $i, X43 : $i]:
% 2.17/2.37         (((X41) != (X43))
% 2.17/2.37          | ~ (r2_hidden @ X41 @ (k4_xboole_0 @ X42 @ (k1_tarski @ X43))))),
% 2.17/2.37      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 2.17/2.37  thf('62', plain,
% 2.17/2.37      (![X42 : $i, X43 : $i]:
% 2.17/2.37         ~ (r2_hidden @ X43 @ (k4_xboole_0 @ X42 @ (k1_tarski @ X43)))),
% 2.17/2.37      inference('simplify', [status(thm)], ['61'])).
% 2.17/2.37  thf('63', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 2.17/2.37      inference('sup-', [status(thm)], ['60', '62'])).
% 2.17/2.37  thf('64', plain,
% 2.17/2.37      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 2.17/2.37      inference('sup-', [status(thm)], ['59', '63'])).
% 2.17/2.37  thf('65', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 2.17/2.37      inference('sup-', [status(thm)], ['50', '64'])).
% 2.17/2.37  thf('66', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 2.17/2.37      inference('sup-', [status(thm)], ['18', '65'])).
% 2.17/2.37  thf('67', plain, (![X46 : $i]: (v1_xboole_0 @ (k1_subset_1 @ X46))),
% 2.17/2.37      inference('cnf', [status(esa)], [fc13_subset_1])).
% 2.17/2.37  thf('68', plain, (![X0 : $i]: ((k1_xboole_0) = (k1_subset_1 @ X0))),
% 2.17/2.37      inference('demod', [status(thm)], ['56', '57'])).
% 2.17/2.37  thf('69', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.17/2.37      inference('demod', [status(thm)], ['67', '68'])).
% 2.17/2.37  thf('70', plain, ($false), inference('demod', [status(thm)], ['66', '69'])).
% 2.17/2.37  
% 2.17/2.37  % SZS output end Refutation
% 2.17/2.37  
% 2.17/2.38  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
