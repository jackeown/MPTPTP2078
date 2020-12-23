%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4dvhmz01G3

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:44 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 139 expanded)
%              Number of leaves         :   34 (  51 expanded)
%              Depth                    :   15
%              Number of atoms          :  779 (1148 expanded)
%              Number of equality atoms :   62 (  97 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t205_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
        <=> ( ( k11_relat_1 @ B @ A )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t205_relat_1])).

thf('0',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('3',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k11_relat_1 @ X40 @ X41 )
        = ( k9_relat_1 @ X40 @ ( k1_tarski @ X41 ) ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X43: $i,X44: $i] :
      ( ( ( k9_relat_1 @ X43 @ X44 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X43 ) @ X44 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k11_relat_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t95_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('11',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X49 ) @ X50 )
      | ( ( k7_relat_1 @ X49 @ X50 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('12',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['15'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X30: $i,X32: $i,X33: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X30 @ X32 ) @ X33 )
      | ~ ( r2_hidden @ X32 @ X33 )
      | ~ ( r2_hidden @ X30 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('19',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
        | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('22',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('23',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( r1_tarski @ X47 @ ( k1_relat_1 @ X48 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X48 @ X47 ) )
        = X47 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('24',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) )
        = ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      = ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(fc10_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('27',plain,(
    ! [X42: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X42 ) )
      | ~ ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf('28',plain,
    ( ( ( v1_xboole_0 @ ( k1_tarski @ sk_A ) )
      | ~ ( v1_xboole_0 @ ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X2 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('32',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X3 @ X3 @ X4 @ X5 )
      = ( k1_enumset1 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('33',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k3_enumset1 @ X6 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('34',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k4_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 @ X14 )
      = ( k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(fc5_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ~ ( v1_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('35',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ~ ( v1_xboole_0 @ ( k4_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc5_subset_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ~ ( v1_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ~ ( v1_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( v1_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','38'])).

thf('40',plain,
    ( ~ ( v1_xboole_0 @ ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['28','39'])).

thf('41',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
      & ( ( k11_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','40'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('43',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['15'])).

thf('45',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k11_relat_1 @ X40 @ X41 )
        = ( k9_relat_1 @ X40 @ ( k1_tarski @ X41 ) ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('46',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X28 ) @ X29 )
      | ( r2_hidden @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t187_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) )
         => ( ( k7_relat_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf('47',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( r1_xboole_0 @ X45 @ ( k1_relat_1 @ X46 ) )
      | ( ( k7_relat_1 @ X46 @ X45 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_tarski @ X1 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('50',plain,
    ( ( ( ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X49: $i,X50: $i] :
      ( ( ( k7_relat_1 @ X49 @ X50 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X49 ) @ X50 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('54',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X43 ) @ X44 )
      | ( ( k9_relat_1 @ X43 @ X44 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('59',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( ( k11_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['45','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('66',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k11_relat_1 @ sk_B @ sk_A )
       != k1_xboole_0 )
      & ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','43','44','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.16  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4dvhmz01G3
% 0.17/0.38  % Computer   : n010.cluster.edu
% 0.17/0.38  % Model      : x86_64 x86_64
% 0.17/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.38  % Memory     : 8042.1875MB
% 0.17/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.38  % CPULimit   : 60
% 0.17/0.38  % DateTime   : Tue Dec  1 11:23:45 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.39  % Number of cores: 8
% 0.17/0.39  % Python version: Python 3.6.8
% 0.17/0.39  % Running in FO mode
% 0.25/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.55  % Solved by: fo/fo7.sh
% 0.25/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.55  % done 98 iterations in 0.047s
% 0.25/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.55  % SZS output start Refutation
% 0.25/0.55  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.25/0.55  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.25/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.25/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.25/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.25/0.55  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.25/0.55  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.25/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.25/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.25/0.55  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.25/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.25/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.25/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.25/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.25/0.55  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.25/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.55  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.25/0.55  thf(t205_relat_1, conjecture,
% 0.25/0.55    (![A:$i,B:$i]:
% 0.25/0.55     ( ( v1_relat_1 @ B ) =>
% 0.25/0.55       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.25/0.55         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.25/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.55    (~( ![A:$i,B:$i]:
% 0.25/0.55        ( ( v1_relat_1 @ B ) =>
% 0.25/0.55          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.25/0.55            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.25/0.55    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.25/0.55  thf('0', plain,
% 0.25/0.55      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))
% 0.25/0.55        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('1', plain,
% 0.25/0.55      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.25/0.55       ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.25/0.55      inference('split', [status(esa)], ['0'])).
% 0.25/0.55  thf('2', plain,
% 0.25/0.55      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.25/0.55         <= ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.25/0.55      inference('split', [status(esa)], ['0'])).
% 0.25/0.55  thf(d16_relat_1, axiom,
% 0.25/0.55    (![A:$i]:
% 0.25/0.55     ( ( v1_relat_1 @ A ) =>
% 0.25/0.55       ( ![B:$i]:
% 0.25/0.55         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.25/0.55  thf('3', plain,
% 0.25/0.55      (![X40 : $i, X41 : $i]:
% 0.25/0.55         (((k11_relat_1 @ X40 @ X41) = (k9_relat_1 @ X40 @ (k1_tarski @ X41)))
% 0.25/0.55          | ~ (v1_relat_1 @ X40))),
% 0.25/0.55      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.25/0.55  thf(t151_relat_1, axiom,
% 0.25/0.55    (![A:$i,B:$i]:
% 0.25/0.55     ( ( v1_relat_1 @ B ) =>
% 0.25/0.55       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.25/0.55         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.25/0.55  thf('4', plain,
% 0.25/0.55      (![X43 : $i, X44 : $i]:
% 0.25/0.55         (((k9_relat_1 @ X43 @ X44) != (k1_xboole_0))
% 0.25/0.55          | (r1_xboole_0 @ (k1_relat_1 @ X43) @ X44)
% 0.25/0.55          | ~ (v1_relat_1 @ X43))),
% 0.25/0.55      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.25/0.55  thf('5', plain,
% 0.25/0.55      (![X0 : $i, X1 : $i]:
% 0.25/0.55         (((k11_relat_1 @ X1 @ X0) != (k1_xboole_0))
% 0.25/0.55          | ~ (v1_relat_1 @ X1)
% 0.25/0.55          | ~ (v1_relat_1 @ X1)
% 0.25/0.55          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ (k1_tarski @ X0)))),
% 0.25/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.25/0.55  thf('6', plain,
% 0.25/0.55      (![X0 : $i, X1 : $i]:
% 0.25/0.55         ((r1_xboole_0 @ (k1_relat_1 @ X1) @ (k1_tarski @ X0))
% 0.25/0.55          | ~ (v1_relat_1 @ X1)
% 0.25/0.55          | ((k11_relat_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.25/0.55      inference('simplify', [status(thm)], ['5'])).
% 0.25/0.55  thf('7', plain,
% 0.25/0.55      (((((k1_xboole_0) != (k1_xboole_0))
% 0.25/0.55         | ~ (v1_relat_1 @ sk_B)
% 0.25/0.55         | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A))))
% 0.25/0.55         <= ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.25/0.55      inference('sup-', [status(thm)], ['2', '6'])).
% 0.25/0.55  thf('8', plain, ((v1_relat_1 @ sk_B)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('9', plain,
% 0.25/0.55      (((((k1_xboole_0) != (k1_xboole_0))
% 0.25/0.55         | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A))))
% 0.25/0.55         <= ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.25/0.55      inference('demod', [status(thm)], ['7', '8'])).
% 0.25/0.55  thf('10', plain,
% 0.25/0.55      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A)))
% 0.25/0.55         <= ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.25/0.55      inference('simplify', [status(thm)], ['9'])).
% 0.25/0.55  thf(t95_relat_1, axiom,
% 0.25/0.55    (![A:$i,B:$i]:
% 0.25/0.55     ( ( v1_relat_1 @ B ) =>
% 0.25/0.55       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.25/0.55         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.25/0.55  thf('11', plain,
% 0.25/0.55      (![X49 : $i, X50 : $i]:
% 0.25/0.55         (~ (r1_xboole_0 @ (k1_relat_1 @ X49) @ X50)
% 0.25/0.55          | ((k7_relat_1 @ X49 @ X50) = (k1_xboole_0))
% 0.25/0.55          | ~ (v1_relat_1 @ X49))),
% 0.25/0.55      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.25/0.55  thf('12', plain,
% 0.25/0.55      (((~ (v1_relat_1 @ sk_B)
% 0.25/0.55         | ((k7_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))
% 0.25/0.55         <= ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.25/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.25/0.55  thf('13', plain, ((v1_relat_1 @ sk_B)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('14', plain,
% 0.25/0.55      ((((k7_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))
% 0.25/0.55         <= ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.25/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.25/0.55  thf('15', plain,
% 0.25/0.55      ((((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))
% 0.25/0.55        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('16', plain,
% 0.25/0.55      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.25/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.25/0.55      inference('split', [status(esa)], ['15'])).
% 0.25/0.55  thf('17', plain,
% 0.25/0.55      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.25/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.25/0.55      inference('split', [status(esa)], ['15'])).
% 0.25/0.55  thf(t38_zfmisc_1, axiom,
% 0.25/0.55    (![A:$i,B:$i,C:$i]:
% 0.25/0.55     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.25/0.55       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.25/0.55  thf('18', plain,
% 0.25/0.55      (![X30 : $i, X32 : $i, X33 : $i]:
% 0.25/0.55         ((r1_tarski @ (k2_tarski @ X30 @ X32) @ X33)
% 0.25/0.55          | ~ (r2_hidden @ X32 @ X33)
% 0.25/0.55          | ~ (r2_hidden @ X30 @ X33))),
% 0.25/0.55      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.25/0.55  thf('19', plain,
% 0.25/0.55      ((![X0 : $i]:
% 0.25/0.55          (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.25/0.55           | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ (k1_relat_1 @ sk_B))))
% 0.25/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.25/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.25/0.55  thf('20', plain,
% 0.25/0.55      (((r1_tarski @ (k2_tarski @ sk_A @ sk_A) @ (k1_relat_1 @ sk_B)))
% 0.25/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.25/0.55      inference('sup-', [status(thm)], ['16', '19'])).
% 0.25/0.55  thf(t69_enumset1, axiom,
% 0.25/0.55    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.25/0.55  thf('21', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.25/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.25/0.55  thf('22', plain,
% 0.25/0.55      (((r1_tarski @ (k1_tarski @ sk_A) @ (k1_relat_1 @ sk_B)))
% 0.25/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.25/0.55      inference('demod', [status(thm)], ['20', '21'])).
% 0.25/0.55  thf(t91_relat_1, axiom,
% 0.25/0.55    (![A:$i,B:$i]:
% 0.25/0.55     ( ( v1_relat_1 @ B ) =>
% 0.25/0.55       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.25/0.55         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.25/0.55  thf('23', plain,
% 0.25/0.55      (![X47 : $i, X48 : $i]:
% 0.25/0.55         (~ (r1_tarski @ X47 @ (k1_relat_1 @ X48))
% 0.25/0.55          | ((k1_relat_1 @ (k7_relat_1 @ X48 @ X47)) = (X47))
% 0.25/0.55          | ~ (v1_relat_1 @ X48))),
% 0.25/0.55      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.25/0.55  thf('24', plain,
% 0.25/0.55      (((~ (v1_relat_1 @ sk_B)
% 0.25/0.55         | ((k1_relat_1 @ (k7_relat_1 @ sk_B @ (k1_tarski @ sk_A)))
% 0.25/0.55             = (k1_tarski @ sk_A))))
% 0.25/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.25/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.25/0.55  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('26', plain,
% 0.25/0.55      ((((k1_relat_1 @ (k7_relat_1 @ sk_B @ (k1_tarski @ sk_A)))
% 0.25/0.55          = (k1_tarski @ sk_A)))
% 0.25/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.25/0.55      inference('demod', [status(thm)], ['24', '25'])).
% 0.25/0.55  thf(fc10_relat_1, axiom,
% 0.25/0.55    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ))).
% 0.25/0.55  thf('27', plain,
% 0.25/0.55      (![X42 : $i]:
% 0.25/0.55         ((v1_xboole_0 @ (k1_relat_1 @ X42)) | ~ (v1_xboole_0 @ X42))),
% 0.25/0.55      inference('cnf', [status(esa)], [fc10_relat_1])).
% 0.25/0.55  thf('28', plain,
% 0.25/0.55      ((((v1_xboole_0 @ (k1_tarski @ sk_A))
% 0.25/0.55         | ~ (v1_xboole_0 @ (k7_relat_1 @ sk_B @ (k1_tarski @ sk_A)))))
% 0.25/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.25/0.55      inference('sup+', [status(thm)], ['26', '27'])).
% 0.25/0.55  thf(t70_enumset1, axiom,
% 0.25/0.55    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.25/0.55  thf('29', plain,
% 0.25/0.55      (![X1 : $i, X2 : $i]:
% 0.25/0.55         ((k1_enumset1 @ X1 @ X1 @ X2) = (k2_tarski @ X1 @ X2))),
% 0.25/0.55      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.25/0.55  thf('30', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.25/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.25/0.55  thf('31', plain,
% 0.25/0.55      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.25/0.55      inference('sup+', [status(thm)], ['29', '30'])).
% 0.25/0.55  thf(t71_enumset1, axiom,
% 0.25/0.55    (![A:$i,B:$i,C:$i]:
% 0.25/0.55     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.25/0.55  thf('32', plain,
% 0.25/0.55      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.25/0.55         ((k2_enumset1 @ X3 @ X3 @ X4 @ X5) = (k1_enumset1 @ X3 @ X4 @ X5))),
% 0.25/0.55      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.25/0.55  thf(t72_enumset1, axiom,
% 0.25/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.25/0.55     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.25/0.55  thf('33', plain,
% 0.25/0.55      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.25/0.55         ((k3_enumset1 @ X6 @ X6 @ X7 @ X8 @ X9)
% 0.25/0.55           = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 0.25/0.55      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.25/0.55  thf(t73_enumset1, axiom,
% 0.25/0.55    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.25/0.55     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.25/0.55       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.25/0.55  thf('34', plain,
% 0.25/0.55      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.25/0.55         ((k4_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 @ X14)
% 0.25/0.55           = (k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14))),
% 0.25/0.55      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.25/0.55  thf(fc5_subset_1, axiom,
% 0.25/0.55    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.25/0.55     ( ~( v1_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) ))).
% 0.25/0.55  thf('35', plain,
% 0.25/0.55      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.25/0.55         ~ (v1_xboole_0 @ (k4_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39))),
% 0.25/0.55      inference('cnf', [status(esa)], [fc5_subset_1])).
% 0.25/0.55  thf('36', plain,
% 0.25/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.25/0.55         ~ (v1_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.25/0.55      inference('sup-', [status(thm)], ['34', '35'])).
% 0.25/0.55  thf('37', plain,
% 0.25/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.25/0.55         ~ (v1_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.25/0.55      inference('sup-', [status(thm)], ['33', '36'])).
% 0.25/0.55  thf('38', plain,
% 0.25/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.55         ~ (v1_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.25/0.55      inference('sup-', [status(thm)], ['32', '37'])).
% 0.25/0.55  thf('39', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.25/0.55      inference('sup-', [status(thm)], ['31', '38'])).
% 0.25/0.55  thf('40', plain,
% 0.25/0.55      ((~ (v1_xboole_0 @ (k7_relat_1 @ sk_B @ (k1_tarski @ sk_A))))
% 0.25/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.25/0.55      inference('clc', [status(thm)], ['28', '39'])).
% 0.25/0.55  thf('41', plain,
% 0.25/0.55      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.25/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) & 
% 0.25/0.55             (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.25/0.55      inference('sup-', [status(thm)], ['14', '40'])).
% 0.25/0.55  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.25/0.55  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.25/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.25/0.55  thf('43', plain,
% 0.25/0.55      (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.25/0.55       ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.25/0.55      inference('demod', [status(thm)], ['41', '42'])).
% 0.25/0.55  thf('44', plain,
% 0.25/0.55      (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.25/0.55       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.25/0.55      inference('split', [status(esa)], ['15'])).
% 0.25/0.55  thf('45', plain,
% 0.25/0.55      (![X40 : $i, X41 : $i]:
% 0.25/0.55         (((k11_relat_1 @ X40 @ X41) = (k9_relat_1 @ X40 @ (k1_tarski @ X41)))
% 0.25/0.55          | ~ (v1_relat_1 @ X40))),
% 0.25/0.55      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.25/0.55  thf(l27_zfmisc_1, axiom,
% 0.25/0.55    (![A:$i,B:$i]:
% 0.25/0.55     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.25/0.55  thf('46', plain,
% 0.25/0.55      (![X28 : $i, X29 : $i]:
% 0.25/0.55         ((r1_xboole_0 @ (k1_tarski @ X28) @ X29) | (r2_hidden @ X28 @ X29))),
% 0.25/0.55      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.25/0.55  thf(t187_relat_1, axiom,
% 0.25/0.55    (![A:$i]:
% 0.25/0.55     ( ( v1_relat_1 @ A ) =>
% 0.25/0.55       ( ![B:$i]:
% 0.25/0.55         ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) ) =>
% 0.25/0.55           ( ( k7_relat_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.25/0.55  thf('47', plain,
% 0.25/0.55      (![X45 : $i, X46 : $i]:
% 0.25/0.55         (~ (r1_xboole_0 @ X45 @ (k1_relat_1 @ X46))
% 0.25/0.55          | ((k7_relat_1 @ X46 @ X45) = (k1_xboole_0))
% 0.25/0.55          | ~ (v1_relat_1 @ X46))),
% 0.25/0.55      inference('cnf', [status(esa)], [t187_relat_1])).
% 0.25/0.55  thf('48', plain,
% 0.25/0.55      (![X0 : $i, X1 : $i]:
% 0.25/0.55         ((r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.25/0.55          | ~ (v1_relat_1 @ X0)
% 0.25/0.55          | ((k7_relat_1 @ X0 @ (k1_tarski @ X1)) = (k1_xboole_0)))),
% 0.25/0.55      inference('sup-', [status(thm)], ['46', '47'])).
% 0.25/0.55  thf('49', plain,
% 0.25/0.55      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.25/0.55         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.25/0.55      inference('split', [status(esa)], ['0'])).
% 0.25/0.55  thf('50', plain,
% 0.25/0.55      (((((k7_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))
% 0.25/0.55         | ~ (v1_relat_1 @ sk_B)))
% 0.25/0.55         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.25/0.55      inference('sup-', [status(thm)], ['48', '49'])).
% 0.25/0.55  thf('51', plain, ((v1_relat_1 @ sk_B)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('52', plain,
% 0.25/0.55      ((((k7_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))
% 0.25/0.55         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.25/0.55      inference('demod', [status(thm)], ['50', '51'])).
% 0.25/0.55  thf('53', plain,
% 0.25/0.55      (![X49 : $i, X50 : $i]:
% 0.25/0.55         (((k7_relat_1 @ X49 @ X50) != (k1_xboole_0))
% 0.25/0.55          | (r1_xboole_0 @ (k1_relat_1 @ X49) @ X50)
% 0.25/0.55          | ~ (v1_relat_1 @ X49))),
% 0.25/0.55      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.25/0.55  thf('54', plain,
% 0.25/0.55      (((((k1_xboole_0) != (k1_xboole_0))
% 0.25/0.55         | ~ (v1_relat_1 @ sk_B)
% 0.25/0.55         | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A))))
% 0.25/0.55         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.25/0.55      inference('sup-', [status(thm)], ['52', '53'])).
% 0.25/0.55  thf('55', plain, ((v1_relat_1 @ sk_B)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('56', plain,
% 0.25/0.55      (((((k1_xboole_0) != (k1_xboole_0))
% 0.25/0.55         | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A))))
% 0.25/0.55         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.25/0.55      inference('demod', [status(thm)], ['54', '55'])).
% 0.25/0.55  thf('57', plain,
% 0.25/0.55      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A)))
% 0.25/0.55         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.25/0.55      inference('simplify', [status(thm)], ['56'])).
% 0.25/0.55  thf('58', plain,
% 0.25/0.55      (![X43 : $i, X44 : $i]:
% 0.25/0.55         (~ (r1_xboole_0 @ (k1_relat_1 @ X43) @ X44)
% 0.25/0.55          | ((k9_relat_1 @ X43 @ X44) = (k1_xboole_0))
% 0.25/0.55          | ~ (v1_relat_1 @ X43))),
% 0.25/0.55      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.25/0.55  thf('59', plain,
% 0.25/0.55      (((~ (v1_relat_1 @ sk_B)
% 0.25/0.55         | ((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))
% 0.25/0.55         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.25/0.55      inference('sup-', [status(thm)], ['57', '58'])).
% 0.25/0.55  thf('60', plain, ((v1_relat_1 @ sk_B)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('61', plain,
% 0.25/0.55      ((((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))
% 0.25/0.55         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.25/0.55      inference('demod', [status(thm)], ['59', '60'])).
% 0.25/0.55  thf('62', plain,
% 0.25/0.55      (((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)) | ~ (v1_relat_1 @ sk_B)))
% 0.25/0.55         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.25/0.55      inference('sup+', [status(thm)], ['45', '61'])).
% 0.25/0.55  thf('63', plain, ((v1_relat_1 @ sk_B)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('64', plain,
% 0.25/0.55      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.25/0.55         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.25/0.55      inference('demod', [status(thm)], ['62', '63'])).
% 0.25/0.55  thf('65', plain,
% 0.25/0.55      ((((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 0.25/0.55         <= (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.25/0.55      inference('split', [status(esa)], ['15'])).
% 0.25/0.55  thf('66', plain,
% 0.25/0.55      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.25/0.55         <= (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) & 
% 0.25/0.55             ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.25/0.55      inference('sup-', [status(thm)], ['64', '65'])).
% 0.25/0.55  thf('67', plain,
% 0.25/0.55      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.25/0.55       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.25/0.55      inference('simplify', [status(thm)], ['66'])).
% 0.25/0.55  thf('68', plain, ($false),
% 0.25/0.55      inference('sat_resolution*', [status(thm)], ['1', '43', '44', '67'])).
% 0.25/0.55  
% 0.25/0.55  % SZS output end Refutation
% 0.25/0.55  
% 0.25/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
