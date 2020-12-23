%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MzHaNaz3Aw

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:36 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 376 expanded)
%              Number of leaves         :   19 ( 114 expanded)
%              Depth                    :   14
%              Number of atoms          :  714 (3453 expanded)
%              Number of equality atoms :   66 ( 332 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t73_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = k1_xboole_0 )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = k1_xboole_0 )
      <=> ( ( r2_hidden @ A @ C )
          & ( r2_hidden @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t73_zfmisc_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
   <= ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_1 )
    | ~ ( r2_hidden @ sk_A @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ sk_C_1 )
    | ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['2'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('4',plain,(
    ! [X14: $i] :
      ( ( k2_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k2_xboole_0 @ X25 @ X26 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t68_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('7',plain,(
    ! [X41: $i,X42: $i] :
      ( ( r2_hidden @ X41 @ X42 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X41 ) @ X42 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t68_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ( r2_hidden @ X6 @ X9 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('11',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ ( k4_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('13',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k2_tarski @ X35 @ X36 )
      = ( k2_xboole_0 @ ( k1_tarski @ X35 ) @ ( k1_tarski @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('14',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k2_xboole_0 @ X25 @ X26 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('15',plain,(
    ! [X41: $i,X42: $i] :
      ( ( r2_hidden @ X41 @ X42 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X41 ) @ X42 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t68_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ X1 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','17'])).

thf('19',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('22',plain,
    ( ( ( k2_xboole_0 @ sk_C_1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('25',plain,(
    ! [X14: $i] :
      ( ( k2_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_C_1
      = ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23','26'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('28',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('29',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('30',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ sk_C_1 ) )
        | ~ ( r2_hidden @ X1 @ ( k2_tarski @ sk_A @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C_1 ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','32'])).

thf('34',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','33'])).

thf('35',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_1 )
   <= ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('36',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('38',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k2_tarski @ X35 @ X36 )
      = ( k2_xboole_0 @ ( k1_tarski @ X35 ) @ ( k1_tarski @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('40',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k2_xboole_0 @ X25 @ X26 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X41: $i,X42: $i] :
      ( ( r2_hidden @ X41 @ X42 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X41 ) @ X42 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t68_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','44'])).

thf('46',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ sk_C_1 ) )
        | ~ ( r2_hidden @ X1 @ ( k2_tarski @ sk_A @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('47',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C_1 ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','47'])).

thf('49',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_1 )
   <= ~ ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('50',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,(
    r2_hidden @ sk_B @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['3','36','50','51'])).

thf('53',plain,(
    r2_hidden @ sk_B @ sk_C_1 ),
    inference(simpl_trail,[status(thm)],['1','52'])).

thf('54',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
   <= ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['19'])).

thf(t48_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ B ) )
     => ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
        = B ) ) )).

thf('55',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X38 @ X39 )
      | ~ ( r2_hidden @ X40 @ X39 )
      | ( ( k2_xboole_0 @ ( k2_tarski @ X38 @ X40 ) @ X39 )
        = X39 ) ) ),
    inference(cnf,[status(esa)],[t48_zfmisc_1])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ X0 ) @ sk_C_1 )
          = sk_C_1 )
        | ~ ( r2_hidden @ X0 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ( ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ X0 ) )
          = sk_C_1 )
        | ~ ( r2_hidden @ X0 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('60',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['3','36','50','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ X0 ) )
        = sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference(simpl_trail,[status(thm)],['58','60'])).

thf('62',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['53','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('64',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('66',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['3','36','50'])).

thf('67',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['65','66'])).

thf('68',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['64','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MzHaNaz3Aw
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.42/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.60  % Solved by: fo/fo7.sh
% 0.42/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.60  % done 323 iterations in 0.152s
% 0.42/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.60  % SZS output start Refutation
% 0.42/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.42/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.60  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.42/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.42/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.42/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.42/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.60  thf(t73_zfmisc_1, conjecture,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_xboole_0 ) ) <=>
% 0.42/0.60       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.42/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.60    (~( ![A:$i,B:$i,C:$i]:
% 0.42/0.60        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_xboole_0 ) ) <=>
% 0.42/0.60          ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ) )),
% 0.42/0.60    inference('cnf.neg', [status(esa)], [t73_zfmisc_1])).
% 0.42/0.60  thf('0', plain,
% 0.42/0.60      (((r2_hidden @ sk_B @ sk_C_1)
% 0.42/0.60        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('1', plain,
% 0.42/0.60      (((r2_hidden @ sk_B @ sk_C_1)) <= (((r2_hidden @ sk_B @ sk_C_1)))),
% 0.42/0.60      inference('split', [status(esa)], ['0'])).
% 0.42/0.60  thf('2', plain,
% 0.42/0.60      ((~ (r2_hidden @ sk_B @ sk_C_1)
% 0.42/0.60        | ~ (r2_hidden @ sk_A @ sk_C_1)
% 0.42/0.60        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) != (k1_xboole_0)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('3', plain,
% 0.42/0.60      (~ (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0))) | 
% 0.42/0.60       ~ ((r2_hidden @ sk_B @ sk_C_1)) | ~ ((r2_hidden @ sk_A @ sk_C_1))),
% 0.42/0.60      inference('split', [status(esa)], ['2'])).
% 0.42/0.60  thf(t1_boole, axiom,
% 0.42/0.60    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.42/0.60  thf('4', plain, (![X14 : $i]: ((k2_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.42/0.60      inference('cnf', [status(esa)], [t1_boole])).
% 0.42/0.60  thf(t46_xboole_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.42/0.60  thf('5', plain,
% 0.42/0.60      (![X25 : $i, X26 : $i]:
% 0.42/0.60         ((k4_xboole_0 @ X25 @ (k2_xboole_0 @ X25 @ X26)) = (k1_xboole_0))),
% 0.42/0.60      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.42/0.60  thf('6', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.42/0.60      inference('sup+', [status(thm)], ['4', '5'])).
% 0.42/0.60  thf(t68_zfmisc_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.42/0.60       ( r2_hidden @ A @ B ) ))).
% 0.42/0.60  thf('7', plain,
% 0.42/0.60      (![X41 : $i, X42 : $i]:
% 0.42/0.60         ((r2_hidden @ X41 @ X42)
% 0.42/0.60          | ((k4_xboole_0 @ (k1_tarski @ X41) @ X42) != (k1_xboole_0)))),
% 0.42/0.60      inference('cnf', [status(esa)], [t68_zfmisc_1])).
% 0.42/0.60  thf('8', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (((k1_xboole_0) != (k1_xboole_0))
% 0.42/0.60          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['6', '7'])).
% 0.42/0.60  thf('9', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.42/0.60      inference('simplify', [status(thm)], ['8'])).
% 0.42/0.60  thf(d5_xboole_0, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.42/0.60       ( ![D:$i]:
% 0.42/0.60         ( ( r2_hidden @ D @ C ) <=>
% 0.42/0.60           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.42/0.60  thf('10', plain,
% 0.42/0.60      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X6 @ X7)
% 0.42/0.60          | (r2_hidden @ X6 @ X8)
% 0.42/0.60          | (r2_hidden @ X6 @ X9)
% 0.42/0.60          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.42/0.60      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.42/0.60  thf('11', plain,
% 0.42/0.60      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.42/0.60         ((r2_hidden @ X6 @ (k4_xboole_0 @ X7 @ X8))
% 0.42/0.60          | (r2_hidden @ X6 @ X8)
% 0.42/0.60          | ~ (r2_hidden @ X6 @ X7))),
% 0.42/0.60      inference('simplify', [status(thm)], ['10'])).
% 0.42/0.60  thf('12', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         ((r2_hidden @ X0 @ X1)
% 0.42/0.60          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['9', '11'])).
% 0.42/0.60  thf(t41_enumset1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( k2_tarski @ A @ B ) =
% 0.42/0.60       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.42/0.60  thf('13', plain,
% 0.42/0.60      (![X35 : $i, X36 : $i]:
% 0.42/0.60         ((k2_tarski @ X35 @ X36)
% 0.42/0.60           = (k2_xboole_0 @ (k1_tarski @ X35) @ (k1_tarski @ X36)))),
% 0.42/0.60      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.42/0.60  thf('14', plain,
% 0.42/0.60      (![X25 : $i, X26 : $i]:
% 0.42/0.60         ((k4_xboole_0 @ X25 @ (k2_xboole_0 @ X25 @ X26)) = (k1_xboole_0))),
% 0.42/0.60      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.42/0.60  thf('15', plain,
% 0.42/0.60      (![X41 : $i, X42 : $i]:
% 0.42/0.60         ((r2_hidden @ X41 @ X42)
% 0.42/0.60          | ((k4_xboole_0 @ (k1_tarski @ X41) @ X42) != (k1_xboole_0)))),
% 0.42/0.60      inference('cnf', [status(esa)], [t68_zfmisc_1])).
% 0.42/0.60  thf('16', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         (((k1_xboole_0) != (k1_xboole_0))
% 0.42/0.60          | (r2_hidden @ X1 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['14', '15'])).
% 0.42/0.60  thf('17', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         (r2_hidden @ X1 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0))),
% 0.42/0.60      inference('simplify', [status(thm)], ['16'])).
% 0.42/0.60  thf('18', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.42/0.60      inference('sup+', [status(thm)], ['13', '17'])).
% 0.42/0.60  thf('19', plain,
% 0.42/0.60      (((r2_hidden @ sk_A @ sk_C_1)
% 0.42/0.60        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('20', plain,
% 0.42/0.60      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0)))
% 0.42/0.60         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.42/0.60                = (k1_xboole_0))))),
% 0.42/0.60      inference('split', [status(esa)], ['19'])).
% 0.42/0.60  thf(t39_xboole_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.42/0.60  thf('21', plain,
% 0.42/0.60      (![X15 : $i, X16 : $i]:
% 0.42/0.60         ((k2_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15))
% 0.42/0.60           = (k2_xboole_0 @ X15 @ X16))),
% 0.42/0.60      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.42/0.60  thf('22', plain,
% 0.42/0.60      ((((k2_xboole_0 @ sk_C_1 @ k1_xboole_0)
% 0.42/0.60          = (k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B))))
% 0.42/0.60         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.42/0.60                = (k1_xboole_0))))),
% 0.42/0.60      inference('sup+', [status(thm)], ['20', '21'])).
% 0.42/0.60  thf(commutativity_k2_xboole_0, axiom,
% 0.42/0.60    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.42/0.60  thf('23', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.42/0.60      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.42/0.60  thf('24', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.42/0.60      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.42/0.60  thf('25', plain, (![X14 : $i]: ((k2_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.42/0.60      inference('cnf', [status(esa)], [t1_boole])).
% 0.42/0.60  thf('26', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.42/0.60      inference('sup+', [status(thm)], ['24', '25'])).
% 0.42/0.60  thf('27', plain,
% 0.42/0.60      ((((sk_C_1) = (k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B))))
% 0.42/0.60         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.42/0.60                = (k1_xboole_0))))),
% 0.42/0.60      inference('demod', [status(thm)], ['22', '23', '26'])).
% 0.42/0.60  thf(t41_xboole_1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.42/0.60       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.42/0.60  thf('28', plain,
% 0.42/0.60      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.42/0.60         ((k4_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ X21)
% 0.42/0.60           = (k4_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X21)))),
% 0.42/0.60      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.42/0.60  thf('29', plain,
% 0.42/0.60      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X10 @ X9)
% 0.42/0.60          | ~ (r2_hidden @ X10 @ X8)
% 0.42/0.60          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.42/0.60      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.42/0.60  thf('30', plain,
% 0.42/0.60      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X10 @ X8)
% 0.42/0.60          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.42/0.60      inference('simplify', [status(thm)], ['29'])).
% 0.42/0.60  thf('31', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X3 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.42/0.60          | ~ (r2_hidden @ X3 @ X0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['28', '30'])).
% 0.42/0.60  thf('32', plain,
% 0.42/0.60      ((![X0 : $i, X1 : $i]:
% 0.42/0.60          (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ sk_C_1))
% 0.42/0.60           | ~ (r2_hidden @ X1 @ (k2_tarski @ sk_A @ sk_B))))
% 0.42/0.60         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.42/0.60                = (k1_xboole_0))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['27', '31'])).
% 0.42/0.60  thf('33', plain,
% 0.42/0.60      ((![X0 : $i]: ~ (r2_hidden @ sk_A @ (k4_xboole_0 @ X0 @ sk_C_1)))
% 0.42/0.60         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.42/0.60                = (k1_xboole_0))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['18', '32'])).
% 0.42/0.60  thf('34', plain,
% 0.42/0.60      (((r2_hidden @ sk_A @ sk_C_1))
% 0.42/0.60         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.42/0.60                = (k1_xboole_0))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['12', '33'])).
% 0.42/0.60  thf('35', plain,
% 0.42/0.60      ((~ (r2_hidden @ sk_A @ sk_C_1)) <= (~ ((r2_hidden @ sk_A @ sk_C_1)))),
% 0.42/0.60      inference('split', [status(esa)], ['2'])).
% 0.42/0.60  thf('36', plain,
% 0.42/0.60      (((r2_hidden @ sk_A @ sk_C_1)) | 
% 0.42/0.60       ~ (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['34', '35'])).
% 0.42/0.60  thf('37', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         ((r2_hidden @ X0 @ X1)
% 0.42/0.60          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['9', '11'])).
% 0.42/0.60  thf('38', plain,
% 0.42/0.60      (![X35 : $i, X36 : $i]:
% 0.42/0.60         ((k2_tarski @ X35 @ X36)
% 0.42/0.60           = (k2_xboole_0 @ (k1_tarski @ X35) @ (k1_tarski @ X36)))),
% 0.42/0.60      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.42/0.60  thf('39', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.42/0.60      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.42/0.60  thf('40', plain,
% 0.42/0.60      (![X25 : $i, X26 : $i]:
% 0.42/0.60         ((k4_xboole_0 @ X25 @ (k2_xboole_0 @ X25 @ X26)) = (k1_xboole_0))),
% 0.42/0.60      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.42/0.60  thf('41', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.42/0.60      inference('sup+', [status(thm)], ['39', '40'])).
% 0.42/0.60  thf('42', plain,
% 0.42/0.60      (![X41 : $i, X42 : $i]:
% 0.42/0.60         ((r2_hidden @ X41 @ X42)
% 0.42/0.60          | ((k4_xboole_0 @ (k1_tarski @ X41) @ X42) != (k1_xboole_0)))),
% 0.42/0.60      inference('cnf', [status(esa)], [t68_zfmisc_1])).
% 0.42/0.60  thf('43', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         (((k1_xboole_0) != (k1_xboole_0))
% 0.42/0.60          | (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['41', '42'])).
% 0.42/0.60  thf('44', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.42/0.60      inference('simplify', [status(thm)], ['43'])).
% 0.42/0.60  thf('45', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 0.42/0.60      inference('sup+', [status(thm)], ['38', '44'])).
% 0.42/0.60  thf('46', plain,
% 0.42/0.60      ((![X0 : $i, X1 : $i]:
% 0.42/0.60          (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ sk_C_1))
% 0.42/0.60           | ~ (r2_hidden @ X1 @ (k2_tarski @ sk_A @ sk_B))))
% 0.42/0.60         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.42/0.60                = (k1_xboole_0))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['27', '31'])).
% 0.42/0.60  thf('47', plain,
% 0.42/0.60      ((![X0 : $i]: ~ (r2_hidden @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_1)))
% 0.42/0.60         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.42/0.60                = (k1_xboole_0))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['45', '46'])).
% 0.42/0.60  thf('48', plain,
% 0.42/0.60      (((r2_hidden @ sk_B @ sk_C_1))
% 0.42/0.60         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.42/0.60                = (k1_xboole_0))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['37', '47'])).
% 0.42/0.60  thf('49', plain,
% 0.42/0.60      ((~ (r2_hidden @ sk_B @ sk_C_1)) <= (~ ((r2_hidden @ sk_B @ sk_C_1)))),
% 0.42/0.60      inference('split', [status(esa)], ['2'])).
% 0.42/0.60  thf('50', plain,
% 0.42/0.60      (((r2_hidden @ sk_B @ sk_C_1)) | 
% 0.42/0.60       ~ (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['48', '49'])).
% 0.42/0.60  thf('51', plain,
% 0.42/0.60      (((r2_hidden @ sk_B @ sk_C_1)) | 
% 0.42/0.60       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 0.42/0.60      inference('split', [status(esa)], ['0'])).
% 0.42/0.60  thf('52', plain, (((r2_hidden @ sk_B @ sk_C_1))),
% 0.42/0.60      inference('sat_resolution*', [status(thm)], ['3', '36', '50', '51'])).
% 0.42/0.60  thf('53', plain, ((r2_hidden @ sk_B @ sk_C_1)),
% 0.42/0.60      inference('simpl_trail', [status(thm)], ['1', '52'])).
% 0.42/0.60  thf('54', plain,
% 0.42/0.60      (((r2_hidden @ sk_A @ sk_C_1)) <= (((r2_hidden @ sk_A @ sk_C_1)))),
% 0.42/0.60      inference('split', [status(esa)], ['19'])).
% 0.42/0.60  thf(t48_zfmisc_1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.42/0.60       ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ))).
% 0.42/0.60  thf('55', plain,
% 0.42/0.60      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X38 @ X39)
% 0.42/0.60          | ~ (r2_hidden @ X40 @ X39)
% 0.42/0.60          | ((k2_xboole_0 @ (k2_tarski @ X38 @ X40) @ X39) = (X39)))),
% 0.42/0.60      inference('cnf', [status(esa)], [t48_zfmisc_1])).
% 0.42/0.60  thf('56', plain,
% 0.42/0.60      ((![X0 : $i]:
% 0.42/0.60          (((k2_xboole_0 @ (k2_tarski @ sk_A @ X0) @ sk_C_1) = (sk_C_1))
% 0.42/0.60           | ~ (r2_hidden @ X0 @ sk_C_1)))
% 0.42/0.60         <= (((r2_hidden @ sk_A @ sk_C_1)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['54', '55'])).
% 0.42/0.60  thf('57', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.42/0.60      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.42/0.60  thf('58', plain,
% 0.42/0.60      ((![X0 : $i]:
% 0.42/0.60          (((k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ X0)) = (sk_C_1))
% 0.42/0.60           | ~ (r2_hidden @ X0 @ sk_C_1)))
% 0.42/0.60         <= (((r2_hidden @ sk_A @ sk_C_1)))),
% 0.42/0.60      inference('demod', [status(thm)], ['56', '57'])).
% 0.42/0.60  thf('59', plain,
% 0.42/0.60      (((r2_hidden @ sk_A @ sk_C_1)) | 
% 0.42/0.60       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 0.42/0.60      inference('split', [status(esa)], ['19'])).
% 0.42/0.60  thf('60', plain, (((r2_hidden @ sk_A @ sk_C_1))),
% 0.42/0.60      inference('sat_resolution*', [status(thm)], ['3', '36', '50', '59'])).
% 0.42/0.60  thf('61', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (((k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ X0)) = (sk_C_1))
% 0.42/0.60          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.42/0.60      inference('simpl_trail', [status(thm)], ['58', '60'])).
% 0.42/0.60  thf('62', plain,
% 0.42/0.60      (((k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)) = (sk_C_1))),
% 0.42/0.60      inference('sup-', [status(thm)], ['53', '61'])).
% 0.42/0.60  thf('63', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.42/0.60      inference('sup+', [status(thm)], ['39', '40'])).
% 0.42/0.60  thf('64', plain,
% 0.42/0.60      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0))),
% 0.42/0.60      inference('sup+', [status(thm)], ['62', '63'])).
% 0.42/0.60  thf('65', plain,
% 0.42/0.60      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) != (k1_xboole_0)))
% 0.42/0.60         <= (~
% 0.42/0.60             (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.42/0.60                = (k1_xboole_0))))),
% 0.42/0.60      inference('split', [status(esa)], ['2'])).
% 0.42/0.60  thf('66', plain,
% 0.42/0.60      (~ (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 0.42/0.60      inference('sat_resolution*', [status(thm)], ['3', '36', '50'])).
% 0.42/0.60  thf('67', plain,
% 0.42/0.60      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) != (k1_xboole_0))),
% 0.42/0.60      inference('simpl_trail', [status(thm)], ['65', '66'])).
% 0.42/0.60  thf('68', plain, ($false),
% 0.42/0.60      inference('simplify_reflect-', [status(thm)], ['64', '67'])).
% 0.42/0.60  
% 0.42/0.60  % SZS output end Refutation
% 0.42/0.60  
% 0.42/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
