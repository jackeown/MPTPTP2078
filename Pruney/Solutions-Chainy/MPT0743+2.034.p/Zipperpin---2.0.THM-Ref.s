%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4Zo6WGbmHH

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:57 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 246 expanded)
%              Number of leaves         :   24 (  76 expanded)
%              Depth                    :   18
%              Number of atoms          :  853 (2002 expanded)
%              Number of equality atoms :   25 (  42 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t33_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
          <=> ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r2_hidden @ A @ B )
            <=> ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_ordinal1])).

thf('0',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( v3_ordinal1 @ X47 )
      | ~ ( v3_ordinal1 @ X48 )
      | ( r1_ordinal1 @ X47 @ X48 )
      | ~ ( r1_tarski @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('9',plain,(
    ! [X39: $i,X41: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X39 ) @ X41 )
      | ~ ( r2_hidden @ X39 @ X41 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('10',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( v3_ordinal1 @ X44 )
      | ~ ( v3_ordinal1 @ X45 )
      | ( r1_ordinal1 @ X44 @ X45 )
      | ( r1_ordinal1 @ X45 @ X44 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( v3_ordinal1 @ X47 )
      | ~ ( v3_ordinal1 @ X48 )
      | ( r1_tarski @ X47 @ X48 )
      | ~ ( r1_ordinal1 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('20',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( r2_hidden @ X53 @ X54 )
      | ~ ( r1_tarski @ X54 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('21',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( v3_ordinal1 @ X47 )
      | ~ ( v3_ordinal1 @ X48 )
      | ( r1_tarski @ X47 @ X48 )
      | ~ ( r1_ordinal1 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('26',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('30',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B )
        | ~ ( r1_tarski @ X0 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_A ) ) @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','31'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('33',plain,(
    ! [X46: $i] :
      ( ( k1_ordinal1 @ X46 )
      = ( k2_xboole_0 @ X46 @ ( k1_tarski @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('34',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('35',plain,(
    ! [X52: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X52 ) )
      | ~ ( v3_ordinal1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('36',plain,(
    ! [X52: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X52 ) )
      | ~ ( v3_ordinal1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('37',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( v3_ordinal1 @ X44 )
      | ~ ( v3_ordinal1 @ X45 )
      | ( r1_ordinal1 @ X44 @ X45 )
      | ( r1_ordinal1 @ X45 @ X44 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('38',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,
    ( ( ( r1_ordinal1 @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( r1_ordinal1 @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_ordinal1 @ sk_B @ ( k1_ordinal1 @ sk_A ) ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( r1_ordinal1 @ sk_B @ ( k1_ordinal1 @ sk_A ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( v3_ordinal1 @ X47 )
      | ~ ( v3_ordinal1 @ X48 )
      | ( r1_tarski @ X47 @ X48 )
      | ~ ( r1_ordinal1 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('46',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['35','48'])).

thf('50',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('53',plain,
    ( ( ~ ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ( ( k1_ordinal1 @ sk_A )
        = sk_B ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k1_ordinal1 @ sk_A )
      = sk_B )
   <= ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','53'])).

thf('55',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('56',plain,
    ( ~ ( r1_ordinal1 @ sk_B @ sk_B )
   <= ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
   <= ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','56'])).

thf('58',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('61',plain,(
    ! [X52: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X52 ) )
      | ~ ( v3_ordinal1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('62',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('63',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( v3_ordinal1 @ X47 )
      | ~ ( v3_ordinal1 @ X48 )
      | ( r1_tarski @ X47 @ X48 )
      | ~ ( r1_ordinal1 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('64',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['67','68'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('70',plain,(
    ! [X11: $i] :
      ( ( k2_tarski @ X11 @ X11 )
      = ( k1_tarski @ X11 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('71',plain,(
    ! [X46: $i] :
      ( ( k1_ordinal1 @ X46 )
      = ( k2_xboole_0 @ X46 @ ( k1_tarski @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k1_ordinal1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('73',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X1 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['69','74'])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('76',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( v3_ordinal1 @ X50 )
      | ( r2_hidden @ X51 @ X50 )
      | ( X51 = X50 )
      | ( r2_hidden @ X50 @ X51 )
      | ~ ( v3_ordinal1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('77',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( r2_hidden @ X53 @ X54 )
      | ~ ( r1_tarski @ X54 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( sk_B = sk_A )
      | ( r2_hidden @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( ( sk_B = sk_A )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('84',plain,
    ( ( sk_B = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('86',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('87',plain,
    ( ( ~ ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ~ ( r1_tarski @ sk_A @ ( k1_ordinal1 @ sk_A ) )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k1_ordinal1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('90',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( sk_B = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('93',plain,
    ( ( sk_A
      = ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['88','91','92'])).

thf(t14_ordinal1,axiom,(
    ! [A: $i] :
      ( A
     != ( k1_ordinal1 @ A ) ) )).

thf('94',plain,(
    ! [X49: $i] :
      ( X49
     != ( k1_ordinal1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t14_ordinal1])).

thf('95',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['93','94'])).

thf('96',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','59','60','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4Zo6WGbmHH
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:07:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.41/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.61  % Solved by: fo/fo7.sh
% 0.41/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.61  % done 326 iterations in 0.153s
% 0.41/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.61  % SZS output start Refutation
% 0.41/0.61  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.41/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.41/0.61  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.41/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.61  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.41/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.41/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.41/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.61  thf(t33_ordinal1, conjecture,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( v3_ordinal1 @ A ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( v3_ordinal1 @ B ) =>
% 0.41/0.61           ( ( r2_hidden @ A @ B ) <=>
% 0.41/0.61             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 0.41/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.61    (~( ![A:$i]:
% 0.41/0.61        ( ( v3_ordinal1 @ A ) =>
% 0.41/0.61          ( ![B:$i]:
% 0.41/0.61            ( ( v3_ordinal1 @ B ) =>
% 0.41/0.61              ( ( r2_hidden @ A @ B ) <=>
% 0.41/0.61                ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ) )),
% 0.41/0.61    inference('cnf.neg', [status(esa)], [t33_ordinal1])).
% 0.41/0.61  thf('0', plain,
% 0.41/0.61      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.41/0.61        | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('1', plain,
% 0.41/0.61      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 0.41/0.61       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.41/0.61      inference('split', [status(esa)], ['0'])).
% 0.41/0.61  thf(d10_xboole_0, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.61  thf('2', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.41/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.61  thf('3', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.41/0.61      inference('simplify', [status(thm)], ['2'])).
% 0.41/0.61  thf(redefinition_r1_ordinal1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.41/0.61       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.41/0.61  thf('4', plain,
% 0.41/0.61      (![X47 : $i, X48 : $i]:
% 0.41/0.61         (~ (v3_ordinal1 @ X47)
% 0.41/0.61          | ~ (v3_ordinal1 @ X48)
% 0.41/0.61          | (r1_ordinal1 @ X47 @ X48)
% 0.41/0.61          | ~ (r1_tarski @ X47 @ X48))),
% 0.41/0.61      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.41/0.61  thf('5', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((r1_ordinal1 @ X0 @ X0) | ~ (v3_ordinal1 @ X0) | ~ (v3_ordinal1 @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['3', '4'])).
% 0.41/0.61  thf('6', plain,
% 0.41/0.61      (![X0 : $i]: (~ (v3_ordinal1 @ X0) | (r1_ordinal1 @ X0 @ X0))),
% 0.41/0.61      inference('simplify', [status(thm)], ['5'])).
% 0.41/0.61  thf('7', plain,
% 0.41/0.61      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('8', plain,
% 0.41/0.61      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.41/0.61      inference('split', [status(esa)], ['7'])).
% 0.41/0.61  thf(l1_zfmisc_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.41/0.61  thf('9', plain,
% 0.41/0.61      (![X39 : $i, X41 : $i]:
% 0.41/0.61         ((r1_tarski @ (k1_tarski @ X39) @ X41) | ~ (r2_hidden @ X39 @ X41))),
% 0.41/0.61      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.41/0.61  thf('10', plain,
% 0.41/0.61      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B))
% 0.41/0.61         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['8', '9'])).
% 0.41/0.61  thf('11', plain, ((v3_ordinal1 @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(connectedness_r1_ordinal1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.41/0.61       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 0.41/0.61  thf('12', plain,
% 0.41/0.61      (![X44 : $i, X45 : $i]:
% 0.41/0.61         (~ (v3_ordinal1 @ X44)
% 0.41/0.61          | ~ (v3_ordinal1 @ X45)
% 0.41/0.61          | (r1_ordinal1 @ X44 @ X45)
% 0.41/0.61          | (r1_ordinal1 @ X45 @ X44))),
% 0.41/0.61      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.41/0.61  thf('13', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((r1_ordinal1 @ X0 @ sk_A)
% 0.41/0.61          | (r1_ordinal1 @ sk_A @ X0)
% 0.41/0.61          | ~ (v3_ordinal1 @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['11', '12'])).
% 0.41/0.61  thf('14', plain,
% 0.41/0.61      (![X47 : $i, X48 : $i]:
% 0.41/0.61         (~ (v3_ordinal1 @ X47)
% 0.41/0.61          | ~ (v3_ordinal1 @ X48)
% 0.41/0.61          | (r1_tarski @ X47 @ X48)
% 0.41/0.61          | ~ (r1_ordinal1 @ X47 @ X48))),
% 0.41/0.61      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.41/0.61  thf('15', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (v3_ordinal1 @ X0)
% 0.41/0.61          | (r1_ordinal1 @ sk_A @ X0)
% 0.41/0.61          | (r1_tarski @ X0 @ sk_A)
% 0.41/0.61          | ~ (v3_ordinal1 @ sk_A)
% 0.41/0.61          | ~ (v3_ordinal1 @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['13', '14'])).
% 0.41/0.61  thf('16', plain, ((v3_ordinal1 @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('17', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (v3_ordinal1 @ X0)
% 0.41/0.61          | (r1_ordinal1 @ sk_A @ X0)
% 0.41/0.61          | (r1_tarski @ X0 @ sk_A)
% 0.41/0.61          | ~ (v3_ordinal1 @ X0))),
% 0.41/0.61      inference('demod', [status(thm)], ['15', '16'])).
% 0.41/0.61  thf('18', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((r1_tarski @ X0 @ sk_A)
% 0.41/0.61          | (r1_ordinal1 @ sk_A @ X0)
% 0.41/0.61          | ~ (v3_ordinal1 @ X0))),
% 0.41/0.61      inference('simplify', [status(thm)], ['17'])).
% 0.41/0.61  thf('19', plain,
% 0.41/0.61      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.41/0.61      inference('split', [status(esa)], ['7'])).
% 0.41/0.61  thf(t7_ordinal1, axiom,
% 0.41/0.61    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.61  thf('20', plain,
% 0.41/0.61      (![X53 : $i, X54 : $i]:
% 0.41/0.61         (~ (r2_hidden @ X53 @ X54) | ~ (r1_tarski @ X54 @ X53))),
% 0.41/0.61      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.41/0.61  thf('21', plain,
% 0.41/0.61      ((~ (r1_tarski @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['19', '20'])).
% 0.41/0.61  thf('22', plain,
% 0.41/0.61      (((~ (v3_ordinal1 @ sk_B) | (r1_ordinal1 @ sk_A @ sk_B)))
% 0.41/0.61         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['18', '21'])).
% 0.41/0.61  thf('23', plain, ((v3_ordinal1 @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('24', plain,
% 0.41/0.61      (((r1_ordinal1 @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.41/0.61      inference('demod', [status(thm)], ['22', '23'])).
% 0.41/0.61  thf('25', plain,
% 0.41/0.61      (![X47 : $i, X48 : $i]:
% 0.41/0.61         (~ (v3_ordinal1 @ X47)
% 0.41/0.61          | ~ (v3_ordinal1 @ X48)
% 0.41/0.61          | (r1_tarski @ X47 @ X48)
% 0.41/0.61          | ~ (r1_ordinal1 @ X47 @ X48))),
% 0.41/0.61      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.41/0.61  thf('26', plain,
% 0.41/0.61      ((((r1_tarski @ sk_A @ sk_B)
% 0.41/0.61         | ~ (v3_ordinal1 @ sk_B)
% 0.41/0.61         | ~ (v3_ordinal1 @ sk_A))) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['24', '25'])).
% 0.41/0.61  thf('27', plain, ((v3_ordinal1 @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('28', plain, ((v3_ordinal1 @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('29', plain,
% 0.41/0.61      (((r1_tarski @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.41/0.61      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.41/0.61  thf(t8_xboole_1, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.41/0.61       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.41/0.61  thf('30', plain,
% 0.41/0.61      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.41/0.61         (~ (r1_tarski @ X8 @ X9)
% 0.41/0.61          | ~ (r1_tarski @ X10 @ X9)
% 0.41/0.61          | (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 0.41/0.61      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.41/0.61  thf('31', plain,
% 0.41/0.61      ((![X0 : $i]:
% 0.41/0.61          ((r1_tarski @ (k2_xboole_0 @ sk_A @ X0) @ sk_B)
% 0.41/0.61           | ~ (r1_tarski @ X0 @ sk_B)))
% 0.41/0.61         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['29', '30'])).
% 0.41/0.61  thf('32', plain,
% 0.41/0.61      (((r1_tarski @ (k2_xboole_0 @ sk_A @ (k1_tarski @ sk_A)) @ sk_B))
% 0.41/0.61         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['10', '31'])).
% 0.41/0.61  thf(d1_ordinal1, axiom,
% 0.41/0.61    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.41/0.61  thf('33', plain,
% 0.41/0.61      (![X46 : $i]:
% 0.41/0.61         ((k1_ordinal1 @ X46) = (k2_xboole_0 @ X46 @ (k1_tarski @ X46)))),
% 0.41/0.61      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.41/0.61  thf('34', plain,
% 0.41/0.61      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.41/0.61         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.41/0.61      inference('demod', [status(thm)], ['32', '33'])).
% 0.41/0.61  thf(t29_ordinal1, axiom,
% 0.41/0.61    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 0.41/0.61  thf('35', plain,
% 0.41/0.61      (![X52 : $i]:
% 0.41/0.61         ((v3_ordinal1 @ (k1_ordinal1 @ X52)) | ~ (v3_ordinal1 @ X52))),
% 0.41/0.61      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.41/0.61  thf('36', plain,
% 0.41/0.61      (![X52 : $i]:
% 0.41/0.61         ((v3_ordinal1 @ (k1_ordinal1 @ X52)) | ~ (v3_ordinal1 @ X52))),
% 0.41/0.61      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.41/0.61  thf('37', plain,
% 0.41/0.61      (![X44 : $i, X45 : $i]:
% 0.41/0.61         (~ (v3_ordinal1 @ X44)
% 0.41/0.61          | ~ (v3_ordinal1 @ X45)
% 0.41/0.61          | (r1_ordinal1 @ X44 @ X45)
% 0.41/0.61          | (r1_ordinal1 @ X45 @ X44))),
% 0.41/0.61      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.41/0.61  thf('38', plain,
% 0.41/0.61      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.41/0.61         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.61      inference('split', [status(esa)], ['0'])).
% 0.41/0.61  thf('39', plain,
% 0.41/0.61      ((((r1_ordinal1 @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.41/0.61         | ~ (v3_ordinal1 @ sk_B)
% 0.41/0.61         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.41/0.61         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['37', '38'])).
% 0.41/0.61  thf('40', plain, ((v3_ordinal1 @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('41', plain,
% 0.41/0.61      ((((r1_ordinal1 @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.41/0.61         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.41/0.61         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.61      inference('demod', [status(thm)], ['39', '40'])).
% 0.41/0.61  thf('42', plain,
% 0.41/0.61      (((~ (v3_ordinal1 @ sk_A) | (r1_ordinal1 @ sk_B @ (k1_ordinal1 @ sk_A))))
% 0.41/0.61         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['36', '41'])).
% 0.41/0.61  thf('43', plain, ((v3_ordinal1 @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('44', plain,
% 0.41/0.61      (((r1_ordinal1 @ sk_B @ (k1_ordinal1 @ sk_A)))
% 0.41/0.61         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.61      inference('demod', [status(thm)], ['42', '43'])).
% 0.41/0.61  thf('45', plain,
% 0.41/0.61      (![X47 : $i, X48 : $i]:
% 0.41/0.61         (~ (v3_ordinal1 @ X47)
% 0.41/0.61          | ~ (v3_ordinal1 @ X48)
% 0.41/0.61          | (r1_tarski @ X47 @ X48)
% 0.41/0.61          | ~ (r1_ordinal1 @ X47 @ X48))),
% 0.41/0.61      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.41/0.61  thf('46', plain,
% 0.41/0.61      ((((r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.41/0.61         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))
% 0.41/0.61         | ~ (v3_ordinal1 @ sk_B)))
% 0.41/0.61         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['44', '45'])).
% 0.41/0.61  thf('47', plain, ((v3_ordinal1 @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('48', plain,
% 0.41/0.61      ((((r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.41/0.61         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.41/0.61         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.61      inference('demod', [status(thm)], ['46', '47'])).
% 0.41/0.61  thf('49', plain,
% 0.41/0.61      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A))))
% 0.41/0.61         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['35', '48'])).
% 0.41/0.61  thf('50', plain, ((v3_ordinal1 @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('51', plain,
% 0.41/0.61      (((r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A)))
% 0.41/0.61         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.61      inference('demod', [status(thm)], ['49', '50'])).
% 0.41/0.61  thf('52', plain,
% 0.41/0.61      (![X0 : $i, X2 : $i]:
% 0.41/0.61         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.41/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.61  thf('53', plain,
% 0.41/0.61      (((~ (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.41/0.61         | ((k1_ordinal1 @ sk_A) = (sk_B))))
% 0.41/0.61         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['51', '52'])).
% 0.41/0.61  thf('54', plain,
% 0.41/0.61      ((((k1_ordinal1 @ sk_A) = (sk_B)))
% 0.41/0.61         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) & 
% 0.41/0.61             ((r2_hidden @ sk_A @ sk_B)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['34', '53'])).
% 0.41/0.61  thf('55', plain,
% 0.41/0.61      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.41/0.61         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.61      inference('split', [status(esa)], ['0'])).
% 0.41/0.61  thf('56', plain,
% 0.41/0.61      ((~ (r1_ordinal1 @ sk_B @ sk_B))
% 0.41/0.61         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) & 
% 0.41/0.61             ((r2_hidden @ sk_A @ sk_B)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['54', '55'])).
% 0.41/0.61  thf('57', plain,
% 0.41/0.61      ((~ (v3_ordinal1 @ sk_B))
% 0.41/0.61         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) & 
% 0.41/0.61             ((r2_hidden @ sk_A @ sk_B)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['6', '56'])).
% 0.41/0.61  thf('58', plain, ((v3_ordinal1 @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('59', plain,
% 0.41/0.61      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 0.41/0.61       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.41/0.61      inference('demod', [status(thm)], ['57', '58'])).
% 0.41/0.61  thf('60', plain,
% 0.41/0.61      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 0.41/0.61       ((r2_hidden @ sk_A @ sk_B))),
% 0.41/0.61      inference('split', [status(esa)], ['7'])).
% 0.41/0.61  thf('61', plain,
% 0.41/0.61      (![X52 : $i]:
% 0.41/0.61         ((v3_ordinal1 @ (k1_ordinal1 @ X52)) | ~ (v3_ordinal1 @ X52))),
% 0.41/0.61      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.41/0.61  thf('62', plain,
% 0.41/0.61      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.41/0.61         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.61      inference('split', [status(esa)], ['7'])).
% 0.41/0.61  thf('63', plain,
% 0.41/0.61      (![X47 : $i, X48 : $i]:
% 0.41/0.61         (~ (v3_ordinal1 @ X47)
% 0.41/0.61          | ~ (v3_ordinal1 @ X48)
% 0.41/0.61          | (r1_tarski @ X47 @ X48)
% 0.41/0.61          | ~ (r1_ordinal1 @ X47 @ X48))),
% 0.41/0.61      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.41/0.61  thf('64', plain,
% 0.41/0.61      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.41/0.61         | ~ (v3_ordinal1 @ sk_B)
% 0.41/0.61         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.41/0.61         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['62', '63'])).
% 0.41/0.61  thf('65', plain, ((v3_ordinal1 @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('66', plain,
% 0.41/0.61      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.41/0.61         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.41/0.61         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.61      inference('demod', [status(thm)], ['64', '65'])).
% 0.41/0.61  thf('67', plain,
% 0.41/0.61      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 0.41/0.61         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['61', '66'])).
% 0.41/0.61  thf('68', plain, ((v3_ordinal1 @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('69', plain,
% 0.41/0.61      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.41/0.61         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.61      inference('demod', [status(thm)], ['67', '68'])).
% 0.41/0.61  thf(t69_enumset1, axiom,
% 0.41/0.61    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.41/0.61  thf('70', plain,
% 0.41/0.61      (![X11 : $i]: ((k2_tarski @ X11 @ X11) = (k1_tarski @ X11))),
% 0.41/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.41/0.61  thf('71', plain,
% 0.41/0.61      (![X46 : $i]:
% 0.41/0.61         ((k1_ordinal1 @ X46) = (k2_xboole_0 @ X46 @ (k1_tarski @ X46)))),
% 0.41/0.61      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.41/0.61  thf('72', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((k1_ordinal1 @ X0) = (k2_xboole_0 @ X0 @ (k2_tarski @ X0 @ X0)))),
% 0.41/0.61      inference('sup+', [status(thm)], ['70', '71'])).
% 0.41/0.61  thf(t11_xboole_1, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.41/0.61  thf('73', plain,
% 0.41/0.61      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.41/0.61         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.41/0.61      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.41/0.61  thf('74', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         (~ (r1_tarski @ (k1_ordinal1 @ X0) @ X1) | (r1_tarski @ X0 @ X1))),
% 0.41/0.61      inference('sup-', [status(thm)], ['72', '73'])).
% 0.41/0.61  thf('75', plain,
% 0.41/0.61      (((r1_tarski @ sk_A @ sk_B))
% 0.41/0.61         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['69', '74'])).
% 0.41/0.61  thf(t24_ordinal1, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( v3_ordinal1 @ A ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( v3_ordinal1 @ B ) =>
% 0.41/0.61           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.41/0.61                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.41/0.61  thf('76', plain,
% 0.41/0.61      (![X50 : $i, X51 : $i]:
% 0.41/0.61         (~ (v3_ordinal1 @ X50)
% 0.41/0.61          | (r2_hidden @ X51 @ X50)
% 0.41/0.61          | ((X51) = (X50))
% 0.41/0.61          | (r2_hidden @ X50 @ X51)
% 0.41/0.61          | ~ (v3_ordinal1 @ X51))),
% 0.41/0.61      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.41/0.61  thf('77', plain,
% 0.41/0.61      (![X53 : $i, X54 : $i]:
% 0.41/0.61         (~ (r2_hidden @ X53 @ X54) | ~ (r1_tarski @ X54 @ X53))),
% 0.41/0.61      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.41/0.61  thf('78', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         (~ (v3_ordinal1 @ X1)
% 0.41/0.61          | (r2_hidden @ X0 @ X1)
% 0.41/0.61          | ((X1) = (X0))
% 0.41/0.61          | ~ (v3_ordinal1 @ X0)
% 0.41/0.61          | ~ (r1_tarski @ X0 @ X1))),
% 0.41/0.61      inference('sup-', [status(thm)], ['76', '77'])).
% 0.41/0.61  thf('79', plain,
% 0.41/0.61      (((~ (v3_ordinal1 @ sk_A)
% 0.41/0.61         | ((sk_B) = (sk_A))
% 0.41/0.61         | (r2_hidden @ sk_A @ sk_B)
% 0.41/0.61         | ~ (v3_ordinal1 @ sk_B)))
% 0.41/0.61         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['75', '78'])).
% 0.41/0.61  thf('80', plain, ((v3_ordinal1 @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('81', plain, ((v3_ordinal1 @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('82', plain,
% 0.41/0.61      (((((sk_B) = (sk_A)) | (r2_hidden @ sk_A @ sk_B)))
% 0.41/0.61         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.61      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.41/0.61  thf('83', plain,
% 0.41/0.61      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.41/0.61      inference('split', [status(esa)], ['0'])).
% 0.41/0.61  thf('84', plain,
% 0.41/0.61      ((((sk_B) = (sk_A)))
% 0.41/0.61         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.41/0.61             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['82', '83'])).
% 0.41/0.61  thf('85', plain,
% 0.41/0.61      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.41/0.61         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.61      inference('demod', [status(thm)], ['67', '68'])).
% 0.41/0.61  thf('86', plain,
% 0.41/0.61      (![X0 : $i, X2 : $i]:
% 0.41/0.61         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.41/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.61  thf('87', plain,
% 0.41/0.61      (((~ (r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.41/0.61         | ((sk_B) = (k1_ordinal1 @ sk_A))))
% 0.41/0.61         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['85', '86'])).
% 0.41/0.61  thf('88', plain,
% 0.41/0.61      (((~ (r1_tarski @ sk_A @ (k1_ordinal1 @ sk_A))
% 0.41/0.61         | ((sk_B) = (k1_ordinal1 @ sk_A))))
% 0.41/0.61         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.41/0.61             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['84', '87'])).
% 0.41/0.61  thf('89', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((k1_ordinal1 @ X0) = (k2_xboole_0 @ X0 @ (k2_tarski @ X0 @ X0)))),
% 0.41/0.61      inference('sup+', [status(thm)], ['70', '71'])).
% 0.41/0.61  thf(t7_xboole_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.41/0.61  thf('90', plain,
% 0.41/0.61      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.41/0.61      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.41/0.61  thf('91', plain, (![X0 : $i]: (r1_tarski @ X0 @ (k1_ordinal1 @ X0))),
% 0.41/0.61      inference('sup+', [status(thm)], ['89', '90'])).
% 0.41/0.61  thf('92', plain,
% 0.41/0.61      ((((sk_B) = (sk_A)))
% 0.41/0.61         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.41/0.61             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['82', '83'])).
% 0.41/0.61  thf('93', plain,
% 0.41/0.61      ((((sk_A) = (k1_ordinal1 @ sk_A)))
% 0.41/0.61         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.41/0.61             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.61      inference('demod', [status(thm)], ['88', '91', '92'])).
% 0.41/0.61  thf(t14_ordinal1, axiom, (![A:$i]: ( ( A ) != ( k1_ordinal1 @ A ) ))).
% 0.41/0.61  thf('94', plain, (![X49 : $i]: ((X49) != (k1_ordinal1 @ X49))),
% 0.41/0.61      inference('cnf', [status(esa)], [t14_ordinal1])).
% 0.41/0.61  thf('95', plain,
% 0.41/0.61      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 0.41/0.61       ((r2_hidden @ sk_A @ sk_B))),
% 0.41/0.61      inference('simplify_reflect-', [status(thm)], ['93', '94'])).
% 0.41/0.61  thf('96', plain, ($false),
% 0.41/0.61      inference('sat_resolution*', [status(thm)], ['1', '59', '60', '95'])).
% 0.41/0.61  
% 0.41/0.61  % SZS output end Refutation
% 0.41/0.61  
% 0.41/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
