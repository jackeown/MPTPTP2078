%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6mJBzn7NzI

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:57 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 246 expanded)
%              Number of leaves         :   24 (  76 expanded)
%              Depth                    :   17
%              Number of atoms          :  841 (2003 expanded)
%              Number of equality atoms :   24 (  40 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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

thf('2',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('4',plain,(
    ! [X26: $i,X28: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X26 ) @ X28 )
      | ~ ( r2_hidden @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('5',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v3_ordinal1 @ X31 )
      | ~ ( v3_ordinal1 @ X32 )
      | ( r1_ordinal1 @ X31 @ X32 )
      | ( r1_ordinal1 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( v3_ordinal1 @ X34 )
      | ~ ( v3_ordinal1 @ X35 )
      | ( r1_tarski @ X34 @ X35 )
      | ~ ( r1_ordinal1 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('15',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ X40 @ X41 )
      | ~ ( r1_tarski @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('16',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( v3_ordinal1 @ X34 )
      | ~ ( v3_ordinal1 @ X35 )
      | ( r1_tarski @ X34 @ X35 )
      | ~ ( r1_ordinal1 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('21',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('25',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B )
        | ~ ( r1_tarski @ X0 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_A ) ) @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['5','26'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('28',plain,(
    ! [X33: $i] :
      ( ( k1_ordinal1 @ X33 )
      = ( k2_xboole_0 @ X33 @ ( k1_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('29',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('30',plain,(
    ! [X39: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X39 ) )
      | ~ ( v3_ordinal1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('31',plain,(
    ! [X39: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X39 ) )
      | ~ ( v3_ordinal1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('32',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v3_ordinal1 @ X31 )
      | ~ ( v3_ordinal1 @ X32 )
      | ( r1_ordinal1 @ X31 @ X32 )
      | ( r1_ordinal1 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('33',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,
    ( ( ( r1_ordinal1 @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( r1_ordinal1 @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_ordinal1 @ sk_B @ ( k1_ordinal1 @ sk_A ) ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( r1_ordinal1 @ sk_B @ ( k1_ordinal1 @ sk_A ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( v3_ordinal1 @ X34 )
      | ~ ( v3_ordinal1 @ X35 )
      | ( r1_tarski @ X34 @ X35 )
      | ~ ( r1_ordinal1 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('41',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['30','43'])).

thf('45',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['44','45'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('47',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('48',plain,
    ( ( ~ ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ( ( k1_ordinal1 @ sk_A )
        = sk_B ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k1_ordinal1 @ sk_A )
      = sk_B )
   <= ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','48'])).

thf('50',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('51',plain,
    ( ~ ( r1_ordinal1 @ sk_B @ sk_B )
   <= ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v3_ordinal1 @ X31 )
      | ~ ( v3_ordinal1 @ X32 )
      | ( r1_ordinal1 @ X31 @ X32 )
      | ( r1_ordinal1 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_B )
      | ( r1_ordinal1 @ sk_B @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r1_ordinal1 @ sk_B @ sk_B ) ),
    inference(eq_fact,[status(thm)],['54'])).

thf('56',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    r1_ordinal1 @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['51','57'])).

thf('59',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('60',plain,(
    ! [X39: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X39 ) )
      | ~ ( v3_ordinal1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('61',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('62',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( v3_ordinal1 @ X34 )
      | ~ ( v3_ordinal1 @ X35 )
      | ( r1_tarski @ X34 @ X35 )
      | ~ ( r1_ordinal1 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('63',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('67',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['66','67'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('69',plain,(
    ! [X11: $i] :
      ( ( k2_tarski @ X11 @ X11 )
      = ( k1_tarski @ X11 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('70',plain,(
    ! [X33: $i] :
      ( ( k1_ordinal1 @ X33 )
      = ( k2_xboole_0 @ X33 @ ( k1_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k1_ordinal1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('72',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X1 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['68','73'])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('75',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v3_ordinal1 @ X37 )
      | ( r2_hidden @ X38 @ X37 )
      | ( X38 = X37 )
      | ( r2_hidden @ X37 @ X38 )
      | ~ ( v3_ordinal1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('76',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ X40 @ X41 )
      | ~ ( r1_tarski @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( sk_B = sk_A )
      | ( r2_hidden @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( ( sk_B = sk_A )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('83',plain,
    ( ( sk_B = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('85',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('86',plain,
    ( ( ~ ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ~ ( r1_tarski @ sk_A @ ( k1_ordinal1 @ sk_A ) )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k1_ordinal1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('89',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( sk_B = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('92',plain,
    ( ( sk_A
      = ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['87','90','91'])).

thf(t14_ordinal1,axiom,(
    ! [A: $i] :
      ( A
     != ( k1_ordinal1 @ A ) ) )).

thf('93',plain,(
    ! [X36: $i] :
      ( X36
     != ( k1_ordinal1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t14_ordinal1])).

thf('94',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['92','93'])).

thf('95',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','58','59','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6mJBzn7NzI
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:55:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.43/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.62  % Solved by: fo/fo7.sh
% 0.43/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.62  % done 325 iterations in 0.164s
% 0.43/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.62  % SZS output start Refutation
% 0.43/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.62  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.43/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.43/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.62  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.43/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.62  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.43/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.43/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.43/0.62  thf(t33_ordinal1, conjecture,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( v3_ordinal1 @ A ) =>
% 0.43/0.62       ( ![B:$i]:
% 0.43/0.62         ( ( v3_ordinal1 @ B ) =>
% 0.43/0.62           ( ( r2_hidden @ A @ B ) <=>
% 0.43/0.62             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 0.43/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.62    (~( ![A:$i]:
% 0.43/0.62        ( ( v3_ordinal1 @ A ) =>
% 0.43/0.62          ( ![B:$i]:
% 0.43/0.62            ( ( v3_ordinal1 @ B ) =>
% 0.43/0.62              ( ( r2_hidden @ A @ B ) <=>
% 0.43/0.62                ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ) )),
% 0.43/0.62    inference('cnf.neg', [status(esa)], [t33_ordinal1])).
% 0.43/0.62  thf('0', plain,
% 0.43/0.62      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.43/0.62        | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('1', plain,
% 0.43/0.62      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 0.43/0.62       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.43/0.62      inference('split', [status(esa)], ['0'])).
% 0.43/0.62  thf('2', plain,
% 0.43/0.62      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('3', plain,
% 0.43/0.62      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.43/0.62      inference('split', [status(esa)], ['2'])).
% 0.43/0.62  thf(l1_zfmisc_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.43/0.62  thf('4', plain,
% 0.43/0.62      (![X26 : $i, X28 : $i]:
% 0.43/0.62         ((r1_tarski @ (k1_tarski @ X26) @ X28) | ~ (r2_hidden @ X26 @ X28))),
% 0.43/0.62      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.43/0.62  thf('5', plain,
% 0.43/0.62      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B))
% 0.43/0.62         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.43/0.62  thf('6', plain, ((v3_ordinal1 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(connectedness_r1_ordinal1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.43/0.62       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 0.43/0.62  thf('7', plain,
% 0.43/0.62      (![X31 : $i, X32 : $i]:
% 0.43/0.62         (~ (v3_ordinal1 @ X31)
% 0.43/0.62          | ~ (v3_ordinal1 @ X32)
% 0.43/0.62          | (r1_ordinal1 @ X31 @ X32)
% 0.43/0.62          | (r1_ordinal1 @ X32 @ X31))),
% 0.43/0.62      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.43/0.62  thf('8', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((r1_ordinal1 @ X0 @ sk_A)
% 0.43/0.62          | (r1_ordinal1 @ sk_A @ X0)
% 0.43/0.62          | ~ (v3_ordinal1 @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['6', '7'])).
% 0.43/0.62  thf(redefinition_r1_ordinal1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.43/0.62       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.43/0.62  thf('9', plain,
% 0.43/0.62      (![X34 : $i, X35 : $i]:
% 0.43/0.62         (~ (v3_ordinal1 @ X34)
% 0.43/0.62          | ~ (v3_ordinal1 @ X35)
% 0.43/0.62          | (r1_tarski @ X34 @ X35)
% 0.43/0.62          | ~ (r1_ordinal1 @ X34 @ X35))),
% 0.43/0.62      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.43/0.62  thf('10', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (~ (v3_ordinal1 @ X0)
% 0.43/0.62          | (r1_ordinal1 @ sk_A @ X0)
% 0.43/0.62          | (r1_tarski @ X0 @ sk_A)
% 0.43/0.62          | ~ (v3_ordinal1 @ sk_A)
% 0.43/0.62          | ~ (v3_ordinal1 @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['8', '9'])).
% 0.43/0.62  thf('11', plain, ((v3_ordinal1 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('12', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (~ (v3_ordinal1 @ X0)
% 0.43/0.62          | (r1_ordinal1 @ sk_A @ X0)
% 0.43/0.62          | (r1_tarski @ X0 @ sk_A)
% 0.43/0.62          | ~ (v3_ordinal1 @ X0))),
% 0.43/0.62      inference('demod', [status(thm)], ['10', '11'])).
% 0.43/0.62  thf('13', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((r1_tarski @ X0 @ sk_A)
% 0.43/0.62          | (r1_ordinal1 @ sk_A @ X0)
% 0.43/0.62          | ~ (v3_ordinal1 @ X0))),
% 0.43/0.62      inference('simplify', [status(thm)], ['12'])).
% 0.43/0.62  thf('14', plain,
% 0.43/0.62      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.43/0.62      inference('split', [status(esa)], ['2'])).
% 0.43/0.62  thf(t7_ordinal1, axiom,
% 0.43/0.62    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.43/0.62  thf('15', plain,
% 0.43/0.62      (![X40 : $i, X41 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X40 @ X41) | ~ (r1_tarski @ X41 @ X40))),
% 0.43/0.62      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.43/0.62  thf('16', plain,
% 0.43/0.62      ((~ (r1_tarski @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['14', '15'])).
% 0.43/0.62  thf('17', plain,
% 0.43/0.62      (((~ (v3_ordinal1 @ sk_B) | (r1_ordinal1 @ sk_A @ sk_B)))
% 0.43/0.62         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['13', '16'])).
% 0.43/0.62  thf('18', plain, ((v3_ordinal1 @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('19', plain,
% 0.43/0.62      (((r1_ordinal1 @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.43/0.62      inference('demod', [status(thm)], ['17', '18'])).
% 0.43/0.62  thf('20', plain,
% 0.43/0.62      (![X34 : $i, X35 : $i]:
% 0.43/0.62         (~ (v3_ordinal1 @ X34)
% 0.43/0.62          | ~ (v3_ordinal1 @ X35)
% 0.43/0.62          | (r1_tarski @ X34 @ X35)
% 0.43/0.62          | ~ (r1_ordinal1 @ X34 @ X35))),
% 0.43/0.62      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.43/0.62  thf('21', plain,
% 0.43/0.62      ((((r1_tarski @ sk_A @ sk_B)
% 0.43/0.62         | ~ (v3_ordinal1 @ sk_B)
% 0.43/0.62         | ~ (v3_ordinal1 @ sk_A))) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['19', '20'])).
% 0.43/0.62  thf('22', plain, ((v3_ordinal1 @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('23', plain, ((v3_ordinal1 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('24', plain,
% 0.43/0.62      (((r1_tarski @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.43/0.62      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.43/0.62  thf(t8_xboole_1, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.43/0.62       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.43/0.62  thf('25', plain,
% 0.43/0.62      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.43/0.62         (~ (r1_tarski @ X8 @ X9)
% 0.43/0.62          | ~ (r1_tarski @ X10 @ X9)
% 0.43/0.62          | (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 0.43/0.62      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.43/0.62  thf('26', plain,
% 0.43/0.62      ((![X0 : $i]:
% 0.43/0.62          ((r1_tarski @ (k2_xboole_0 @ sk_A @ X0) @ sk_B)
% 0.43/0.62           | ~ (r1_tarski @ X0 @ sk_B)))
% 0.43/0.62         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['24', '25'])).
% 0.43/0.62  thf('27', plain,
% 0.43/0.62      (((r1_tarski @ (k2_xboole_0 @ sk_A @ (k1_tarski @ sk_A)) @ sk_B))
% 0.43/0.62         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['5', '26'])).
% 0.43/0.62  thf(d1_ordinal1, axiom,
% 0.43/0.62    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.43/0.62  thf('28', plain,
% 0.43/0.62      (![X33 : $i]:
% 0.43/0.62         ((k1_ordinal1 @ X33) = (k2_xboole_0 @ X33 @ (k1_tarski @ X33)))),
% 0.43/0.62      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.43/0.62  thf('29', plain,
% 0.43/0.62      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.43/0.62         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.43/0.62      inference('demod', [status(thm)], ['27', '28'])).
% 0.43/0.62  thf(t29_ordinal1, axiom,
% 0.43/0.62    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 0.43/0.62  thf('30', plain,
% 0.43/0.62      (![X39 : $i]:
% 0.43/0.62         ((v3_ordinal1 @ (k1_ordinal1 @ X39)) | ~ (v3_ordinal1 @ X39))),
% 0.43/0.62      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.43/0.62  thf('31', plain,
% 0.43/0.62      (![X39 : $i]:
% 0.43/0.62         ((v3_ordinal1 @ (k1_ordinal1 @ X39)) | ~ (v3_ordinal1 @ X39))),
% 0.43/0.62      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.43/0.62  thf('32', plain,
% 0.43/0.62      (![X31 : $i, X32 : $i]:
% 0.43/0.62         (~ (v3_ordinal1 @ X31)
% 0.43/0.62          | ~ (v3_ordinal1 @ X32)
% 0.43/0.62          | (r1_ordinal1 @ X31 @ X32)
% 0.43/0.62          | (r1_ordinal1 @ X32 @ X31))),
% 0.43/0.62      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.43/0.62  thf('33', plain,
% 0.43/0.62      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.43/0.62         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.43/0.62      inference('split', [status(esa)], ['0'])).
% 0.43/0.62  thf('34', plain,
% 0.43/0.62      ((((r1_ordinal1 @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.43/0.62         | ~ (v3_ordinal1 @ sk_B)
% 0.43/0.62         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.43/0.62         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['32', '33'])).
% 0.43/0.62  thf('35', plain, ((v3_ordinal1 @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('36', plain,
% 0.43/0.62      ((((r1_ordinal1 @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.43/0.62         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.43/0.62         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.43/0.62      inference('demod', [status(thm)], ['34', '35'])).
% 0.43/0.62  thf('37', plain,
% 0.43/0.62      (((~ (v3_ordinal1 @ sk_A) | (r1_ordinal1 @ sk_B @ (k1_ordinal1 @ sk_A))))
% 0.43/0.62         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['31', '36'])).
% 0.43/0.62  thf('38', plain, ((v3_ordinal1 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('39', plain,
% 0.43/0.62      (((r1_ordinal1 @ sk_B @ (k1_ordinal1 @ sk_A)))
% 0.43/0.62         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.43/0.62      inference('demod', [status(thm)], ['37', '38'])).
% 0.43/0.62  thf('40', plain,
% 0.43/0.62      (![X34 : $i, X35 : $i]:
% 0.43/0.62         (~ (v3_ordinal1 @ X34)
% 0.43/0.62          | ~ (v3_ordinal1 @ X35)
% 0.43/0.62          | (r1_tarski @ X34 @ X35)
% 0.43/0.62          | ~ (r1_ordinal1 @ X34 @ X35))),
% 0.43/0.62      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.43/0.62  thf('41', plain,
% 0.43/0.62      ((((r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.43/0.62         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))
% 0.43/0.62         | ~ (v3_ordinal1 @ sk_B)))
% 0.43/0.62         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['39', '40'])).
% 0.43/0.62  thf('42', plain, ((v3_ordinal1 @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('43', plain,
% 0.43/0.62      ((((r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.43/0.62         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.43/0.62         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.43/0.62      inference('demod', [status(thm)], ['41', '42'])).
% 0.43/0.62  thf('44', plain,
% 0.43/0.62      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A))))
% 0.43/0.62         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['30', '43'])).
% 0.43/0.62  thf('45', plain, ((v3_ordinal1 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('46', plain,
% 0.43/0.62      (((r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A)))
% 0.43/0.62         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.43/0.62      inference('demod', [status(thm)], ['44', '45'])).
% 0.43/0.62  thf(d10_xboole_0, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.43/0.62  thf('47', plain,
% 0.43/0.62      (![X0 : $i, X2 : $i]:
% 0.43/0.62         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.43/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.43/0.62  thf('48', plain,
% 0.43/0.62      (((~ (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.43/0.62         | ((k1_ordinal1 @ sk_A) = (sk_B))))
% 0.43/0.62         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['46', '47'])).
% 0.43/0.62  thf('49', plain,
% 0.43/0.62      ((((k1_ordinal1 @ sk_A) = (sk_B)))
% 0.43/0.62         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) & 
% 0.43/0.62             ((r2_hidden @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['29', '48'])).
% 0.43/0.62  thf('50', plain,
% 0.43/0.62      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.43/0.62         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.43/0.62      inference('split', [status(esa)], ['0'])).
% 0.43/0.62  thf('51', plain,
% 0.43/0.62      ((~ (r1_ordinal1 @ sk_B @ sk_B))
% 0.43/0.62         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) & 
% 0.43/0.62             ((r2_hidden @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['49', '50'])).
% 0.43/0.62  thf('52', plain, ((v3_ordinal1 @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('53', plain,
% 0.43/0.62      (![X31 : $i, X32 : $i]:
% 0.43/0.62         (~ (v3_ordinal1 @ X31)
% 0.43/0.62          | ~ (v3_ordinal1 @ X32)
% 0.43/0.62          | (r1_ordinal1 @ X31 @ X32)
% 0.43/0.62          | (r1_ordinal1 @ X32 @ X31))),
% 0.43/0.62      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.43/0.62  thf('54', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((r1_ordinal1 @ X0 @ sk_B)
% 0.43/0.62          | (r1_ordinal1 @ sk_B @ X0)
% 0.43/0.62          | ~ (v3_ordinal1 @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['52', '53'])).
% 0.43/0.62  thf('55', plain, ((~ (v3_ordinal1 @ sk_B) | (r1_ordinal1 @ sk_B @ sk_B))),
% 0.43/0.62      inference('eq_fact', [status(thm)], ['54'])).
% 0.43/0.62  thf('56', plain, ((v3_ordinal1 @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('57', plain, ((r1_ordinal1 @ sk_B @ sk_B)),
% 0.43/0.62      inference('demod', [status(thm)], ['55', '56'])).
% 0.43/0.62  thf('58', plain,
% 0.43/0.62      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 0.43/0.62       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.43/0.62      inference('demod', [status(thm)], ['51', '57'])).
% 0.43/0.62  thf('59', plain,
% 0.43/0.62      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 0.43/0.62       ((r2_hidden @ sk_A @ sk_B))),
% 0.43/0.62      inference('split', [status(esa)], ['2'])).
% 0.43/0.62  thf('60', plain,
% 0.43/0.62      (![X39 : $i]:
% 0.43/0.62         ((v3_ordinal1 @ (k1_ordinal1 @ X39)) | ~ (v3_ordinal1 @ X39))),
% 0.43/0.62      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.43/0.62  thf('61', plain,
% 0.43/0.62      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.43/0.62         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.43/0.62      inference('split', [status(esa)], ['2'])).
% 0.43/0.62  thf('62', plain,
% 0.43/0.62      (![X34 : $i, X35 : $i]:
% 0.43/0.62         (~ (v3_ordinal1 @ X34)
% 0.43/0.62          | ~ (v3_ordinal1 @ X35)
% 0.43/0.62          | (r1_tarski @ X34 @ X35)
% 0.43/0.62          | ~ (r1_ordinal1 @ X34 @ X35))),
% 0.43/0.62      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.43/0.62  thf('63', plain,
% 0.43/0.62      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.43/0.62         | ~ (v3_ordinal1 @ sk_B)
% 0.43/0.62         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.43/0.62         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['61', '62'])).
% 0.43/0.62  thf('64', plain, ((v3_ordinal1 @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('65', plain,
% 0.43/0.62      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.43/0.62         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.43/0.62         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.43/0.62      inference('demod', [status(thm)], ['63', '64'])).
% 0.43/0.62  thf('66', plain,
% 0.43/0.62      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 0.43/0.62         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['60', '65'])).
% 0.43/0.62  thf('67', plain, ((v3_ordinal1 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('68', plain,
% 0.43/0.62      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.43/0.62         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.43/0.62      inference('demod', [status(thm)], ['66', '67'])).
% 0.43/0.62  thf(t69_enumset1, axiom,
% 0.43/0.62    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.43/0.62  thf('69', plain,
% 0.43/0.62      (![X11 : $i]: ((k2_tarski @ X11 @ X11) = (k1_tarski @ X11))),
% 0.43/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.43/0.62  thf('70', plain,
% 0.43/0.62      (![X33 : $i]:
% 0.43/0.62         ((k1_ordinal1 @ X33) = (k2_xboole_0 @ X33 @ (k1_tarski @ X33)))),
% 0.43/0.62      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.43/0.62  thf('71', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((k1_ordinal1 @ X0) = (k2_xboole_0 @ X0 @ (k2_tarski @ X0 @ X0)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['69', '70'])).
% 0.43/0.62  thf(t11_xboole_1, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.43/0.62  thf('72', plain,
% 0.43/0.62      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.43/0.62         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.43/0.62      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.43/0.62  thf('73', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (~ (r1_tarski @ (k1_ordinal1 @ X0) @ X1) | (r1_tarski @ X0 @ X1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['71', '72'])).
% 0.43/0.63  thf('74', plain,
% 0.43/0.63      (((r1_tarski @ sk_A @ sk_B))
% 0.43/0.63         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['68', '73'])).
% 0.43/0.63  thf(t24_ordinal1, axiom,
% 0.43/0.63    (![A:$i]:
% 0.43/0.63     ( ( v3_ordinal1 @ A ) =>
% 0.43/0.63       ( ![B:$i]:
% 0.43/0.63         ( ( v3_ordinal1 @ B ) =>
% 0.43/0.63           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.43/0.63                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.43/0.63  thf('75', plain,
% 0.43/0.63      (![X37 : $i, X38 : $i]:
% 0.43/0.63         (~ (v3_ordinal1 @ X37)
% 0.43/0.63          | (r2_hidden @ X38 @ X37)
% 0.43/0.63          | ((X38) = (X37))
% 0.43/0.63          | (r2_hidden @ X37 @ X38)
% 0.43/0.63          | ~ (v3_ordinal1 @ X38))),
% 0.43/0.63      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.43/0.63  thf('76', plain,
% 0.43/0.63      (![X40 : $i, X41 : $i]:
% 0.43/0.63         (~ (r2_hidden @ X40 @ X41) | ~ (r1_tarski @ X41 @ X40))),
% 0.43/0.63      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.43/0.63  thf('77', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i]:
% 0.43/0.63         (~ (v3_ordinal1 @ X1)
% 0.43/0.63          | (r2_hidden @ X0 @ X1)
% 0.43/0.63          | ((X1) = (X0))
% 0.43/0.63          | ~ (v3_ordinal1 @ X0)
% 0.43/0.63          | ~ (r1_tarski @ X0 @ X1))),
% 0.43/0.63      inference('sup-', [status(thm)], ['75', '76'])).
% 0.43/0.63  thf('78', plain,
% 0.43/0.63      (((~ (v3_ordinal1 @ sk_A)
% 0.43/0.63         | ((sk_B) = (sk_A))
% 0.43/0.63         | (r2_hidden @ sk_A @ sk_B)
% 0.43/0.63         | ~ (v3_ordinal1 @ sk_B)))
% 0.43/0.63         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['74', '77'])).
% 0.43/0.63  thf('79', plain, ((v3_ordinal1 @ sk_A)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('80', plain, ((v3_ordinal1 @ sk_B)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('81', plain,
% 0.43/0.63      (((((sk_B) = (sk_A)) | (r2_hidden @ sk_A @ sk_B)))
% 0.43/0.63         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.43/0.63      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.43/0.63  thf('82', plain,
% 0.43/0.63      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.43/0.63      inference('split', [status(esa)], ['0'])).
% 0.43/0.63  thf('83', plain,
% 0.43/0.63      ((((sk_B) = (sk_A)))
% 0.43/0.63         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.43/0.63             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['81', '82'])).
% 0.43/0.63  thf('84', plain,
% 0.43/0.63      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.43/0.63         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.43/0.63      inference('demod', [status(thm)], ['66', '67'])).
% 0.43/0.63  thf('85', plain,
% 0.43/0.63      (![X0 : $i, X2 : $i]:
% 0.43/0.63         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.43/0.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.43/0.63  thf('86', plain,
% 0.43/0.63      (((~ (r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.43/0.63         | ((sk_B) = (k1_ordinal1 @ sk_A))))
% 0.43/0.63         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['84', '85'])).
% 0.43/0.63  thf('87', plain,
% 0.43/0.63      (((~ (r1_tarski @ sk_A @ (k1_ordinal1 @ sk_A))
% 0.43/0.63         | ((sk_B) = (k1_ordinal1 @ sk_A))))
% 0.43/0.63         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.43/0.63             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['83', '86'])).
% 0.43/0.63  thf('88', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         ((k1_ordinal1 @ X0) = (k2_xboole_0 @ X0 @ (k2_tarski @ X0 @ X0)))),
% 0.43/0.63      inference('sup+', [status(thm)], ['69', '70'])).
% 0.43/0.63  thf(t7_xboole_1, axiom,
% 0.43/0.63    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.43/0.63  thf('89', plain,
% 0.43/0.63      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.43/0.63      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.43/0.63  thf('90', plain, (![X0 : $i]: (r1_tarski @ X0 @ (k1_ordinal1 @ X0))),
% 0.43/0.63      inference('sup+', [status(thm)], ['88', '89'])).
% 0.43/0.63  thf('91', plain,
% 0.43/0.63      ((((sk_B) = (sk_A)))
% 0.43/0.63         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.43/0.63             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['81', '82'])).
% 0.43/0.63  thf('92', plain,
% 0.43/0.63      ((((sk_A) = (k1_ordinal1 @ sk_A)))
% 0.43/0.63         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.43/0.63             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.43/0.63      inference('demod', [status(thm)], ['87', '90', '91'])).
% 0.43/0.63  thf(t14_ordinal1, axiom, (![A:$i]: ( ( A ) != ( k1_ordinal1 @ A ) ))).
% 0.43/0.63  thf('93', plain, (![X36 : $i]: ((X36) != (k1_ordinal1 @ X36))),
% 0.43/0.63      inference('cnf', [status(esa)], [t14_ordinal1])).
% 0.43/0.63  thf('94', plain,
% 0.43/0.63      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 0.43/0.63       ((r2_hidden @ sk_A @ sk_B))),
% 0.43/0.63      inference('simplify_reflect-', [status(thm)], ['92', '93'])).
% 0.43/0.63  thf('95', plain, ($false),
% 0.43/0.63      inference('sat_resolution*', [status(thm)], ['1', '58', '59', '94'])).
% 0.43/0.63  
% 0.43/0.63  % SZS output end Refutation
% 0.43/0.63  
% 0.50/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
