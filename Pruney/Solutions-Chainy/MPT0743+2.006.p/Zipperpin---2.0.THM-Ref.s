%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xr6fjYSe30

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:53 EST 2020

% Result     : Theorem 4.83s
% Output     : Refutation 4.83s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 395 expanded)
%              Number of leaves         :   24 ( 120 expanded)
%              Depth                    :   18
%              Number of atoms          :  723 (3160 expanded)
%              Number of equality atoms :   21 (  84 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('3',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v3_ordinal1 @ X37 )
      | ( r1_ordinal1 @ X38 @ X37 )
      | ( r2_hidden @ X37 @ X38 )
      | ~ ( v3_ordinal1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('4',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('5',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v3_ordinal1 @ X35 )
      | ~ ( v3_ordinal1 @ X36 )
      | ( r1_tarski @ X35 @ X36 )
      | ~ ( r1_ordinal1 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('10',plain,
    ( ( ( r1_tarski @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('14',plain,(
    ! [X39: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X39 ) )
      | ~ ( v3_ordinal1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('15',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v3_ordinal1 @ X35 )
      | ~ ( v3_ordinal1 @ X36 )
      | ( r1_tarski @ X35 @ X36 )
      | ~ ( r1_ordinal1 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('18',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('24',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('25',plain,(
    ! [X34: $i] :
      ( ( k1_ordinal1 @ X34 )
      = ( k2_xboole_0 @ X34 @ ( k1_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X32 @ X33 ) )
      = ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('27',plain,(
    ! [X34: $i] :
      ( ( k1_ordinal1 @ X34 )
      = ( k3_tarski @ ( k2_tarski @ X34 @ ( k1_tarski @ X34 ) ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k1_ordinal1 @ X0 )
      = ( k3_tarski @ ( k2_tarski @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('29',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X11 @ X13 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('30',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X32 @ X33 ) )
      = ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('31',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X11 @ X13 ) ) @ X12 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X1 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['23','32'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_A )
      | ( sk_B = sk_A ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_B = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','35'])).

thf('37',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('38',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X34: $i] :
      ( ( k1_ordinal1 @ X34 )
      = ( k3_tarski @ ( k2_tarski @ X34 @ ( k1_tarski @ X34 ) ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('40',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['40'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('42',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r2_hidden @ X29 @ X30 )
      | ~ ( r1_tarski @ ( k1_tarski @ X29 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('44',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('45',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X32 @ X33 ) )
      = ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('47',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k3_tarski @ ( k2_tarski @ X5 @ X3 ) ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['43','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','48'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('50',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ X40 @ X41 )
      | ~ ( r1_tarski @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('51',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['38','51'])).

thf('53',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','52'])).

thf('54',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','53'])).

thf('55',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['15'])).

thf('56',plain,(
    ! [X29: $i,X31: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X29 ) @ X31 )
      | ~ ( r2_hidden @ X29 @ X31 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('57',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['15'])).

thf('59',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['2','52','58'])).

thf('60',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(simpl_trail,[status(thm)],['57','59'])).

thf('61',plain,(
    ! [X39: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X39 ) )
      | ~ ( v3_ordinal1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('62',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v3_ordinal1 @ X37 )
      | ( r1_ordinal1 @ X38 @ X37 )
      | ( r2_hidden @ X37 @ X38 )
      | ~ ( v3_ordinal1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('63',plain,(
    ! [X34: $i] :
      ( ( k1_ordinal1 @ X34 )
      = ( k3_tarski @ ( k2_tarski @ X34 @ ( k1_tarski @ X34 ) ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('64',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('65',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X32 @ X33 ) )
      = ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('67',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k3_tarski @ ( k2_tarski @ X5 @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['61','69'])).

thf('71',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ X40 @ X41 )
      | ~ ( r1_tarski @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_B )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['60','72'])).

thf('74',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['15'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('79',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['2','52','58'])).

thf('81',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['79','80'])).

thf('82',plain,(
    r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ),
    inference(clc,[status(thm)],['76','81'])).

thf('83',plain,(
    $false ),
    inference(demod,[status(thm)],['54','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xr6fjYSe30
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:48:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 4.83/5.03  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.83/5.03  % Solved by: fo/fo7.sh
% 4.83/5.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.83/5.03  % done 7600 iterations in 4.589s
% 4.83/5.03  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.83/5.03  % SZS output start Refutation
% 4.83/5.03  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 4.83/5.03  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 4.83/5.03  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 4.83/5.03  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.83/5.03  thf(sk_A_type, type, sk_A: $i).
% 4.83/5.03  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.83/5.03  thf(sk_B_type, type, sk_B: $i).
% 4.83/5.03  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 4.83/5.03  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 4.83/5.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.83/5.03  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 4.83/5.03  thf(t33_ordinal1, conjecture,
% 4.83/5.03    (![A:$i]:
% 4.83/5.03     ( ( v3_ordinal1 @ A ) =>
% 4.83/5.03       ( ![B:$i]:
% 4.83/5.03         ( ( v3_ordinal1 @ B ) =>
% 4.83/5.03           ( ( r2_hidden @ A @ B ) <=>
% 4.83/5.03             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 4.83/5.03  thf(zf_stmt_0, negated_conjecture,
% 4.83/5.03    (~( ![A:$i]:
% 4.83/5.03        ( ( v3_ordinal1 @ A ) =>
% 4.83/5.03          ( ![B:$i]:
% 4.83/5.03            ( ( v3_ordinal1 @ B ) =>
% 4.83/5.03              ( ( r2_hidden @ A @ B ) <=>
% 4.83/5.03                ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ) )),
% 4.83/5.03    inference('cnf.neg', [status(esa)], [t33_ordinal1])).
% 4.83/5.03  thf('0', plain,
% 4.83/5.03      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 4.83/5.03        | ~ (r2_hidden @ sk_A @ sk_B))),
% 4.83/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.83/5.03  thf('1', plain,
% 4.83/5.03      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 4.83/5.03         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 4.83/5.03      inference('split', [status(esa)], ['0'])).
% 4.83/5.03  thf('2', plain,
% 4.83/5.03      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 4.83/5.03       ~ ((r2_hidden @ sk_A @ sk_B))),
% 4.83/5.03      inference('split', [status(esa)], ['0'])).
% 4.83/5.03  thf(t26_ordinal1, axiom,
% 4.83/5.03    (![A:$i]:
% 4.83/5.03     ( ( v3_ordinal1 @ A ) =>
% 4.83/5.03       ( ![B:$i]:
% 4.83/5.03         ( ( v3_ordinal1 @ B ) =>
% 4.83/5.03           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 4.83/5.03  thf('3', plain,
% 4.83/5.03      (![X37 : $i, X38 : $i]:
% 4.83/5.03         (~ (v3_ordinal1 @ X37)
% 4.83/5.03          | (r1_ordinal1 @ X38 @ X37)
% 4.83/5.03          | (r2_hidden @ X37 @ X38)
% 4.83/5.03          | ~ (v3_ordinal1 @ X38))),
% 4.83/5.03      inference('cnf', [status(esa)], [t26_ordinal1])).
% 4.83/5.03  thf('4', plain,
% 4.83/5.03      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 4.83/5.03      inference('split', [status(esa)], ['0'])).
% 4.83/5.03  thf('5', plain,
% 4.83/5.03      (((~ (v3_ordinal1 @ sk_B)
% 4.83/5.03         | (r1_ordinal1 @ sk_B @ sk_A)
% 4.83/5.03         | ~ (v3_ordinal1 @ sk_A))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 4.83/5.03      inference('sup-', [status(thm)], ['3', '4'])).
% 4.83/5.03  thf('6', plain, ((v3_ordinal1 @ sk_B)),
% 4.83/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.83/5.03  thf('7', plain, ((v3_ordinal1 @ sk_A)),
% 4.83/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.83/5.03  thf('8', plain,
% 4.83/5.03      (((r1_ordinal1 @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 4.83/5.03      inference('demod', [status(thm)], ['5', '6', '7'])).
% 4.83/5.03  thf(redefinition_r1_ordinal1, axiom,
% 4.83/5.03    (![A:$i,B:$i]:
% 4.83/5.03     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 4.83/5.03       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 4.83/5.03  thf('9', plain,
% 4.83/5.03      (![X35 : $i, X36 : $i]:
% 4.83/5.03         (~ (v3_ordinal1 @ X35)
% 4.83/5.03          | ~ (v3_ordinal1 @ X36)
% 4.83/5.03          | (r1_tarski @ X35 @ X36)
% 4.83/5.03          | ~ (r1_ordinal1 @ X35 @ X36))),
% 4.83/5.03      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 4.83/5.03  thf('10', plain,
% 4.83/5.03      ((((r1_tarski @ sk_B @ sk_A)
% 4.83/5.03         | ~ (v3_ordinal1 @ sk_A)
% 4.83/5.03         | ~ (v3_ordinal1 @ sk_B))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 4.83/5.03      inference('sup-', [status(thm)], ['8', '9'])).
% 4.83/5.03  thf('11', plain, ((v3_ordinal1 @ sk_A)),
% 4.83/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.83/5.03  thf('12', plain, ((v3_ordinal1 @ sk_B)),
% 4.83/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.83/5.03  thf('13', plain,
% 4.83/5.03      (((r1_tarski @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 4.83/5.03      inference('demod', [status(thm)], ['10', '11', '12'])).
% 4.83/5.03  thf(t29_ordinal1, axiom,
% 4.83/5.03    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 4.83/5.03  thf('14', plain,
% 4.83/5.03      (![X39 : $i]:
% 4.83/5.03         ((v3_ordinal1 @ (k1_ordinal1 @ X39)) | ~ (v3_ordinal1 @ X39))),
% 4.83/5.03      inference('cnf', [status(esa)], [t29_ordinal1])).
% 4.83/5.03  thf('15', plain,
% 4.83/5.03      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 4.83/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.83/5.03  thf('16', plain,
% 4.83/5.03      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 4.83/5.03         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 4.83/5.03      inference('split', [status(esa)], ['15'])).
% 4.83/5.03  thf('17', plain,
% 4.83/5.03      (![X35 : $i, X36 : $i]:
% 4.83/5.03         (~ (v3_ordinal1 @ X35)
% 4.83/5.03          | ~ (v3_ordinal1 @ X36)
% 4.83/5.03          | (r1_tarski @ X35 @ X36)
% 4.83/5.03          | ~ (r1_ordinal1 @ X35 @ X36))),
% 4.83/5.03      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 4.83/5.03  thf('18', plain,
% 4.83/5.03      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 4.83/5.03         | ~ (v3_ordinal1 @ sk_B)
% 4.83/5.03         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 4.83/5.03         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 4.83/5.03      inference('sup-', [status(thm)], ['16', '17'])).
% 4.83/5.03  thf('19', plain, ((v3_ordinal1 @ sk_B)),
% 4.83/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.83/5.03  thf('20', plain,
% 4.83/5.03      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 4.83/5.03         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 4.83/5.03         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 4.83/5.03      inference('demod', [status(thm)], ['18', '19'])).
% 4.83/5.03  thf('21', plain,
% 4.83/5.03      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 4.83/5.03         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 4.83/5.03      inference('sup-', [status(thm)], ['14', '20'])).
% 4.83/5.03  thf('22', plain, ((v3_ordinal1 @ sk_A)),
% 4.83/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.83/5.03  thf('23', plain,
% 4.83/5.03      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 4.83/5.03         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 4.83/5.03      inference('demod', [status(thm)], ['21', '22'])).
% 4.83/5.03  thf(t69_enumset1, axiom,
% 4.83/5.03    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 4.83/5.03  thf('24', plain,
% 4.83/5.03      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 4.83/5.03      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.83/5.03  thf(d1_ordinal1, axiom,
% 4.83/5.03    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 4.83/5.03  thf('25', plain,
% 4.83/5.03      (![X34 : $i]:
% 4.83/5.03         ((k1_ordinal1 @ X34) = (k2_xboole_0 @ X34 @ (k1_tarski @ X34)))),
% 4.83/5.03      inference('cnf', [status(esa)], [d1_ordinal1])).
% 4.83/5.03  thf(l51_zfmisc_1, axiom,
% 4.83/5.03    (![A:$i,B:$i]:
% 4.83/5.03     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 4.83/5.03  thf('26', plain,
% 4.83/5.03      (![X32 : $i, X33 : $i]:
% 4.83/5.03         ((k3_tarski @ (k2_tarski @ X32 @ X33)) = (k2_xboole_0 @ X32 @ X33))),
% 4.83/5.03      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 4.83/5.03  thf('27', plain,
% 4.83/5.03      (![X34 : $i]:
% 4.83/5.03         ((k1_ordinal1 @ X34)
% 4.83/5.03           = (k3_tarski @ (k2_tarski @ X34 @ (k1_tarski @ X34))))),
% 4.83/5.03      inference('demod', [status(thm)], ['25', '26'])).
% 4.83/5.03  thf('28', plain,
% 4.83/5.03      (![X0 : $i]:
% 4.83/5.03         ((k1_ordinal1 @ X0)
% 4.83/5.03           = (k3_tarski @ (k2_tarski @ X0 @ (k2_tarski @ X0 @ X0))))),
% 4.83/5.03      inference('sup+', [status(thm)], ['24', '27'])).
% 4.83/5.03  thf(t11_xboole_1, axiom,
% 4.83/5.03    (![A:$i,B:$i,C:$i]:
% 4.83/5.03     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 4.83/5.03  thf('29', plain,
% 4.83/5.03      (![X11 : $i, X12 : $i, X13 : $i]:
% 4.83/5.03         ((r1_tarski @ X11 @ X12)
% 4.83/5.03          | ~ (r1_tarski @ (k2_xboole_0 @ X11 @ X13) @ X12))),
% 4.83/5.03      inference('cnf', [status(esa)], [t11_xboole_1])).
% 4.83/5.03  thf('30', plain,
% 4.83/5.03      (![X32 : $i, X33 : $i]:
% 4.83/5.03         ((k3_tarski @ (k2_tarski @ X32 @ X33)) = (k2_xboole_0 @ X32 @ X33))),
% 4.83/5.03      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 4.83/5.03  thf('31', plain,
% 4.83/5.03      (![X11 : $i, X12 : $i, X13 : $i]:
% 4.83/5.03         ((r1_tarski @ X11 @ X12)
% 4.83/5.03          | ~ (r1_tarski @ (k3_tarski @ (k2_tarski @ X11 @ X13)) @ X12))),
% 4.83/5.03      inference('demod', [status(thm)], ['29', '30'])).
% 4.83/5.03  thf('32', plain,
% 4.83/5.03      (![X0 : $i, X1 : $i]:
% 4.83/5.03         (~ (r1_tarski @ (k1_ordinal1 @ X0) @ X1) | (r1_tarski @ X0 @ X1))),
% 4.83/5.03      inference('sup-', [status(thm)], ['28', '31'])).
% 4.83/5.03  thf('33', plain,
% 4.83/5.03      (((r1_tarski @ sk_A @ sk_B))
% 4.83/5.03         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 4.83/5.03      inference('sup-', [status(thm)], ['23', '32'])).
% 4.83/5.03  thf(d10_xboole_0, axiom,
% 4.83/5.03    (![A:$i,B:$i]:
% 4.83/5.03     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.83/5.03  thf('34', plain,
% 4.83/5.03      (![X8 : $i, X10 : $i]:
% 4.83/5.03         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 4.83/5.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.83/5.03  thf('35', plain,
% 4.83/5.03      (((~ (r1_tarski @ sk_B @ sk_A) | ((sk_B) = (sk_A))))
% 4.83/5.03         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 4.83/5.03      inference('sup-', [status(thm)], ['33', '34'])).
% 4.83/5.03  thf('36', plain,
% 4.83/5.03      ((((sk_B) = (sk_A)))
% 4.83/5.03         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 4.83/5.03             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 4.83/5.03      inference('sup-', [status(thm)], ['13', '35'])).
% 4.83/5.03  thf('37', plain,
% 4.83/5.03      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 4.83/5.03         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 4.83/5.03      inference('demod', [status(thm)], ['21', '22'])).
% 4.83/5.03  thf('38', plain,
% 4.83/5.03      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_A))
% 4.83/5.03         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 4.83/5.03             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 4.83/5.03      inference('sup+', [status(thm)], ['36', '37'])).
% 4.83/5.03  thf('39', plain,
% 4.83/5.03      (![X34 : $i]:
% 4.83/5.03         ((k1_ordinal1 @ X34)
% 4.83/5.03           = (k3_tarski @ (k2_tarski @ X34 @ (k1_tarski @ X34))))),
% 4.83/5.03      inference('demod', [status(thm)], ['25', '26'])).
% 4.83/5.03  thf('40', plain,
% 4.83/5.03      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 4.83/5.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.83/5.03  thf('41', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 4.83/5.03      inference('simplify', [status(thm)], ['40'])).
% 4.83/5.03  thf(l1_zfmisc_1, axiom,
% 4.83/5.03    (![A:$i,B:$i]:
% 4.83/5.03     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 4.83/5.03  thf('42', plain,
% 4.83/5.03      (![X29 : $i, X30 : $i]:
% 4.83/5.03         ((r2_hidden @ X29 @ X30) | ~ (r1_tarski @ (k1_tarski @ X29) @ X30))),
% 4.83/5.03      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 4.83/5.03  thf('43', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 4.83/5.03      inference('sup-', [status(thm)], ['41', '42'])).
% 4.83/5.03  thf(d3_xboole_0, axiom,
% 4.83/5.03    (![A:$i,B:$i,C:$i]:
% 4.83/5.03     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 4.83/5.03       ( ![D:$i]:
% 4.83/5.03         ( ( r2_hidden @ D @ C ) <=>
% 4.83/5.03           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 4.83/5.03  thf('44', plain,
% 4.83/5.03      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 4.83/5.03         (~ (r2_hidden @ X2 @ X3)
% 4.83/5.03          | (r2_hidden @ X2 @ X4)
% 4.83/5.03          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 4.83/5.03      inference('cnf', [status(esa)], [d3_xboole_0])).
% 4.83/5.03  thf('45', plain,
% 4.83/5.03      (![X2 : $i, X3 : $i, X5 : $i]:
% 4.83/5.03         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 4.83/5.03      inference('simplify', [status(thm)], ['44'])).
% 4.83/5.03  thf('46', plain,
% 4.83/5.03      (![X32 : $i, X33 : $i]:
% 4.83/5.03         ((k3_tarski @ (k2_tarski @ X32 @ X33)) = (k2_xboole_0 @ X32 @ X33))),
% 4.83/5.03      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 4.83/5.03  thf('47', plain,
% 4.83/5.03      (![X2 : $i, X3 : $i, X5 : $i]:
% 4.83/5.03         ((r2_hidden @ X2 @ (k3_tarski @ (k2_tarski @ X5 @ X3)))
% 4.83/5.03          | ~ (r2_hidden @ X2 @ X3))),
% 4.83/5.03      inference('demod', [status(thm)], ['45', '46'])).
% 4.83/5.03  thf('48', plain,
% 4.83/5.03      (![X0 : $i, X1 : $i]:
% 4.83/5.03         (r2_hidden @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ (k1_tarski @ X0))))),
% 4.83/5.03      inference('sup-', [status(thm)], ['43', '47'])).
% 4.83/5.03  thf('49', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_ordinal1 @ X0))),
% 4.83/5.03      inference('sup+', [status(thm)], ['39', '48'])).
% 4.83/5.03  thf(t7_ordinal1, axiom,
% 4.83/5.03    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.83/5.03  thf('50', plain,
% 4.83/5.03      (![X40 : $i, X41 : $i]:
% 4.83/5.03         (~ (r2_hidden @ X40 @ X41) | ~ (r1_tarski @ X41 @ X40))),
% 4.83/5.03      inference('cnf', [status(esa)], [t7_ordinal1])).
% 4.83/5.03  thf('51', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X0)),
% 4.83/5.03      inference('sup-', [status(thm)], ['49', '50'])).
% 4.83/5.03  thf('52', plain,
% 4.83/5.03      (((r2_hidden @ sk_A @ sk_B)) | 
% 4.83/5.03       ~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 4.83/5.03      inference('sup-', [status(thm)], ['38', '51'])).
% 4.83/5.03  thf('53', plain, (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 4.83/5.03      inference('sat_resolution*', [status(thm)], ['2', '52'])).
% 4.83/5.03  thf('54', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 4.83/5.03      inference('simpl_trail', [status(thm)], ['1', '53'])).
% 4.83/5.03  thf('55', plain,
% 4.83/5.03      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 4.83/5.03      inference('split', [status(esa)], ['15'])).
% 4.83/5.03  thf('56', plain,
% 4.83/5.03      (![X29 : $i, X31 : $i]:
% 4.83/5.03         ((r1_tarski @ (k1_tarski @ X29) @ X31) | ~ (r2_hidden @ X29 @ X31))),
% 4.83/5.03      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 4.83/5.03  thf('57', plain,
% 4.83/5.03      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B))
% 4.83/5.03         <= (((r2_hidden @ sk_A @ sk_B)))),
% 4.83/5.03      inference('sup-', [status(thm)], ['55', '56'])).
% 4.83/5.03  thf('58', plain,
% 4.83/5.03      (((r2_hidden @ sk_A @ sk_B)) | 
% 4.83/5.03       ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 4.83/5.03      inference('split', [status(esa)], ['15'])).
% 4.83/5.03  thf('59', plain, (((r2_hidden @ sk_A @ sk_B))),
% 4.83/5.03      inference('sat_resolution*', [status(thm)], ['2', '52', '58'])).
% 4.83/5.03  thf('60', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 4.83/5.03      inference('simpl_trail', [status(thm)], ['57', '59'])).
% 4.83/5.03  thf('61', plain,
% 4.83/5.03      (![X39 : $i]:
% 4.83/5.03         ((v3_ordinal1 @ (k1_ordinal1 @ X39)) | ~ (v3_ordinal1 @ X39))),
% 4.83/5.03      inference('cnf', [status(esa)], [t29_ordinal1])).
% 4.83/5.03  thf('62', plain,
% 4.83/5.03      (![X37 : $i, X38 : $i]:
% 4.83/5.03         (~ (v3_ordinal1 @ X37)
% 4.83/5.03          | (r1_ordinal1 @ X38 @ X37)
% 4.83/5.03          | (r2_hidden @ X37 @ X38)
% 4.83/5.03          | ~ (v3_ordinal1 @ X38))),
% 4.83/5.03      inference('cnf', [status(esa)], [t26_ordinal1])).
% 4.83/5.03  thf('63', plain,
% 4.83/5.03      (![X34 : $i]:
% 4.83/5.03         ((k1_ordinal1 @ X34)
% 4.83/5.03           = (k3_tarski @ (k2_tarski @ X34 @ (k1_tarski @ X34))))),
% 4.83/5.03      inference('demod', [status(thm)], ['25', '26'])).
% 4.83/5.03  thf('64', plain,
% 4.83/5.03      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 4.83/5.03         (~ (r2_hidden @ X6 @ X4)
% 4.83/5.03          | (r2_hidden @ X6 @ X5)
% 4.83/5.03          | (r2_hidden @ X6 @ X3)
% 4.83/5.03          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 4.83/5.03      inference('cnf', [status(esa)], [d3_xboole_0])).
% 4.83/5.03  thf('65', plain,
% 4.83/5.03      (![X3 : $i, X5 : $i, X6 : $i]:
% 4.83/5.03         ((r2_hidden @ X6 @ X3)
% 4.83/5.03          | (r2_hidden @ X6 @ X5)
% 4.83/5.03          | ~ (r2_hidden @ X6 @ (k2_xboole_0 @ X5 @ X3)))),
% 4.83/5.03      inference('simplify', [status(thm)], ['64'])).
% 4.83/5.03  thf('66', plain,
% 4.83/5.03      (![X32 : $i, X33 : $i]:
% 4.83/5.03         ((k3_tarski @ (k2_tarski @ X32 @ X33)) = (k2_xboole_0 @ X32 @ X33))),
% 4.83/5.03      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 4.83/5.03  thf('67', plain,
% 4.83/5.03      (![X3 : $i, X5 : $i, X6 : $i]:
% 4.83/5.03         ((r2_hidden @ X6 @ X3)
% 4.83/5.03          | (r2_hidden @ X6 @ X5)
% 4.83/5.03          | ~ (r2_hidden @ X6 @ (k3_tarski @ (k2_tarski @ X5 @ X3))))),
% 4.83/5.03      inference('demod', [status(thm)], ['65', '66'])).
% 4.83/5.03  thf('68', plain,
% 4.83/5.03      (![X0 : $i, X1 : $i]:
% 4.83/5.03         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 4.83/5.03          | (r2_hidden @ X1 @ X0)
% 4.83/5.03          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 4.83/5.03      inference('sup-', [status(thm)], ['63', '67'])).
% 4.83/5.03  thf('69', plain,
% 4.83/5.03      (![X0 : $i, X1 : $i]:
% 4.83/5.03         (~ (v3_ordinal1 @ (k1_ordinal1 @ X0))
% 4.83/5.03          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1)
% 4.83/5.03          | ~ (v3_ordinal1 @ X1)
% 4.83/5.03          | (r2_hidden @ X1 @ (k1_tarski @ X0))
% 4.83/5.03          | (r2_hidden @ X1 @ X0))),
% 4.83/5.03      inference('sup-', [status(thm)], ['62', '68'])).
% 4.83/5.03  thf('70', plain,
% 4.83/5.03      (![X0 : $i, X1 : $i]:
% 4.83/5.03         (~ (v3_ordinal1 @ X0)
% 4.83/5.03          | (r2_hidden @ X1 @ X0)
% 4.83/5.03          | (r2_hidden @ X1 @ (k1_tarski @ X0))
% 4.83/5.03          | ~ (v3_ordinal1 @ X1)
% 4.83/5.03          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1))),
% 4.83/5.03      inference('sup-', [status(thm)], ['61', '69'])).
% 4.83/5.03  thf('71', plain,
% 4.83/5.03      (![X40 : $i, X41 : $i]:
% 4.83/5.03         (~ (r2_hidden @ X40 @ X41) | ~ (r1_tarski @ X41 @ X40))),
% 4.83/5.03      inference('cnf', [status(esa)], [t7_ordinal1])).
% 4.83/5.03  thf('72', plain,
% 4.83/5.03      (![X0 : $i, X1 : $i]:
% 4.83/5.03         ((r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1)
% 4.83/5.03          | ~ (v3_ordinal1 @ X1)
% 4.83/5.03          | (r2_hidden @ X1 @ X0)
% 4.83/5.03          | ~ (v3_ordinal1 @ X0)
% 4.83/5.03          | ~ (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 4.83/5.03      inference('sup-', [status(thm)], ['70', '71'])).
% 4.83/5.03  thf('73', plain,
% 4.83/5.03      ((~ (v3_ordinal1 @ sk_A)
% 4.83/5.03        | (r2_hidden @ sk_B @ sk_A)
% 4.83/5.03        | ~ (v3_ordinal1 @ sk_B)
% 4.83/5.03        | (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 4.83/5.03      inference('sup-', [status(thm)], ['60', '72'])).
% 4.83/5.03  thf('74', plain, ((v3_ordinal1 @ sk_A)),
% 4.83/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.83/5.03  thf('75', plain, ((v3_ordinal1 @ sk_B)),
% 4.83/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.83/5.03  thf('76', plain,
% 4.83/5.03      (((r2_hidden @ sk_B @ sk_A) | (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 4.83/5.03      inference('demod', [status(thm)], ['73', '74', '75'])).
% 4.83/5.03  thf('77', plain,
% 4.83/5.03      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 4.83/5.03      inference('split', [status(esa)], ['15'])).
% 4.83/5.03  thf(antisymmetry_r2_hidden, axiom,
% 4.83/5.03    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 4.83/5.03  thf('78', plain,
% 4.83/5.03      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 4.83/5.03      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 4.83/5.03  thf('79', plain,
% 4.83/5.03      ((~ (r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 4.83/5.03      inference('sup-', [status(thm)], ['77', '78'])).
% 4.83/5.03  thf('80', plain, (((r2_hidden @ sk_A @ sk_B))),
% 4.83/5.03      inference('sat_resolution*', [status(thm)], ['2', '52', '58'])).
% 4.83/5.03  thf('81', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 4.83/5.03      inference('simpl_trail', [status(thm)], ['79', '80'])).
% 4.83/5.03  thf('82', plain, ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 4.83/5.03      inference('clc', [status(thm)], ['76', '81'])).
% 4.83/5.03  thf('83', plain, ($false), inference('demod', [status(thm)], ['54', '82'])).
% 4.83/5.03  
% 4.83/5.03  % SZS output end Refutation
% 4.83/5.03  
% 4.83/5.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
