%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Feg79AexSM

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:52 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 954 expanded)
%              Number of leaves         :   22 ( 276 expanded)
%              Depth                    :   27
%              Number of atoms          :  994 (7763 expanded)
%              Number of equality atoms :   32 ( 135 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

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
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X35 @ X36 )
      | ~ ( r1_tarski @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('3',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('6',plain,(
    ! [X34: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X34 ) )
      | ~ ( v3_ordinal1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('7',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v3_ordinal1 @ X25 )
      | ~ ( v3_ordinal1 @ X26 )
      | ( r1_tarski @ X25 @ X26 )
      | ~ ( r1_ordinal1 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('9',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('15',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v3_ordinal1 @ X32 )
      | ( r1_ordinal1 @ X33 @ X32 )
      | ( r2_hidden @ X32 @ X33 )
      | ~ ( v3_ordinal1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('16',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('17',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v3_ordinal1 @ X25 )
      | ~ ( v3_ordinal1 @ X26 )
      | ( r1_tarski @ X25 @ X26 )
      | ~ ( r1_ordinal1 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('22',plain,
    ( ( ( r1_tarski @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('26',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r2_xboole_0 @ X8 @ X10 )
      | ( X8 = X10 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('27',plain,
    ( ( ( sk_B = sk_A )
      | ( r2_xboole_0 @ sk_B @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t21_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_xboole_0 @ A @ B )
           => ( r2_hidden @ A @ B ) ) ) ) )).

thf('28',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v3_ordinal1 @ X30 )
      | ( r2_hidden @ X31 @ X30 )
      | ~ ( r2_xboole_0 @ X31 @ X30 )
      | ~ ( v1_ordinal1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t21_ordinal1])).

thf('29',plain,
    ( ( ( sk_B = sk_A )
      | ~ ( v1_ordinal1 @ sk_B )
      | ( r2_hidden @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('31',plain,(
    ! [X21: $i] :
      ( ( v1_ordinal1 @ X21 )
      | ~ ( v3_ordinal1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('32',plain,(
    v1_ordinal1 @ sk_B ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( ( sk_B = sk_A )
      | ( r2_hidden @ sk_B @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['29','32','33'])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('35',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r2_hidden @ X28 @ ( k1_ordinal1 @ X29 ) )
      | ~ ( r2_hidden @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('36',plain,
    ( ( ( sk_B = sk_A )
      | ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X35 @ X36 )
      | ~ ( r1_tarski @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('38',plain,
    ( ( ( sk_B = sk_A )
      | ~ ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_B = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','38'])).

thf('40',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('41',plain,(
    ! [X11: $i,X13: $i] :
      ( ( X11 = X13 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('42',plain,
    ( ( ~ ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ~ ( r1_tarski @ sk_A @ ( k1_ordinal1 @ sk_A ) )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X34: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X34 ) )
      | ~ ( v3_ordinal1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('45',plain,(
    ! [X34: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X34 ) )
      | ~ ( v3_ordinal1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('46',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('47',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v3_ordinal1 @ X22 )
      | ~ ( v3_ordinal1 @ X23 )
      | ( r1_ordinal1 @ X22 @ X23 )
      | ( r1_ordinal1 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v3_ordinal1 @ X25 )
      | ~ ( v3_ordinal1 @ X26 )
      | ( r1_tarski @ X25 @ X26 )
      | ~ ( r1_ordinal1 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r2_hidden @ X28 @ ( k1_ordinal1 @ X29 ) )
      | ( X28 != X29 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('55',plain,(
    ! [X29: $i] :
      ( r2_hidden @ X29 @ ( k1_ordinal1 @ X29 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X35 @ X36 )
      | ~ ( r1_tarski @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('57',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) )
    | ( r1_ordinal1 @ sk_A @ ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','57'])).

thf('59',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_A @ ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','58'])).

thf('60',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    r1_ordinal1 @ sk_A @ ( k1_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v3_ordinal1 @ X25 )
      | ~ ( v3_ordinal1 @ X26 )
      | ( r1_tarski @ X25 @ X26 )
      | ~ ( r1_ordinal1 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('63',plain,
    ( ( r1_tarski @ sk_A @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( r1_tarski @ sk_A @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r1_tarski @ sk_A @ ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','65'])).

thf('67',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    r1_tarski @ sk_A @ ( k1_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_B = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','38'])).

thf('70',plain,
    ( ( sk_A
      = ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('72',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ( X11 != X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('74',plain,(
    ! [X12: $i] :
      ( r1_tarski @ X12 @ X12 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['72','74'])).

thf('76',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('77',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['5','75','76'])).

thf('78',plain,(
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['3','77'])).

thf('79',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v3_ordinal1 @ X22 )
      | ~ ( v3_ordinal1 @ X23 )
      | ( r1_ordinal1 @ X22 @ X23 )
      | ( r1_ordinal1 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X34: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X34 ) )
      | ~ ( v3_ordinal1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('83',plain,(
    ! [X34: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X34 ) )
      | ~ ( v3_ordinal1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('84',plain,(
    ! [X34: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X34 ) )
      | ~ ( v3_ordinal1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('85',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v3_ordinal1 @ X22 )
      | ~ ( v3_ordinal1 @ X23 )
      | ( r1_ordinal1 @ X22 @ X23 )
      | ( r1_ordinal1 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('86',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('87',plain,
    ( ( ( r1_ordinal1 @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( ( r1_ordinal1 @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_ordinal1 @ sk_B @ ( k1_ordinal1 @ sk_A ) ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['84','89'])).

thf('91',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( r1_ordinal1 @ sk_B @ ( k1_ordinal1 @ sk_A ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v3_ordinal1 @ X25 )
      | ~ ( v3_ordinal1 @ X26 )
      | ( r1_tarski @ X25 @ X26 )
      | ~ ( r1_ordinal1 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('94',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['83','96'])).

thf('98',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r2_xboole_0 @ X8 @ X10 )
      | ( X8 = X10 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('101',plain,
    ( ( ( sk_B
        = ( k1_ordinal1 @ sk_A ) )
      | ( r2_xboole_0 @ sk_B @ ( k1_ordinal1 @ sk_A ) ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v3_ordinal1 @ X30 )
      | ( r2_hidden @ X31 @ X30 )
      | ~ ( r2_xboole_0 @ X31 @ X30 )
      | ~ ( v1_ordinal1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t21_ordinal1])).

thf('103',plain,
    ( ( ( sk_B
        = ( k1_ordinal1 @ sk_A ) )
      | ~ ( v1_ordinal1 @ sk_B )
      | ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v1_ordinal1 @ sk_B ),
    inference('sup-',[status(thm)],['30','31'])).

thf('105',plain,
    ( ( ( sk_B
        = ( k1_ordinal1 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['5','75'])).

thf('107',plain,
    ( ( sk_B
      = ( k1_ordinal1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['105','106'])).

thf('108',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
    | ( sk_B
      = ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','107'])).

thf('109',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
    | ( sk_B
      = ( k1_ordinal1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X27: $i,X28: $i] :
      ( ( X28 = X27 )
      | ( r2_hidden @ X28 @ X27 )
      | ~ ( r2_hidden @ X28 @ ( k1_ordinal1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('112',plain,
    ( ( sk_B
      = ( k1_ordinal1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('115',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['5','75','76'])).

thf('117',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( sk_B = sk_A )
    | ( sk_B
      = ( k1_ordinal1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['112','117'])).

thf('119',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('120',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['5','75'])).

thf('121',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['119','120'])).

thf('122',plain,
    ( ~ ( r1_ordinal1 @ sk_B @ sk_B )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['118','121'])).

thf('123',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['81','122'])).

thf('124',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    sk_B = sk_A ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X12: $i] :
      ( r1_tarski @ X12 @ X12 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('127',plain,(
    $false ),
    inference(demod,[status(thm)],['78','125','126'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Feg79AexSM
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:58:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.51/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.51/0.70  % Solved by: fo/fo7.sh
% 0.51/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.70  % done 610 iterations in 0.255s
% 0.51/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.51/0.70  % SZS output start Refutation
% 0.51/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.70  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.51/0.70  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.51/0.70  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.51/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.51/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.51/0.70  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.51/0.70  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.51/0.70  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.51/0.70  thf(t33_ordinal1, conjecture,
% 0.51/0.70    (![A:$i]:
% 0.51/0.70     ( ( v3_ordinal1 @ A ) =>
% 0.51/0.70       ( ![B:$i]:
% 0.51/0.70         ( ( v3_ordinal1 @ B ) =>
% 0.51/0.70           ( ( r2_hidden @ A @ B ) <=>
% 0.51/0.70             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 0.51/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.70    (~( ![A:$i]:
% 0.51/0.70        ( ( v3_ordinal1 @ A ) =>
% 0.51/0.70          ( ![B:$i]:
% 0.51/0.70            ( ( v3_ordinal1 @ B ) =>
% 0.51/0.70              ( ( r2_hidden @ A @ B ) <=>
% 0.51/0.70                ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ) )),
% 0.51/0.70    inference('cnf.neg', [status(esa)], [t33_ordinal1])).
% 0.51/0.70  thf('0', plain,
% 0.51/0.70      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('1', plain,
% 0.51/0.70      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.51/0.70      inference('split', [status(esa)], ['0'])).
% 0.51/0.70  thf(t7_ordinal1, axiom,
% 0.51/0.70    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.51/0.70  thf('2', plain,
% 0.51/0.70      (![X35 : $i, X36 : $i]:
% 0.51/0.70         (~ (r2_hidden @ X35 @ X36) | ~ (r1_tarski @ X36 @ X35))),
% 0.51/0.70      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.51/0.70  thf('3', plain,
% 0.51/0.70      ((~ (r1_tarski @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['1', '2'])).
% 0.51/0.70  thf('4', plain,
% 0.51/0.70      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.51/0.70        | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('5', plain,
% 0.51/0.70      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 0.51/0.70       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.51/0.70      inference('split', [status(esa)], ['4'])).
% 0.51/0.70  thf(t29_ordinal1, axiom,
% 0.51/0.70    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 0.51/0.70  thf('6', plain,
% 0.51/0.70      (![X34 : $i]:
% 0.51/0.70         ((v3_ordinal1 @ (k1_ordinal1 @ X34)) | ~ (v3_ordinal1 @ X34))),
% 0.51/0.70      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.51/0.70  thf('7', plain,
% 0.51/0.70      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.51/0.70         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.51/0.70      inference('split', [status(esa)], ['0'])).
% 0.51/0.70  thf(redefinition_r1_ordinal1, axiom,
% 0.51/0.70    (![A:$i,B:$i]:
% 0.51/0.70     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.51/0.70       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.51/0.70  thf('8', plain,
% 0.51/0.70      (![X25 : $i, X26 : $i]:
% 0.51/0.70         (~ (v3_ordinal1 @ X25)
% 0.51/0.70          | ~ (v3_ordinal1 @ X26)
% 0.51/0.70          | (r1_tarski @ X25 @ X26)
% 0.51/0.70          | ~ (r1_ordinal1 @ X25 @ X26))),
% 0.51/0.70      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.51/0.70  thf('9', plain,
% 0.51/0.70      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.51/0.70         | ~ (v3_ordinal1 @ sk_B)
% 0.51/0.70         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.51/0.70         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['7', '8'])).
% 0.51/0.70  thf('10', plain, ((v3_ordinal1 @ sk_B)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('11', plain,
% 0.51/0.70      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.51/0.70         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.51/0.70         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.51/0.70      inference('demod', [status(thm)], ['9', '10'])).
% 0.51/0.70  thf('12', plain,
% 0.51/0.70      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 0.51/0.70         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['6', '11'])).
% 0.51/0.70  thf('13', plain, ((v3_ordinal1 @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('14', plain,
% 0.51/0.70      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.51/0.70         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.51/0.70      inference('demod', [status(thm)], ['12', '13'])).
% 0.51/0.70  thf(t26_ordinal1, axiom,
% 0.51/0.70    (![A:$i]:
% 0.51/0.70     ( ( v3_ordinal1 @ A ) =>
% 0.51/0.70       ( ![B:$i]:
% 0.51/0.70         ( ( v3_ordinal1 @ B ) =>
% 0.51/0.70           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.51/0.70  thf('15', plain,
% 0.51/0.70      (![X32 : $i, X33 : $i]:
% 0.51/0.70         (~ (v3_ordinal1 @ X32)
% 0.51/0.70          | (r1_ordinal1 @ X33 @ X32)
% 0.51/0.70          | (r2_hidden @ X32 @ X33)
% 0.51/0.70          | ~ (v3_ordinal1 @ X33))),
% 0.51/0.70      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.51/0.70  thf('16', plain,
% 0.51/0.70      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.51/0.70      inference('split', [status(esa)], ['4'])).
% 0.51/0.70  thf('17', plain,
% 0.51/0.70      (((~ (v3_ordinal1 @ sk_B)
% 0.51/0.70         | (r1_ordinal1 @ sk_B @ sk_A)
% 0.51/0.70         | ~ (v3_ordinal1 @ sk_A))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['15', '16'])).
% 0.51/0.70  thf('18', plain, ((v3_ordinal1 @ sk_B)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('19', plain, ((v3_ordinal1 @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('20', plain,
% 0.51/0.70      (((r1_ordinal1 @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.51/0.70      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.51/0.70  thf('21', plain,
% 0.51/0.70      (![X25 : $i, X26 : $i]:
% 0.51/0.70         (~ (v3_ordinal1 @ X25)
% 0.51/0.70          | ~ (v3_ordinal1 @ X26)
% 0.51/0.70          | (r1_tarski @ X25 @ X26)
% 0.51/0.70          | ~ (r1_ordinal1 @ X25 @ X26))),
% 0.51/0.70      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.51/0.70  thf('22', plain,
% 0.51/0.70      ((((r1_tarski @ sk_B @ sk_A)
% 0.51/0.70         | ~ (v3_ordinal1 @ sk_A)
% 0.51/0.70         | ~ (v3_ordinal1 @ sk_B))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['20', '21'])).
% 0.51/0.70  thf('23', plain, ((v3_ordinal1 @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('24', plain, ((v3_ordinal1 @ sk_B)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('25', plain,
% 0.51/0.70      (((r1_tarski @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.51/0.70      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.51/0.70  thf(d8_xboole_0, axiom,
% 0.51/0.70    (![A:$i,B:$i]:
% 0.51/0.70     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.51/0.70       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.51/0.70  thf('26', plain,
% 0.51/0.70      (![X8 : $i, X10 : $i]:
% 0.51/0.70         ((r2_xboole_0 @ X8 @ X10) | ((X8) = (X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.51/0.70      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.51/0.70  thf('27', plain,
% 0.51/0.70      (((((sk_B) = (sk_A)) | (r2_xboole_0 @ sk_B @ sk_A)))
% 0.51/0.70         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['25', '26'])).
% 0.51/0.70  thf(t21_ordinal1, axiom,
% 0.51/0.70    (![A:$i]:
% 0.51/0.70     ( ( v1_ordinal1 @ A ) =>
% 0.51/0.70       ( ![B:$i]:
% 0.51/0.70         ( ( v3_ordinal1 @ B ) =>
% 0.51/0.70           ( ( r2_xboole_0 @ A @ B ) => ( r2_hidden @ A @ B ) ) ) ) ))).
% 0.51/0.70  thf('28', plain,
% 0.51/0.70      (![X30 : $i, X31 : $i]:
% 0.51/0.70         (~ (v3_ordinal1 @ X30)
% 0.51/0.70          | (r2_hidden @ X31 @ X30)
% 0.51/0.70          | ~ (r2_xboole_0 @ X31 @ X30)
% 0.51/0.70          | ~ (v1_ordinal1 @ X31))),
% 0.51/0.70      inference('cnf', [status(esa)], [t21_ordinal1])).
% 0.51/0.70  thf('29', plain,
% 0.51/0.70      (((((sk_B) = (sk_A))
% 0.51/0.70         | ~ (v1_ordinal1 @ sk_B)
% 0.51/0.70         | (r2_hidden @ sk_B @ sk_A)
% 0.51/0.70         | ~ (v3_ordinal1 @ sk_A))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['27', '28'])).
% 0.51/0.70  thf('30', plain, ((v3_ordinal1 @ sk_B)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf(cc1_ordinal1, axiom,
% 0.51/0.70    (![A:$i]:
% 0.51/0.70     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 0.51/0.70  thf('31', plain,
% 0.51/0.70      (![X21 : $i]: ((v1_ordinal1 @ X21) | ~ (v3_ordinal1 @ X21))),
% 0.51/0.70      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.51/0.70  thf('32', plain, ((v1_ordinal1 @ sk_B)),
% 0.51/0.70      inference('sup-', [status(thm)], ['30', '31'])).
% 0.51/0.70  thf('33', plain, ((v3_ordinal1 @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('34', plain,
% 0.51/0.70      (((((sk_B) = (sk_A)) | (r2_hidden @ sk_B @ sk_A)))
% 0.51/0.70         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.51/0.70      inference('demod', [status(thm)], ['29', '32', '33'])).
% 0.51/0.70  thf(t13_ordinal1, axiom,
% 0.51/0.70    (![A:$i,B:$i]:
% 0.51/0.70     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.51/0.70       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.51/0.70  thf('35', plain,
% 0.51/0.70      (![X28 : $i, X29 : $i]:
% 0.51/0.70         ((r2_hidden @ X28 @ (k1_ordinal1 @ X29)) | ~ (r2_hidden @ X28 @ X29))),
% 0.51/0.70      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.51/0.70  thf('36', plain,
% 0.51/0.70      (((((sk_B) = (sk_A)) | (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))))
% 0.51/0.70         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['34', '35'])).
% 0.51/0.70  thf('37', plain,
% 0.51/0.70      (![X35 : $i, X36 : $i]:
% 0.51/0.70         (~ (r2_hidden @ X35 @ X36) | ~ (r1_tarski @ X36 @ X35))),
% 0.51/0.70      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.51/0.70  thf('38', plain,
% 0.51/0.70      (((((sk_B) = (sk_A)) | ~ (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 0.51/0.70         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['36', '37'])).
% 0.51/0.70  thf('39', plain,
% 0.51/0.70      ((((sk_B) = (sk_A)))
% 0.51/0.70         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.51/0.70             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['14', '38'])).
% 0.51/0.70  thf('40', plain,
% 0.51/0.70      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.51/0.70         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.51/0.70      inference('demod', [status(thm)], ['12', '13'])).
% 0.51/0.70  thf(d10_xboole_0, axiom,
% 0.51/0.70    (![A:$i,B:$i]:
% 0.51/0.70     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.51/0.70  thf('41', plain,
% 0.51/0.70      (![X11 : $i, X13 : $i]:
% 0.51/0.70         (((X11) = (X13))
% 0.51/0.70          | ~ (r1_tarski @ X13 @ X11)
% 0.51/0.70          | ~ (r1_tarski @ X11 @ X13))),
% 0.51/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.51/0.70  thf('42', plain,
% 0.51/0.70      (((~ (r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.51/0.70         | ((sk_B) = (k1_ordinal1 @ sk_A))))
% 0.51/0.70         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['40', '41'])).
% 0.51/0.70  thf('43', plain,
% 0.51/0.70      (((~ (r1_tarski @ sk_A @ (k1_ordinal1 @ sk_A))
% 0.51/0.70         | ((sk_B) = (k1_ordinal1 @ sk_A))))
% 0.51/0.70         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.51/0.70             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['39', '42'])).
% 0.51/0.70  thf('44', plain,
% 0.51/0.70      (![X34 : $i]:
% 0.51/0.70         ((v3_ordinal1 @ (k1_ordinal1 @ X34)) | ~ (v3_ordinal1 @ X34))),
% 0.51/0.70      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.51/0.70  thf('45', plain,
% 0.51/0.70      (![X34 : $i]:
% 0.51/0.70         ((v3_ordinal1 @ (k1_ordinal1 @ X34)) | ~ (v3_ordinal1 @ X34))),
% 0.51/0.70      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.51/0.70  thf('46', plain, ((v3_ordinal1 @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf(connectedness_r1_ordinal1, axiom,
% 0.51/0.70    (![A:$i,B:$i]:
% 0.51/0.70     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.51/0.70       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 0.51/0.70  thf('47', plain,
% 0.51/0.70      (![X22 : $i, X23 : $i]:
% 0.51/0.70         (~ (v3_ordinal1 @ X22)
% 0.51/0.70          | ~ (v3_ordinal1 @ X23)
% 0.51/0.70          | (r1_ordinal1 @ X22 @ X23)
% 0.51/0.70          | (r1_ordinal1 @ X23 @ X22))),
% 0.51/0.70      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.51/0.70  thf('48', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         ((r1_ordinal1 @ X0 @ sk_A)
% 0.51/0.70          | (r1_ordinal1 @ sk_A @ X0)
% 0.51/0.70          | ~ (v3_ordinal1 @ X0))),
% 0.51/0.70      inference('sup-', [status(thm)], ['46', '47'])).
% 0.51/0.70  thf('49', plain,
% 0.51/0.70      (![X25 : $i, X26 : $i]:
% 0.51/0.70         (~ (v3_ordinal1 @ X25)
% 0.51/0.70          | ~ (v3_ordinal1 @ X26)
% 0.51/0.70          | (r1_tarski @ X25 @ X26)
% 0.51/0.70          | ~ (r1_ordinal1 @ X25 @ X26))),
% 0.51/0.70      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.51/0.70  thf('50', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (~ (v3_ordinal1 @ X0)
% 0.51/0.70          | (r1_ordinal1 @ sk_A @ X0)
% 0.51/0.70          | (r1_tarski @ X0 @ sk_A)
% 0.51/0.70          | ~ (v3_ordinal1 @ sk_A)
% 0.51/0.70          | ~ (v3_ordinal1 @ X0))),
% 0.51/0.70      inference('sup-', [status(thm)], ['48', '49'])).
% 0.51/0.70  thf('51', plain, ((v3_ordinal1 @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('52', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (~ (v3_ordinal1 @ X0)
% 0.51/0.70          | (r1_ordinal1 @ sk_A @ X0)
% 0.51/0.70          | (r1_tarski @ X0 @ sk_A)
% 0.51/0.70          | ~ (v3_ordinal1 @ X0))),
% 0.51/0.70      inference('demod', [status(thm)], ['50', '51'])).
% 0.51/0.70  thf('53', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         ((r1_tarski @ X0 @ sk_A)
% 0.51/0.70          | (r1_ordinal1 @ sk_A @ X0)
% 0.51/0.70          | ~ (v3_ordinal1 @ X0))),
% 0.51/0.70      inference('simplify', [status(thm)], ['52'])).
% 0.51/0.70  thf('54', plain,
% 0.51/0.70      (![X28 : $i, X29 : $i]:
% 0.51/0.70         ((r2_hidden @ X28 @ (k1_ordinal1 @ X29)) | ((X28) != (X29)))),
% 0.51/0.70      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.51/0.70  thf('55', plain, (![X29 : $i]: (r2_hidden @ X29 @ (k1_ordinal1 @ X29))),
% 0.51/0.70      inference('simplify', [status(thm)], ['54'])).
% 0.51/0.70  thf('56', plain,
% 0.51/0.70      (![X35 : $i, X36 : $i]:
% 0.51/0.70         (~ (r2_hidden @ X35 @ X36) | ~ (r1_tarski @ X36 @ X35))),
% 0.51/0.70      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.51/0.70  thf('57', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X0)),
% 0.51/0.70      inference('sup-', [status(thm)], ['55', '56'])).
% 0.51/0.70  thf('58', plain,
% 0.51/0.70      ((~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))
% 0.51/0.70        | (r1_ordinal1 @ sk_A @ (k1_ordinal1 @ sk_A)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['53', '57'])).
% 0.51/0.70  thf('59', plain,
% 0.51/0.70      ((~ (v3_ordinal1 @ sk_A) | (r1_ordinal1 @ sk_A @ (k1_ordinal1 @ sk_A)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['45', '58'])).
% 0.51/0.70  thf('60', plain, ((v3_ordinal1 @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('61', plain, ((r1_ordinal1 @ sk_A @ (k1_ordinal1 @ sk_A))),
% 0.51/0.70      inference('demod', [status(thm)], ['59', '60'])).
% 0.51/0.70  thf('62', plain,
% 0.51/0.70      (![X25 : $i, X26 : $i]:
% 0.51/0.70         (~ (v3_ordinal1 @ X25)
% 0.51/0.70          | ~ (v3_ordinal1 @ X26)
% 0.51/0.70          | (r1_tarski @ X25 @ X26)
% 0.51/0.70          | ~ (r1_ordinal1 @ X25 @ X26))),
% 0.51/0.70      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.51/0.70  thf('63', plain,
% 0.51/0.70      (((r1_tarski @ sk_A @ (k1_ordinal1 @ sk_A))
% 0.51/0.70        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))
% 0.51/0.70        | ~ (v3_ordinal1 @ sk_A))),
% 0.51/0.70      inference('sup-', [status(thm)], ['61', '62'])).
% 0.51/0.70  thf('64', plain, ((v3_ordinal1 @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('65', plain,
% 0.51/0.70      (((r1_tarski @ sk_A @ (k1_ordinal1 @ sk_A))
% 0.51/0.70        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 0.51/0.70      inference('demod', [status(thm)], ['63', '64'])).
% 0.51/0.70  thf('66', plain,
% 0.51/0.70      ((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ sk_A @ (k1_ordinal1 @ sk_A)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['44', '65'])).
% 0.51/0.70  thf('67', plain, ((v3_ordinal1 @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('68', plain, ((r1_tarski @ sk_A @ (k1_ordinal1 @ sk_A))),
% 0.51/0.70      inference('demod', [status(thm)], ['66', '67'])).
% 0.51/0.70  thf('69', plain,
% 0.51/0.70      ((((sk_B) = (sk_A)))
% 0.51/0.70         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.51/0.70             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['14', '38'])).
% 0.51/0.70  thf('70', plain,
% 0.51/0.70      ((((sk_A) = (k1_ordinal1 @ sk_A)))
% 0.51/0.70         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.51/0.70             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.51/0.70      inference('demod', [status(thm)], ['43', '68', '69'])).
% 0.51/0.70  thf('71', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X0)),
% 0.51/0.70      inference('sup-', [status(thm)], ['55', '56'])).
% 0.51/0.70  thf('72', plain,
% 0.51/0.70      ((~ (r1_tarski @ sk_A @ sk_A))
% 0.51/0.70         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.51/0.70             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['70', '71'])).
% 0.51/0.70  thf('73', plain,
% 0.51/0.70      (![X11 : $i, X12 : $i]: ((r1_tarski @ X11 @ X12) | ((X11) != (X12)))),
% 0.51/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.51/0.70  thf('74', plain, (![X12 : $i]: (r1_tarski @ X12 @ X12)),
% 0.51/0.70      inference('simplify', [status(thm)], ['73'])).
% 0.51/0.70  thf('75', plain,
% 0.51/0.70      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.51/0.70       ~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.51/0.70      inference('demod', [status(thm)], ['72', '74'])).
% 0.51/0.70  thf('76', plain,
% 0.51/0.70      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.51/0.70       ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.51/0.70      inference('split', [status(esa)], ['0'])).
% 0.51/0.70  thf('77', plain, (((r2_hidden @ sk_A @ sk_B))),
% 0.51/0.70      inference('sat_resolution*', [status(thm)], ['5', '75', '76'])).
% 0.51/0.70  thf('78', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 0.51/0.70      inference('simpl_trail', [status(thm)], ['3', '77'])).
% 0.51/0.70  thf('79', plain,
% 0.51/0.70      (![X22 : $i, X23 : $i]:
% 0.51/0.70         (~ (v3_ordinal1 @ X22)
% 0.51/0.70          | ~ (v3_ordinal1 @ X23)
% 0.51/0.70          | (r1_ordinal1 @ X22 @ X23)
% 0.51/0.70          | (r1_ordinal1 @ X23 @ X22))),
% 0.51/0.70      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.51/0.70  thf('80', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         ((r1_ordinal1 @ X0 @ X0) | ~ (v3_ordinal1 @ X0) | ~ (v3_ordinal1 @ X0))),
% 0.51/0.70      inference('eq_fact', [status(thm)], ['79'])).
% 0.51/0.70  thf('81', plain,
% 0.51/0.70      (![X0 : $i]: (~ (v3_ordinal1 @ X0) | (r1_ordinal1 @ X0 @ X0))),
% 0.51/0.70      inference('simplify', [status(thm)], ['80'])).
% 0.51/0.70  thf('82', plain,
% 0.51/0.70      (![X34 : $i]:
% 0.51/0.70         ((v3_ordinal1 @ (k1_ordinal1 @ X34)) | ~ (v3_ordinal1 @ X34))),
% 0.51/0.70      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.51/0.70  thf('83', plain,
% 0.51/0.70      (![X34 : $i]:
% 0.51/0.70         ((v3_ordinal1 @ (k1_ordinal1 @ X34)) | ~ (v3_ordinal1 @ X34))),
% 0.51/0.70      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.51/0.70  thf('84', plain,
% 0.51/0.70      (![X34 : $i]:
% 0.51/0.70         ((v3_ordinal1 @ (k1_ordinal1 @ X34)) | ~ (v3_ordinal1 @ X34))),
% 0.51/0.70      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.51/0.70  thf('85', plain,
% 0.51/0.70      (![X22 : $i, X23 : $i]:
% 0.51/0.70         (~ (v3_ordinal1 @ X22)
% 0.51/0.70          | ~ (v3_ordinal1 @ X23)
% 0.51/0.70          | (r1_ordinal1 @ X22 @ X23)
% 0.51/0.70          | (r1_ordinal1 @ X23 @ X22))),
% 0.51/0.70      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.51/0.70  thf('86', plain,
% 0.51/0.70      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.51/0.70         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.51/0.70      inference('split', [status(esa)], ['4'])).
% 0.51/0.70  thf('87', plain,
% 0.51/0.70      ((((r1_ordinal1 @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.51/0.70         | ~ (v3_ordinal1 @ sk_B)
% 0.51/0.70         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.51/0.70         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['85', '86'])).
% 0.51/0.70  thf('88', plain, ((v3_ordinal1 @ sk_B)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('89', plain,
% 0.51/0.70      ((((r1_ordinal1 @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.51/0.70         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.51/0.70         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.51/0.70      inference('demod', [status(thm)], ['87', '88'])).
% 0.51/0.70  thf('90', plain,
% 0.51/0.70      (((~ (v3_ordinal1 @ sk_A) | (r1_ordinal1 @ sk_B @ (k1_ordinal1 @ sk_A))))
% 0.51/0.70         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['84', '89'])).
% 0.51/0.70  thf('91', plain, ((v3_ordinal1 @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('92', plain,
% 0.51/0.70      (((r1_ordinal1 @ sk_B @ (k1_ordinal1 @ sk_A)))
% 0.51/0.70         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.51/0.70      inference('demod', [status(thm)], ['90', '91'])).
% 0.51/0.70  thf('93', plain,
% 0.51/0.70      (![X25 : $i, X26 : $i]:
% 0.51/0.70         (~ (v3_ordinal1 @ X25)
% 0.51/0.70          | ~ (v3_ordinal1 @ X26)
% 0.51/0.70          | (r1_tarski @ X25 @ X26)
% 0.51/0.70          | ~ (r1_ordinal1 @ X25 @ X26))),
% 0.51/0.70      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.51/0.70  thf('94', plain,
% 0.51/0.70      ((((r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.51/0.70         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))
% 0.51/0.70         | ~ (v3_ordinal1 @ sk_B)))
% 0.51/0.70         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['92', '93'])).
% 0.51/0.70  thf('95', plain, ((v3_ordinal1 @ sk_B)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('96', plain,
% 0.51/0.70      ((((r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.51/0.70         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.51/0.70         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.51/0.70      inference('demod', [status(thm)], ['94', '95'])).
% 0.51/0.70  thf('97', plain,
% 0.51/0.70      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A))))
% 0.51/0.70         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['83', '96'])).
% 0.51/0.70  thf('98', plain, ((v3_ordinal1 @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('99', plain,
% 0.51/0.70      (((r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A)))
% 0.51/0.70         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.51/0.70      inference('demod', [status(thm)], ['97', '98'])).
% 0.51/0.70  thf('100', plain,
% 0.51/0.70      (![X8 : $i, X10 : $i]:
% 0.51/0.70         ((r2_xboole_0 @ X8 @ X10) | ((X8) = (X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.51/0.70      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.51/0.70  thf('101', plain,
% 0.51/0.70      (((((sk_B) = (k1_ordinal1 @ sk_A))
% 0.51/0.70         | (r2_xboole_0 @ sk_B @ (k1_ordinal1 @ sk_A))))
% 0.51/0.70         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['99', '100'])).
% 0.51/0.70  thf('102', plain,
% 0.51/0.70      (![X30 : $i, X31 : $i]:
% 0.51/0.70         (~ (v3_ordinal1 @ X30)
% 0.51/0.70          | (r2_hidden @ X31 @ X30)
% 0.51/0.70          | ~ (r2_xboole_0 @ X31 @ X30)
% 0.51/0.70          | ~ (v1_ordinal1 @ X31))),
% 0.51/0.70      inference('cnf', [status(esa)], [t21_ordinal1])).
% 0.51/0.70  thf('103', plain,
% 0.51/0.70      (((((sk_B) = (k1_ordinal1 @ sk_A))
% 0.51/0.70         | ~ (v1_ordinal1 @ sk_B)
% 0.51/0.70         | (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.51/0.70         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.51/0.70         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['101', '102'])).
% 0.51/0.70  thf('104', plain, ((v1_ordinal1 @ sk_B)),
% 0.51/0.70      inference('sup-', [status(thm)], ['30', '31'])).
% 0.51/0.70  thf('105', plain,
% 0.51/0.70      (((((sk_B) = (k1_ordinal1 @ sk_A))
% 0.51/0.70         | (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.51/0.70         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.51/0.70         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.51/0.70      inference('demod', [status(thm)], ['103', '104'])).
% 0.51/0.70  thf('106', plain, (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.51/0.70      inference('sat_resolution*', [status(thm)], ['5', '75'])).
% 0.51/0.70  thf('107', plain,
% 0.51/0.70      ((((sk_B) = (k1_ordinal1 @ sk_A))
% 0.51/0.70        | (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.51/0.70        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 0.51/0.70      inference('simpl_trail', [status(thm)], ['105', '106'])).
% 0.51/0.70  thf('108', plain,
% 0.51/0.70      ((~ (v3_ordinal1 @ sk_A)
% 0.51/0.70        | (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.51/0.70        | ((sk_B) = (k1_ordinal1 @ sk_A)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['82', '107'])).
% 0.51/0.70  thf('109', plain, ((v3_ordinal1 @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('110', plain,
% 0.51/0.70      (((r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.51/0.70        | ((sk_B) = (k1_ordinal1 @ sk_A)))),
% 0.51/0.70      inference('demod', [status(thm)], ['108', '109'])).
% 0.51/0.70  thf('111', plain,
% 0.51/0.70      (![X27 : $i, X28 : $i]:
% 0.51/0.70         (((X28) = (X27))
% 0.51/0.70          | (r2_hidden @ X28 @ X27)
% 0.51/0.70          | ~ (r2_hidden @ X28 @ (k1_ordinal1 @ X27)))),
% 0.51/0.70      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.51/0.70  thf('112', plain,
% 0.51/0.70      ((((sk_B) = (k1_ordinal1 @ sk_A))
% 0.51/0.70        | (r2_hidden @ sk_B @ sk_A)
% 0.51/0.70        | ((sk_B) = (sk_A)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['110', '111'])).
% 0.51/0.70  thf('113', plain,
% 0.51/0.70      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.51/0.70      inference('split', [status(esa)], ['0'])).
% 0.51/0.70  thf(antisymmetry_r2_hidden, axiom,
% 0.51/0.70    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.51/0.70  thf('114', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.51/0.70      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.51/0.70  thf('115', plain,
% 0.51/0.70      ((~ (r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['113', '114'])).
% 0.51/0.70  thf('116', plain, (((r2_hidden @ sk_A @ sk_B))),
% 0.51/0.70      inference('sat_resolution*', [status(thm)], ['5', '75', '76'])).
% 0.51/0.70  thf('117', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 0.51/0.70      inference('simpl_trail', [status(thm)], ['115', '116'])).
% 0.51/0.70  thf('118', plain, ((((sk_B) = (sk_A)) | ((sk_B) = (k1_ordinal1 @ sk_A)))),
% 0.51/0.70      inference('clc', [status(thm)], ['112', '117'])).
% 0.51/0.70  thf('119', plain,
% 0.51/0.70      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.51/0.70         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.51/0.70      inference('split', [status(esa)], ['4'])).
% 0.51/0.70  thf('120', plain, (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.51/0.70      inference('sat_resolution*', [status(thm)], ['5', '75'])).
% 0.51/0.70  thf('121', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 0.51/0.70      inference('simpl_trail', [status(thm)], ['119', '120'])).
% 0.51/0.70  thf('122', plain, ((~ (r1_ordinal1 @ sk_B @ sk_B) | ((sk_B) = (sk_A)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['118', '121'])).
% 0.51/0.70  thf('123', plain, ((~ (v3_ordinal1 @ sk_B) | ((sk_B) = (sk_A)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['81', '122'])).
% 0.51/0.70  thf('124', plain, ((v3_ordinal1 @ sk_B)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('125', plain, (((sk_B) = (sk_A))),
% 0.51/0.70      inference('demod', [status(thm)], ['123', '124'])).
% 0.51/0.70  thf('126', plain, (![X12 : $i]: (r1_tarski @ X12 @ X12)),
% 0.51/0.70      inference('simplify', [status(thm)], ['73'])).
% 0.51/0.70  thf('127', plain, ($false),
% 0.51/0.70      inference('demod', [status(thm)], ['78', '125', '126'])).
% 0.51/0.70  
% 0.51/0.70  % SZS output end Refutation
% 0.51/0.70  
% 0.51/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
