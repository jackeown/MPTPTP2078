%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.S3IKh5ADFe

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:53 EST 2020

% Result     : Theorem 36.25s
% Output     : Refutation 36.25s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 796 expanded)
%              Number of leaves         :   22 ( 234 expanded)
%              Depth                    :   24
%              Number of atoms          :  935 (6591 expanded)
%              Number of equality atoms :   19 (  91 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('3',plain,(
    ! [X50: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X50 ) )
      | ~ ( v3_ordinal1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('4',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( v3_ordinal1 @ X45 )
      | ~ ( v3_ordinal1 @ X46 )
      | ( r1_tarski @ X45 @ X46 )
      | ~ ( r1_ordinal1 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('7',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('13',plain,(
    ! [X11: $i] :
      ( ( k2_tarski @ X11 @ X11 )
      = ( k1_tarski @ X11 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('14',plain,(
    ! [X44: $i] :
      ( ( k1_ordinal1 @ X44 )
      = ( k2_xboole_0 @ X44 @ ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k1_ordinal1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('16',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v3_ordinal1 @ X48 )
      | ( r1_ordinal1 @ X49 @ X48 )
      | ( r2_hidden @ X48 @ X49 )
      | ~ ( v3_ordinal1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('17',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X5 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('18',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X5 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','19'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('21',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ X51 @ X52 )
      | ~ ( r1_tarski @ X52 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['12','22'])).

thf('24',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( v3_ordinal1 @ X45 )
      | ~ ( v3_ordinal1 @ X46 )
      | ( r1_tarski @ X45 @ X46 )
      | ~ ( r1_ordinal1 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('28',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v3_ordinal1 @ X48 )
      | ( r1_ordinal1 @ X49 @ X48 )
      | ( r2_hidden @ X48 @ X49 )
      | ~ ( v3_ordinal1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('33',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( v3_ordinal1 @ X45 )
      | ~ ( v3_ordinal1 @ X46 )
      | ( r1_tarski @ X45 @ X46 )
      | ~ ( r1_ordinal1 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('39',plain,
    ( ( ( r1_tarski @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('43',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('44',plain,
    ( ( ~ ( r1_tarski @ sk_A @ sk_B )
      | ( sk_A = sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','44'])).

thf('46',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('47',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('48',plain,
    ( ( ~ ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ~ ( r1_tarski @ sk_A @ ( k1_ordinal1 @ sk_A ) )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X50: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X50 ) )
      | ~ ( v3_ordinal1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('51',plain,(
    ! [X50: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X50 ) )
      | ~ ( v3_ordinal1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('52',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v3_ordinal1 @ X48 )
      | ( r1_ordinal1 @ X49 @ X48 )
      | ( r2_hidden @ X48 @ X49 )
      | ~ ( v3_ordinal1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('54',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v3_ordinal1 @ X48 )
      | ( r1_ordinal1 @ X49 @ X48 )
      | ( r2_hidden @ X48 @ X49 )
      | ~ ( v3_ordinal1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','58'])).

thf('60',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( v3_ordinal1 @ X45 )
      | ~ ( v3_ordinal1 @ X46 )
      | ( r1_tarski @ X45 @ X46 )
      | ~ ( r1_ordinal1 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('65',plain,(
    ! [X47: $i] :
      ( r2_hidden @ X47 @ ( k1_ordinal1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('66',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ X51 @ X52 )
      | ~ ( r1_tarski @ X52 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('67',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( r1_ordinal1 @ sk_A @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_A @ ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','68'])).

thf('70',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    r1_ordinal1 @ sk_A @ ( k1_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( v3_ordinal1 @ X45 )
      | ~ ( v3_ordinal1 @ X46 )
      | ( r1_tarski @ X45 @ X46 )
      | ~ ( r1_ordinal1 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('73',plain,
    ( ( r1_tarski @ sk_A @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( r1_tarski @ sk_A @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r1_tarski @ sk_A @ ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','75'])).

thf('77',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    r1_tarski @ sk_A @ ( k1_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','44'])).

thf('80',plain,
    ( ( sk_A
      = ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('82',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('84',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['82','84'])).

thf('86',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','85'])).

thf('87',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','86'])).

thf('88',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('89',plain,(
    ! [X39: $i,X41: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X39 ) @ X41 )
      | ~ ( r2_hidden @ X39 @ X41 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('90',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('92',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['2','85','91'])).

thf('93',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(simpl_trail,[status(thm)],['90','92'])).

thf('94',plain,(
    ! [X50: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X50 ) )
      | ~ ( v3_ordinal1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('95',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v3_ordinal1 @ X48 )
      | ( r1_ordinal1 @ X49 @ X48 )
      | ( r2_hidden @ X48 @ X49 )
      | ~ ( v3_ordinal1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('96',plain,(
    ! [X44: $i] :
      ( ( k1_ordinal1 @ X44 )
      = ( k2_xboole_0 @ X44 @ ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('97',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('98',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['96','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['94','100'])).

thf('102',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ X51 @ X52 )
      | ~ ( r1_tarski @ X52 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_B )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['93','103'])).

thf('105',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('110',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['2','85','91'])).

thf('112',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['110','111'])).

thf('113',plain,(
    r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ),
    inference(clc,[status(thm)],['107','112'])).

thf('114',plain,(
    $false ),
    inference(demod,[status(thm)],['87','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.S3IKh5ADFe
% 0.17/0.38  % Computer   : n025.cluster.edu
% 0.17/0.38  % Model      : x86_64 x86_64
% 0.17/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.38  % Memory     : 8042.1875MB
% 0.17/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.38  % CPULimit   : 60
% 0.17/0.38  % DateTime   : Tue Dec  1 13:26:36 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.17/0.38  % Python version: Python 3.6.8
% 0.17/0.38  % Running in FO mode
% 36.25/36.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 36.25/36.44  % Solved by: fo/fo7.sh
% 36.25/36.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 36.25/36.44  % done 50901 iterations in 35.988s
% 36.25/36.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 36.25/36.44  % SZS output start Refutation
% 36.25/36.44  thf(sk_A_type, type, sk_A: $i).
% 36.25/36.44  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 36.25/36.44  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 36.25/36.44  thf(sk_B_type, type, sk_B: $i).
% 36.25/36.44  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 36.25/36.44  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 36.25/36.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 36.25/36.44  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 36.25/36.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 36.25/36.44  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 36.25/36.44  thf(t33_ordinal1, conjecture,
% 36.25/36.44    (![A:$i]:
% 36.25/36.44     ( ( v3_ordinal1 @ A ) =>
% 36.25/36.44       ( ![B:$i]:
% 36.25/36.44         ( ( v3_ordinal1 @ B ) =>
% 36.25/36.44           ( ( r2_hidden @ A @ B ) <=>
% 36.25/36.44             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 36.25/36.44  thf(zf_stmt_0, negated_conjecture,
% 36.25/36.44    (~( ![A:$i]:
% 36.25/36.44        ( ( v3_ordinal1 @ A ) =>
% 36.25/36.44          ( ![B:$i]:
% 36.25/36.44            ( ( v3_ordinal1 @ B ) =>
% 36.25/36.44              ( ( r2_hidden @ A @ B ) <=>
% 36.25/36.44                ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ) )),
% 36.25/36.44    inference('cnf.neg', [status(esa)], [t33_ordinal1])).
% 36.25/36.44  thf('0', plain,
% 36.25/36.44      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 36.25/36.44        | ~ (r2_hidden @ sk_A @ sk_B))),
% 36.25/36.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.25/36.44  thf('1', plain,
% 36.25/36.44      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 36.25/36.44         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 36.25/36.44      inference('split', [status(esa)], ['0'])).
% 36.25/36.44  thf('2', plain,
% 36.25/36.44      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 36.25/36.44       ~ ((r2_hidden @ sk_A @ sk_B))),
% 36.25/36.44      inference('split', [status(esa)], ['0'])).
% 36.25/36.44  thf(t29_ordinal1, axiom,
% 36.25/36.44    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 36.25/36.44  thf('3', plain,
% 36.25/36.44      (![X50 : $i]:
% 36.25/36.44         ((v3_ordinal1 @ (k1_ordinal1 @ X50)) | ~ (v3_ordinal1 @ X50))),
% 36.25/36.44      inference('cnf', [status(esa)], [t29_ordinal1])).
% 36.25/36.44  thf('4', plain,
% 36.25/36.44      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 36.25/36.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.25/36.44  thf('5', plain,
% 36.25/36.44      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 36.25/36.44         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 36.25/36.44      inference('split', [status(esa)], ['4'])).
% 36.25/36.44  thf(redefinition_r1_ordinal1, axiom,
% 36.25/36.44    (![A:$i,B:$i]:
% 36.25/36.44     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 36.25/36.44       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 36.25/36.44  thf('6', plain,
% 36.25/36.44      (![X45 : $i, X46 : $i]:
% 36.25/36.44         (~ (v3_ordinal1 @ X45)
% 36.25/36.44          | ~ (v3_ordinal1 @ X46)
% 36.25/36.44          | (r1_tarski @ X45 @ X46)
% 36.25/36.44          | ~ (r1_ordinal1 @ X45 @ X46))),
% 36.25/36.44      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 36.25/36.44  thf('7', plain,
% 36.25/36.44      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 36.25/36.44         | ~ (v3_ordinal1 @ sk_B)
% 36.25/36.44         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 36.25/36.44         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 36.25/36.44      inference('sup-', [status(thm)], ['5', '6'])).
% 36.25/36.44  thf('8', plain, ((v3_ordinal1 @ sk_B)),
% 36.25/36.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.25/36.44  thf('9', plain,
% 36.25/36.44      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 36.25/36.44         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 36.25/36.44         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 36.25/36.44      inference('demod', [status(thm)], ['7', '8'])).
% 36.25/36.44  thf('10', plain,
% 36.25/36.44      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 36.25/36.44         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 36.25/36.44      inference('sup-', [status(thm)], ['3', '9'])).
% 36.25/36.44  thf('11', plain, ((v3_ordinal1 @ sk_A)),
% 36.25/36.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.25/36.44  thf('12', plain,
% 36.25/36.44      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 36.25/36.44         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 36.25/36.44      inference('demod', [status(thm)], ['10', '11'])).
% 36.25/36.44  thf(t69_enumset1, axiom,
% 36.25/36.44    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 36.25/36.44  thf('13', plain,
% 36.25/36.44      (![X11 : $i]: ((k2_tarski @ X11 @ X11) = (k1_tarski @ X11))),
% 36.25/36.44      inference('cnf', [status(esa)], [t69_enumset1])).
% 36.25/36.44  thf(d1_ordinal1, axiom,
% 36.25/36.44    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 36.25/36.44  thf('14', plain,
% 36.25/36.44      (![X44 : $i]:
% 36.25/36.44         ((k1_ordinal1 @ X44) = (k2_xboole_0 @ X44 @ (k1_tarski @ X44)))),
% 36.25/36.44      inference('cnf', [status(esa)], [d1_ordinal1])).
% 36.25/36.44  thf('15', plain,
% 36.25/36.44      (![X0 : $i]:
% 36.25/36.44         ((k1_ordinal1 @ X0) = (k2_xboole_0 @ X0 @ (k2_tarski @ X0 @ X0)))),
% 36.25/36.44      inference('sup+', [status(thm)], ['13', '14'])).
% 36.25/36.44  thf(t26_ordinal1, axiom,
% 36.25/36.44    (![A:$i]:
% 36.25/36.44     ( ( v3_ordinal1 @ A ) =>
% 36.25/36.44       ( ![B:$i]:
% 36.25/36.44         ( ( v3_ordinal1 @ B ) =>
% 36.25/36.44           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 36.25/36.44  thf('16', plain,
% 36.25/36.44      (![X48 : $i, X49 : $i]:
% 36.25/36.44         (~ (v3_ordinal1 @ X48)
% 36.25/36.44          | (r1_ordinal1 @ X49 @ X48)
% 36.25/36.44          | (r2_hidden @ X48 @ X49)
% 36.25/36.44          | ~ (v3_ordinal1 @ X49))),
% 36.25/36.44      inference('cnf', [status(esa)], [t26_ordinal1])).
% 36.25/36.44  thf(d3_xboole_0, axiom,
% 36.25/36.44    (![A:$i,B:$i,C:$i]:
% 36.25/36.44     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 36.25/36.44       ( ![D:$i]:
% 36.25/36.44         ( ( r2_hidden @ D @ C ) <=>
% 36.25/36.44           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 36.25/36.44  thf('17', plain,
% 36.25/36.44      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 36.25/36.44         (~ (r2_hidden @ X2 @ X5)
% 36.25/36.44          | (r2_hidden @ X2 @ X4)
% 36.25/36.44          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 36.25/36.44      inference('cnf', [status(esa)], [d3_xboole_0])).
% 36.25/36.44  thf('18', plain,
% 36.25/36.44      (![X2 : $i, X3 : $i, X5 : $i]:
% 36.25/36.44         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X5))),
% 36.25/36.44      inference('simplify', [status(thm)], ['17'])).
% 36.25/36.44  thf('19', plain,
% 36.25/36.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.25/36.44         (~ (v3_ordinal1 @ X0)
% 36.25/36.44          | (r1_ordinal1 @ X0 @ X1)
% 36.25/36.44          | ~ (v3_ordinal1 @ X1)
% 36.25/36.44          | (r2_hidden @ X1 @ (k2_xboole_0 @ X0 @ X2)))),
% 36.25/36.44      inference('sup-', [status(thm)], ['16', '18'])).
% 36.25/36.44  thf('20', plain,
% 36.25/36.44      (![X0 : $i, X1 : $i]:
% 36.25/36.44         ((r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 36.25/36.44          | ~ (v3_ordinal1 @ X1)
% 36.25/36.44          | (r1_ordinal1 @ X0 @ X1)
% 36.25/36.44          | ~ (v3_ordinal1 @ X0))),
% 36.25/36.44      inference('sup+', [status(thm)], ['15', '19'])).
% 36.25/36.44  thf(t7_ordinal1, axiom,
% 36.25/36.44    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 36.25/36.44  thf('21', plain,
% 36.25/36.44      (![X51 : $i, X52 : $i]:
% 36.25/36.44         (~ (r2_hidden @ X51 @ X52) | ~ (r1_tarski @ X52 @ X51))),
% 36.25/36.44      inference('cnf', [status(esa)], [t7_ordinal1])).
% 36.25/36.44  thf('22', plain,
% 36.25/36.44      (![X0 : $i, X1 : $i]:
% 36.25/36.44         (~ (v3_ordinal1 @ X0)
% 36.25/36.44          | (r1_ordinal1 @ X0 @ X1)
% 36.25/36.44          | ~ (v3_ordinal1 @ X1)
% 36.25/36.44          | ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X1))),
% 36.25/36.44      inference('sup-', [status(thm)], ['20', '21'])).
% 36.25/36.44  thf('23', plain,
% 36.25/36.44      (((~ (v3_ordinal1 @ sk_B)
% 36.25/36.44         | (r1_ordinal1 @ sk_A @ sk_B)
% 36.25/36.44         | ~ (v3_ordinal1 @ sk_A)))
% 36.25/36.44         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 36.25/36.44      inference('sup-', [status(thm)], ['12', '22'])).
% 36.25/36.44  thf('24', plain, ((v3_ordinal1 @ sk_B)),
% 36.25/36.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.25/36.44  thf('25', plain, ((v3_ordinal1 @ sk_A)),
% 36.25/36.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.25/36.44  thf('26', plain,
% 36.25/36.44      (((r1_ordinal1 @ sk_A @ sk_B))
% 36.25/36.44         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 36.25/36.44      inference('demod', [status(thm)], ['23', '24', '25'])).
% 36.25/36.44  thf('27', plain,
% 36.25/36.44      (![X45 : $i, X46 : $i]:
% 36.25/36.44         (~ (v3_ordinal1 @ X45)
% 36.25/36.44          | ~ (v3_ordinal1 @ X46)
% 36.25/36.44          | (r1_tarski @ X45 @ X46)
% 36.25/36.44          | ~ (r1_ordinal1 @ X45 @ X46))),
% 36.25/36.44      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 36.25/36.44  thf('28', plain,
% 36.25/36.44      ((((r1_tarski @ sk_A @ sk_B)
% 36.25/36.44         | ~ (v3_ordinal1 @ sk_B)
% 36.25/36.44         | ~ (v3_ordinal1 @ sk_A)))
% 36.25/36.44         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 36.25/36.44      inference('sup-', [status(thm)], ['26', '27'])).
% 36.25/36.44  thf('29', plain, ((v3_ordinal1 @ sk_B)),
% 36.25/36.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.25/36.44  thf('30', plain, ((v3_ordinal1 @ sk_A)),
% 36.25/36.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.25/36.44  thf('31', plain,
% 36.25/36.44      (((r1_tarski @ sk_A @ sk_B))
% 36.25/36.44         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 36.25/36.44      inference('demod', [status(thm)], ['28', '29', '30'])).
% 36.25/36.44  thf('32', plain,
% 36.25/36.44      (![X48 : $i, X49 : $i]:
% 36.25/36.44         (~ (v3_ordinal1 @ X48)
% 36.25/36.44          | (r1_ordinal1 @ X49 @ X48)
% 36.25/36.44          | (r2_hidden @ X48 @ X49)
% 36.25/36.44          | ~ (v3_ordinal1 @ X49))),
% 36.25/36.44      inference('cnf', [status(esa)], [t26_ordinal1])).
% 36.25/36.44  thf('33', plain,
% 36.25/36.44      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 36.25/36.44      inference('split', [status(esa)], ['0'])).
% 36.25/36.44  thf('34', plain,
% 36.25/36.44      (((~ (v3_ordinal1 @ sk_B)
% 36.25/36.44         | (r1_ordinal1 @ sk_B @ sk_A)
% 36.25/36.44         | ~ (v3_ordinal1 @ sk_A))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 36.25/36.44      inference('sup-', [status(thm)], ['32', '33'])).
% 36.25/36.44  thf('35', plain, ((v3_ordinal1 @ sk_B)),
% 36.25/36.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.25/36.44  thf('36', plain, ((v3_ordinal1 @ sk_A)),
% 36.25/36.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.25/36.44  thf('37', plain,
% 36.25/36.44      (((r1_ordinal1 @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 36.25/36.44      inference('demod', [status(thm)], ['34', '35', '36'])).
% 36.25/36.44  thf('38', plain,
% 36.25/36.44      (![X45 : $i, X46 : $i]:
% 36.25/36.44         (~ (v3_ordinal1 @ X45)
% 36.25/36.44          | ~ (v3_ordinal1 @ X46)
% 36.25/36.44          | (r1_tarski @ X45 @ X46)
% 36.25/36.44          | ~ (r1_ordinal1 @ X45 @ X46))),
% 36.25/36.44      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 36.25/36.44  thf('39', plain,
% 36.25/36.44      ((((r1_tarski @ sk_B @ sk_A)
% 36.25/36.44         | ~ (v3_ordinal1 @ sk_A)
% 36.25/36.44         | ~ (v3_ordinal1 @ sk_B))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 36.25/36.45      inference('sup-', [status(thm)], ['37', '38'])).
% 36.25/36.45  thf('40', plain, ((v3_ordinal1 @ sk_A)),
% 36.25/36.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.25/36.45  thf('41', plain, ((v3_ordinal1 @ sk_B)),
% 36.25/36.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.25/36.45  thf('42', plain,
% 36.25/36.45      (((r1_tarski @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 36.25/36.45      inference('demod', [status(thm)], ['39', '40', '41'])).
% 36.25/36.45  thf(d10_xboole_0, axiom,
% 36.25/36.45    (![A:$i,B:$i]:
% 36.25/36.45     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 36.25/36.45  thf('43', plain,
% 36.25/36.45      (![X8 : $i, X10 : $i]:
% 36.25/36.45         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 36.25/36.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 36.25/36.45  thf('44', plain,
% 36.25/36.45      (((~ (r1_tarski @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 36.25/36.45         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 36.25/36.45      inference('sup-', [status(thm)], ['42', '43'])).
% 36.25/36.45  thf('45', plain,
% 36.25/36.45      ((((sk_A) = (sk_B)))
% 36.25/36.45         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 36.25/36.45             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 36.25/36.45      inference('sup-', [status(thm)], ['31', '44'])).
% 36.25/36.45  thf('46', plain,
% 36.25/36.45      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 36.25/36.45         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 36.25/36.45      inference('demod', [status(thm)], ['10', '11'])).
% 36.25/36.45  thf('47', plain,
% 36.25/36.45      (![X8 : $i, X10 : $i]:
% 36.25/36.45         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 36.25/36.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 36.25/36.45  thf('48', plain,
% 36.25/36.45      (((~ (r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A))
% 36.25/36.45         | ((sk_B) = (k1_ordinal1 @ sk_A))))
% 36.25/36.45         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 36.25/36.45      inference('sup-', [status(thm)], ['46', '47'])).
% 36.25/36.45  thf('49', plain,
% 36.25/36.45      (((~ (r1_tarski @ sk_A @ (k1_ordinal1 @ sk_A))
% 36.25/36.45         | ((sk_B) = (k1_ordinal1 @ sk_A))))
% 36.25/36.45         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 36.25/36.45             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 36.25/36.45      inference('sup-', [status(thm)], ['45', '48'])).
% 36.25/36.45  thf('50', plain,
% 36.25/36.45      (![X50 : $i]:
% 36.25/36.45         ((v3_ordinal1 @ (k1_ordinal1 @ X50)) | ~ (v3_ordinal1 @ X50))),
% 36.25/36.45      inference('cnf', [status(esa)], [t29_ordinal1])).
% 36.25/36.45  thf('51', plain,
% 36.25/36.45      (![X50 : $i]:
% 36.25/36.45         ((v3_ordinal1 @ (k1_ordinal1 @ X50)) | ~ (v3_ordinal1 @ X50))),
% 36.25/36.45      inference('cnf', [status(esa)], [t29_ordinal1])).
% 36.25/36.45  thf('52', plain, ((v3_ordinal1 @ sk_A)),
% 36.25/36.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.25/36.45  thf('53', plain,
% 36.25/36.45      (![X48 : $i, X49 : $i]:
% 36.25/36.45         (~ (v3_ordinal1 @ X48)
% 36.25/36.45          | (r1_ordinal1 @ X49 @ X48)
% 36.25/36.45          | (r2_hidden @ X48 @ X49)
% 36.25/36.45          | ~ (v3_ordinal1 @ X49))),
% 36.25/36.45      inference('cnf', [status(esa)], [t26_ordinal1])).
% 36.25/36.45  thf('54', plain,
% 36.25/36.45      (![X48 : $i, X49 : $i]:
% 36.25/36.45         (~ (v3_ordinal1 @ X48)
% 36.25/36.45          | (r1_ordinal1 @ X49 @ X48)
% 36.25/36.45          | (r2_hidden @ X48 @ X49)
% 36.25/36.45          | ~ (v3_ordinal1 @ X49))),
% 36.25/36.45      inference('cnf', [status(esa)], [t26_ordinal1])).
% 36.25/36.45  thf(antisymmetry_r2_hidden, axiom,
% 36.25/36.45    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 36.25/36.45  thf('55', plain,
% 36.25/36.45      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 36.25/36.45      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 36.25/36.45  thf('56', plain,
% 36.25/36.45      (![X0 : $i, X1 : $i]:
% 36.25/36.45         (~ (v3_ordinal1 @ X0)
% 36.25/36.45          | (r1_ordinal1 @ X0 @ X1)
% 36.25/36.45          | ~ (v3_ordinal1 @ X1)
% 36.25/36.45          | ~ (r2_hidden @ X0 @ X1))),
% 36.25/36.45      inference('sup-', [status(thm)], ['54', '55'])).
% 36.25/36.45  thf('57', plain,
% 36.25/36.45      (![X0 : $i, X1 : $i]:
% 36.25/36.45         (~ (v3_ordinal1 @ X0)
% 36.25/36.45          | (r1_ordinal1 @ X0 @ X1)
% 36.25/36.45          | ~ (v3_ordinal1 @ X1)
% 36.25/36.45          | ~ (v3_ordinal1 @ X0)
% 36.25/36.45          | (r1_ordinal1 @ X1 @ X0)
% 36.25/36.45          | ~ (v3_ordinal1 @ X1))),
% 36.25/36.45      inference('sup-', [status(thm)], ['53', '56'])).
% 36.25/36.45  thf('58', plain,
% 36.25/36.45      (![X0 : $i, X1 : $i]:
% 36.25/36.45         ((r1_ordinal1 @ X1 @ X0)
% 36.25/36.45          | ~ (v3_ordinal1 @ X1)
% 36.25/36.45          | (r1_ordinal1 @ X0 @ X1)
% 36.25/36.45          | ~ (v3_ordinal1 @ X0))),
% 36.25/36.45      inference('simplify', [status(thm)], ['57'])).
% 36.25/36.45  thf('59', plain,
% 36.25/36.45      (![X0 : $i]:
% 36.25/36.45         (~ (v3_ordinal1 @ X0)
% 36.25/36.45          | (r1_ordinal1 @ X0 @ sk_A)
% 36.25/36.45          | (r1_ordinal1 @ sk_A @ X0))),
% 36.25/36.45      inference('sup-', [status(thm)], ['52', '58'])).
% 36.25/36.45  thf('60', plain,
% 36.25/36.45      (![X45 : $i, X46 : $i]:
% 36.25/36.45         (~ (v3_ordinal1 @ X45)
% 36.25/36.45          | ~ (v3_ordinal1 @ X46)
% 36.25/36.45          | (r1_tarski @ X45 @ X46)
% 36.25/36.45          | ~ (r1_ordinal1 @ X45 @ X46))),
% 36.25/36.45      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 36.25/36.45  thf('61', plain,
% 36.25/36.45      (![X0 : $i]:
% 36.25/36.45         ((r1_ordinal1 @ sk_A @ X0)
% 36.25/36.45          | ~ (v3_ordinal1 @ X0)
% 36.25/36.45          | (r1_tarski @ X0 @ sk_A)
% 36.25/36.45          | ~ (v3_ordinal1 @ sk_A)
% 36.25/36.45          | ~ (v3_ordinal1 @ X0))),
% 36.25/36.45      inference('sup-', [status(thm)], ['59', '60'])).
% 36.25/36.45  thf('62', plain, ((v3_ordinal1 @ sk_A)),
% 36.25/36.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.25/36.45  thf('63', plain,
% 36.25/36.45      (![X0 : $i]:
% 36.25/36.45         ((r1_ordinal1 @ sk_A @ X0)
% 36.25/36.45          | ~ (v3_ordinal1 @ X0)
% 36.25/36.45          | (r1_tarski @ X0 @ sk_A)
% 36.25/36.45          | ~ (v3_ordinal1 @ X0))),
% 36.25/36.45      inference('demod', [status(thm)], ['61', '62'])).
% 36.25/36.45  thf('64', plain,
% 36.25/36.45      (![X0 : $i]:
% 36.25/36.45         ((r1_tarski @ X0 @ sk_A)
% 36.25/36.45          | ~ (v3_ordinal1 @ X0)
% 36.25/36.45          | (r1_ordinal1 @ sk_A @ X0))),
% 36.25/36.45      inference('simplify', [status(thm)], ['63'])).
% 36.25/36.45  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 36.25/36.45  thf('65', plain, (![X47 : $i]: (r2_hidden @ X47 @ (k1_ordinal1 @ X47))),
% 36.25/36.45      inference('cnf', [status(esa)], [t10_ordinal1])).
% 36.25/36.45  thf('66', plain,
% 36.25/36.45      (![X51 : $i, X52 : $i]:
% 36.25/36.45         (~ (r2_hidden @ X51 @ X52) | ~ (r1_tarski @ X52 @ X51))),
% 36.25/36.45      inference('cnf', [status(esa)], [t7_ordinal1])).
% 36.25/36.45  thf('67', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X0)),
% 36.25/36.45      inference('sup-', [status(thm)], ['65', '66'])).
% 36.25/36.45  thf('68', plain,
% 36.25/36.45      (((r1_ordinal1 @ sk_A @ (k1_ordinal1 @ sk_A))
% 36.25/36.45        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 36.25/36.45      inference('sup-', [status(thm)], ['64', '67'])).
% 36.25/36.45  thf('69', plain,
% 36.25/36.45      ((~ (v3_ordinal1 @ sk_A) | (r1_ordinal1 @ sk_A @ (k1_ordinal1 @ sk_A)))),
% 36.25/36.45      inference('sup-', [status(thm)], ['51', '68'])).
% 36.25/36.45  thf('70', plain, ((v3_ordinal1 @ sk_A)),
% 36.25/36.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.25/36.45  thf('71', plain, ((r1_ordinal1 @ sk_A @ (k1_ordinal1 @ sk_A))),
% 36.25/36.45      inference('demod', [status(thm)], ['69', '70'])).
% 36.25/36.45  thf('72', plain,
% 36.25/36.45      (![X45 : $i, X46 : $i]:
% 36.25/36.45         (~ (v3_ordinal1 @ X45)
% 36.25/36.45          | ~ (v3_ordinal1 @ X46)
% 36.25/36.45          | (r1_tarski @ X45 @ X46)
% 36.25/36.45          | ~ (r1_ordinal1 @ X45 @ X46))),
% 36.25/36.45      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 36.25/36.45  thf('73', plain,
% 36.25/36.45      (((r1_tarski @ sk_A @ (k1_ordinal1 @ sk_A))
% 36.25/36.45        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))
% 36.25/36.45        | ~ (v3_ordinal1 @ sk_A))),
% 36.25/36.45      inference('sup-', [status(thm)], ['71', '72'])).
% 36.25/36.45  thf('74', plain, ((v3_ordinal1 @ sk_A)),
% 36.25/36.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.25/36.45  thf('75', plain,
% 36.25/36.45      (((r1_tarski @ sk_A @ (k1_ordinal1 @ sk_A))
% 36.25/36.45        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 36.25/36.45      inference('demod', [status(thm)], ['73', '74'])).
% 36.25/36.45  thf('76', plain,
% 36.25/36.45      ((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ sk_A @ (k1_ordinal1 @ sk_A)))),
% 36.25/36.45      inference('sup-', [status(thm)], ['50', '75'])).
% 36.25/36.45  thf('77', plain, ((v3_ordinal1 @ sk_A)),
% 36.25/36.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.25/36.45  thf('78', plain, ((r1_tarski @ sk_A @ (k1_ordinal1 @ sk_A))),
% 36.25/36.45      inference('demod', [status(thm)], ['76', '77'])).
% 36.25/36.45  thf('79', plain,
% 36.25/36.45      ((((sk_A) = (sk_B)))
% 36.25/36.45         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 36.25/36.45             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 36.25/36.45      inference('sup-', [status(thm)], ['31', '44'])).
% 36.25/36.45  thf('80', plain,
% 36.25/36.45      ((((sk_A) = (k1_ordinal1 @ sk_A)))
% 36.25/36.45         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 36.25/36.45             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 36.25/36.45      inference('demod', [status(thm)], ['49', '78', '79'])).
% 36.25/36.45  thf('81', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X0)),
% 36.25/36.45      inference('sup-', [status(thm)], ['65', '66'])).
% 36.25/36.45  thf('82', plain,
% 36.25/36.45      ((~ (r1_tarski @ sk_A @ sk_A))
% 36.25/36.45         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 36.25/36.45             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 36.25/36.45      inference('sup-', [status(thm)], ['80', '81'])).
% 36.25/36.45  thf('83', plain,
% 36.25/36.45      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 36.25/36.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 36.25/36.45  thf('84', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 36.25/36.45      inference('simplify', [status(thm)], ['83'])).
% 36.25/36.45  thf('85', plain,
% 36.25/36.45      (((r2_hidden @ sk_A @ sk_B)) | 
% 36.25/36.45       ~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 36.25/36.45      inference('demod', [status(thm)], ['82', '84'])).
% 36.25/36.45  thf('86', plain, (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 36.25/36.45      inference('sat_resolution*', [status(thm)], ['2', '85'])).
% 36.25/36.45  thf('87', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 36.25/36.45      inference('simpl_trail', [status(thm)], ['1', '86'])).
% 36.25/36.45  thf('88', plain,
% 36.25/36.45      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 36.25/36.45      inference('split', [status(esa)], ['4'])).
% 36.25/36.45  thf(l1_zfmisc_1, axiom,
% 36.25/36.45    (![A:$i,B:$i]:
% 36.25/36.45     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 36.25/36.45  thf('89', plain,
% 36.25/36.45      (![X39 : $i, X41 : $i]:
% 36.25/36.45         ((r1_tarski @ (k1_tarski @ X39) @ X41) | ~ (r2_hidden @ X39 @ X41))),
% 36.25/36.45      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 36.25/36.45  thf('90', plain,
% 36.25/36.45      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B))
% 36.25/36.45         <= (((r2_hidden @ sk_A @ sk_B)))),
% 36.25/36.45      inference('sup-', [status(thm)], ['88', '89'])).
% 36.25/36.45  thf('91', plain,
% 36.25/36.45      (((r2_hidden @ sk_A @ sk_B)) | 
% 36.25/36.45       ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 36.25/36.45      inference('split', [status(esa)], ['4'])).
% 36.25/36.45  thf('92', plain, (((r2_hidden @ sk_A @ sk_B))),
% 36.25/36.45      inference('sat_resolution*', [status(thm)], ['2', '85', '91'])).
% 36.25/36.45  thf('93', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 36.25/36.45      inference('simpl_trail', [status(thm)], ['90', '92'])).
% 36.25/36.45  thf('94', plain,
% 36.25/36.45      (![X50 : $i]:
% 36.25/36.45         ((v3_ordinal1 @ (k1_ordinal1 @ X50)) | ~ (v3_ordinal1 @ X50))),
% 36.25/36.45      inference('cnf', [status(esa)], [t29_ordinal1])).
% 36.25/36.45  thf('95', plain,
% 36.25/36.45      (![X48 : $i, X49 : $i]:
% 36.25/36.45         (~ (v3_ordinal1 @ X48)
% 36.25/36.45          | (r1_ordinal1 @ X49 @ X48)
% 36.25/36.45          | (r2_hidden @ X48 @ X49)
% 36.25/36.45          | ~ (v3_ordinal1 @ X49))),
% 36.25/36.45      inference('cnf', [status(esa)], [t26_ordinal1])).
% 36.25/36.45  thf('96', plain,
% 36.25/36.45      (![X44 : $i]:
% 36.25/36.45         ((k1_ordinal1 @ X44) = (k2_xboole_0 @ X44 @ (k1_tarski @ X44)))),
% 36.25/36.45      inference('cnf', [status(esa)], [d1_ordinal1])).
% 36.25/36.45  thf('97', plain,
% 36.25/36.45      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 36.25/36.45         (~ (r2_hidden @ X6 @ X4)
% 36.25/36.45          | (r2_hidden @ X6 @ X5)
% 36.25/36.45          | (r2_hidden @ X6 @ X3)
% 36.25/36.45          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 36.25/36.45      inference('cnf', [status(esa)], [d3_xboole_0])).
% 36.25/36.45  thf('98', plain,
% 36.25/36.45      (![X3 : $i, X5 : $i, X6 : $i]:
% 36.25/36.45         ((r2_hidden @ X6 @ X3)
% 36.25/36.45          | (r2_hidden @ X6 @ X5)
% 36.25/36.45          | ~ (r2_hidden @ X6 @ (k2_xboole_0 @ X5 @ X3)))),
% 36.25/36.45      inference('simplify', [status(thm)], ['97'])).
% 36.25/36.45  thf('99', plain,
% 36.25/36.45      (![X0 : $i, X1 : $i]:
% 36.25/36.45         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 36.25/36.45          | (r2_hidden @ X1 @ X0)
% 36.25/36.45          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 36.25/36.45      inference('sup-', [status(thm)], ['96', '98'])).
% 36.25/36.45  thf('100', plain,
% 36.25/36.45      (![X0 : $i, X1 : $i]:
% 36.25/36.45         (~ (v3_ordinal1 @ (k1_ordinal1 @ X0))
% 36.25/36.45          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1)
% 36.25/36.45          | ~ (v3_ordinal1 @ X1)
% 36.25/36.45          | (r2_hidden @ X1 @ (k1_tarski @ X0))
% 36.25/36.45          | (r2_hidden @ X1 @ X0))),
% 36.25/36.45      inference('sup-', [status(thm)], ['95', '99'])).
% 36.25/36.45  thf('101', plain,
% 36.25/36.45      (![X0 : $i, X1 : $i]:
% 36.25/36.45         (~ (v3_ordinal1 @ X0)
% 36.25/36.45          | (r2_hidden @ X1 @ X0)
% 36.25/36.45          | (r2_hidden @ X1 @ (k1_tarski @ X0))
% 36.25/36.45          | ~ (v3_ordinal1 @ X1)
% 36.25/36.45          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1))),
% 36.25/36.45      inference('sup-', [status(thm)], ['94', '100'])).
% 36.25/36.45  thf('102', plain,
% 36.25/36.45      (![X51 : $i, X52 : $i]:
% 36.25/36.45         (~ (r2_hidden @ X51 @ X52) | ~ (r1_tarski @ X52 @ X51))),
% 36.25/36.45      inference('cnf', [status(esa)], [t7_ordinal1])).
% 36.25/36.45  thf('103', plain,
% 36.25/36.45      (![X0 : $i, X1 : $i]:
% 36.25/36.45         ((r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1)
% 36.25/36.45          | ~ (v3_ordinal1 @ X1)
% 36.25/36.45          | (r2_hidden @ X1 @ X0)
% 36.25/36.45          | ~ (v3_ordinal1 @ X0)
% 36.25/36.45          | ~ (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 36.25/36.45      inference('sup-', [status(thm)], ['101', '102'])).
% 36.25/36.45  thf('104', plain,
% 36.25/36.45      ((~ (v3_ordinal1 @ sk_A)
% 36.25/36.45        | (r2_hidden @ sk_B @ sk_A)
% 36.25/36.45        | ~ (v3_ordinal1 @ sk_B)
% 36.25/36.45        | (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 36.25/36.45      inference('sup-', [status(thm)], ['93', '103'])).
% 36.25/36.45  thf('105', plain, ((v3_ordinal1 @ sk_A)),
% 36.25/36.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.25/36.45  thf('106', plain, ((v3_ordinal1 @ sk_B)),
% 36.25/36.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.25/36.45  thf('107', plain,
% 36.25/36.45      (((r2_hidden @ sk_B @ sk_A) | (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 36.25/36.45      inference('demod', [status(thm)], ['104', '105', '106'])).
% 36.25/36.45  thf('108', plain,
% 36.25/36.45      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 36.25/36.45      inference('split', [status(esa)], ['4'])).
% 36.25/36.45  thf('109', plain,
% 36.25/36.45      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 36.25/36.45      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 36.25/36.45  thf('110', plain,
% 36.25/36.45      ((~ (r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 36.25/36.45      inference('sup-', [status(thm)], ['108', '109'])).
% 36.25/36.45  thf('111', plain, (((r2_hidden @ sk_A @ sk_B))),
% 36.25/36.45      inference('sat_resolution*', [status(thm)], ['2', '85', '91'])).
% 36.25/36.45  thf('112', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 36.25/36.45      inference('simpl_trail', [status(thm)], ['110', '111'])).
% 36.25/36.45  thf('113', plain, ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 36.25/36.45      inference('clc', [status(thm)], ['107', '112'])).
% 36.25/36.45  thf('114', plain, ($false), inference('demod', [status(thm)], ['87', '113'])).
% 36.25/36.45  
% 36.25/36.45  % SZS output end Refutation
% 36.25/36.45  
% 36.25/36.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
