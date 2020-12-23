%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XQDeLqo6ge

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:00 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 152 expanded)
%              Number of leaves         :   26 (  52 expanded)
%              Depth                    :   13
%              Number of atoms          :  695 (1204 expanded)
%              Number of equality atoms :   22 (  26 expanded)
%              Maximal formula depth    :   12 (   6 average)

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

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t34_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
          <=> ( r1_ordinal1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
            <=> ( r1_ordinal1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_ordinal1])).

thf('0',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v3_ordinal1 @ X27 )
      | ( r1_ordinal1 @ X28 @ X27 )
      | ( r2_hidden @ X27 @ X28 )
      | ~ ( v3_ordinal1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X18: $i,X20: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X18 ) @ X20 )
      | ~ ( r2_hidden @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('7',plain,(
    ! [X22: $i] :
      ( ( k1_ordinal1 @ X22 )
      = ( k2_xboole_0 @ X22 @ ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('9',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('12',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X29 @ X30 )
      | ~ ( r1_tarski @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('13',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','13'])).

thf('15',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( r1_ordinal1 @ sk_A @ sk_B )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v3_ordinal1 @ X27 )
      | ( r1_ordinal1 @ X28 @ X27 )
      | ( r2_hidden @ X27 @ X28 )
      | ~ ( v3_ordinal1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( r1_ordinal1 @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( r1_ordinal1 @ sk_A @ sk_B )
      | ( r1_ordinal1 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('29',plain,(
    ! [X22: $i] :
      ( ( k1_ordinal1 @ X22 )
      = ( k2_xboole_0 @ X22 @ ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('30',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v3_ordinal1 @ X27 )
      | ( r1_ordinal1 @ X28 @ X27 )
      | ( r2_hidden @ X27 @ X28 )
      | ~ ( v3_ordinal1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('31',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X5 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('32',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X5 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','33'])).

thf('35',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('40',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v3_ordinal1 @ X23 )
      | ~ ( v3_ordinal1 @ X24 )
      | ( r1_tarski @ X23 @ X24 )
      | ~ ( r1_ordinal1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('41',plain,
    ( ( ( r1_tarski @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('46',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v3_ordinal1 @ X23 )
      | ~ ( v3_ordinal1 @ X24 )
      | ( r1_tarski @ X23 @ X24 )
      | ~ ( r1_ordinal1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('47',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('51',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r2_xboole_0 @ X8 @ X10 )
      | ( X8 = X10 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('52',plain,
    ( ( ( sk_A = sk_B )
      | ( r2_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(t21_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_xboole_0 @ A @ B )
           => ( r2_hidden @ A @ B ) ) ) ) )).

thf('53',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v3_ordinal1 @ X25 )
      | ( r2_hidden @ X26 @ X25 )
      | ~ ( r2_xboole_0 @ X26 @ X25 )
      | ~ ( v1_ordinal1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t21_ordinal1])).

thf('54',plain,
    ( ( ( sk_A = sk_B )
      | ~ ( v1_ordinal1 @ sk_A )
      | ( r2_hidden @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('56',plain,(
    ! [X21: $i] :
      ( ( v1_ordinal1 @ X21 )
      | ~ ( v3_ordinal1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('57',plain,(
    v1_ordinal1 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( ( sk_A = sk_B )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['54','57','58'])).

thf('60',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X29 @ X30 )
      | ~ ( r1_tarski @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('61',plain,
    ( ( ( sk_A = sk_B )
      | ~ ( r1_tarski @ sk_B @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','61'])).

thf('63',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('64',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X22: $i] :
      ( ( k1_ordinal1 @ X22 )
      = ( k2_xboole_0 @ X22 @ ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('66',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('67',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X12 != X11 )
      | ( r2_hidden @ X12 @ X13 )
      | ( X13
       != ( k2_tarski @ X14 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('68',plain,(
    ! [X11: $i,X14: $i] :
      ( r2_hidden @ X11 @ ( k2_tarski @ X14 @ X11 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','68'])).

thf('70',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('71',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['69','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','72'])).

thf('74',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['64','73'])).

thf('75',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','27','28','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XQDeLqo6ge
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:54:33 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.37/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.63  % Solved by: fo/fo7.sh
% 0.37/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.63  % done 307 iterations in 0.181s
% 0.37/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.63  % SZS output start Refutation
% 0.37/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.63  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.37/0.63  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.37/0.63  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.37/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.63  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.63  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.37/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.63  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.37/0.63  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.37/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.63  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.63  thf(t34_ordinal1, conjecture,
% 0.37/0.63    (![A:$i]:
% 0.37/0.63     ( ( v3_ordinal1 @ A ) =>
% 0.37/0.63       ( ![B:$i]:
% 0.37/0.63         ( ( v3_ordinal1 @ B ) =>
% 0.37/0.63           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.37/0.63             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.37/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.63    (~( ![A:$i]:
% 0.37/0.63        ( ( v3_ordinal1 @ A ) =>
% 0.37/0.63          ( ![B:$i]:
% 0.37/0.63            ( ( v3_ordinal1 @ B ) =>
% 0.37/0.63              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.37/0.63                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 0.37/0.63    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 0.37/0.63  thf('0', plain,
% 0.37/0.63      ((~ (r1_ordinal1 @ sk_A @ sk_B)
% 0.37/0.63        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('1', plain,
% 0.37/0.63      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.37/0.63       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.37/0.63      inference('split', [status(esa)], ['0'])).
% 0.37/0.63  thf(t26_ordinal1, axiom,
% 0.37/0.63    (![A:$i]:
% 0.37/0.63     ( ( v3_ordinal1 @ A ) =>
% 0.37/0.63       ( ![B:$i]:
% 0.37/0.63         ( ( v3_ordinal1 @ B ) =>
% 0.37/0.63           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.37/0.63  thf('2', plain,
% 0.37/0.63      (![X27 : $i, X28 : $i]:
% 0.37/0.63         (~ (v3_ordinal1 @ X27)
% 0.37/0.63          | (r1_ordinal1 @ X28 @ X27)
% 0.37/0.63          | (r2_hidden @ X27 @ X28)
% 0.37/0.63          | ~ (v3_ordinal1 @ X28))),
% 0.37/0.63      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.37/0.63  thf(l1_zfmisc_1, axiom,
% 0.37/0.63    (![A:$i,B:$i]:
% 0.37/0.63     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.37/0.63  thf('3', plain,
% 0.37/0.63      (![X18 : $i, X20 : $i]:
% 0.37/0.63         ((r1_tarski @ (k1_tarski @ X18) @ X20) | ~ (r2_hidden @ X18 @ X20))),
% 0.37/0.63      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.37/0.63  thf('4', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]:
% 0.37/0.63         (~ (v3_ordinal1 @ X0)
% 0.37/0.63          | (r1_ordinal1 @ X0 @ X1)
% 0.37/0.63          | ~ (v3_ordinal1 @ X1)
% 0.37/0.63          | (r1_tarski @ (k1_tarski @ X1) @ X0))),
% 0.37/0.63      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.63  thf('5', plain,
% 0.37/0.63      (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('6', plain,
% 0.37/0.63      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.37/0.63         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.63      inference('split', [status(esa)], ['5'])).
% 0.37/0.63  thf(d1_ordinal1, axiom,
% 0.37/0.63    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.37/0.63  thf('7', plain,
% 0.37/0.63      (![X22 : $i]:
% 0.37/0.63         ((k1_ordinal1 @ X22) = (k2_xboole_0 @ X22 @ (k1_tarski @ X22)))),
% 0.37/0.63      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.37/0.63  thf(d3_xboole_0, axiom,
% 0.37/0.63    (![A:$i,B:$i,C:$i]:
% 0.37/0.63     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.37/0.63       ( ![D:$i]:
% 0.37/0.63         ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.63           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.37/0.63  thf('8', plain,
% 0.37/0.63      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.37/0.63         (~ (r2_hidden @ X6 @ X4)
% 0.37/0.63          | (r2_hidden @ X6 @ X5)
% 0.37/0.63          | (r2_hidden @ X6 @ X3)
% 0.37/0.63          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.37/0.63      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.37/0.63  thf('9', plain,
% 0.37/0.63      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.37/0.63         ((r2_hidden @ X6 @ X3)
% 0.37/0.63          | (r2_hidden @ X6 @ X5)
% 0.37/0.63          | ~ (r2_hidden @ X6 @ (k2_xboole_0 @ X5 @ X3)))),
% 0.37/0.63      inference('simplify', [status(thm)], ['8'])).
% 0.37/0.63  thf('10', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]:
% 0.37/0.63         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.37/0.63          | (r2_hidden @ X1 @ X0)
% 0.37/0.63          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['7', '9'])).
% 0.37/0.63  thf('11', plain,
% 0.37/0.63      ((((r2_hidden @ sk_A @ (k1_tarski @ sk_B)) | (r2_hidden @ sk_A @ sk_B)))
% 0.37/0.63         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.63      inference('sup-', [status(thm)], ['6', '10'])).
% 0.37/0.63  thf(t7_ordinal1, axiom,
% 0.37/0.63    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.63  thf('12', plain,
% 0.37/0.63      (![X29 : $i, X30 : $i]:
% 0.37/0.63         (~ (r2_hidden @ X29 @ X30) | ~ (r1_tarski @ X30 @ X29))),
% 0.37/0.63      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.37/0.63  thf('13', plain,
% 0.37/0.63      ((((r2_hidden @ sk_A @ sk_B) | ~ (r1_tarski @ (k1_tarski @ sk_B) @ sk_A)))
% 0.37/0.63         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.63      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.63  thf('14', plain,
% 0.37/0.63      (((~ (v3_ordinal1 @ sk_B)
% 0.37/0.63         | (r1_ordinal1 @ sk_A @ sk_B)
% 0.37/0.63         | ~ (v3_ordinal1 @ sk_A)
% 0.37/0.63         | (r2_hidden @ sk_A @ sk_B)))
% 0.37/0.63         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.63      inference('sup-', [status(thm)], ['4', '13'])).
% 0.37/0.63  thf('15', plain, ((v3_ordinal1 @ sk_B)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('16', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('17', plain,
% 0.37/0.63      ((((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ sk_B)))
% 0.37/0.63         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.63      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.37/0.63  thf('18', plain,
% 0.37/0.63      (![X27 : $i, X28 : $i]:
% 0.37/0.63         (~ (v3_ordinal1 @ X27)
% 0.37/0.63          | (r1_ordinal1 @ X28 @ X27)
% 0.37/0.63          | (r2_hidden @ X27 @ X28)
% 0.37/0.63          | ~ (v3_ordinal1 @ X28))),
% 0.37/0.63      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.37/0.63  thf(antisymmetry_r2_hidden, axiom,
% 0.37/0.63    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.37/0.63  thf('19', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.37/0.63      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.37/0.63  thf('20', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]:
% 0.37/0.63         (~ (v3_ordinal1 @ X0)
% 0.37/0.63          | (r1_ordinal1 @ X0 @ X1)
% 0.37/0.63          | ~ (v3_ordinal1 @ X1)
% 0.37/0.63          | ~ (r2_hidden @ X0 @ X1))),
% 0.37/0.63      inference('sup-', [status(thm)], ['18', '19'])).
% 0.37/0.63  thf('21', plain,
% 0.37/0.63      ((((r1_ordinal1 @ sk_A @ sk_B)
% 0.37/0.63         | ~ (v3_ordinal1 @ sk_B)
% 0.37/0.63         | (r1_ordinal1 @ sk_A @ sk_B)
% 0.37/0.63         | ~ (v3_ordinal1 @ sk_A)))
% 0.37/0.63         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.63      inference('sup-', [status(thm)], ['17', '20'])).
% 0.37/0.63  thf('22', plain, ((v3_ordinal1 @ sk_B)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('23', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('24', plain,
% 0.37/0.63      ((((r1_ordinal1 @ sk_A @ sk_B) | (r1_ordinal1 @ sk_A @ sk_B)))
% 0.37/0.63         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.63      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.37/0.63  thf('25', plain,
% 0.37/0.63      (((r1_ordinal1 @ sk_A @ sk_B))
% 0.37/0.63         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.63      inference('simplify', [status(thm)], ['24'])).
% 0.37/0.63  thf('26', plain,
% 0.37/0.63      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.37/0.63      inference('split', [status(esa)], ['0'])).
% 0.37/0.63  thf('27', plain,
% 0.37/0.63      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.37/0.63       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['25', '26'])).
% 0.37/0.63  thf('28', plain,
% 0.37/0.63      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.37/0.63       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.37/0.63      inference('split', [status(esa)], ['5'])).
% 0.37/0.63  thf('29', plain,
% 0.37/0.63      (![X22 : $i]:
% 0.37/0.63         ((k1_ordinal1 @ X22) = (k2_xboole_0 @ X22 @ (k1_tarski @ X22)))),
% 0.37/0.63      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.37/0.63  thf('30', plain,
% 0.37/0.63      (![X27 : $i, X28 : $i]:
% 0.37/0.63         (~ (v3_ordinal1 @ X27)
% 0.37/0.63          | (r1_ordinal1 @ X28 @ X27)
% 0.37/0.63          | (r2_hidden @ X27 @ X28)
% 0.37/0.63          | ~ (v3_ordinal1 @ X28))),
% 0.37/0.63      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.37/0.63  thf('31', plain,
% 0.37/0.63      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.37/0.63         (~ (r2_hidden @ X2 @ X5)
% 0.37/0.63          | (r2_hidden @ X2 @ X4)
% 0.37/0.63          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.37/0.63      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.37/0.63  thf('32', plain,
% 0.37/0.63      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.37/0.63         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X5))),
% 0.37/0.63      inference('simplify', [status(thm)], ['31'])).
% 0.37/0.63  thf('33', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.63         (~ (v3_ordinal1 @ X0)
% 0.37/0.63          | (r1_ordinal1 @ X0 @ X1)
% 0.37/0.63          | ~ (v3_ordinal1 @ X1)
% 0.37/0.63          | (r2_hidden @ X1 @ (k2_xboole_0 @ X0 @ X2)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['30', '32'])).
% 0.37/0.63  thf('34', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]:
% 0.37/0.63         ((r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.37/0.63          | ~ (v3_ordinal1 @ X1)
% 0.37/0.63          | (r1_ordinal1 @ X0 @ X1)
% 0.37/0.63          | ~ (v3_ordinal1 @ X0))),
% 0.37/0.63      inference('sup+', [status(thm)], ['29', '33'])).
% 0.37/0.63  thf('35', plain,
% 0.37/0.63      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.37/0.63         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.63      inference('split', [status(esa)], ['0'])).
% 0.37/0.63  thf('36', plain,
% 0.37/0.63      (((~ (v3_ordinal1 @ sk_B)
% 0.37/0.63         | (r1_ordinal1 @ sk_B @ sk_A)
% 0.37/0.63         | ~ (v3_ordinal1 @ sk_A)))
% 0.37/0.63         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.63      inference('sup-', [status(thm)], ['34', '35'])).
% 0.37/0.63  thf('37', plain, ((v3_ordinal1 @ sk_B)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('38', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('39', plain,
% 0.37/0.63      (((r1_ordinal1 @ sk_B @ sk_A))
% 0.37/0.63         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.63      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.37/0.63  thf(redefinition_r1_ordinal1, axiom,
% 0.37/0.63    (![A:$i,B:$i]:
% 0.37/0.63     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.37/0.63       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.37/0.63  thf('40', plain,
% 0.37/0.63      (![X23 : $i, X24 : $i]:
% 0.37/0.63         (~ (v3_ordinal1 @ X23)
% 0.37/0.63          | ~ (v3_ordinal1 @ X24)
% 0.37/0.63          | (r1_tarski @ X23 @ X24)
% 0.37/0.63          | ~ (r1_ordinal1 @ X23 @ X24))),
% 0.37/0.63      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.37/0.63  thf('41', plain,
% 0.37/0.63      ((((r1_tarski @ sk_B @ sk_A)
% 0.37/0.63         | ~ (v3_ordinal1 @ sk_A)
% 0.37/0.63         | ~ (v3_ordinal1 @ sk_B)))
% 0.37/0.63         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.63      inference('sup-', [status(thm)], ['39', '40'])).
% 0.37/0.63  thf('42', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('43', plain, ((v3_ordinal1 @ sk_B)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('44', plain,
% 0.37/0.63      (((r1_tarski @ sk_B @ sk_A))
% 0.37/0.63         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.63      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.37/0.63  thf('45', plain,
% 0.37/0.63      (((r1_ordinal1 @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.37/0.63      inference('split', [status(esa)], ['5'])).
% 0.37/0.63  thf('46', plain,
% 0.37/0.63      (![X23 : $i, X24 : $i]:
% 0.37/0.63         (~ (v3_ordinal1 @ X23)
% 0.37/0.63          | ~ (v3_ordinal1 @ X24)
% 0.37/0.63          | (r1_tarski @ X23 @ X24)
% 0.37/0.63          | ~ (r1_ordinal1 @ X23 @ X24))),
% 0.37/0.63      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.37/0.63  thf('47', plain,
% 0.37/0.63      ((((r1_tarski @ sk_A @ sk_B)
% 0.37/0.63         | ~ (v3_ordinal1 @ sk_B)
% 0.37/0.63         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['45', '46'])).
% 0.37/0.63  thf('48', plain, ((v3_ordinal1 @ sk_B)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('49', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('50', plain,
% 0.37/0.63      (((r1_tarski @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.37/0.63      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.37/0.63  thf(d8_xboole_0, axiom,
% 0.37/0.63    (![A:$i,B:$i]:
% 0.37/0.63     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.37/0.63       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.37/0.63  thf('51', plain,
% 0.37/0.63      (![X8 : $i, X10 : $i]:
% 0.37/0.63         ((r2_xboole_0 @ X8 @ X10) | ((X8) = (X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.37/0.63      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.37/0.63  thf('52', plain,
% 0.37/0.63      (((((sk_A) = (sk_B)) | (r2_xboole_0 @ sk_A @ sk_B)))
% 0.37/0.63         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['50', '51'])).
% 0.37/0.63  thf(t21_ordinal1, axiom,
% 0.37/0.63    (![A:$i]:
% 0.37/0.63     ( ( v1_ordinal1 @ A ) =>
% 0.37/0.63       ( ![B:$i]:
% 0.37/0.63         ( ( v3_ordinal1 @ B ) =>
% 0.37/0.63           ( ( r2_xboole_0 @ A @ B ) => ( r2_hidden @ A @ B ) ) ) ) ))).
% 0.37/0.63  thf('53', plain,
% 0.37/0.63      (![X25 : $i, X26 : $i]:
% 0.37/0.63         (~ (v3_ordinal1 @ X25)
% 0.37/0.63          | (r2_hidden @ X26 @ X25)
% 0.37/0.63          | ~ (r2_xboole_0 @ X26 @ X25)
% 0.37/0.63          | ~ (v1_ordinal1 @ X26))),
% 0.37/0.63      inference('cnf', [status(esa)], [t21_ordinal1])).
% 0.37/0.63  thf('54', plain,
% 0.37/0.63      (((((sk_A) = (sk_B))
% 0.37/0.63         | ~ (v1_ordinal1 @ sk_A)
% 0.37/0.63         | (r2_hidden @ sk_A @ sk_B)
% 0.37/0.63         | ~ (v3_ordinal1 @ sk_B))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['52', '53'])).
% 0.37/0.63  thf('55', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf(cc1_ordinal1, axiom,
% 0.37/0.63    (![A:$i]:
% 0.37/0.63     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 0.37/0.63  thf('56', plain,
% 0.37/0.63      (![X21 : $i]: ((v1_ordinal1 @ X21) | ~ (v3_ordinal1 @ X21))),
% 0.37/0.63      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.37/0.63  thf('57', plain, ((v1_ordinal1 @ sk_A)),
% 0.37/0.63      inference('sup-', [status(thm)], ['55', '56'])).
% 0.37/0.63  thf('58', plain, ((v3_ordinal1 @ sk_B)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('59', plain,
% 0.37/0.63      (((((sk_A) = (sk_B)) | (r2_hidden @ sk_A @ sk_B)))
% 0.37/0.63         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.37/0.63      inference('demod', [status(thm)], ['54', '57', '58'])).
% 0.37/0.63  thf('60', plain,
% 0.37/0.63      (![X29 : $i, X30 : $i]:
% 0.37/0.63         (~ (r2_hidden @ X29 @ X30) | ~ (r1_tarski @ X30 @ X29))),
% 0.37/0.63      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.37/0.63  thf('61', plain,
% 0.37/0.63      (((((sk_A) = (sk_B)) | ~ (r1_tarski @ sk_B @ sk_A)))
% 0.37/0.63         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['59', '60'])).
% 0.37/0.63  thf('62', plain,
% 0.37/0.63      ((((sk_A) = (sk_B)))
% 0.37/0.63         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.37/0.63             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['44', '61'])).
% 0.37/0.63  thf('63', plain,
% 0.37/0.63      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.37/0.63         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.63      inference('split', [status(esa)], ['0'])).
% 0.37/0.63  thf('64', plain,
% 0.37/0.63      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 0.37/0.63         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.37/0.63             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['62', '63'])).
% 0.37/0.63  thf('65', plain,
% 0.37/0.63      (![X22 : $i]:
% 0.37/0.63         ((k1_ordinal1 @ X22) = (k2_xboole_0 @ X22 @ (k1_tarski @ X22)))),
% 0.37/0.63      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.37/0.63  thf(t69_enumset1, axiom,
% 0.37/0.63    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.37/0.63  thf('66', plain,
% 0.37/0.63      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.37/0.63      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.63  thf(d2_tarski, axiom,
% 0.37/0.63    (![A:$i,B:$i,C:$i]:
% 0.37/0.63     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.37/0.63       ( ![D:$i]:
% 0.37/0.63         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.37/0.63  thf('67', plain,
% 0.37/0.63      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.63         (((X12) != (X11))
% 0.37/0.63          | (r2_hidden @ X12 @ X13)
% 0.37/0.63          | ((X13) != (k2_tarski @ X14 @ X11)))),
% 0.37/0.63      inference('cnf', [status(esa)], [d2_tarski])).
% 0.37/0.63  thf('68', plain,
% 0.37/0.63      (![X11 : $i, X14 : $i]: (r2_hidden @ X11 @ (k2_tarski @ X14 @ X11))),
% 0.37/0.63      inference('simplify', [status(thm)], ['67'])).
% 0.37/0.63  thf('69', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.37/0.63      inference('sup+', [status(thm)], ['66', '68'])).
% 0.37/0.63  thf('70', plain,
% 0.37/0.63      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.37/0.63         (~ (r2_hidden @ X2 @ X3)
% 0.37/0.63          | (r2_hidden @ X2 @ X4)
% 0.37/0.63          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.37/0.63      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.37/0.63  thf('71', plain,
% 0.37/0.63      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.37/0.63         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 0.37/0.63      inference('simplify', [status(thm)], ['70'])).
% 0.37/0.63  thf('72', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]:
% 0.37/0.63         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['69', '71'])).
% 0.37/0.63  thf('73', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_ordinal1 @ X0))),
% 0.37/0.63      inference('sup+', [status(thm)], ['65', '72'])).
% 0.37/0.63  thf('74', plain,
% 0.37/0.63      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.37/0.63       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.37/0.63      inference('demod', [status(thm)], ['64', '73'])).
% 0.37/0.63  thf('75', plain, ($false),
% 0.37/0.63      inference('sat_resolution*', [status(thm)], ['1', '27', '28', '74'])).
% 0.37/0.63  
% 0.37/0.63  % SZS output end Refutation
% 0.37/0.63  
% 0.45/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
