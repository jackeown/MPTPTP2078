%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EbF2FsbLP5

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 140 expanded)
%              Number of leaves         :   23 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  633 (1092 expanded)
%              Number of equality atoms :   29 (  35 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

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
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v3_ordinal1 @ X23 )
      | ~ ( v3_ordinal1 @ X24 )
      | ( r1_ordinal1 @ X23 @ X24 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['9'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('11',plain,(
    ! [X19: $i] :
      ( ( k1_ordinal1 @ X19 )
      = ( k2_xboole_0 @ X19 @ ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X6
       != ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('13',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ( r2_hidden @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('16',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ( X16 = X13 )
      | ( X15
       != ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('17',plain,(
    ! [X13: $i,X16: $i] :
      ( ( X16 = X13 )
      | ~ ( r2_hidden @ X16 @ ( k1_tarski @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B_1 )
      | ( sk_A = sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ( r1_tarski @ X20 @ X21 )
      | ~ ( v1_ordinal1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('20',plain,
    ( ( ( sk_A = sk_B_1 )
      | ~ ( v1_ordinal1 @ sk_B_1 )
      | ( r1_tarski @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('22',plain,(
    ! [X18: $i] :
      ( ( v1_ordinal1 @ X18 )
      | ~ ( v3_ordinal1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('23',plain,(
    v1_ordinal1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( r1_tarski @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v3_ordinal1 @ X23 )
      | ~ ( v3_ordinal1 @ X24 )
      | ( r1_ordinal1 @ X23 @ X24 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('26',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( r1_ordinal1 @ sk_A @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( r1_ordinal1 @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,
    ( ( sk_A = sk_B_1 )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['8','33'])).

thf('35',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['9'])).

thf('38',plain,(
    ! [X19: $i] :
      ( ( k1_ordinal1 @ X19 )
      = ( k2_xboole_0 @ X19 @ ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('39',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['9'])).

thf('40',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v3_ordinal1 @ X23 )
      | ~ ( v3_ordinal1 @ X24 )
      | ( r1_tarski @ X23 @ X24 )
      | ~ ( r1_ordinal1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('41',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( r1_tarski @ sk_A @ sk_B_1 )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('45',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r2_xboole_0 @ X10 @ X12 )
      | ( X10 = X12 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('46',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( r2_xboole_0 @ sk_A @ sk_B_1 ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(t21_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_xboole_0 @ A @ B )
           => ( r2_hidden @ A @ B ) ) ) ) )).

thf('47',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v3_ordinal1 @ X25 )
      | ( r2_hidden @ X26 @ X25 )
      | ~ ( r2_xboole_0 @ X26 @ X25 )
      | ~ ( v1_ordinal1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t21_ordinal1])).

thf('48',plain,
    ( ( ( sk_A = sk_B_1 )
      | ~ ( v1_ordinal1 @ sk_A )
      | ( r2_hidden @ sk_A @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_B_1 ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X18: $i] :
      ( ( v1_ordinal1 @ X18 )
      | ~ ( v3_ordinal1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('51',plain,(
    v1_ordinal1 @ sk_A ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( r2_hidden @ sk_A @ sk_B_1 ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['48','51','52'])).

thf('54',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X7 )
      | ( r2_hidden @ X4 @ X6 )
      | ( X6
       != ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('55',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k2_xboole_0 @ X7 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X7 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( sk_A = sk_B_1 )
        | ( r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ X0 ) ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
      | ( sk_A = sk_B_1 ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['38','56'])).

thf('58',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('59',plain,
    ( ( sk_A = sk_B_1 )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
      & ( r1_ordinal1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('61',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
      & ( r1_ordinal1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X19: $i] :
      ( ( k1_ordinal1 @ X19 )
      = ( k2_xboole_0 @ X19 @ ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('63',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( X14 != X13 )
      | ( r2_hidden @ X14 @ X15 )
      | ( X15
       != ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('64',plain,(
    ! [X13: $i] :
      ( r2_hidden @ X13 @ ( k1_tarski @ X13 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( X6
       != ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('66',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k2_xboole_0 @ X7 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['62','67'])).

thf('69',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['61','68'])).

thf('70',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','36','37','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EbF2FsbLP5
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:35:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 210 iterations in 0.100s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.21/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.21/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.56  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.21/0.56  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.21/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.56  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.21/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.56  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.21/0.56  thf(t34_ordinal1, conjecture,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( v3_ordinal1 @ A ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( v3_ordinal1 @ B ) =>
% 0.21/0.56           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.21/0.56             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ![A:$i]:
% 0.21/0.56        ( ( v3_ordinal1 @ A ) =>
% 0.21/0.56          ( ![B:$i]:
% 0.21/0.56            ( ( v3_ordinal1 @ B ) =>
% 0.21/0.56              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.21/0.56                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 0.21/0.56  thf('0', plain,
% 0.21/0.56      ((~ (r1_ordinal1 @ sk_A @ sk_B_1)
% 0.21/0.56        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('1', plain,
% 0.21/0.56      (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 0.21/0.56       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.21/0.56      inference('split', [status(esa)], ['0'])).
% 0.21/0.56  thf(d3_tarski, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.56  thf('2', plain,
% 0.21/0.56      (![X1 : $i, X3 : $i]:
% 0.21/0.56         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.56  thf('3', plain,
% 0.21/0.56      (![X1 : $i, X3 : $i]:
% 0.21/0.56         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.56  thf('4', plain,
% 0.21/0.56      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.56  thf('5', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.21/0.56      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.56  thf(redefinition_r1_ordinal1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.21/0.56       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.21/0.56  thf('6', plain,
% 0.21/0.56      (![X23 : $i, X24 : $i]:
% 0.21/0.56         (~ (v3_ordinal1 @ X23)
% 0.21/0.56          | ~ (v3_ordinal1 @ X24)
% 0.21/0.56          | (r1_ordinal1 @ X23 @ X24)
% 0.21/0.56          | ~ (r1_tarski @ X23 @ X24))),
% 0.21/0.56      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.21/0.56  thf('7', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r1_ordinal1 @ X0 @ X0) | ~ (v3_ordinal1 @ X0) | ~ (v3_ordinal1 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.56  thf('8', plain,
% 0.21/0.56      (![X0 : $i]: (~ (v3_ordinal1 @ X0) | (r1_ordinal1 @ X0 @ X0))),
% 0.21/0.56      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.56  thf('9', plain,
% 0.21/0.56      (((r1_ordinal1 @ sk_A @ sk_B_1)
% 0.21/0.56        | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('10', plain,
% 0.21/0.56      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))
% 0.21/0.56         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.56      inference('split', [status(esa)], ['9'])).
% 0.21/0.56  thf(d1_ordinal1, axiom,
% 0.21/0.56    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.21/0.56  thf('11', plain,
% 0.21/0.56      (![X19 : $i]:
% 0.21/0.56         ((k1_ordinal1 @ X19) = (k2_xboole_0 @ X19 @ (k1_tarski @ X19)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.21/0.56  thf(d3_xboole_0, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.21/0.56       ( ![D:$i]:
% 0.21/0.56         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.56           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.21/0.56  thf('12', plain,
% 0.21/0.56      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X8 @ X6)
% 0.21/0.56          | (r2_hidden @ X8 @ X7)
% 0.21/0.56          | (r2_hidden @ X8 @ X5)
% 0.21/0.56          | ((X6) != (k2_xboole_0 @ X7 @ X5)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.21/0.56  thf('13', plain,
% 0.21/0.56      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.21/0.56         ((r2_hidden @ X8 @ X5)
% 0.21/0.56          | (r2_hidden @ X8 @ X7)
% 0.21/0.56          | ~ (r2_hidden @ X8 @ (k2_xboole_0 @ X7 @ X5)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.56  thf('14', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.21/0.56          | (r2_hidden @ X1 @ X0)
% 0.21/0.56          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['11', '13'])).
% 0.21/0.56  thf('15', plain,
% 0.21/0.56      ((((r2_hidden @ sk_A @ (k1_tarski @ sk_B_1))
% 0.21/0.56         | (r2_hidden @ sk_A @ sk_B_1)))
% 0.21/0.56         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['10', '14'])).
% 0.21/0.56  thf(d1_tarski, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.56  thf('16', plain,
% 0.21/0.56      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X16 @ X15)
% 0.21/0.56          | ((X16) = (X13))
% 0.21/0.56          | ((X15) != (k1_tarski @ X13)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.56  thf('17', plain,
% 0.21/0.56      (![X13 : $i, X16 : $i]:
% 0.21/0.56         (((X16) = (X13)) | ~ (r2_hidden @ X16 @ (k1_tarski @ X13)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.56  thf('18', plain,
% 0.21/0.56      ((((r2_hidden @ sk_A @ sk_B_1) | ((sk_A) = (sk_B_1))))
% 0.21/0.56         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['15', '17'])).
% 0.21/0.56  thf(d2_ordinal1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( v1_ordinal1 @ A ) <=>
% 0.21/0.56       ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( r1_tarski @ B @ A ) ) ) ))).
% 0.21/0.56  thf('19', plain,
% 0.21/0.56      (![X20 : $i, X21 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X20 @ X21)
% 0.21/0.56          | (r1_tarski @ X20 @ X21)
% 0.21/0.56          | ~ (v1_ordinal1 @ X21))),
% 0.21/0.56      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.21/0.56  thf('20', plain,
% 0.21/0.56      (((((sk_A) = (sk_B_1))
% 0.21/0.56         | ~ (v1_ordinal1 @ sk_B_1)
% 0.21/0.56         | (r1_tarski @ sk_A @ sk_B_1)))
% 0.21/0.56         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.56  thf('21', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(cc1_ordinal1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 0.21/0.56  thf('22', plain,
% 0.21/0.56      (![X18 : $i]: ((v1_ordinal1 @ X18) | ~ (v3_ordinal1 @ X18))),
% 0.21/0.56      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.21/0.56  thf('23', plain, ((v1_ordinal1 @ sk_B_1)),
% 0.21/0.56      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.56  thf('24', plain,
% 0.21/0.56      (((((sk_A) = (sk_B_1)) | (r1_tarski @ sk_A @ sk_B_1)))
% 0.21/0.56         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.56      inference('demod', [status(thm)], ['20', '23'])).
% 0.21/0.56  thf('25', plain,
% 0.21/0.56      (![X23 : $i, X24 : $i]:
% 0.21/0.56         (~ (v3_ordinal1 @ X23)
% 0.21/0.56          | ~ (v3_ordinal1 @ X24)
% 0.21/0.56          | (r1_ordinal1 @ X23 @ X24)
% 0.21/0.56          | ~ (r1_tarski @ X23 @ X24))),
% 0.21/0.56      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.21/0.56  thf('26', plain,
% 0.21/0.56      (((((sk_A) = (sk_B_1))
% 0.21/0.56         | (r1_ordinal1 @ sk_A @ sk_B_1)
% 0.21/0.56         | ~ (v3_ordinal1 @ sk_B_1)
% 0.21/0.56         | ~ (v3_ordinal1 @ sk_A)))
% 0.21/0.56         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.56  thf('27', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('28', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('29', plain,
% 0.21/0.56      (((((sk_A) = (sk_B_1)) | (r1_ordinal1 @ sk_A @ sk_B_1)))
% 0.21/0.56         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.56      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.21/0.56  thf('30', plain,
% 0.21/0.56      ((~ (r1_ordinal1 @ sk_A @ sk_B_1)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.21/0.56      inference('split', [status(esa)], ['0'])).
% 0.21/0.56  thf('31', plain,
% 0.21/0.56      ((((sk_A) = (sk_B_1)))
% 0.21/0.56         <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) & 
% 0.21/0.56             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.56  thf('32', plain,
% 0.21/0.56      ((~ (r1_ordinal1 @ sk_A @ sk_B_1)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.21/0.56      inference('split', [status(esa)], ['0'])).
% 0.21/0.56  thf('33', plain,
% 0.21/0.56      ((~ (r1_ordinal1 @ sk_A @ sk_A))
% 0.21/0.56         <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) & 
% 0.21/0.56             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.56  thf('34', plain,
% 0.21/0.56      ((~ (v3_ordinal1 @ sk_A))
% 0.21/0.56         <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) & 
% 0.21/0.56             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['8', '33'])).
% 0.21/0.56  thf('35', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('36', plain,
% 0.21/0.56      (((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 0.21/0.56       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.21/0.56      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.56  thf('37', plain,
% 0.21/0.56      (((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 0.21/0.56       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.21/0.56      inference('split', [status(esa)], ['9'])).
% 0.21/0.56  thf('38', plain,
% 0.21/0.56      (![X19 : $i]:
% 0.21/0.56         ((k1_ordinal1 @ X19) = (k2_xboole_0 @ X19 @ (k1_tarski @ X19)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.21/0.56  thf('39', plain,
% 0.21/0.56      (((r1_ordinal1 @ sk_A @ sk_B_1)) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.21/0.56      inference('split', [status(esa)], ['9'])).
% 0.21/0.56  thf('40', plain,
% 0.21/0.56      (![X23 : $i, X24 : $i]:
% 0.21/0.56         (~ (v3_ordinal1 @ X23)
% 0.21/0.56          | ~ (v3_ordinal1 @ X24)
% 0.21/0.56          | (r1_tarski @ X23 @ X24)
% 0.21/0.56          | ~ (r1_ordinal1 @ X23 @ X24))),
% 0.21/0.56      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.21/0.56  thf('41', plain,
% 0.21/0.56      ((((r1_tarski @ sk_A @ sk_B_1)
% 0.21/0.56         | ~ (v3_ordinal1 @ sk_B_1)
% 0.21/0.56         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.56  thf('42', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('43', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('44', plain,
% 0.21/0.56      (((r1_tarski @ sk_A @ sk_B_1)) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.21/0.56      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.21/0.56  thf(d8_xboole_0, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.21/0.56       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.21/0.56  thf('45', plain,
% 0.21/0.56      (![X10 : $i, X12 : $i]:
% 0.21/0.56         ((r2_xboole_0 @ X10 @ X12)
% 0.21/0.56          | ((X10) = (X12))
% 0.21/0.56          | ~ (r1_tarski @ X10 @ X12))),
% 0.21/0.56      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.21/0.56  thf('46', plain,
% 0.21/0.56      (((((sk_A) = (sk_B_1)) | (r2_xboole_0 @ sk_A @ sk_B_1)))
% 0.21/0.56         <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.56  thf(t21_ordinal1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( v1_ordinal1 @ A ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( v3_ordinal1 @ B ) =>
% 0.21/0.56           ( ( r2_xboole_0 @ A @ B ) => ( r2_hidden @ A @ B ) ) ) ) ))).
% 0.21/0.56  thf('47', plain,
% 0.21/0.56      (![X25 : $i, X26 : $i]:
% 0.21/0.56         (~ (v3_ordinal1 @ X25)
% 0.21/0.56          | (r2_hidden @ X26 @ X25)
% 0.21/0.56          | ~ (r2_xboole_0 @ X26 @ X25)
% 0.21/0.56          | ~ (v1_ordinal1 @ X26))),
% 0.21/0.56      inference('cnf', [status(esa)], [t21_ordinal1])).
% 0.21/0.56  thf('48', plain,
% 0.21/0.56      (((((sk_A) = (sk_B_1))
% 0.21/0.56         | ~ (v1_ordinal1 @ sk_A)
% 0.21/0.56         | (r2_hidden @ sk_A @ sk_B_1)
% 0.21/0.56         | ~ (v3_ordinal1 @ sk_B_1))) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.56  thf('49', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('50', plain,
% 0.21/0.56      (![X18 : $i]: ((v1_ordinal1 @ X18) | ~ (v3_ordinal1 @ X18))),
% 0.21/0.56      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.21/0.56  thf('51', plain, ((v1_ordinal1 @ sk_A)),
% 0.21/0.56      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.56  thf('52', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('53', plain,
% 0.21/0.56      (((((sk_A) = (sk_B_1)) | (r2_hidden @ sk_A @ sk_B_1)))
% 0.21/0.56         <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.21/0.56      inference('demod', [status(thm)], ['48', '51', '52'])).
% 0.21/0.56  thf('54', plain,
% 0.21/0.56      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X4 @ X7)
% 0.21/0.56          | (r2_hidden @ X4 @ X6)
% 0.21/0.56          | ((X6) != (k2_xboole_0 @ X7 @ X5)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.21/0.56  thf('55', plain,
% 0.21/0.56      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.21/0.56         ((r2_hidden @ X4 @ (k2_xboole_0 @ X7 @ X5)) | ~ (r2_hidden @ X4 @ X7))),
% 0.21/0.56      inference('simplify', [status(thm)], ['54'])).
% 0.21/0.56  thf('56', plain,
% 0.21/0.56      ((![X0 : $i]:
% 0.21/0.56          (((sk_A) = (sk_B_1))
% 0.21/0.56           | (r2_hidden @ sk_A @ (k2_xboole_0 @ sk_B_1 @ X0))))
% 0.21/0.56         <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['53', '55'])).
% 0.21/0.56  thf('57', plain,
% 0.21/0.56      ((((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)) | ((sk_A) = (sk_B_1))))
% 0.21/0.56         <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['38', '56'])).
% 0.21/0.56  thf('58', plain,
% 0.21/0.56      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))
% 0.21/0.56         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.56      inference('split', [status(esa)], ['0'])).
% 0.21/0.56  thf('59', plain,
% 0.21/0.56      ((((sk_A) = (sk_B_1)))
% 0.21/0.56         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))) & 
% 0.21/0.56             ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.56  thf('60', plain,
% 0.21/0.56      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))
% 0.21/0.56         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.56      inference('split', [status(esa)], ['0'])).
% 0.21/0.56  thf('61', plain,
% 0.21/0.56      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 0.21/0.56         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))) & 
% 0.21/0.56             ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.56  thf('62', plain,
% 0.21/0.56      (![X19 : $i]:
% 0.21/0.56         ((k1_ordinal1 @ X19) = (k2_xboole_0 @ X19 @ (k1_tarski @ X19)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.21/0.56  thf('63', plain,
% 0.21/0.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.56         (((X14) != (X13))
% 0.21/0.56          | (r2_hidden @ X14 @ X15)
% 0.21/0.56          | ((X15) != (k1_tarski @ X13)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.56  thf('64', plain, (![X13 : $i]: (r2_hidden @ X13 @ (k1_tarski @ X13))),
% 0.21/0.56      inference('simplify', [status(thm)], ['63'])).
% 0.21/0.56  thf('65', plain,
% 0.21/0.56      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X4 @ X5)
% 0.21/0.56          | (r2_hidden @ X4 @ X6)
% 0.21/0.56          | ((X6) != (k2_xboole_0 @ X7 @ X5)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.21/0.56  thf('66', plain,
% 0.21/0.56      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.21/0.56         ((r2_hidden @ X4 @ (k2_xboole_0 @ X7 @ X5)) | ~ (r2_hidden @ X4 @ X5))),
% 0.21/0.56      inference('simplify', [status(thm)], ['65'])).
% 0.21/0.56  thf('67', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['64', '66'])).
% 0.21/0.56  thf('68', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_ordinal1 @ X0))),
% 0.21/0.56      inference('sup+', [status(thm)], ['62', '67'])).
% 0.21/0.56  thf('69', plain,
% 0.21/0.56      (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 0.21/0.56       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.21/0.56      inference('demod', [status(thm)], ['61', '68'])).
% 0.21/0.56  thf('70', plain, ($false),
% 0.21/0.56      inference('sat_resolution*', [status(thm)], ['1', '36', '37', '69'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.21/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
