%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8eUQDqokNQ

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:55 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  135 (5755 expanded)
%              Number of leaves         :   16 (1650 expanded)
%              Depth                    :   36
%              Number of atoms          :  941 (50172 expanded)
%              Number of equality atoms :   37 ( 996 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v3_ordinal1 @ X11 )
      | ( r1_ordinal1 @ X12 @ X11 )
      | ( r2_hidden @ X11 @ X12 )
      | ~ ( v3_ordinal1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('5',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('6',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_ordinal1 @ X3 )
      | ~ ( v3_ordinal1 @ X4 )
      | ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_ordinal1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('11',plain,
    ( ( ( r1_tarski @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v3_ordinal1 @ X9 )
      | ( r2_hidden @ X10 @ X9 )
      | ( X10 = X9 )
      | ( r2_hidden @ X9 @ X10 )
      | ~ ( v3_ordinal1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('16',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( sk_A = sk_B )
      | ( r2_hidden @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( sk_A = sk_B )
      | ( r2_hidden @ sk_B @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('22',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ ( k1_ordinal1 @ X8 ) )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('23',plain,
    ( ( ( sk_A = sk_B )
      | ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('24',plain,(
    ! [X13: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X13 ) )
      | ~ ( v3_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('25',plain,(
    ! [X13: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X13 ) )
      | ~ ( v3_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('26',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_ordinal1 @ X3 )
      | ~ ( v3_ordinal1 @ X4 )
      | ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_ordinal1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('28',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('35',plain,
    ( ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) )
      | ( r2_hidden @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) )
      | ( r2_hidden @ ( k1_ordinal1 @ sk_A ) @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r2_hidden @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['24','37'])).

thf('39',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( ( r2_hidden @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['38','39'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('42',plain,
    ( ( ( sk_B
        = ( k1_ordinal1 @ sk_A ) )
      | ~ ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( sk_A = sk_B )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','42'])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('44',plain,(
    ! [X5: $i] :
      ( r2_hidden @ X5 @ ( k1_ordinal1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('45',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('46',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_A )
      | ( sk_A = sk_B ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('49',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('51',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('53',plain,
    ( ( ( sk_B
        = ( k1_ordinal1 @ sk_A ) )
      | ~ ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('54',plain,
    ( ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X5: $i] :
      ( r2_hidden @ X5 @ ( k1_ordinal1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('56',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('57',plain,
    ( ( sk_A
      = ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    ! [X5: $i] :
      ( r2_hidden @ X5 @ ( k1_ordinal1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('59',plain,
    ( ( r2_hidden @ sk_A @ sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['51','59'])).

thf('61',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('62',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['3','60','61'])).

thf('63',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simpl_trail,[status(thm)],['1','62'])).

thf('64',plain,(
    ! [X13: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X13 ) )
      | ~ ( v3_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('65',plain,(
    ! [X13: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X13 ) )
      | ~ ( v3_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('66',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v3_ordinal1 @ X11 )
      | ( r1_ordinal1 @ X12 @ X11 )
      | ( r2_hidden @ X11 @ X12 )
      | ~ ( v3_ordinal1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('67',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v3_ordinal1 @ X11 )
      | ( r1_ordinal1 @ X12 @ X11 )
      | ( r2_hidden @ X11 @ X12 )
      | ~ ( v3_ordinal1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_ordinal1 @ X3 )
      | ~ ( v3_ordinal1 @ X4 )
      | ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_ordinal1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('76',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['3','60'])).

thf('77',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['75','76'])).

thf('78',plain,
    ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ sk_B )
    | ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','80'])).

thf('82',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('85',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( ( k1_ordinal1 @ sk_A )
      = sk_B )
    | ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( ( k1_ordinal1 @ sk_A )
      = sk_B )
    | ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
    | ( ( k1_ordinal1 @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['64','87'])).

thf('89',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
    | ( ( k1_ordinal1 @ sk_A )
      = sk_B ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X7 = X6 )
      | ( r2_hidden @ X7 @ X6 )
      | ~ ( r2_hidden @ X7 @ ( k1_ordinal1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('92',plain,
    ( ( ( k1_ordinal1 @ sk_A )
      = sk_B )
    | ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('95',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['3','60','61'])).

thf('97',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( sk_B = sk_A )
    | ( ( k1_ordinal1 @ sk_A )
      = sk_B ) ),
    inference(clc,[status(thm)],['92','97'])).

thf('99',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['75','76'])).

thf('100',plain,
    ( ~ ( r1_ordinal1 @ sk_B @ sk_B )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( sk_B = sk_A )
    | ( ( k1_ordinal1 @ sk_A )
      = sk_B ) ),
    inference(clc,[status(thm)],['92','97'])).

thf('102',plain,(
    ! [X13: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X13 ) )
      | ~ ( v3_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('104',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['75','76'])).

thf('105',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r1_ordinal1 @ sk_B @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( r1_ordinal1 @ sk_B @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_B @ ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['102','107'])).

thf('109',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    r1_ordinal1 @ sk_B @ ( k1_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_B )
    | ( sk_B = sk_A ) ),
    inference('sup+',[status(thm)],['101','110'])).

thf('112',plain,(
    sk_B = sk_A ),
    inference(clc,[status(thm)],['100','111'])).

thf('113',plain,(
    r2_hidden @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['63','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('115',plain,(
    ~ ( r2_hidden @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    r2_hidden @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['63','112'])).

thf('117',plain,(
    $false ),
    inference(demod,[status(thm)],['115','116'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8eUQDqokNQ
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:12:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.61  % Solved by: fo/fo7.sh
% 0.39/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.61  % done 352 iterations in 0.145s
% 0.39/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.61  % SZS output start Refutation
% 0.39/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.61  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.39/0.61  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.39/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.61  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.39/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.61  thf(t33_ordinal1, conjecture,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( v3_ordinal1 @ A ) =>
% 0.39/0.61       ( ![B:$i]:
% 0.39/0.61         ( ( v3_ordinal1 @ B ) =>
% 0.39/0.61           ( ( r2_hidden @ A @ B ) <=>
% 0.39/0.61             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 0.39/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.61    (~( ![A:$i]:
% 0.39/0.61        ( ( v3_ordinal1 @ A ) =>
% 0.39/0.61          ( ![B:$i]:
% 0.39/0.61            ( ( v3_ordinal1 @ B ) =>
% 0.39/0.61              ( ( r2_hidden @ A @ B ) <=>
% 0.39/0.61                ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ) )),
% 0.39/0.61    inference('cnf.neg', [status(esa)], [t33_ordinal1])).
% 0.39/0.61  thf('0', plain,
% 0.39/0.61      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('1', plain,
% 0.39/0.61      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.39/0.61      inference('split', [status(esa)], ['0'])).
% 0.39/0.61  thf('2', plain,
% 0.39/0.61      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.39/0.61        | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('3', plain,
% 0.39/0.61      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 0.39/0.61       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.39/0.61      inference('split', [status(esa)], ['2'])).
% 0.39/0.61  thf(t26_ordinal1, axiom,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( v3_ordinal1 @ A ) =>
% 0.39/0.61       ( ![B:$i]:
% 0.39/0.61         ( ( v3_ordinal1 @ B ) =>
% 0.39/0.61           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.39/0.61  thf('4', plain,
% 0.39/0.61      (![X11 : $i, X12 : $i]:
% 0.39/0.61         (~ (v3_ordinal1 @ X11)
% 0.39/0.61          | (r1_ordinal1 @ X12 @ X11)
% 0.39/0.61          | (r2_hidden @ X11 @ X12)
% 0.39/0.61          | ~ (v3_ordinal1 @ X12))),
% 0.39/0.61      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.39/0.61  thf('5', plain,
% 0.39/0.61      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.39/0.61      inference('split', [status(esa)], ['2'])).
% 0.39/0.61  thf('6', plain,
% 0.39/0.61      (((~ (v3_ordinal1 @ sk_B)
% 0.39/0.61         | (r1_ordinal1 @ sk_B @ sk_A)
% 0.39/0.61         | ~ (v3_ordinal1 @ sk_A))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.39/0.61  thf('7', plain, ((v3_ordinal1 @ sk_B)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('8', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('9', plain,
% 0.39/0.61      (((r1_ordinal1 @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.39/0.61      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.39/0.61  thf(redefinition_r1_ordinal1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.39/0.61       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.39/0.61  thf('10', plain,
% 0.39/0.61      (![X3 : $i, X4 : $i]:
% 0.39/0.61         (~ (v3_ordinal1 @ X3)
% 0.39/0.61          | ~ (v3_ordinal1 @ X4)
% 0.39/0.61          | (r1_tarski @ X3 @ X4)
% 0.39/0.61          | ~ (r1_ordinal1 @ X3 @ X4))),
% 0.39/0.61      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.39/0.61  thf('11', plain,
% 0.39/0.61      ((((r1_tarski @ sk_B @ sk_A)
% 0.39/0.61         | ~ (v3_ordinal1 @ sk_A)
% 0.39/0.61         | ~ (v3_ordinal1 @ sk_B))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['9', '10'])).
% 0.39/0.61  thf('12', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('13', plain, ((v3_ordinal1 @ sk_B)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('14', plain,
% 0.39/0.61      (((r1_tarski @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.39/0.61      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.39/0.61  thf(t24_ordinal1, axiom,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( v3_ordinal1 @ A ) =>
% 0.39/0.61       ( ![B:$i]:
% 0.39/0.61         ( ( v3_ordinal1 @ B ) =>
% 0.39/0.61           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.39/0.61                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.39/0.61  thf('15', plain,
% 0.39/0.61      (![X9 : $i, X10 : $i]:
% 0.39/0.61         (~ (v3_ordinal1 @ X9)
% 0.39/0.61          | (r2_hidden @ X10 @ X9)
% 0.39/0.61          | ((X10) = (X9))
% 0.39/0.61          | (r2_hidden @ X9 @ X10)
% 0.39/0.61          | ~ (v3_ordinal1 @ X10))),
% 0.39/0.61      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.39/0.61  thf(t7_ordinal1, axiom,
% 0.39/0.61    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.39/0.61  thf('16', plain,
% 0.39/0.61      (![X14 : $i, X15 : $i]:
% 0.39/0.61         (~ (r2_hidden @ X14 @ X15) | ~ (r1_tarski @ X15 @ X14))),
% 0.39/0.61      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.39/0.61  thf('17', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (~ (v3_ordinal1 @ X1)
% 0.39/0.61          | (r2_hidden @ X0 @ X1)
% 0.39/0.61          | ((X1) = (X0))
% 0.39/0.61          | ~ (v3_ordinal1 @ X0)
% 0.39/0.61          | ~ (r1_tarski @ X0 @ X1))),
% 0.39/0.61      inference('sup-', [status(thm)], ['15', '16'])).
% 0.39/0.61  thf('18', plain,
% 0.39/0.61      (((~ (v3_ordinal1 @ sk_B)
% 0.39/0.61         | ((sk_A) = (sk_B))
% 0.39/0.61         | (r2_hidden @ sk_B @ sk_A)
% 0.39/0.61         | ~ (v3_ordinal1 @ sk_A))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['14', '17'])).
% 0.39/0.61  thf('19', plain, ((v3_ordinal1 @ sk_B)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('20', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('21', plain,
% 0.39/0.61      (((((sk_A) = (sk_B)) | (r2_hidden @ sk_B @ sk_A)))
% 0.39/0.61         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.39/0.61      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.39/0.61  thf(t13_ordinal1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.39/0.61       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.39/0.61  thf('22', plain,
% 0.39/0.61      (![X7 : $i, X8 : $i]:
% 0.39/0.61         ((r2_hidden @ X7 @ (k1_ordinal1 @ X8)) | ~ (r2_hidden @ X7 @ X8))),
% 0.39/0.61      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.39/0.61  thf('23', plain,
% 0.39/0.61      (((((sk_A) = (sk_B)) | (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))))
% 0.39/0.61         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['21', '22'])).
% 0.39/0.61  thf(t29_ordinal1, axiom,
% 0.39/0.61    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 0.39/0.61  thf('24', plain,
% 0.39/0.61      (![X13 : $i]:
% 0.39/0.61         ((v3_ordinal1 @ (k1_ordinal1 @ X13)) | ~ (v3_ordinal1 @ X13))),
% 0.39/0.61      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.39/0.61  thf('25', plain,
% 0.39/0.61      (![X13 : $i]:
% 0.39/0.61         ((v3_ordinal1 @ (k1_ordinal1 @ X13)) | ~ (v3_ordinal1 @ X13))),
% 0.39/0.61      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.39/0.61  thf('26', plain,
% 0.39/0.61      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.39/0.61         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.39/0.61      inference('split', [status(esa)], ['0'])).
% 0.39/0.61  thf('27', plain,
% 0.39/0.61      (![X3 : $i, X4 : $i]:
% 0.39/0.61         (~ (v3_ordinal1 @ X3)
% 0.39/0.61          | ~ (v3_ordinal1 @ X4)
% 0.39/0.61          | (r1_tarski @ X3 @ X4)
% 0.39/0.61          | ~ (r1_ordinal1 @ X3 @ X4))),
% 0.39/0.61      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.39/0.61  thf('28', plain,
% 0.39/0.61      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.39/0.61         | ~ (v3_ordinal1 @ sk_B)
% 0.39/0.61         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.39/0.61         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['26', '27'])).
% 0.39/0.61  thf('29', plain, ((v3_ordinal1 @ sk_B)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('30', plain,
% 0.39/0.61      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.39/0.61         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.39/0.61         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.39/0.61      inference('demod', [status(thm)], ['28', '29'])).
% 0.39/0.61  thf('31', plain,
% 0.39/0.61      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 0.39/0.61         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['25', '30'])).
% 0.39/0.61  thf('32', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('33', plain,
% 0.39/0.61      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.39/0.61         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.39/0.61      inference('demod', [status(thm)], ['31', '32'])).
% 0.39/0.61  thf('34', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (~ (v3_ordinal1 @ X1)
% 0.39/0.61          | (r2_hidden @ X0 @ X1)
% 0.39/0.61          | ((X1) = (X0))
% 0.39/0.61          | ~ (v3_ordinal1 @ X0)
% 0.39/0.61          | ~ (r1_tarski @ X0 @ X1))),
% 0.39/0.61      inference('sup-', [status(thm)], ['15', '16'])).
% 0.39/0.61  thf('35', plain,
% 0.39/0.61      (((~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))
% 0.39/0.61         | ((sk_B) = (k1_ordinal1 @ sk_A))
% 0.39/0.61         | (r2_hidden @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.39/0.61         | ~ (v3_ordinal1 @ sk_B)))
% 0.39/0.61         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['33', '34'])).
% 0.39/0.61  thf('36', plain, ((v3_ordinal1 @ sk_B)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('37', plain,
% 0.39/0.61      (((~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))
% 0.39/0.61         | ((sk_B) = (k1_ordinal1 @ sk_A))
% 0.39/0.61         | (r2_hidden @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 0.39/0.61         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.39/0.61      inference('demod', [status(thm)], ['35', '36'])).
% 0.39/0.61  thf('38', plain,
% 0.39/0.61      (((~ (v3_ordinal1 @ sk_A)
% 0.39/0.61         | (r2_hidden @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.39/0.61         | ((sk_B) = (k1_ordinal1 @ sk_A))))
% 0.39/0.61         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['24', '37'])).
% 0.39/0.61  thf('39', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('40', plain,
% 0.39/0.61      ((((r2_hidden @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.39/0.61         | ((sk_B) = (k1_ordinal1 @ sk_A))))
% 0.39/0.61         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.39/0.61      inference('demod', [status(thm)], ['38', '39'])).
% 0.39/0.61  thf(antisymmetry_r2_hidden, axiom,
% 0.39/0.61    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.39/0.61  thf('41', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.39/0.61      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.39/0.61  thf('42', plain,
% 0.39/0.61      (((((sk_B) = (k1_ordinal1 @ sk_A))
% 0.39/0.61         | ~ (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))))
% 0.39/0.61         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['40', '41'])).
% 0.39/0.61  thf('43', plain,
% 0.39/0.61      (((((sk_A) = (sk_B)) | ((sk_B) = (k1_ordinal1 @ sk_A))))
% 0.39/0.61         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.39/0.61             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['23', '42'])).
% 0.39/0.61  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.39/0.61  thf('44', plain, (![X5 : $i]: (r2_hidden @ X5 @ (k1_ordinal1 @ X5))),
% 0.39/0.61      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.39/0.61  thf('45', plain,
% 0.39/0.61      (![X14 : $i, X15 : $i]:
% 0.39/0.61         (~ (r2_hidden @ X14 @ X15) | ~ (r1_tarski @ X15 @ X14))),
% 0.39/0.61      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.39/0.61  thf('46', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X0)),
% 0.39/0.61      inference('sup-', [status(thm)], ['44', '45'])).
% 0.39/0.61  thf('47', plain,
% 0.39/0.61      (((~ (r1_tarski @ sk_B @ sk_A) | ((sk_A) = (sk_B))))
% 0.39/0.61         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.39/0.61             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['43', '46'])).
% 0.39/0.61  thf('48', plain,
% 0.39/0.61      (((r1_tarski @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.39/0.61      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.39/0.61  thf('49', plain,
% 0.39/0.61      ((((sk_A) = (sk_B)))
% 0.39/0.61         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.39/0.61             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.39/0.61      inference('demod', [status(thm)], ['47', '48'])).
% 0.39/0.61  thf('50', plain,
% 0.39/0.61      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.39/0.61      inference('split', [status(esa)], ['2'])).
% 0.39/0.61  thf('51', plain,
% 0.39/0.61      ((~ (r2_hidden @ sk_A @ sk_A))
% 0.39/0.61         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.39/0.61             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['49', '50'])).
% 0.39/0.61  thf('52', plain,
% 0.39/0.61      ((((sk_A) = (sk_B)))
% 0.39/0.61         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.39/0.61             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.39/0.61      inference('demod', [status(thm)], ['47', '48'])).
% 0.39/0.61  thf('53', plain,
% 0.39/0.61      (((((sk_B) = (k1_ordinal1 @ sk_A))
% 0.39/0.61         | ~ (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))))
% 0.39/0.61         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['40', '41'])).
% 0.39/0.61  thf('54', plain,
% 0.39/0.61      (((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A))
% 0.39/0.61         | ((sk_B) = (k1_ordinal1 @ sk_A))))
% 0.39/0.61         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.39/0.61             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['52', '53'])).
% 0.39/0.61  thf('55', plain, (![X5 : $i]: (r2_hidden @ X5 @ (k1_ordinal1 @ X5))),
% 0.39/0.61      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.39/0.61  thf('56', plain,
% 0.39/0.61      ((((sk_A) = (sk_B)))
% 0.39/0.61         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.39/0.61             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.39/0.61      inference('demod', [status(thm)], ['47', '48'])).
% 0.39/0.61  thf('57', plain,
% 0.39/0.61      ((((sk_A) = (k1_ordinal1 @ sk_A)))
% 0.39/0.61         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.39/0.61             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.39/0.61      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.39/0.61  thf('58', plain, (![X5 : $i]: (r2_hidden @ X5 @ (k1_ordinal1 @ X5))),
% 0.39/0.61      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.39/0.61  thf('59', plain,
% 0.39/0.61      (((r2_hidden @ sk_A @ sk_A))
% 0.39/0.61         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.39/0.61             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.39/0.61      inference('sup+', [status(thm)], ['57', '58'])).
% 0.39/0.61  thf('60', plain,
% 0.39/0.61      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.39/0.61       ~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.39/0.61      inference('demod', [status(thm)], ['51', '59'])).
% 0.39/0.61  thf('61', plain,
% 0.39/0.61      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.39/0.61       ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.39/0.61      inference('split', [status(esa)], ['0'])).
% 0.39/0.61  thf('62', plain, (((r2_hidden @ sk_A @ sk_B))),
% 0.39/0.61      inference('sat_resolution*', [status(thm)], ['3', '60', '61'])).
% 0.39/0.61  thf('63', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.39/0.61      inference('simpl_trail', [status(thm)], ['1', '62'])).
% 0.39/0.61  thf('64', plain,
% 0.39/0.61      (![X13 : $i]:
% 0.39/0.61         ((v3_ordinal1 @ (k1_ordinal1 @ X13)) | ~ (v3_ordinal1 @ X13))),
% 0.39/0.61      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.39/0.61  thf('65', plain,
% 0.39/0.61      (![X13 : $i]:
% 0.39/0.61         ((v3_ordinal1 @ (k1_ordinal1 @ X13)) | ~ (v3_ordinal1 @ X13))),
% 0.39/0.61      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.39/0.61  thf('66', plain,
% 0.39/0.61      (![X11 : $i, X12 : $i]:
% 0.39/0.61         (~ (v3_ordinal1 @ X11)
% 0.39/0.61          | (r1_ordinal1 @ X12 @ X11)
% 0.39/0.61          | (r2_hidden @ X11 @ X12)
% 0.39/0.61          | ~ (v3_ordinal1 @ X12))),
% 0.39/0.61      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.39/0.61  thf('67', plain,
% 0.39/0.61      (![X11 : $i, X12 : $i]:
% 0.39/0.61         (~ (v3_ordinal1 @ X11)
% 0.39/0.61          | (r1_ordinal1 @ X12 @ X11)
% 0.39/0.61          | (r2_hidden @ X11 @ X12)
% 0.39/0.61          | ~ (v3_ordinal1 @ X12))),
% 0.39/0.61      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.39/0.61  thf('68', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.39/0.61      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.39/0.61  thf('69', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (~ (v3_ordinal1 @ X0)
% 0.39/0.61          | (r1_ordinal1 @ X0 @ X1)
% 0.39/0.61          | ~ (v3_ordinal1 @ X1)
% 0.39/0.61          | ~ (r2_hidden @ X0 @ X1))),
% 0.39/0.61      inference('sup-', [status(thm)], ['67', '68'])).
% 0.39/0.61  thf('70', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (~ (v3_ordinal1 @ X0)
% 0.39/0.61          | (r1_ordinal1 @ X0 @ X1)
% 0.39/0.61          | ~ (v3_ordinal1 @ X1)
% 0.39/0.61          | ~ (v3_ordinal1 @ X0)
% 0.39/0.61          | (r1_ordinal1 @ X1 @ X0)
% 0.39/0.61          | ~ (v3_ordinal1 @ X1))),
% 0.39/0.61      inference('sup-', [status(thm)], ['66', '69'])).
% 0.39/0.61  thf('71', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((r1_ordinal1 @ X1 @ X0)
% 0.39/0.61          | ~ (v3_ordinal1 @ X1)
% 0.39/0.61          | (r1_ordinal1 @ X0 @ X1)
% 0.39/0.61          | ~ (v3_ordinal1 @ X0))),
% 0.39/0.61      inference('simplify', [status(thm)], ['70'])).
% 0.39/0.61  thf('72', plain,
% 0.39/0.61      (![X3 : $i, X4 : $i]:
% 0.39/0.61         (~ (v3_ordinal1 @ X3)
% 0.39/0.61          | ~ (v3_ordinal1 @ X4)
% 0.39/0.61          | (r1_tarski @ X3 @ X4)
% 0.39/0.61          | ~ (r1_ordinal1 @ X3 @ X4))),
% 0.39/0.61      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.39/0.61  thf('73', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (~ (v3_ordinal1 @ X0)
% 0.39/0.61          | (r1_ordinal1 @ X0 @ X1)
% 0.39/0.61          | ~ (v3_ordinal1 @ X1)
% 0.39/0.61          | (r1_tarski @ X1 @ X0)
% 0.39/0.61          | ~ (v3_ordinal1 @ X0)
% 0.39/0.61          | ~ (v3_ordinal1 @ X1))),
% 0.39/0.61      inference('sup-', [status(thm)], ['71', '72'])).
% 0.39/0.61  thf('74', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((r1_tarski @ X1 @ X0)
% 0.39/0.61          | ~ (v3_ordinal1 @ X1)
% 0.39/0.61          | (r1_ordinal1 @ X0 @ X1)
% 0.39/0.61          | ~ (v3_ordinal1 @ X0))),
% 0.39/0.61      inference('simplify', [status(thm)], ['73'])).
% 0.39/0.61  thf('75', plain,
% 0.39/0.61      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.39/0.61         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.39/0.61      inference('split', [status(esa)], ['2'])).
% 0.39/0.61  thf('76', plain, (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.39/0.61      inference('sat_resolution*', [status(thm)], ['3', '60'])).
% 0.39/0.61  thf('77', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 0.39/0.61      inference('simpl_trail', [status(thm)], ['75', '76'])).
% 0.39/0.61  thf('78', plain,
% 0.39/0.61      ((~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))
% 0.39/0.61        | ~ (v3_ordinal1 @ sk_B)
% 0.39/0.61        | (r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['74', '77'])).
% 0.39/0.61  thf('79', plain, ((v3_ordinal1 @ sk_B)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('80', plain,
% 0.39/0.61      ((~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))
% 0.39/0.61        | (r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A)))),
% 0.39/0.61      inference('demod', [status(thm)], ['78', '79'])).
% 0.39/0.61  thf('81', plain,
% 0.39/0.61      ((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['65', '80'])).
% 0.39/0.61  thf('82', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('83', plain, ((r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A))),
% 0.39/0.61      inference('demod', [status(thm)], ['81', '82'])).
% 0.39/0.61  thf('84', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (~ (v3_ordinal1 @ X1)
% 0.39/0.61          | (r2_hidden @ X0 @ X1)
% 0.39/0.61          | ((X1) = (X0))
% 0.39/0.61          | ~ (v3_ordinal1 @ X0)
% 0.39/0.61          | ~ (r1_tarski @ X0 @ X1))),
% 0.39/0.61      inference('sup-', [status(thm)], ['15', '16'])).
% 0.39/0.61  thf('85', plain,
% 0.39/0.61      ((~ (v3_ordinal1 @ sk_B)
% 0.39/0.61        | ((k1_ordinal1 @ sk_A) = (sk_B))
% 0.39/0.61        | (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.39/0.61        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['83', '84'])).
% 0.39/0.61  thf('86', plain, ((v3_ordinal1 @ sk_B)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('87', plain,
% 0.39/0.61      ((((k1_ordinal1 @ sk_A) = (sk_B))
% 0.39/0.61        | (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.39/0.61        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 0.39/0.61      inference('demod', [status(thm)], ['85', '86'])).
% 0.39/0.61  thf('88', plain,
% 0.39/0.61      ((~ (v3_ordinal1 @ sk_A)
% 0.39/0.61        | (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.39/0.61        | ((k1_ordinal1 @ sk_A) = (sk_B)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['64', '87'])).
% 0.39/0.61  thf('89', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('90', plain,
% 0.39/0.61      (((r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.39/0.61        | ((k1_ordinal1 @ sk_A) = (sk_B)))),
% 0.39/0.61      inference('demod', [status(thm)], ['88', '89'])).
% 0.39/0.61  thf('91', plain,
% 0.39/0.61      (![X6 : $i, X7 : $i]:
% 0.39/0.61         (((X7) = (X6))
% 0.39/0.61          | (r2_hidden @ X7 @ X6)
% 0.39/0.61          | ~ (r2_hidden @ X7 @ (k1_ordinal1 @ X6)))),
% 0.39/0.61      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.39/0.61  thf('92', plain,
% 0.39/0.61      ((((k1_ordinal1 @ sk_A) = (sk_B))
% 0.39/0.61        | (r2_hidden @ sk_B @ sk_A)
% 0.39/0.61        | ((sk_B) = (sk_A)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['90', '91'])).
% 0.39/0.61  thf('93', plain,
% 0.39/0.61      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.39/0.61      inference('split', [status(esa)], ['0'])).
% 0.39/0.61  thf('94', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.39/0.61      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.39/0.61  thf('95', plain,
% 0.39/0.61      ((~ (r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['93', '94'])).
% 0.39/0.61  thf('96', plain, (((r2_hidden @ sk_A @ sk_B))),
% 0.39/0.61      inference('sat_resolution*', [status(thm)], ['3', '60', '61'])).
% 0.39/0.61  thf('97', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 0.39/0.61      inference('simpl_trail', [status(thm)], ['95', '96'])).
% 0.39/0.61  thf('98', plain, ((((sk_B) = (sk_A)) | ((k1_ordinal1 @ sk_A) = (sk_B)))),
% 0.39/0.61      inference('clc', [status(thm)], ['92', '97'])).
% 0.39/0.61  thf('99', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 0.39/0.61      inference('simpl_trail', [status(thm)], ['75', '76'])).
% 0.39/0.61  thf('100', plain, ((~ (r1_ordinal1 @ sk_B @ sk_B) | ((sk_B) = (sk_A)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['98', '99'])).
% 0.39/0.61  thf('101', plain, ((((sk_B) = (sk_A)) | ((k1_ordinal1 @ sk_A) = (sk_B)))),
% 0.39/0.61      inference('clc', [status(thm)], ['92', '97'])).
% 0.39/0.61  thf('102', plain,
% 0.39/0.61      (![X13 : $i]:
% 0.39/0.61         ((v3_ordinal1 @ (k1_ordinal1 @ X13)) | ~ (v3_ordinal1 @ X13))),
% 0.39/0.61      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.39/0.61  thf('103', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((r1_ordinal1 @ X1 @ X0)
% 0.39/0.61          | ~ (v3_ordinal1 @ X1)
% 0.39/0.61          | (r1_ordinal1 @ X0 @ X1)
% 0.39/0.61          | ~ (v3_ordinal1 @ X0))),
% 0.39/0.61      inference('simplify', [status(thm)], ['70'])).
% 0.39/0.61  thf('104', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 0.39/0.61      inference('simpl_trail', [status(thm)], ['75', '76'])).
% 0.39/0.61  thf('105', plain,
% 0.39/0.61      ((~ (v3_ordinal1 @ sk_B)
% 0.39/0.61        | (r1_ordinal1 @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.39/0.61        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['103', '104'])).
% 0.39/0.61  thf('106', plain, ((v3_ordinal1 @ sk_B)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('107', plain,
% 0.39/0.61      (((r1_ordinal1 @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.39/0.61        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 0.39/0.61      inference('demod', [status(thm)], ['105', '106'])).
% 0.39/0.61  thf('108', plain,
% 0.39/0.61      ((~ (v3_ordinal1 @ sk_A) | (r1_ordinal1 @ sk_B @ (k1_ordinal1 @ sk_A)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['102', '107'])).
% 0.39/0.61  thf('109', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('110', plain, ((r1_ordinal1 @ sk_B @ (k1_ordinal1 @ sk_A))),
% 0.39/0.61      inference('demod', [status(thm)], ['108', '109'])).
% 0.39/0.61  thf('111', plain, (((r1_ordinal1 @ sk_B @ sk_B) | ((sk_B) = (sk_A)))),
% 0.39/0.61      inference('sup+', [status(thm)], ['101', '110'])).
% 0.39/0.61  thf('112', plain, (((sk_B) = (sk_A))),
% 0.39/0.61      inference('clc', [status(thm)], ['100', '111'])).
% 0.39/0.61  thf('113', plain, ((r2_hidden @ sk_A @ sk_A)),
% 0.39/0.61      inference('demod', [status(thm)], ['63', '112'])).
% 0.39/0.61  thf('114', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.39/0.61      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.39/0.61  thf('115', plain, (~ (r2_hidden @ sk_A @ sk_A)),
% 0.39/0.61      inference('sup-', [status(thm)], ['113', '114'])).
% 0.39/0.61  thf('116', plain, ((r2_hidden @ sk_A @ sk_A)),
% 0.39/0.61      inference('demod', [status(thm)], ['63', '112'])).
% 0.39/0.61  thf('117', plain, ($false), inference('demod', [status(thm)], ['115', '116'])).
% 0.39/0.61  
% 0.39/0.61  % SZS output end Refutation
% 0.39/0.61  
% 0.39/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
