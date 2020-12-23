%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5rhrKNtGCv

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:11 EST 2020

% Result     : Theorem 4.00s
% Output     : Refutation 4.00s
% Verified   : 
% Statistics : Number of formulae       :  149 (1927 expanded)
%              Number of leaves         :   21 ( 514 expanded)
%              Depth                    :   42
%              Number of atoms          : 1012 (18875 expanded)
%              Number of equality atoms :   44 (1674 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_ordinal1_type,type,(
    v4_ordinal1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(t42_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ~ ( ~ ( v4_ordinal1 @ A )
            & ! [B: $i] :
                ( ( v3_ordinal1 @ B )
               => ( A
                 != ( k1_ordinal1 @ B ) ) ) )
        & ~ ( ? [B: $i] :
                ( ( A
                  = ( k1_ordinal1 @ B ) )
                & ( v3_ordinal1 @ B ) )
            & ( v4_ordinal1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ( ~ ( ~ ( v4_ordinal1 @ A )
              & ! [B: $i] :
                  ( ( v3_ordinal1 @ B )
                 => ( A
                   != ( k1_ordinal1 @ B ) ) ) )
          & ~ ( ? [B: $i] :
                  ( ( A
                    = ( k1_ordinal1 @ B ) )
                  & ( v3_ordinal1 @ B ) )
              & ( v4_ordinal1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t42_ordinal1])).

thf('0',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v3_ordinal1 @ X14 )
      | ~ ( v3_ordinal1 @ X15 )
      | ( r1_ordinal1 @ X14 @ X15 )
      | ( r1_ordinal1 @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_ordinal1 @ X17 )
      | ~ ( v3_ordinal1 @ X18 )
      | ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_ordinal1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('6',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v3_ordinal1 @ X25 )
      | ( r2_hidden @ X26 @ X25 )
      | ( X26 = X25 )
      | ( r2_hidden @ X25 @ X26 )
      | ~ ( v3_ordinal1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('7',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X35 @ X36 )
      | ~ ( r1_tarski @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( sk_A = X0 )
      | ( r2_hidden @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( sk_A = X0 )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ( sk_A = X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t41_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v4_ordinal1 @ A )
      <=> ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r2_hidden @ B @ A )
             => ( r2_hidden @ ( k1_ordinal1 @ B ) @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X33: $i] :
      ( ~ ( r2_hidden @ ( k1_ordinal1 @ ( sk_B_2 @ X33 ) ) @ X33 )
      | ( v4_ordinal1 @ X33 )
      | ~ ( v3_ordinal1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf('14',plain,
    ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) )
    | ( r1_ordinal1 @ sk_A @ ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) )
    | ( sk_A
      = ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( v4_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('15',plain,(
    ! [X27: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X27 ) )
      | ~ ( v3_ordinal1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('16',plain,(
    ! [X27: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X27 ) )
      | ~ ( v3_ordinal1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('17',plain,(
    ! [X27: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X27 ) )
      | ~ ( v3_ordinal1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('18',plain,(
    ! [X33: $i] :
      ( ( v3_ordinal1 @ ( sk_B_2 @ X33 ) )
      | ( v4_ordinal1 @ X33 )
      | ~ ( v3_ordinal1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf('19',plain,(
    ! [X33: $i] :
      ( ( v3_ordinal1 @ ( sk_B_2 @ X33 ) )
      | ( v4_ordinal1 @ X33 )
      | ~ ( v3_ordinal1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf('20',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X33: $i] :
      ( ( r2_hidden @ ( sk_B_2 @ X33 ) @ X33 )
      | ( v4_ordinal1 @ X33 )
      | ~ ( v3_ordinal1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf('24',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X35 @ X36 )
      | ~ ( r1_tarski @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( v3_ordinal1 @ ( sk_B_2 @ sk_A ) )
    | ( r1_ordinal1 @ ( sk_B_2 @ sk_A ) @ sk_A )
    | ( v4_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ~ ( v3_ordinal1 @ ( sk_B_2 @ sk_A ) )
    | ( r1_ordinal1 @ ( sk_B_2 @ sk_A ) @ sk_A )
    | ( v4_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( v4_ordinal1 @ sk_A )
    | ( v3_ordinal1 @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( v4_ordinal1 @ sk_A )
   <= ~ ( v4_ordinal1 @ sk_A ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,
    ( ~ ( v4_ordinal1 @ sk_A )
    | ( sk_A
      = ( k1_ordinal1 @ sk_B_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ~ ( v4_ordinal1 @ sk_A )
    | ( sk_A
      = ( k1_ordinal1 @ sk_B_3 ) ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,(
    ! [X37: $i] :
      ( ~ ( v3_ordinal1 @ X37 )
      | ( sk_A
       != ( k1_ordinal1 @ X37 ) )
      | ( v4_ordinal1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v4_ordinal1 @ sk_A )
   <= ( v4_ordinal1 @ sk_A ) ),
    inference(split,[status(esa)],['33'])).

thf('35',plain,
    ( ( sk_A
      = ( k1_ordinal1 @ sk_B_3 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_3 ) ) ),
    inference(split,[status(esa)],['31'])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('36',plain,(
    ! [X22: $i] :
      ( r2_hidden @ X22 @ ( k1_ordinal1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('37',plain,
    ( ( r2_hidden @ sk_B_3 @ sk_A )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_3 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v4_ordinal1 @ X33 )
      | ~ ( r2_hidden @ X34 @ X33 )
      | ( r2_hidden @ ( k1_ordinal1 @ X34 ) @ X33 )
      | ~ ( v3_ordinal1 @ X34 )
      | ~ ( v3_ordinal1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf('39',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B_3 )
      | ( r2_hidden @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A )
      | ~ ( v4_ordinal1 @ sk_A ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( r2_hidden @ sk_B_3 @ sk_A )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_3 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf(t23_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v3_ordinal1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( v3_ordinal1 @ A ) ) ) )).

thf('42',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v3_ordinal1 @ X23 )
      | ~ ( v3_ordinal1 @ X24 )
      | ~ ( r2_hidden @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('43',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( v3_ordinal1 @ sk_B_3 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v3_ordinal1 @ sk_B_3 )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_A
      = ( k1_ordinal1 @ sk_B_3 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_3 ) ) ),
    inference(split,[status(esa)],['31'])).

thf('47',plain,
    ( ( ( r2_hidden @ sk_A @ sk_A )
      | ~ ( v4_ordinal1 @ sk_A ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['39','40','45','46'])).

thf('48',plain,
    ( ( r2_hidden @ sk_A @ sk_A )
   <= ( ( v4_ordinal1 @ sk_A )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_3 ) ) ) ),
    inference('sup-',[status(thm)],['34','47'])).

thf('49',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X35 @ X36 )
      | ~ ( r1_tarski @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('50',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
   <= ( ( v4_ordinal1 @ sk_A )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_3 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('51',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('52',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( sk_A
     != ( k1_ordinal1 @ sk_B_3 ) )
    | ~ ( v4_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['50','52'])).

thf('54',plain,(
    ~ ( v4_ordinal1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['32','53'])).

thf('55',plain,(
    ~ ( v4_ordinal1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['30','54'])).

thf('56',plain,
    ( ( r1_ordinal1 @ ( sk_B_2 @ sk_A ) @ sk_A )
    | ~ ( v3_ordinal1 @ ( sk_B_2 @ sk_A ) ) ),
    inference(clc,[status(thm)],['28','55'])).

thf('57',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( v4_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ ( sk_B_2 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['19','56'])).

thf('58',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v4_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ ( sk_B_2 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( v4_ordinal1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['30','54'])).

thf('61',plain,(
    r1_ordinal1 @ ( sk_B_2 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['59','60'])).

thf(t34_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
          <=> ( r1_ordinal1 @ A @ B ) ) ) ) )).

thf('62',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v3_ordinal1 @ X30 )
      | ~ ( r1_ordinal1 @ X31 @ X30 )
      | ( r2_hidden @ X31 @ ( k1_ordinal1 @ X30 ) )
      | ~ ( v3_ordinal1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t34_ordinal1])).

thf('63',plain,
    ( ~ ( v3_ordinal1 @ ( sk_B_2 @ sk_A ) )
    | ( r2_hidden @ ( sk_B_2 @ sk_A ) @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ~ ( v3_ordinal1 @ ( sk_B_2 @ sk_A ) )
    | ( r2_hidden @ ( sk_B_2 @ sk_A ) @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( v4_ordinal1 @ sk_A )
    | ( r2_hidden @ ( sk_B_2 @ sk_A ) @ ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','65'])).

thf('67',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v4_ordinal1 @ sk_A )
    | ( r2_hidden @ ( sk_B_2 @ sk_A ) @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( v4_ordinal1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['30','54'])).

thf('70',plain,(
    r2_hidden @ ( sk_B_2 @ sk_A ) @ ( k1_ordinal1 @ sk_A ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v3_ordinal1 @ X23 )
      | ~ ( v3_ordinal1 @ X24 )
      | ~ ( r2_hidden @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('72',plain,
    ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) )
    | ( v3_ordinal1 @ ( sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( v3_ordinal1 @ ( sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','72'])).

thf('74',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v3_ordinal1 @ ( sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X33: $i] :
      ( ( r2_hidden @ ( sk_B_2 @ X33 ) @ X33 )
      | ( v4_ordinal1 @ X33 )
      | ~ ( v3_ordinal1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf(t33_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
          <=> ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) )).

thf('77',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v3_ordinal1 @ X28 )
      | ~ ( r2_hidden @ X29 @ X28 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X29 ) @ X28 )
      | ~ ( v3_ordinal1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t33_ordinal1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ ( sk_B_2 @ X0 ) )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ ( sk_B_2 @ X0 ) ) @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ ( k1_ordinal1 @ ( sk_B_2 @ X0 ) ) @ X0 )
      | ~ ( v3_ordinal1 @ ( sk_B_2 @ X0 ) )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( v4_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['75','79'])).

thf('81',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v4_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ~ ( v4_ordinal1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['30','54'])).

thf('84',plain,(
    r1_ordinal1 @ ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) @ sk_A ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v3_ordinal1 @ X30 )
      | ~ ( r1_ordinal1 @ X31 @ X30 )
      | ( r2_hidden @ X31 @ ( k1_ordinal1 @ X30 ) )
      | ~ ( v3_ordinal1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t34_ordinal1])).

thf('86',plain,
    ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) )
    | ( r2_hidden @ ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) )
    | ( r2_hidden @ ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( v3_ordinal1 @ ( sk_B_2 @ sk_A ) )
    | ( r2_hidden @ ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) @ ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','88'])).

thf('90',plain,(
    v3_ordinal1 @ ( sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('91',plain,(
    r2_hidden @ ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) @ ( k1_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v3_ordinal1 @ X23 )
      | ~ ( v3_ordinal1 @ X24 )
      | ~ ( r2_hidden @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('93',plain,
    ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) )
    | ( v3_ordinal1 @ ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( v3_ordinal1 @ ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','93'])).

thf('95',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v3_ordinal1 @ ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( r1_ordinal1 @ sk_A @ ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) )
    | ( sk_A
      = ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) )
    | ( v4_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['14','96','97'])).

thf('99',plain,(
    ~ ( v4_ordinal1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['30','54'])).

thf('100',plain,
    ( ( sk_A
      = ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) )
    | ( r1_ordinal1 @ sk_A @ ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_ordinal1 @ X17 )
      | ~ ( v3_ordinal1 @ X18 )
      | ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_ordinal1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('102',plain,
    ( ( sk_A
      = ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) )
    | ( r1_tarski @ sk_A @ ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v3_ordinal1 @ ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('104',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( sk_A
      = ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) )
    | ( r1_tarski @ sk_A @ ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,(
    ! [X27: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X27 ) )
      | ~ ( v3_ordinal1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('107',plain,(
    r1_ordinal1 @ ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) @ sk_A ),
    inference(clc,[status(thm)],['82','83'])).

thf('108',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_ordinal1 @ X17 )
      | ~ ( v3_ordinal1 @ X18 )
      | ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_ordinal1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('109',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) @ sk_A )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ~ ( v3_ordinal1 @ ( sk_B_2 @ sk_A ) )
    | ( r1_tarski @ ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['106','111'])).

thf('113',plain,(
    v3_ordinal1 @ ( sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('114',plain,(
    r1_tarski @ ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('116',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) )
    | ( sk_A
      = ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( sk_A
    = ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) ),
    inference(clc,[status(thm)],['105','116'])).

thf('118',plain,(
    ! [X37: $i] :
      ( ~ ( v3_ordinal1 @ X37 )
      | ( sk_A
       != ( k1_ordinal1 @ X37 ) )
      | ( v3_ordinal1 @ sk_B_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ! [X37: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X37 ) )
        | ~ ( v3_ordinal1 @ X37 ) )
   <= ! [X37: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X37 ) )
        | ~ ( v3_ordinal1 @ X37 ) ) ),
    inference(split,[status(esa)],['118'])).

thf('120',plain,
    ( ! [X37: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X37 ) )
        | ~ ( v3_ordinal1 @ X37 ) )
    | ( v4_ordinal1 @ sk_A ) ),
    inference(split,[status(esa)],['33'])).

thf('121',plain,(
    ! [X37: $i] :
      ( ( sk_A
       != ( k1_ordinal1 @ X37 ) )
      | ~ ( v3_ordinal1 @ X37 ) ) ),
    inference('sat_resolution*',[status(thm)],['32','53','120'])).

thf('122',plain,(
    ! [X37: $i] :
      ( ( sk_A
       != ( k1_ordinal1 @ X37 ) )
      | ~ ( v3_ordinal1 @ X37 ) ) ),
    inference(simpl_trail,[status(thm)],['119','121'])).

thf('123',plain,
    ( ( sk_A != sk_A )
    | ~ ( v3_ordinal1 @ ( sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['117','122'])).

thf('124',plain,(
    v3_ordinal1 @ ( sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('125',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    $false ),
    inference(simplify,[status(thm)],['125'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5rhrKNtGCv
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:19:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 4.00/4.18  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.00/4.18  % Solved by: fo/fo7.sh
% 4.00/4.18  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.00/4.18  % done 2949 iterations in 3.690s
% 4.00/4.18  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.00/4.18  % SZS output start Refutation
% 4.00/4.18  thf(v4_ordinal1_type, type, v4_ordinal1: $i > $o).
% 4.00/4.18  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.00/4.18  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 4.00/4.18  thf(sk_B_2_type, type, sk_B_2: $i > $i).
% 4.00/4.18  thf(sk_A_type, type, sk_A: $i).
% 4.00/4.18  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.00/4.18  thf(sk_B_3_type, type, sk_B_3: $i).
% 4.00/4.18  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 4.00/4.18  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 4.00/4.18  thf(t42_ordinal1, conjecture,
% 4.00/4.18    (![A:$i]:
% 4.00/4.18     ( ( v3_ordinal1 @ A ) =>
% 4.00/4.18       ( ( ~( ( ~( v4_ordinal1 @ A ) ) & 
% 4.00/4.18              ( ![B:$i]:
% 4.00/4.18                ( ( v3_ordinal1 @ B ) => ( ( A ) != ( k1_ordinal1 @ B ) ) ) ) ) ) & 
% 4.00/4.18         ( ~( ( ?[B:$i]:
% 4.00/4.18                ( ( ( A ) = ( k1_ordinal1 @ B ) ) & ( v3_ordinal1 @ B ) ) ) & 
% 4.00/4.18              ( v4_ordinal1 @ A ) ) ) ) ))).
% 4.00/4.18  thf(zf_stmt_0, negated_conjecture,
% 4.00/4.18    (~( ![A:$i]:
% 4.00/4.18        ( ( v3_ordinal1 @ A ) =>
% 4.00/4.18          ( ( ~( ( ~( v4_ordinal1 @ A ) ) & 
% 4.00/4.18                 ( ![B:$i]:
% 4.00/4.18                   ( ( v3_ordinal1 @ B ) => ( ( A ) != ( k1_ordinal1 @ B ) ) ) ) ) ) & 
% 4.00/4.18            ( ~( ( ?[B:$i]:
% 4.00/4.18                   ( ( ( A ) = ( k1_ordinal1 @ B ) ) & ( v3_ordinal1 @ B ) ) ) & 
% 4.00/4.18                 ( v4_ordinal1 @ A ) ) ) ) ) )),
% 4.00/4.18    inference('cnf.neg', [status(esa)], [t42_ordinal1])).
% 4.00/4.18  thf('0', plain, ((v3_ordinal1 @ sk_A)),
% 4.00/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.18  thf(connectedness_r1_ordinal1, axiom,
% 4.00/4.18    (![A:$i,B:$i]:
% 4.00/4.18     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 4.00/4.18       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 4.00/4.18  thf('1', plain,
% 4.00/4.18      (![X14 : $i, X15 : $i]:
% 4.00/4.18         (~ (v3_ordinal1 @ X14)
% 4.00/4.18          | ~ (v3_ordinal1 @ X15)
% 4.00/4.18          | (r1_ordinal1 @ X14 @ X15)
% 4.00/4.18          | (r1_ordinal1 @ X15 @ X14))),
% 4.00/4.18      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 4.00/4.18  thf(redefinition_r1_ordinal1, axiom,
% 4.00/4.18    (![A:$i,B:$i]:
% 4.00/4.18     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 4.00/4.18       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 4.00/4.18  thf('2', plain,
% 4.00/4.18      (![X17 : $i, X18 : $i]:
% 4.00/4.18         (~ (v3_ordinal1 @ X17)
% 4.00/4.18          | ~ (v3_ordinal1 @ X18)
% 4.00/4.18          | (r1_tarski @ X17 @ X18)
% 4.00/4.18          | ~ (r1_ordinal1 @ X17 @ X18))),
% 4.00/4.18      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 4.00/4.18  thf('3', plain,
% 4.00/4.18      (![X0 : $i, X1 : $i]:
% 4.00/4.18         ((r1_ordinal1 @ X0 @ X1)
% 4.00/4.18          | ~ (v3_ordinal1 @ X0)
% 4.00/4.18          | ~ (v3_ordinal1 @ X1)
% 4.00/4.18          | (r1_tarski @ X1 @ X0)
% 4.00/4.18          | ~ (v3_ordinal1 @ X0)
% 4.00/4.18          | ~ (v3_ordinal1 @ X1))),
% 4.00/4.18      inference('sup-', [status(thm)], ['1', '2'])).
% 4.00/4.18  thf('4', plain,
% 4.00/4.18      (![X0 : $i, X1 : $i]:
% 4.00/4.18         ((r1_tarski @ X1 @ X0)
% 4.00/4.18          | ~ (v3_ordinal1 @ X1)
% 4.00/4.18          | ~ (v3_ordinal1 @ X0)
% 4.00/4.18          | (r1_ordinal1 @ X0 @ X1))),
% 4.00/4.18      inference('simplify', [status(thm)], ['3'])).
% 4.00/4.18  thf('5', plain,
% 4.00/4.18      (![X0 : $i]:
% 4.00/4.18         ((r1_ordinal1 @ sk_A @ X0)
% 4.00/4.18          | ~ (v3_ordinal1 @ X0)
% 4.00/4.18          | (r1_tarski @ X0 @ sk_A))),
% 4.00/4.18      inference('sup-', [status(thm)], ['0', '4'])).
% 4.00/4.18  thf(t24_ordinal1, axiom,
% 4.00/4.18    (![A:$i]:
% 4.00/4.18     ( ( v3_ordinal1 @ A ) =>
% 4.00/4.18       ( ![B:$i]:
% 4.00/4.18         ( ( v3_ordinal1 @ B ) =>
% 4.00/4.18           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 4.00/4.18                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 4.00/4.18  thf('6', plain,
% 4.00/4.18      (![X25 : $i, X26 : $i]:
% 4.00/4.18         (~ (v3_ordinal1 @ X25)
% 4.00/4.18          | (r2_hidden @ X26 @ X25)
% 4.00/4.18          | ((X26) = (X25))
% 4.00/4.18          | (r2_hidden @ X25 @ X26)
% 4.00/4.18          | ~ (v3_ordinal1 @ X26))),
% 4.00/4.18      inference('cnf', [status(esa)], [t24_ordinal1])).
% 4.00/4.18  thf(t7_ordinal1, axiom,
% 4.00/4.18    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.00/4.18  thf('7', plain,
% 4.00/4.18      (![X35 : $i, X36 : $i]:
% 4.00/4.18         (~ (r2_hidden @ X35 @ X36) | ~ (r1_tarski @ X36 @ X35))),
% 4.00/4.18      inference('cnf', [status(esa)], [t7_ordinal1])).
% 4.00/4.18  thf('8', plain,
% 4.00/4.18      (![X0 : $i, X1 : $i]:
% 4.00/4.18         (~ (v3_ordinal1 @ X1)
% 4.00/4.18          | (r2_hidden @ X0 @ X1)
% 4.00/4.18          | ((X1) = (X0))
% 4.00/4.18          | ~ (v3_ordinal1 @ X0)
% 4.00/4.18          | ~ (r1_tarski @ X0 @ X1))),
% 4.00/4.18      inference('sup-', [status(thm)], ['6', '7'])).
% 4.00/4.18  thf('9', plain,
% 4.00/4.18      (![X0 : $i]:
% 4.00/4.18         (~ (v3_ordinal1 @ X0)
% 4.00/4.18          | (r1_ordinal1 @ sk_A @ X0)
% 4.00/4.18          | ~ (v3_ordinal1 @ X0)
% 4.00/4.18          | ((sk_A) = (X0))
% 4.00/4.18          | (r2_hidden @ X0 @ sk_A)
% 4.00/4.18          | ~ (v3_ordinal1 @ sk_A))),
% 4.00/4.18      inference('sup-', [status(thm)], ['5', '8'])).
% 4.00/4.18  thf('10', plain, ((v3_ordinal1 @ sk_A)),
% 4.00/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.18  thf('11', plain,
% 4.00/4.18      (![X0 : $i]:
% 4.00/4.18         (~ (v3_ordinal1 @ X0)
% 4.00/4.18          | (r1_ordinal1 @ sk_A @ X0)
% 4.00/4.18          | ~ (v3_ordinal1 @ X0)
% 4.00/4.18          | ((sk_A) = (X0))
% 4.00/4.18          | (r2_hidden @ X0 @ sk_A))),
% 4.00/4.18      inference('demod', [status(thm)], ['9', '10'])).
% 4.00/4.18  thf('12', plain,
% 4.00/4.18      (![X0 : $i]:
% 4.00/4.18         ((r2_hidden @ X0 @ sk_A)
% 4.00/4.18          | ((sk_A) = (X0))
% 4.00/4.18          | (r1_ordinal1 @ sk_A @ X0)
% 4.00/4.18          | ~ (v3_ordinal1 @ X0))),
% 4.00/4.18      inference('simplify', [status(thm)], ['11'])).
% 4.00/4.18  thf(t41_ordinal1, axiom,
% 4.00/4.18    (![A:$i]:
% 4.00/4.18     ( ( v3_ordinal1 @ A ) =>
% 4.00/4.18       ( ( v4_ordinal1 @ A ) <=>
% 4.00/4.18         ( ![B:$i]:
% 4.00/4.18           ( ( v3_ordinal1 @ B ) =>
% 4.00/4.18             ( ( r2_hidden @ B @ A ) => ( r2_hidden @ ( k1_ordinal1 @ B ) @ A ) ) ) ) ) ))).
% 4.00/4.18  thf('13', plain,
% 4.00/4.18      (![X33 : $i]:
% 4.00/4.18         (~ (r2_hidden @ (k1_ordinal1 @ (sk_B_2 @ X33)) @ X33)
% 4.00/4.18          | (v4_ordinal1 @ X33)
% 4.00/4.18          | ~ (v3_ordinal1 @ X33))),
% 4.00/4.18      inference('cnf', [status(esa)], [t41_ordinal1])).
% 4.00/4.18  thf('14', plain,
% 4.00/4.18      ((~ (v3_ordinal1 @ (k1_ordinal1 @ (sk_B_2 @ sk_A)))
% 4.00/4.18        | (r1_ordinal1 @ sk_A @ (k1_ordinal1 @ (sk_B_2 @ sk_A)))
% 4.00/4.18        | ((sk_A) = (k1_ordinal1 @ (sk_B_2 @ sk_A)))
% 4.00/4.18        | ~ (v3_ordinal1 @ sk_A)
% 4.00/4.18        | (v4_ordinal1 @ sk_A))),
% 4.00/4.18      inference('sup-', [status(thm)], ['12', '13'])).
% 4.00/4.18  thf(t29_ordinal1, axiom,
% 4.00/4.18    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 4.00/4.18  thf('15', plain,
% 4.00/4.18      (![X27 : $i]:
% 4.00/4.18         ((v3_ordinal1 @ (k1_ordinal1 @ X27)) | ~ (v3_ordinal1 @ X27))),
% 4.00/4.18      inference('cnf', [status(esa)], [t29_ordinal1])).
% 4.00/4.18  thf('16', plain,
% 4.00/4.18      (![X27 : $i]:
% 4.00/4.18         ((v3_ordinal1 @ (k1_ordinal1 @ X27)) | ~ (v3_ordinal1 @ X27))),
% 4.00/4.18      inference('cnf', [status(esa)], [t29_ordinal1])).
% 4.00/4.18  thf('17', plain,
% 4.00/4.18      (![X27 : $i]:
% 4.00/4.18         ((v3_ordinal1 @ (k1_ordinal1 @ X27)) | ~ (v3_ordinal1 @ X27))),
% 4.00/4.18      inference('cnf', [status(esa)], [t29_ordinal1])).
% 4.00/4.18  thf('18', plain,
% 4.00/4.18      (![X33 : $i]:
% 4.00/4.18         ((v3_ordinal1 @ (sk_B_2 @ X33))
% 4.00/4.18          | (v4_ordinal1 @ X33)
% 4.00/4.18          | ~ (v3_ordinal1 @ X33))),
% 4.00/4.18      inference('cnf', [status(esa)], [t41_ordinal1])).
% 4.00/4.18  thf('19', plain,
% 4.00/4.18      (![X33 : $i]:
% 4.00/4.18         ((v3_ordinal1 @ (sk_B_2 @ X33))
% 4.00/4.18          | (v4_ordinal1 @ X33)
% 4.00/4.18          | ~ (v3_ordinal1 @ X33))),
% 4.00/4.18      inference('cnf', [status(esa)], [t41_ordinal1])).
% 4.00/4.18  thf('20', plain, ((v3_ordinal1 @ sk_A)),
% 4.00/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.18  thf('21', plain,
% 4.00/4.18      (![X0 : $i, X1 : $i]:
% 4.00/4.18         ((r1_tarski @ X1 @ X0)
% 4.00/4.18          | ~ (v3_ordinal1 @ X1)
% 4.00/4.18          | ~ (v3_ordinal1 @ X0)
% 4.00/4.18          | (r1_ordinal1 @ X0 @ X1))),
% 4.00/4.18      inference('simplify', [status(thm)], ['3'])).
% 4.00/4.18  thf('22', plain,
% 4.00/4.18      (![X0 : $i]:
% 4.00/4.18         ((r1_ordinal1 @ X0 @ sk_A)
% 4.00/4.18          | ~ (v3_ordinal1 @ X0)
% 4.00/4.18          | (r1_tarski @ sk_A @ X0))),
% 4.00/4.18      inference('sup-', [status(thm)], ['20', '21'])).
% 4.00/4.18  thf('23', plain,
% 4.00/4.18      (![X33 : $i]:
% 4.00/4.18         ((r2_hidden @ (sk_B_2 @ X33) @ X33)
% 4.00/4.18          | (v4_ordinal1 @ X33)
% 4.00/4.18          | ~ (v3_ordinal1 @ X33))),
% 4.00/4.18      inference('cnf', [status(esa)], [t41_ordinal1])).
% 4.00/4.18  thf('24', plain,
% 4.00/4.18      (![X35 : $i, X36 : $i]:
% 4.00/4.18         (~ (r2_hidden @ X35 @ X36) | ~ (r1_tarski @ X36 @ X35))),
% 4.00/4.18      inference('cnf', [status(esa)], [t7_ordinal1])).
% 4.00/4.18  thf('25', plain,
% 4.00/4.18      (![X0 : $i]:
% 4.00/4.18         (~ (v3_ordinal1 @ X0)
% 4.00/4.18          | (v4_ordinal1 @ X0)
% 4.00/4.18          | ~ (r1_tarski @ X0 @ (sk_B_2 @ X0)))),
% 4.00/4.18      inference('sup-', [status(thm)], ['23', '24'])).
% 4.00/4.18  thf('26', plain,
% 4.00/4.18      ((~ (v3_ordinal1 @ (sk_B_2 @ sk_A))
% 4.00/4.18        | (r1_ordinal1 @ (sk_B_2 @ sk_A) @ sk_A)
% 4.00/4.18        | (v4_ordinal1 @ sk_A)
% 4.00/4.18        | ~ (v3_ordinal1 @ sk_A))),
% 4.00/4.18      inference('sup-', [status(thm)], ['22', '25'])).
% 4.00/4.18  thf('27', plain, ((v3_ordinal1 @ sk_A)),
% 4.00/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.18  thf('28', plain,
% 4.00/4.18      ((~ (v3_ordinal1 @ (sk_B_2 @ sk_A))
% 4.00/4.18        | (r1_ordinal1 @ (sk_B_2 @ sk_A) @ sk_A)
% 4.00/4.18        | (v4_ordinal1 @ sk_A))),
% 4.00/4.18      inference('demod', [status(thm)], ['26', '27'])).
% 4.00/4.18  thf('29', plain, ((~ (v4_ordinal1 @ sk_A) | (v3_ordinal1 @ sk_B_3))),
% 4.00/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.18  thf('30', plain, ((~ (v4_ordinal1 @ sk_A)) <= (~ ((v4_ordinal1 @ sk_A)))),
% 4.00/4.18      inference('split', [status(esa)], ['29'])).
% 4.00/4.18  thf('31', plain,
% 4.00/4.18      ((~ (v4_ordinal1 @ sk_A) | ((sk_A) = (k1_ordinal1 @ sk_B_3)))),
% 4.00/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.18  thf('32', plain,
% 4.00/4.18      (~ ((v4_ordinal1 @ sk_A)) | (((sk_A) = (k1_ordinal1 @ sk_B_3)))),
% 4.00/4.18      inference('split', [status(esa)], ['31'])).
% 4.00/4.18  thf('33', plain,
% 4.00/4.18      (![X37 : $i]:
% 4.00/4.18         (~ (v3_ordinal1 @ X37)
% 4.00/4.18          | ((sk_A) != (k1_ordinal1 @ X37))
% 4.00/4.18          | (v4_ordinal1 @ sk_A))),
% 4.00/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.18  thf('34', plain, (((v4_ordinal1 @ sk_A)) <= (((v4_ordinal1 @ sk_A)))),
% 4.00/4.18      inference('split', [status(esa)], ['33'])).
% 4.00/4.18  thf('35', plain,
% 4.00/4.18      ((((sk_A) = (k1_ordinal1 @ sk_B_3)))
% 4.00/4.18         <= ((((sk_A) = (k1_ordinal1 @ sk_B_3))))),
% 4.00/4.18      inference('split', [status(esa)], ['31'])).
% 4.00/4.18  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 4.00/4.18  thf('36', plain, (![X22 : $i]: (r2_hidden @ X22 @ (k1_ordinal1 @ X22))),
% 4.00/4.18      inference('cnf', [status(esa)], [t10_ordinal1])).
% 4.00/4.18  thf('37', plain,
% 4.00/4.18      (((r2_hidden @ sk_B_3 @ sk_A)) <= ((((sk_A) = (k1_ordinal1 @ sk_B_3))))),
% 4.00/4.18      inference('sup+', [status(thm)], ['35', '36'])).
% 4.00/4.18  thf('38', plain,
% 4.00/4.18      (![X33 : $i, X34 : $i]:
% 4.00/4.18         (~ (v4_ordinal1 @ X33)
% 4.00/4.18          | ~ (r2_hidden @ X34 @ X33)
% 4.00/4.18          | (r2_hidden @ (k1_ordinal1 @ X34) @ X33)
% 4.00/4.18          | ~ (v3_ordinal1 @ X34)
% 4.00/4.18          | ~ (v3_ordinal1 @ X33))),
% 4.00/4.18      inference('cnf', [status(esa)], [t41_ordinal1])).
% 4.00/4.18  thf('39', plain,
% 4.00/4.18      (((~ (v3_ordinal1 @ sk_A)
% 4.00/4.18         | ~ (v3_ordinal1 @ sk_B_3)
% 4.00/4.18         | (r2_hidden @ (k1_ordinal1 @ sk_B_3) @ sk_A)
% 4.00/4.18         | ~ (v4_ordinal1 @ sk_A))) <= ((((sk_A) = (k1_ordinal1 @ sk_B_3))))),
% 4.00/4.18      inference('sup-', [status(thm)], ['37', '38'])).
% 4.00/4.18  thf('40', plain, ((v3_ordinal1 @ sk_A)),
% 4.00/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.18  thf('41', plain,
% 4.00/4.18      (((r2_hidden @ sk_B_3 @ sk_A)) <= ((((sk_A) = (k1_ordinal1 @ sk_B_3))))),
% 4.00/4.18      inference('sup+', [status(thm)], ['35', '36'])).
% 4.00/4.18  thf(t23_ordinal1, axiom,
% 4.00/4.18    (![A:$i,B:$i]:
% 4.00/4.18     ( ( v3_ordinal1 @ B ) => ( ( r2_hidden @ A @ B ) => ( v3_ordinal1 @ A ) ) ))).
% 4.00/4.18  thf('42', plain,
% 4.00/4.18      (![X23 : $i, X24 : $i]:
% 4.00/4.18         ((v3_ordinal1 @ X23)
% 4.00/4.18          | ~ (v3_ordinal1 @ X24)
% 4.00/4.18          | ~ (r2_hidden @ X23 @ X24))),
% 4.00/4.18      inference('cnf', [status(esa)], [t23_ordinal1])).
% 4.00/4.18  thf('43', plain,
% 4.00/4.18      (((~ (v3_ordinal1 @ sk_A) | (v3_ordinal1 @ sk_B_3)))
% 4.00/4.18         <= ((((sk_A) = (k1_ordinal1 @ sk_B_3))))),
% 4.00/4.18      inference('sup-', [status(thm)], ['41', '42'])).
% 4.00/4.18  thf('44', plain, ((v3_ordinal1 @ sk_A)),
% 4.00/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.18  thf('45', plain,
% 4.00/4.18      (((v3_ordinal1 @ sk_B_3)) <= ((((sk_A) = (k1_ordinal1 @ sk_B_3))))),
% 4.00/4.18      inference('demod', [status(thm)], ['43', '44'])).
% 4.00/4.18  thf('46', plain,
% 4.00/4.18      ((((sk_A) = (k1_ordinal1 @ sk_B_3)))
% 4.00/4.18         <= ((((sk_A) = (k1_ordinal1 @ sk_B_3))))),
% 4.00/4.18      inference('split', [status(esa)], ['31'])).
% 4.00/4.18  thf('47', plain,
% 4.00/4.18      ((((r2_hidden @ sk_A @ sk_A) | ~ (v4_ordinal1 @ sk_A)))
% 4.00/4.18         <= ((((sk_A) = (k1_ordinal1 @ sk_B_3))))),
% 4.00/4.18      inference('demod', [status(thm)], ['39', '40', '45', '46'])).
% 4.00/4.18  thf('48', plain,
% 4.00/4.18      (((r2_hidden @ sk_A @ sk_A))
% 4.00/4.18         <= (((v4_ordinal1 @ sk_A)) & (((sk_A) = (k1_ordinal1 @ sk_B_3))))),
% 4.00/4.18      inference('sup-', [status(thm)], ['34', '47'])).
% 4.00/4.18  thf('49', plain,
% 4.00/4.18      (![X35 : $i, X36 : $i]:
% 4.00/4.18         (~ (r2_hidden @ X35 @ X36) | ~ (r1_tarski @ X36 @ X35))),
% 4.00/4.18      inference('cnf', [status(esa)], [t7_ordinal1])).
% 4.00/4.18  thf('50', plain,
% 4.00/4.18      ((~ (r1_tarski @ sk_A @ sk_A))
% 4.00/4.18         <= (((v4_ordinal1 @ sk_A)) & (((sk_A) = (k1_ordinal1 @ sk_B_3))))),
% 4.00/4.18      inference('sup-', [status(thm)], ['48', '49'])).
% 4.00/4.18  thf(d10_xboole_0, axiom,
% 4.00/4.18    (![A:$i,B:$i]:
% 4.00/4.18     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.00/4.18  thf('51', plain,
% 4.00/4.18      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 4.00/4.18      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.00/4.18  thf('52', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 4.00/4.18      inference('simplify', [status(thm)], ['51'])).
% 4.00/4.18  thf('53', plain,
% 4.00/4.18      (~ (((sk_A) = (k1_ordinal1 @ sk_B_3))) | ~ ((v4_ordinal1 @ sk_A))),
% 4.00/4.18      inference('demod', [status(thm)], ['50', '52'])).
% 4.00/4.18  thf('54', plain, (~ ((v4_ordinal1 @ sk_A))),
% 4.00/4.18      inference('sat_resolution*', [status(thm)], ['32', '53'])).
% 4.00/4.18  thf('55', plain, (~ (v4_ordinal1 @ sk_A)),
% 4.00/4.18      inference('simpl_trail', [status(thm)], ['30', '54'])).
% 4.00/4.18  thf('56', plain,
% 4.00/4.18      (((r1_ordinal1 @ (sk_B_2 @ sk_A) @ sk_A)
% 4.00/4.18        | ~ (v3_ordinal1 @ (sk_B_2 @ sk_A)))),
% 4.00/4.18      inference('clc', [status(thm)], ['28', '55'])).
% 4.00/4.18  thf('57', plain,
% 4.00/4.18      ((~ (v3_ordinal1 @ sk_A)
% 4.00/4.18        | (v4_ordinal1 @ sk_A)
% 4.00/4.18        | (r1_ordinal1 @ (sk_B_2 @ sk_A) @ sk_A))),
% 4.00/4.18      inference('sup-', [status(thm)], ['19', '56'])).
% 4.00/4.18  thf('58', plain, ((v3_ordinal1 @ sk_A)),
% 4.00/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.18  thf('59', plain,
% 4.00/4.18      (((v4_ordinal1 @ sk_A) | (r1_ordinal1 @ (sk_B_2 @ sk_A) @ sk_A))),
% 4.00/4.18      inference('demod', [status(thm)], ['57', '58'])).
% 4.00/4.18  thf('60', plain, (~ (v4_ordinal1 @ sk_A)),
% 4.00/4.18      inference('simpl_trail', [status(thm)], ['30', '54'])).
% 4.00/4.18  thf('61', plain, ((r1_ordinal1 @ (sk_B_2 @ sk_A) @ sk_A)),
% 4.00/4.18      inference('clc', [status(thm)], ['59', '60'])).
% 4.00/4.18  thf(t34_ordinal1, axiom,
% 4.00/4.18    (![A:$i]:
% 4.00/4.18     ( ( v3_ordinal1 @ A ) =>
% 4.00/4.18       ( ![B:$i]:
% 4.00/4.18         ( ( v3_ordinal1 @ B ) =>
% 4.00/4.18           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 4.00/4.18             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 4.00/4.18  thf('62', plain,
% 4.00/4.18      (![X30 : $i, X31 : $i]:
% 4.00/4.18         (~ (v3_ordinal1 @ X30)
% 4.00/4.18          | ~ (r1_ordinal1 @ X31 @ X30)
% 4.00/4.18          | (r2_hidden @ X31 @ (k1_ordinal1 @ X30))
% 4.00/4.18          | ~ (v3_ordinal1 @ X31))),
% 4.00/4.18      inference('cnf', [status(esa)], [t34_ordinal1])).
% 4.00/4.18  thf('63', plain,
% 4.00/4.18      ((~ (v3_ordinal1 @ (sk_B_2 @ sk_A))
% 4.00/4.18        | (r2_hidden @ (sk_B_2 @ sk_A) @ (k1_ordinal1 @ sk_A))
% 4.00/4.18        | ~ (v3_ordinal1 @ sk_A))),
% 4.00/4.18      inference('sup-', [status(thm)], ['61', '62'])).
% 4.00/4.18  thf('64', plain, ((v3_ordinal1 @ sk_A)),
% 4.00/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.18  thf('65', plain,
% 4.00/4.18      ((~ (v3_ordinal1 @ (sk_B_2 @ sk_A))
% 4.00/4.18        | (r2_hidden @ (sk_B_2 @ sk_A) @ (k1_ordinal1 @ sk_A)))),
% 4.00/4.18      inference('demod', [status(thm)], ['63', '64'])).
% 4.00/4.18  thf('66', plain,
% 4.00/4.18      ((~ (v3_ordinal1 @ sk_A)
% 4.00/4.18        | (v4_ordinal1 @ sk_A)
% 4.00/4.18        | (r2_hidden @ (sk_B_2 @ sk_A) @ (k1_ordinal1 @ sk_A)))),
% 4.00/4.18      inference('sup-', [status(thm)], ['18', '65'])).
% 4.00/4.18  thf('67', plain, ((v3_ordinal1 @ sk_A)),
% 4.00/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.18  thf('68', plain,
% 4.00/4.18      (((v4_ordinal1 @ sk_A)
% 4.00/4.18        | (r2_hidden @ (sk_B_2 @ sk_A) @ (k1_ordinal1 @ sk_A)))),
% 4.00/4.18      inference('demod', [status(thm)], ['66', '67'])).
% 4.00/4.18  thf('69', plain, (~ (v4_ordinal1 @ sk_A)),
% 4.00/4.18      inference('simpl_trail', [status(thm)], ['30', '54'])).
% 4.00/4.18  thf('70', plain, ((r2_hidden @ (sk_B_2 @ sk_A) @ (k1_ordinal1 @ sk_A))),
% 4.00/4.18      inference('clc', [status(thm)], ['68', '69'])).
% 4.00/4.18  thf('71', plain,
% 4.00/4.18      (![X23 : $i, X24 : $i]:
% 4.00/4.18         ((v3_ordinal1 @ X23)
% 4.00/4.18          | ~ (v3_ordinal1 @ X24)
% 4.00/4.18          | ~ (r2_hidden @ X23 @ X24))),
% 4.00/4.18      inference('cnf', [status(esa)], [t23_ordinal1])).
% 4.00/4.18  thf('72', plain,
% 4.00/4.18      ((~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))
% 4.00/4.18        | (v3_ordinal1 @ (sk_B_2 @ sk_A)))),
% 4.00/4.18      inference('sup-', [status(thm)], ['70', '71'])).
% 4.00/4.18  thf('73', plain,
% 4.00/4.18      ((~ (v3_ordinal1 @ sk_A) | (v3_ordinal1 @ (sk_B_2 @ sk_A)))),
% 4.00/4.18      inference('sup-', [status(thm)], ['17', '72'])).
% 4.00/4.18  thf('74', plain, ((v3_ordinal1 @ sk_A)),
% 4.00/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.18  thf('75', plain, ((v3_ordinal1 @ (sk_B_2 @ sk_A))),
% 4.00/4.18      inference('demod', [status(thm)], ['73', '74'])).
% 4.00/4.18  thf('76', plain,
% 4.00/4.18      (![X33 : $i]:
% 4.00/4.18         ((r2_hidden @ (sk_B_2 @ X33) @ X33)
% 4.00/4.18          | (v4_ordinal1 @ X33)
% 4.00/4.18          | ~ (v3_ordinal1 @ X33))),
% 4.00/4.18      inference('cnf', [status(esa)], [t41_ordinal1])).
% 4.00/4.18  thf(t33_ordinal1, axiom,
% 4.00/4.18    (![A:$i]:
% 4.00/4.18     ( ( v3_ordinal1 @ A ) =>
% 4.00/4.18       ( ![B:$i]:
% 4.00/4.18         ( ( v3_ordinal1 @ B ) =>
% 4.00/4.18           ( ( r2_hidden @ A @ B ) <=>
% 4.00/4.18             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 4.00/4.18  thf('77', plain,
% 4.00/4.18      (![X28 : $i, X29 : $i]:
% 4.00/4.18         (~ (v3_ordinal1 @ X28)
% 4.00/4.18          | ~ (r2_hidden @ X29 @ X28)
% 4.00/4.18          | (r1_ordinal1 @ (k1_ordinal1 @ X29) @ X28)
% 4.00/4.18          | ~ (v3_ordinal1 @ X29))),
% 4.00/4.18      inference('cnf', [status(esa)], [t33_ordinal1])).
% 4.00/4.18  thf('78', plain,
% 4.00/4.18      (![X0 : $i]:
% 4.00/4.18         (~ (v3_ordinal1 @ X0)
% 4.00/4.18          | (v4_ordinal1 @ X0)
% 4.00/4.18          | ~ (v3_ordinal1 @ (sk_B_2 @ X0))
% 4.00/4.18          | (r1_ordinal1 @ (k1_ordinal1 @ (sk_B_2 @ X0)) @ X0)
% 4.00/4.18          | ~ (v3_ordinal1 @ X0))),
% 4.00/4.18      inference('sup-', [status(thm)], ['76', '77'])).
% 4.00/4.18  thf('79', plain,
% 4.00/4.18      (![X0 : $i]:
% 4.00/4.18         ((r1_ordinal1 @ (k1_ordinal1 @ (sk_B_2 @ X0)) @ X0)
% 4.00/4.18          | ~ (v3_ordinal1 @ (sk_B_2 @ X0))
% 4.00/4.18          | (v4_ordinal1 @ X0)
% 4.00/4.18          | ~ (v3_ordinal1 @ X0))),
% 4.00/4.18      inference('simplify', [status(thm)], ['78'])).
% 4.00/4.18  thf('80', plain,
% 4.00/4.18      ((~ (v3_ordinal1 @ sk_A)
% 4.00/4.18        | (v4_ordinal1 @ sk_A)
% 4.00/4.18        | (r1_ordinal1 @ (k1_ordinal1 @ (sk_B_2 @ sk_A)) @ sk_A))),
% 4.00/4.18      inference('sup-', [status(thm)], ['75', '79'])).
% 4.00/4.18  thf('81', plain, ((v3_ordinal1 @ sk_A)),
% 4.00/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.18  thf('82', plain,
% 4.00/4.18      (((v4_ordinal1 @ sk_A)
% 4.00/4.18        | (r1_ordinal1 @ (k1_ordinal1 @ (sk_B_2 @ sk_A)) @ sk_A))),
% 4.00/4.18      inference('demod', [status(thm)], ['80', '81'])).
% 4.00/4.18  thf('83', plain, (~ (v4_ordinal1 @ sk_A)),
% 4.00/4.18      inference('simpl_trail', [status(thm)], ['30', '54'])).
% 4.00/4.18  thf('84', plain, ((r1_ordinal1 @ (k1_ordinal1 @ (sk_B_2 @ sk_A)) @ sk_A)),
% 4.00/4.18      inference('clc', [status(thm)], ['82', '83'])).
% 4.00/4.18  thf('85', plain,
% 4.00/4.18      (![X30 : $i, X31 : $i]:
% 4.00/4.18         (~ (v3_ordinal1 @ X30)
% 4.00/4.18          | ~ (r1_ordinal1 @ X31 @ X30)
% 4.00/4.18          | (r2_hidden @ X31 @ (k1_ordinal1 @ X30))
% 4.00/4.18          | ~ (v3_ordinal1 @ X31))),
% 4.00/4.18      inference('cnf', [status(esa)], [t34_ordinal1])).
% 4.00/4.18  thf('86', plain,
% 4.00/4.18      ((~ (v3_ordinal1 @ (k1_ordinal1 @ (sk_B_2 @ sk_A)))
% 4.00/4.18        | (r2_hidden @ (k1_ordinal1 @ (sk_B_2 @ sk_A)) @ (k1_ordinal1 @ sk_A))
% 4.00/4.18        | ~ (v3_ordinal1 @ sk_A))),
% 4.00/4.18      inference('sup-', [status(thm)], ['84', '85'])).
% 4.00/4.18  thf('87', plain, ((v3_ordinal1 @ sk_A)),
% 4.00/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.18  thf('88', plain,
% 4.00/4.18      ((~ (v3_ordinal1 @ (k1_ordinal1 @ (sk_B_2 @ sk_A)))
% 4.00/4.18        | (r2_hidden @ (k1_ordinal1 @ (sk_B_2 @ sk_A)) @ (k1_ordinal1 @ sk_A)))),
% 4.00/4.18      inference('demod', [status(thm)], ['86', '87'])).
% 4.00/4.18  thf('89', plain,
% 4.00/4.18      ((~ (v3_ordinal1 @ (sk_B_2 @ sk_A))
% 4.00/4.18        | (r2_hidden @ (k1_ordinal1 @ (sk_B_2 @ sk_A)) @ (k1_ordinal1 @ sk_A)))),
% 4.00/4.18      inference('sup-', [status(thm)], ['16', '88'])).
% 4.00/4.18  thf('90', plain, ((v3_ordinal1 @ (sk_B_2 @ sk_A))),
% 4.00/4.18      inference('demod', [status(thm)], ['73', '74'])).
% 4.00/4.18  thf('91', plain,
% 4.00/4.18      ((r2_hidden @ (k1_ordinal1 @ (sk_B_2 @ sk_A)) @ (k1_ordinal1 @ sk_A))),
% 4.00/4.18      inference('demod', [status(thm)], ['89', '90'])).
% 4.00/4.18  thf('92', plain,
% 4.00/4.18      (![X23 : $i, X24 : $i]:
% 4.00/4.18         ((v3_ordinal1 @ X23)
% 4.00/4.18          | ~ (v3_ordinal1 @ X24)
% 4.00/4.18          | ~ (r2_hidden @ X23 @ X24))),
% 4.00/4.18      inference('cnf', [status(esa)], [t23_ordinal1])).
% 4.00/4.18  thf('93', plain,
% 4.00/4.18      ((~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))
% 4.00/4.18        | (v3_ordinal1 @ (k1_ordinal1 @ (sk_B_2 @ sk_A))))),
% 4.00/4.18      inference('sup-', [status(thm)], ['91', '92'])).
% 4.00/4.18  thf('94', plain,
% 4.00/4.18      ((~ (v3_ordinal1 @ sk_A)
% 4.00/4.18        | (v3_ordinal1 @ (k1_ordinal1 @ (sk_B_2 @ sk_A))))),
% 4.00/4.18      inference('sup-', [status(thm)], ['15', '93'])).
% 4.00/4.18  thf('95', plain, ((v3_ordinal1 @ sk_A)),
% 4.00/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.18  thf('96', plain, ((v3_ordinal1 @ (k1_ordinal1 @ (sk_B_2 @ sk_A)))),
% 4.00/4.18      inference('demod', [status(thm)], ['94', '95'])).
% 4.00/4.18  thf('97', plain, ((v3_ordinal1 @ sk_A)),
% 4.00/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.18  thf('98', plain,
% 4.00/4.18      (((r1_ordinal1 @ sk_A @ (k1_ordinal1 @ (sk_B_2 @ sk_A)))
% 4.00/4.18        | ((sk_A) = (k1_ordinal1 @ (sk_B_2 @ sk_A)))
% 4.00/4.18        | (v4_ordinal1 @ sk_A))),
% 4.00/4.18      inference('demod', [status(thm)], ['14', '96', '97'])).
% 4.00/4.18  thf('99', plain, (~ (v4_ordinal1 @ sk_A)),
% 4.00/4.18      inference('simpl_trail', [status(thm)], ['30', '54'])).
% 4.00/4.18  thf('100', plain,
% 4.00/4.18      ((((sk_A) = (k1_ordinal1 @ (sk_B_2 @ sk_A)))
% 4.00/4.18        | (r1_ordinal1 @ sk_A @ (k1_ordinal1 @ (sk_B_2 @ sk_A))))),
% 4.00/4.18      inference('clc', [status(thm)], ['98', '99'])).
% 4.00/4.18  thf('101', plain,
% 4.00/4.18      (![X17 : $i, X18 : $i]:
% 4.00/4.18         (~ (v3_ordinal1 @ X17)
% 4.00/4.18          | ~ (v3_ordinal1 @ X18)
% 4.00/4.18          | (r1_tarski @ X17 @ X18)
% 4.00/4.18          | ~ (r1_ordinal1 @ X17 @ X18))),
% 4.00/4.18      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 4.00/4.18  thf('102', plain,
% 4.00/4.18      ((((sk_A) = (k1_ordinal1 @ (sk_B_2 @ sk_A)))
% 4.00/4.18        | (r1_tarski @ sk_A @ (k1_ordinal1 @ (sk_B_2 @ sk_A)))
% 4.00/4.18        | ~ (v3_ordinal1 @ (k1_ordinal1 @ (sk_B_2 @ sk_A)))
% 4.00/4.18        | ~ (v3_ordinal1 @ sk_A))),
% 4.00/4.18      inference('sup-', [status(thm)], ['100', '101'])).
% 4.00/4.18  thf('103', plain, ((v3_ordinal1 @ (k1_ordinal1 @ (sk_B_2 @ sk_A)))),
% 4.00/4.18      inference('demod', [status(thm)], ['94', '95'])).
% 4.00/4.18  thf('104', plain, ((v3_ordinal1 @ sk_A)),
% 4.00/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.18  thf('105', plain,
% 4.00/4.18      ((((sk_A) = (k1_ordinal1 @ (sk_B_2 @ sk_A)))
% 4.00/4.18        | (r1_tarski @ sk_A @ (k1_ordinal1 @ (sk_B_2 @ sk_A))))),
% 4.00/4.18      inference('demod', [status(thm)], ['102', '103', '104'])).
% 4.00/4.18  thf('106', plain,
% 4.00/4.18      (![X27 : $i]:
% 4.00/4.18         ((v3_ordinal1 @ (k1_ordinal1 @ X27)) | ~ (v3_ordinal1 @ X27))),
% 4.00/4.18      inference('cnf', [status(esa)], [t29_ordinal1])).
% 4.00/4.18  thf('107', plain, ((r1_ordinal1 @ (k1_ordinal1 @ (sk_B_2 @ sk_A)) @ sk_A)),
% 4.00/4.18      inference('clc', [status(thm)], ['82', '83'])).
% 4.00/4.18  thf('108', plain,
% 4.00/4.18      (![X17 : $i, X18 : $i]:
% 4.00/4.18         (~ (v3_ordinal1 @ X17)
% 4.00/4.18          | ~ (v3_ordinal1 @ X18)
% 4.00/4.18          | (r1_tarski @ X17 @ X18)
% 4.00/4.18          | ~ (r1_ordinal1 @ X17 @ X18))),
% 4.00/4.18      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 4.00/4.18  thf('109', plain,
% 4.00/4.18      (((r1_tarski @ (k1_ordinal1 @ (sk_B_2 @ sk_A)) @ sk_A)
% 4.00/4.18        | ~ (v3_ordinal1 @ sk_A)
% 4.00/4.18        | ~ (v3_ordinal1 @ (k1_ordinal1 @ (sk_B_2 @ sk_A))))),
% 4.00/4.18      inference('sup-', [status(thm)], ['107', '108'])).
% 4.00/4.18  thf('110', plain, ((v3_ordinal1 @ sk_A)),
% 4.00/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.18  thf('111', plain,
% 4.00/4.18      (((r1_tarski @ (k1_ordinal1 @ (sk_B_2 @ sk_A)) @ sk_A)
% 4.00/4.18        | ~ (v3_ordinal1 @ (k1_ordinal1 @ (sk_B_2 @ sk_A))))),
% 4.00/4.18      inference('demod', [status(thm)], ['109', '110'])).
% 4.00/4.18  thf('112', plain,
% 4.00/4.18      ((~ (v3_ordinal1 @ (sk_B_2 @ sk_A))
% 4.00/4.18        | (r1_tarski @ (k1_ordinal1 @ (sk_B_2 @ sk_A)) @ sk_A))),
% 4.00/4.18      inference('sup-', [status(thm)], ['106', '111'])).
% 4.00/4.18  thf('113', plain, ((v3_ordinal1 @ (sk_B_2 @ sk_A))),
% 4.00/4.18      inference('demod', [status(thm)], ['73', '74'])).
% 4.00/4.18  thf('114', plain, ((r1_tarski @ (k1_ordinal1 @ (sk_B_2 @ sk_A)) @ sk_A)),
% 4.00/4.18      inference('demod', [status(thm)], ['112', '113'])).
% 4.00/4.18  thf('115', plain,
% 4.00/4.18      (![X4 : $i, X6 : $i]:
% 4.00/4.18         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 4.00/4.18      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.00/4.18  thf('116', plain,
% 4.00/4.18      ((~ (r1_tarski @ sk_A @ (k1_ordinal1 @ (sk_B_2 @ sk_A)))
% 4.00/4.18        | ((sk_A) = (k1_ordinal1 @ (sk_B_2 @ sk_A))))),
% 4.00/4.18      inference('sup-', [status(thm)], ['114', '115'])).
% 4.00/4.18  thf('117', plain, (((sk_A) = (k1_ordinal1 @ (sk_B_2 @ sk_A)))),
% 4.00/4.18      inference('clc', [status(thm)], ['105', '116'])).
% 4.00/4.18  thf('118', plain,
% 4.00/4.18      (![X37 : $i]:
% 4.00/4.18         (~ (v3_ordinal1 @ X37)
% 4.00/4.18          | ((sk_A) != (k1_ordinal1 @ X37))
% 4.00/4.18          | (v3_ordinal1 @ sk_B_3))),
% 4.00/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.18  thf('119', plain,
% 4.00/4.18      ((![X37 : $i]: (((sk_A) != (k1_ordinal1 @ X37)) | ~ (v3_ordinal1 @ X37)))
% 4.00/4.18         <= ((![X37 : $i]:
% 4.00/4.18                (((sk_A) != (k1_ordinal1 @ X37)) | ~ (v3_ordinal1 @ X37))))),
% 4.00/4.18      inference('split', [status(esa)], ['118'])).
% 4.00/4.18  thf('120', plain,
% 4.00/4.18      ((![X37 : $i]: (((sk_A) != (k1_ordinal1 @ X37)) | ~ (v3_ordinal1 @ X37))) | 
% 4.00/4.18       ((v4_ordinal1 @ sk_A))),
% 4.00/4.18      inference('split', [status(esa)], ['33'])).
% 4.00/4.18  thf('121', plain,
% 4.00/4.18      ((![X37 : $i]: (((sk_A) != (k1_ordinal1 @ X37)) | ~ (v3_ordinal1 @ X37)))),
% 4.00/4.18      inference('sat_resolution*', [status(thm)], ['32', '53', '120'])).
% 4.00/4.18  thf('122', plain,
% 4.00/4.18      (![X37 : $i]: (((sk_A) != (k1_ordinal1 @ X37)) | ~ (v3_ordinal1 @ X37))),
% 4.00/4.18      inference('simpl_trail', [status(thm)], ['119', '121'])).
% 4.00/4.18  thf('123', plain, ((((sk_A) != (sk_A)) | ~ (v3_ordinal1 @ (sk_B_2 @ sk_A)))),
% 4.00/4.18      inference('sup-', [status(thm)], ['117', '122'])).
% 4.00/4.18  thf('124', plain, ((v3_ordinal1 @ (sk_B_2 @ sk_A))),
% 4.00/4.18      inference('demod', [status(thm)], ['73', '74'])).
% 4.00/4.18  thf('125', plain, (((sk_A) != (sk_A))),
% 4.00/4.18      inference('demod', [status(thm)], ['123', '124'])).
% 4.00/4.18  thf('126', plain, ($false), inference('simplify', [status(thm)], ['125'])).
% 4.00/4.18  
% 4.00/4.18  % SZS output end Refutation
% 4.00/4.18  
% 4.00/4.19  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
