%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PU88dz9Qx8

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:11 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  128 (1102 expanded)
%              Number of leaves         :   23 ( 297 expanded)
%              Depth                    :   41
%              Number of atoms          :  804 (10744 expanded)
%              Number of equality atoms :   36 ( 972 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i > $i )).

thf(v4_ordinal1_type,type,(
    v4_ordinal1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('0',plain,(
    ! [X21: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X21 ) )
      | ~ ( v3_ordinal1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('1',plain,(
    ! [X21: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X21 ) )
      | ~ ( v3_ordinal1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf(t41_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v4_ordinal1 @ A )
      <=> ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r2_hidden @ B @ A )
             => ( r2_hidden @ ( k1_ordinal1 @ B ) @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X27: $i] :
      ( ( v3_ordinal1 @ ( sk_B_2 @ X27 ) )
      | ( v4_ordinal1 @ X27 )
      | ~ ( v3_ordinal1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf('3',plain,(
    ! [X27: $i] :
      ( ( v3_ordinal1 @ ( sk_B_2 @ X27 ) )
      | ( v4_ordinal1 @ X27 )
      | ~ ( v3_ordinal1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

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

thf('4',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_ordinal1 @ X7 )
      | ~ ( v3_ordinal1 @ X8 )
      | ( r1_ordinal1 @ X7 @ X8 )
      | ( r1_ordinal1 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v3_ordinal1 @ X10 )
      | ~ ( v3_ordinal1 @ X11 )
      | ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_ordinal1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ sk_A )
      | ( r1_tarski @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ sk_A )
      | ( r1_tarski @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r1_ordinal1 @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X27: $i] :
      ( ( r2_hidden @ ( sk_B_2 @ X27 ) @ X27 )
      | ( v4_ordinal1 @ X27 )
      | ~ ( v3_ordinal1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('13',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X29 @ X30 )
      | ~ ( r1_tarski @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( v3_ordinal1 @ ( sk_B_2 @ sk_A ) )
    | ( r1_ordinal1 @ ( sk_B_2 @ sk_A ) @ sk_A )
    | ( v4_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( v3_ordinal1 @ ( sk_B_2 @ sk_A ) )
    | ( r1_ordinal1 @ ( sk_B_2 @ sk_A ) @ sk_A )
    | ( v4_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( v4_ordinal1 @ sk_A )
    | ( v3_ordinal1 @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( v4_ordinal1 @ sk_A )
   <= ~ ( v4_ordinal1 @ sk_A ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,
    ( ~ ( v4_ordinal1 @ sk_A )
    | ( sk_A
      = ( k1_ordinal1 @ sk_B_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( v4_ordinal1 @ sk_A )
    | ( sk_A
      = ( k1_ordinal1 @ sk_B_3 ) ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,(
    ! [X31: $i] :
      ( ~ ( v3_ordinal1 @ X31 )
      | ( sk_A
       != ( k1_ordinal1 @ X31 ) )
      | ( v4_ordinal1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v4_ordinal1 @ sk_A )
   <= ( v4_ordinal1 @ sk_A ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,
    ( ( sk_A
      = ( k1_ordinal1 @ sk_B_3 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_3 ) ) ),
    inference(split,[status(esa)],['20'])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('25',plain,(
    ! [X15: $i] :
      ( r2_hidden @ X15 @ ( k1_ordinal1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('26',plain,
    ( ( r2_hidden @ sk_B_3 @ sk_A )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_3 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v4_ordinal1 @ X27 )
      | ~ ( r2_hidden @ X28 @ X27 )
      | ( r2_hidden @ ( k1_ordinal1 @ X28 ) @ X27 )
      | ~ ( v3_ordinal1 @ X28 )
      | ~ ( v3_ordinal1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf('28',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B_3 )
      | ( r2_hidden @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A )
      | ~ ( v4_ordinal1 @ sk_A ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( r2_hidden @ sk_B_3 @ sk_A )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_3 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t23_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v3_ordinal1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( v3_ordinal1 @ A ) ) ) )).

thf('31',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v3_ordinal1 @ X19 )
      | ~ ( v3_ordinal1 @ X20 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('32',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( v3_ordinal1 @ sk_B_3 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v3_ordinal1 @ sk_B_3 )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_A
      = ( k1_ordinal1 @ sk_B_3 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_3 ) ) ),
    inference(split,[status(esa)],['20'])).

thf('36',plain,
    ( ( ( r2_hidden @ sk_A @ sk_A )
      | ~ ( v4_ordinal1 @ sk_A ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['28','29','34','35'])).

thf('37',plain,
    ( ( r2_hidden @ sk_A @ sk_A )
   <= ( ( v4_ordinal1 @ sk_A )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_3 ) ) ) ),
    inference('sup-',[status(thm)],['23','36'])).

thf('38',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X29 @ X30 )
      | ~ ( r1_tarski @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('39',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
   <= ( ( v4_ordinal1 @ sk_A )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_3 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( sk_A
     != ( k1_ordinal1 @ sk_B_3 ) )
    | ~ ( v4_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['39','41'])).

thf('43',plain,(
    ~ ( v4_ordinal1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['21','42'])).

thf('44',plain,(
    ~ ( v4_ordinal1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['19','43'])).

thf('45',plain,
    ( ( r1_ordinal1 @ ( sk_B_2 @ sk_A ) @ sk_A )
    | ~ ( v3_ordinal1 @ ( sk_B_2 @ sk_A ) ) ),
    inference(clc,[status(thm)],['17','44'])).

thf('46',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( v4_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ ( sk_B_2 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['3','45'])).

thf('47',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v4_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ ( sk_B_2 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v4_ordinal1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['19','43'])).

thf('50',plain,(
    r1_ordinal1 @ ( sk_B_2 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['48','49'])).

thf(t34_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
          <=> ( r1_ordinal1 @ A @ B ) ) ) ) )).

thf('51',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v3_ordinal1 @ X24 )
      | ~ ( r1_ordinal1 @ X25 @ X24 )
      | ( r2_hidden @ X25 @ ( k1_ordinal1 @ X24 ) )
      | ~ ( v3_ordinal1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t34_ordinal1])).

thf('52',plain,
    ( ~ ( v3_ordinal1 @ ( sk_B_2 @ sk_A ) )
    | ( r2_hidden @ ( sk_B_2 @ sk_A ) @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ~ ( v3_ordinal1 @ ( sk_B_2 @ sk_A ) )
    | ( r2_hidden @ ( sk_B_2 @ sk_A ) @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( v4_ordinal1 @ sk_A )
    | ( r2_hidden @ ( sk_B_2 @ sk_A ) @ ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','54'])).

thf('56',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v4_ordinal1 @ sk_A )
    | ( r2_hidden @ ( sk_B_2 @ sk_A ) @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v4_ordinal1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['19','43'])).

thf('59',plain,(
    r2_hidden @ ( sk_B_2 @ sk_A ) @ ( k1_ordinal1 @ sk_A ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v3_ordinal1 @ X19 )
      | ~ ( v3_ordinal1 @ X20 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('61',plain,
    ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) )
    | ( v3_ordinal1 @ ( sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( v3_ordinal1 @ ( sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','61'])).

thf('63',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v3_ordinal1 @ ( sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X27: $i] :
      ( ( r2_hidden @ ( sk_B_2 @ X27 ) @ X27 )
      | ( v4_ordinal1 @ X27 )
      | ~ ( v3_ordinal1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf(s1_xboole_0__e3_53__ordinal1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
    ! [C: $i] :
      ( ( r2_hidden @ C @ B )
    <=> ( ( r2_hidden @ C @ A )
        & ( v3_ordinal1 @ C ) ) ) )).

thf('66',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ X14 @ ( sk_B @ X13 ) )
      | ~ ( v3_ordinal1 @ X14 )
      | ~ ( r2_hidden @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[s1_xboole_0__e3_53__ordinal1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ ( sk_B_2 @ X0 ) )
      | ( r2_hidden @ ( sk_B_2 @ X0 ) @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( r2_hidden @ ( sk_B_2 @ sk_A ) @ ( sk_B @ sk_A ) )
    | ( v4_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( r2_hidden @ ( sk_B_2 @ sk_A ) @ ( sk_B @ sk_A ) )
    | ( v4_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v4_ordinal1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['19','43'])).

thf('72',plain,(
    r2_hidden @ ( sk_B_2 @ sk_A ) @ ( sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ~ ( r2_hidden @ X12 @ ( sk_B @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[s1_xboole_0__e3_53__ordinal1])).

thf('74',plain,(
    r2_hidden @ ( sk_B_2 @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['72','73'])).

thf(t33_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
          <=> ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) )).

thf('75',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v3_ordinal1 @ X22 )
      | ~ ( r2_hidden @ X23 @ X22 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X23 ) @ X22 )
      | ~ ( v3_ordinal1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t33_ordinal1])).

thf('76',plain,
    ( ~ ( v3_ordinal1 @ ( sk_B_2 @ sk_A ) )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v3_ordinal1 @ ( sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('78',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    r1_ordinal1 @ ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v3_ordinal1 @ X24 )
      | ~ ( r1_ordinal1 @ X25 @ X24 )
      | ( r2_hidden @ X25 @ ( k1_ordinal1 @ X24 ) )
      | ~ ( v3_ordinal1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t34_ordinal1])).

thf('81',plain,
    ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) )
    | ( r2_hidden @ ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) )
    | ( r2_hidden @ ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ~ ( v3_ordinal1 @ ( sk_B_2 @ sk_A ) )
    | ( r2_hidden @ ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) @ ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','83'])).

thf('85',plain,(
    v3_ordinal1 @ ( sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('86',plain,(
    r2_hidden @ ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) @ ( k1_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['84','85'])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('87',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X17 = X16 )
      | ( r2_hidden @ X17 @ X16 )
      | ~ ( r2_hidden @ X17 @ ( k1_ordinal1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('88',plain,
    ( ( r2_hidden @ ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) ) @ sk_A )
    | ( ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X27: $i] :
      ( ~ ( r2_hidden @ ( k1_ordinal1 @ ( sk_B_2 @ X27 ) ) @ X27 )
      | ( v4_ordinal1 @ X27 )
      | ~ ( v3_ordinal1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf('90',plain,
    ( ( ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) )
      = sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( v4_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) )
      = sk_A )
    | ( v4_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( v4_ordinal1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['19','43'])).

thf('94',plain,
    ( ( k1_ordinal1 @ ( sk_B_2 @ sk_A ) )
    = sk_A ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X31: $i] :
      ( ~ ( v3_ordinal1 @ X31 )
      | ( sk_A
       != ( k1_ordinal1 @ X31 ) )
      | ( v3_ordinal1 @ sk_B_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ! [X31: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X31 ) )
        | ~ ( v3_ordinal1 @ X31 ) )
   <= ! [X31: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X31 ) )
        | ~ ( v3_ordinal1 @ X31 ) ) ),
    inference(split,[status(esa)],['95'])).

thf('97',plain,
    ( ! [X31: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X31 ) )
        | ~ ( v3_ordinal1 @ X31 ) )
    | ( v4_ordinal1 @ sk_A ) ),
    inference(split,[status(esa)],['22'])).

thf('98',plain,(
    ! [X31: $i] :
      ( ( sk_A
       != ( k1_ordinal1 @ X31 ) )
      | ~ ( v3_ordinal1 @ X31 ) ) ),
    inference('sat_resolution*',[status(thm)],['21','42','97'])).

thf('99',plain,(
    ! [X31: $i] :
      ( ( sk_A
       != ( k1_ordinal1 @ X31 ) )
      | ~ ( v3_ordinal1 @ X31 ) ) ),
    inference(simpl_trail,[status(thm)],['96','98'])).

thf('100',plain,
    ( ( sk_A != sk_A )
    | ~ ( v3_ordinal1 @ ( sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['94','99'])).

thf('101',plain,(
    v3_ordinal1 @ ( sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('102',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    $false ),
    inference(simplify,[status(thm)],['102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PU88dz9Qx8
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:48:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.55/0.75  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.55/0.75  % Solved by: fo/fo7.sh
% 0.55/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.75  % done 768 iterations in 0.304s
% 0.55/0.75  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.55/0.75  % SZS output start Refutation
% 0.55/0.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.55/0.75  thf(sk_B_2_type, type, sk_B_2: $i > $i).
% 0.55/0.75  thf(v4_ordinal1_type, type, v4_ordinal1: $i > $o).
% 0.55/0.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.75  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.55/0.75  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.55/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.75  thf(sk_B_3_type, type, sk_B_3: $i).
% 0.55/0.75  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.55/0.75  thf(sk_B_type, type, sk_B: $i > $i).
% 0.55/0.75  thf(t29_ordinal1, axiom,
% 0.55/0.75    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 0.55/0.75  thf('0', plain,
% 0.55/0.75      (![X21 : $i]:
% 0.55/0.75         ((v3_ordinal1 @ (k1_ordinal1 @ X21)) | ~ (v3_ordinal1 @ X21))),
% 0.55/0.75      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.55/0.75  thf('1', plain,
% 0.55/0.75      (![X21 : $i]:
% 0.55/0.75         ((v3_ordinal1 @ (k1_ordinal1 @ X21)) | ~ (v3_ordinal1 @ X21))),
% 0.55/0.75      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.55/0.75  thf(t41_ordinal1, axiom,
% 0.55/0.75    (![A:$i]:
% 0.55/0.75     ( ( v3_ordinal1 @ A ) =>
% 0.55/0.75       ( ( v4_ordinal1 @ A ) <=>
% 0.55/0.75         ( ![B:$i]:
% 0.55/0.75           ( ( v3_ordinal1 @ B ) =>
% 0.55/0.75             ( ( r2_hidden @ B @ A ) => ( r2_hidden @ ( k1_ordinal1 @ B ) @ A ) ) ) ) ) ))).
% 0.55/0.75  thf('2', plain,
% 0.55/0.75      (![X27 : $i]:
% 0.55/0.75         ((v3_ordinal1 @ (sk_B_2 @ X27))
% 0.55/0.75          | (v4_ordinal1 @ X27)
% 0.55/0.75          | ~ (v3_ordinal1 @ X27))),
% 0.55/0.75      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.55/0.75  thf('3', plain,
% 0.55/0.75      (![X27 : $i]:
% 0.55/0.75         ((v3_ordinal1 @ (sk_B_2 @ X27))
% 0.55/0.75          | (v4_ordinal1 @ X27)
% 0.55/0.75          | ~ (v3_ordinal1 @ X27))),
% 0.55/0.75      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.55/0.75  thf(t42_ordinal1, conjecture,
% 0.55/0.75    (![A:$i]:
% 0.55/0.75     ( ( v3_ordinal1 @ A ) =>
% 0.55/0.75       ( ( ~( ( ~( v4_ordinal1 @ A ) ) & 
% 0.55/0.75              ( ![B:$i]:
% 0.55/0.75                ( ( v3_ordinal1 @ B ) => ( ( A ) != ( k1_ordinal1 @ B ) ) ) ) ) ) & 
% 0.55/0.75         ( ~( ( ?[B:$i]:
% 0.55/0.76                ( ( ( A ) = ( k1_ordinal1 @ B ) ) & ( v3_ordinal1 @ B ) ) ) & 
% 0.55/0.76              ( v4_ordinal1 @ A ) ) ) ) ))).
% 0.55/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.76    (~( ![A:$i]:
% 0.55/0.76        ( ( v3_ordinal1 @ A ) =>
% 0.55/0.76          ( ( ~( ( ~( v4_ordinal1 @ A ) ) & 
% 0.55/0.76                 ( ![B:$i]:
% 0.55/0.76                   ( ( v3_ordinal1 @ B ) => ( ( A ) != ( k1_ordinal1 @ B ) ) ) ) ) ) & 
% 0.55/0.76            ( ~( ( ?[B:$i]:
% 0.55/0.76                   ( ( ( A ) = ( k1_ordinal1 @ B ) ) & ( v3_ordinal1 @ B ) ) ) & 
% 0.55/0.76                 ( v4_ordinal1 @ A ) ) ) ) ) )),
% 0.55/0.76    inference('cnf.neg', [status(esa)], [t42_ordinal1])).
% 0.55/0.76  thf('4', plain, ((v3_ordinal1 @ sk_A)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf(connectedness_r1_ordinal1, axiom,
% 0.55/0.76    (![A:$i,B:$i]:
% 0.55/0.76     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.55/0.76       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 0.55/0.76  thf('5', plain,
% 0.55/0.76      (![X7 : $i, X8 : $i]:
% 0.55/0.76         (~ (v3_ordinal1 @ X7)
% 0.55/0.76          | ~ (v3_ordinal1 @ X8)
% 0.55/0.76          | (r1_ordinal1 @ X7 @ X8)
% 0.55/0.76          | (r1_ordinal1 @ X8 @ X7))),
% 0.55/0.76      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.55/0.76  thf('6', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         ((r1_ordinal1 @ X0 @ sk_A)
% 0.55/0.76          | (r1_ordinal1 @ sk_A @ X0)
% 0.55/0.76          | ~ (v3_ordinal1 @ X0))),
% 0.55/0.76      inference('sup-', [status(thm)], ['4', '5'])).
% 0.55/0.76  thf(redefinition_r1_ordinal1, axiom,
% 0.55/0.76    (![A:$i,B:$i]:
% 0.55/0.76     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.55/0.76       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.55/0.76  thf('7', plain,
% 0.55/0.76      (![X10 : $i, X11 : $i]:
% 0.55/0.76         (~ (v3_ordinal1 @ X10)
% 0.55/0.76          | ~ (v3_ordinal1 @ X11)
% 0.55/0.76          | (r1_tarski @ X10 @ X11)
% 0.55/0.76          | ~ (r1_ordinal1 @ X10 @ X11))),
% 0.55/0.76      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.55/0.76  thf('8', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         (~ (v3_ordinal1 @ X0)
% 0.55/0.76          | (r1_ordinal1 @ X0 @ sk_A)
% 0.55/0.76          | (r1_tarski @ sk_A @ X0)
% 0.55/0.76          | ~ (v3_ordinal1 @ X0)
% 0.55/0.76          | ~ (v3_ordinal1 @ sk_A))),
% 0.55/0.76      inference('sup-', [status(thm)], ['6', '7'])).
% 0.55/0.76  thf('9', plain, ((v3_ordinal1 @ sk_A)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('10', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         (~ (v3_ordinal1 @ X0)
% 0.55/0.76          | (r1_ordinal1 @ X0 @ sk_A)
% 0.55/0.76          | (r1_tarski @ sk_A @ X0)
% 0.55/0.76          | ~ (v3_ordinal1 @ X0))),
% 0.55/0.76      inference('demod', [status(thm)], ['8', '9'])).
% 0.55/0.76  thf('11', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         ((r1_tarski @ sk_A @ X0)
% 0.55/0.76          | (r1_ordinal1 @ X0 @ sk_A)
% 0.55/0.76          | ~ (v3_ordinal1 @ X0))),
% 0.55/0.76      inference('simplify', [status(thm)], ['10'])).
% 0.55/0.76  thf('12', plain,
% 0.55/0.76      (![X27 : $i]:
% 0.55/0.76         ((r2_hidden @ (sk_B_2 @ X27) @ X27)
% 0.55/0.76          | (v4_ordinal1 @ X27)
% 0.55/0.76          | ~ (v3_ordinal1 @ X27))),
% 0.55/0.76      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.55/0.76  thf(t7_ordinal1, axiom,
% 0.55/0.76    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.55/0.76  thf('13', plain,
% 0.55/0.76      (![X29 : $i, X30 : $i]:
% 0.55/0.76         (~ (r2_hidden @ X29 @ X30) | ~ (r1_tarski @ X30 @ X29))),
% 0.55/0.76      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.55/0.76  thf('14', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         (~ (v3_ordinal1 @ X0)
% 0.55/0.76          | (v4_ordinal1 @ X0)
% 0.55/0.76          | ~ (r1_tarski @ X0 @ (sk_B_2 @ X0)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['12', '13'])).
% 0.55/0.76  thf('15', plain,
% 0.55/0.76      ((~ (v3_ordinal1 @ (sk_B_2 @ sk_A))
% 0.55/0.76        | (r1_ordinal1 @ (sk_B_2 @ sk_A) @ sk_A)
% 0.55/0.76        | (v4_ordinal1 @ sk_A)
% 0.55/0.76        | ~ (v3_ordinal1 @ sk_A))),
% 0.55/0.76      inference('sup-', [status(thm)], ['11', '14'])).
% 0.55/0.76  thf('16', plain, ((v3_ordinal1 @ sk_A)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('17', plain,
% 0.55/0.76      ((~ (v3_ordinal1 @ (sk_B_2 @ sk_A))
% 0.55/0.76        | (r1_ordinal1 @ (sk_B_2 @ sk_A) @ sk_A)
% 0.55/0.76        | (v4_ordinal1 @ sk_A))),
% 0.55/0.76      inference('demod', [status(thm)], ['15', '16'])).
% 0.55/0.76  thf('18', plain, ((~ (v4_ordinal1 @ sk_A) | (v3_ordinal1 @ sk_B_3))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('19', plain, ((~ (v4_ordinal1 @ sk_A)) <= (~ ((v4_ordinal1 @ sk_A)))),
% 0.55/0.76      inference('split', [status(esa)], ['18'])).
% 0.55/0.76  thf('20', plain,
% 0.55/0.76      ((~ (v4_ordinal1 @ sk_A) | ((sk_A) = (k1_ordinal1 @ sk_B_3)))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('21', plain,
% 0.55/0.76      (~ ((v4_ordinal1 @ sk_A)) | (((sk_A) = (k1_ordinal1 @ sk_B_3)))),
% 0.55/0.76      inference('split', [status(esa)], ['20'])).
% 0.55/0.76  thf('22', plain,
% 0.55/0.76      (![X31 : $i]:
% 0.55/0.76         (~ (v3_ordinal1 @ X31)
% 0.55/0.76          | ((sk_A) != (k1_ordinal1 @ X31))
% 0.55/0.76          | (v4_ordinal1 @ sk_A))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('23', plain, (((v4_ordinal1 @ sk_A)) <= (((v4_ordinal1 @ sk_A)))),
% 0.55/0.76      inference('split', [status(esa)], ['22'])).
% 0.55/0.76  thf('24', plain,
% 0.55/0.76      ((((sk_A) = (k1_ordinal1 @ sk_B_3)))
% 0.55/0.76         <= ((((sk_A) = (k1_ordinal1 @ sk_B_3))))),
% 0.55/0.76      inference('split', [status(esa)], ['20'])).
% 0.55/0.76  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.55/0.76  thf('25', plain, (![X15 : $i]: (r2_hidden @ X15 @ (k1_ordinal1 @ X15))),
% 0.55/0.76      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.55/0.76  thf('26', plain,
% 0.55/0.76      (((r2_hidden @ sk_B_3 @ sk_A)) <= ((((sk_A) = (k1_ordinal1 @ sk_B_3))))),
% 0.55/0.76      inference('sup+', [status(thm)], ['24', '25'])).
% 0.55/0.76  thf('27', plain,
% 0.55/0.76      (![X27 : $i, X28 : $i]:
% 0.55/0.76         (~ (v4_ordinal1 @ X27)
% 0.55/0.76          | ~ (r2_hidden @ X28 @ X27)
% 0.55/0.76          | (r2_hidden @ (k1_ordinal1 @ X28) @ X27)
% 0.55/0.76          | ~ (v3_ordinal1 @ X28)
% 0.55/0.76          | ~ (v3_ordinal1 @ X27))),
% 0.55/0.76      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.55/0.76  thf('28', plain,
% 0.55/0.76      (((~ (v3_ordinal1 @ sk_A)
% 0.55/0.76         | ~ (v3_ordinal1 @ sk_B_3)
% 0.55/0.76         | (r2_hidden @ (k1_ordinal1 @ sk_B_3) @ sk_A)
% 0.55/0.76         | ~ (v4_ordinal1 @ sk_A))) <= ((((sk_A) = (k1_ordinal1 @ sk_B_3))))),
% 0.55/0.76      inference('sup-', [status(thm)], ['26', '27'])).
% 0.55/0.76  thf('29', plain, ((v3_ordinal1 @ sk_A)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('30', plain,
% 0.55/0.76      (((r2_hidden @ sk_B_3 @ sk_A)) <= ((((sk_A) = (k1_ordinal1 @ sk_B_3))))),
% 0.55/0.76      inference('sup+', [status(thm)], ['24', '25'])).
% 0.55/0.76  thf(t23_ordinal1, axiom,
% 0.55/0.76    (![A:$i,B:$i]:
% 0.55/0.76     ( ( v3_ordinal1 @ B ) => ( ( r2_hidden @ A @ B ) => ( v3_ordinal1 @ A ) ) ))).
% 0.55/0.76  thf('31', plain,
% 0.55/0.76      (![X19 : $i, X20 : $i]:
% 0.55/0.76         ((v3_ordinal1 @ X19)
% 0.55/0.76          | ~ (v3_ordinal1 @ X20)
% 0.55/0.76          | ~ (r2_hidden @ X19 @ X20))),
% 0.55/0.76      inference('cnf', [status(esa)], [t23_ordinal1])).
% 0.55/0.76  thf('32', plain,
% 0.55/0.76      (((~ (v3_ordinal1 @ sk_A) | (v3_ordinal1 @ sk_B_3)))
% 0.55/0.76         <= ((((sk_A) = (k1_ordinal1 @ sk_B_3))))),
% 0.55/0.76      inference('sup-', [status(thm)], ['30', '31'])).
% 0.55/0.76  thf('33', plain, ((v3_ordinal1 @ sk_A)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('34', plain,
% 0.55/0.76      (((v3_ordinal1 @ sk_B_3)) <= ((((sk_A) = (k1_ordinal1 @ sk_B_3))))),
% 0.55/0.76      inference('demod', [status(thm)], ['32', '33'])).
% 0.55/0.76  thf('35', plain,
% 0.55/0.76      ((((sk_A) = (k1_ordinal1 @ sk_B_3)))
% 0.55/0.76         <= ((((sk_A) = (k1_ordinal1 @ sk_B_3))))),
% 0.55/0.76      inference('split', [status(esa)], ['20'])).
% 0.55/0.76  thf('36', plain,
% 0.55/0.76      ((((r2_hidden @ sk_A @ sk_A) | ~ (v4_ordinal1 @ sk_A)))
% 0.55/0.76         <= ((((sk_A) = (k1_ordinal1 @ sk_B_3))))),
% 0.55/0.76      inference('demod', [status(thm)], ['28', '29', '34', '35'])).
% 0.55/0.76  thf('37', plain,
% 0.55/0.76      (((r2_hidden @ sk_A @ sk_A))
% 0.55/0.76         <= (((v4_ordinal1 @ sk_A)) & (((sk_A) = (k1_ordinal1 @ sk_B_3))))),
% 0.55/0.76      inference('sup-', [status(thm)], ['23', '36'])).
% 0.55/0.76  thf('38', plain,
% 0.55/0.76      (![X29 : $i, X30 : $i]:
% 0.55/0.76         (~ (r2_hidden @ X29 @ X30) | ~ (r1_tarski @ X30 @ X29))),
% 0.55/0.76      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.55/0.76  thf('39', plain,
% 0.55/0.76      ((~ (r1_tarski @ sk_A @ sk_A))
% 0.55/0.76         <= (((v4_ordinal1 @ sk_A)) & (((sk_A) = (k1_ordinal1 @ sk_B_3))))),
% 0.55/0.76      inference('sup-', [status(thm)], ['37', '38'])).
% 0.55/0.76  thf(d10_xboole_0, axiom,
% 0.55/0.76    (![A:$i,B:$i]:
% 0.55/0.76     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.55/0.76  thf('40', plain,
% 0.55/0.76      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.55/0.76      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.55/0.76  thf('41', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.55/0.76      inference('simplify', [status(thm)], ['40'])).
% 0.55/0.76  thf('42', plain,
% 0.55/0.76      (~ (((sk_A) = (k1_ordinal1 @ sk_B_3))) | ~ ((v4_ordinal1 @ sk_A))),
% 0.55/0.76      inference('demod', [status(thm)], ['39', '41'])).
% 0.55/0.76  thf('43', plain, (~ ((v4_ordinal1 @ sk_A))),
% 0.55/0.76      inference('sat_resolution*', [status(thm)], ['21', '42'])).
% 0.55/0.76  thf('44', plain, (~ (v4_ordinal1 @ sk_A)),
% 0.55/0.76      inference('simpl_trail', [status(thm)], ['19', '43'])).
% 0.55/0.76  thf('45', plain,
% 0.55/0.76      (((r1_ordinal1 @ (sk_B_2 @ sk_A) @ sk_A)
% 0.55/0.76        | ~ (v3_ordinal1 @ (sk_B_2 @ sk_A)))),
% 0.55/0.76      inference('clc', [status(thm)], ['17', '44'])).
% 0.55/0.76  thf('46', plain,
% 0.55/0.76      ((~ (v3_ordinal1 @ sk_A)
% 0.55/0.76        | (v4_ordinal1 @ sk_A)
% 0.55/0.76        | (r1_ordinal1 @ (sk_B_2 @ sk_A) @ sk_A))),
% 0.55/0.76      inference('sup-', [status(thm)], ['3', '45'])).
% 0.55/0.76  thf('47', plain, ((v3_ordinal1 @ sk_A)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('48', plain,
% 0.55/0.76      (((v4_ordinal1 @ sk_A) | (r1_ordinal1 @ (sk_B_2 @ sk_A) @ sk_A))),
% 0.55/0.76      inference('demod', [status(thm)], ['46', '47'])).
% 0.55/0.76  thf('49', plain, (~ (v4_ordinal1 @ sk_A)),
% 0.55/0.76      inference('simpl_trail', [status(thm)], ['19', '43'])).
% 0.55/0.76  thf('50', plain, ((r1_ordinal1 @ (sk_B_2 @ sk_A) @ sk_A)),
% 0.55/0.76      inference('clc', [status(thm)], ['48', '49'])).
% 0.55/0.76  thf(t34_ordinal1, axiom,
% 0.55/0.76    (![A:$i]:
% 0.55/0.76     ( ( v3_ordinal1 @ A ) =>
% 0.55/0.76       ( ![B:$i]:
% 0.55/0.76         ( ( v3_ordinal1 @ B ) =>
% 0.55/0.76           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.55/0.76             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.55/0.76  thf('51', plain,
% 0.55/0.76      (![X24 : $i, X25 : $i]:
% 0.55/0.76         (~ (v3_ordinal1 @ X24)
% 0.55/0.76          | ~ (r1_ordinal1 @ X25 @ X24)
% 0.55/0.76          | (r2_hidden @ X25 @ (k1_ordinal1 @ X24))
% 0.55/0.76          | ~ (v3_ordinal1 @ X25))),
% 0.55/0.76      inference('cnf', [status(esa)], [t34_ordinal1])).
% 0.55/0.76  thf('52', plain,
% 0.55/0.76      ((~ (v3_ordinal1 @ (sk_B_2 @ sk_A))
% 0.55/0.76        | (r2_hidden @ (sk_B_2 @ sk_A) @ (k1_ordinal1 @ sk_A))
% 0.55/0.76        | ~ (v3_ordinal1 @ sk_A))),
% 0.55/0.76      inference('sup-', [status(thm)], ['50', '51'])).
% 0.55/0.76  thf('53', plain, ((v3_ordinal1 @ sk_A)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('54', plain,
% 0.55/0.76      ((~ (v3_ordinal1 @ (sk_B_2 @ sk_A))
% 0.55/0.76        | (r2_hidden @ (sk_B_2 @ sk_A) @ (k1_ordinal1 @ sk_A)))),
% 0.55/0.76      inference('demod', [status(thm)], ['52', '53'])).
% 0.55/0.76  thf('55', plain,
% 0.55/0.76      ((~ (v3_ordinal1 @ sk_A)
% 0.55/0.76        | (v4_ordinal1 @ sk_A)
% 0.55/0.76        | (r2_hidden @ (sk_B_2 @ sk_A) @ (k1_ordinal1 @ sk_A)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['2', '54'])).
% 0.55/0.76  thf('56', plain, ((v3_ordinal1 @ sk_A)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('57', plain,
% 0.55/0.76      (((v4_ordinal1 @ sk_A)
% 0.55/0.76        | (r2_hidden @ (sk_B_2 @ sk_A) @ (k1_ordinal1 @ sk_A)))),
% 0.55/0.76      inference('demod', [status(thm)], ['55', '56'])).
% 0.55/0.76  thf('58', plain, (~ (v4_ordinal1 @ sk_A)),
% 0.55/0.76      inference('simpl_trail', [status(thm)], ['19', '43'])).
% 0.55/0.76  thf('59', plain, ((r2_hidden @ (sk_B_2 @ sk_A) @ (k1_ordinal1 @ sk_A))),
% 0.55/0.76      inference('clc', [status(thm)], ['57', '58'])).
% 0.55/0.76  thf('60', plain,
% 0.55/0.76      (![X19 : $i, X20 : $i]:
% 0.55/0.76         ((v3_ordinal1 @ X19)
% 0.55/0.76          | ~ (v3_ordinal1 @ X20)
% 0.55/0.76          | ~ (r2_hidden @ X19 @ X20))),
% 0.55/0.76      inference('cnf', [status(esa)], [t23_ordinal1])).
% 0.55/0.76  thf('61', plain,
% 0.55/0.76      ((~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))
% 0.55/0.76        | (v3_ordinal1 @ (sk_B_2 @ sk_A)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['59', '60'])).
% 0.55/0.76  thf('62', plain,
% 0.55/0.76      ((~ (v3_ordinal1 @ sk_A) | (v3_ordinal1 @ (sk_B_2 @ sk_A)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['1', '61'])).
% 0.55/0.76  thf('63', plain, ((v3_ordinal1 @ sk_A)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('64', plain, ((v3_ordinal1 @ (sk_B_2 @ sk_A))),
% 0.55/0.76      inference('demod', [status(thm)], ['62', '63'])).
% 0.55/0.76  thf('65', plain,
% 0.55/0.76      (![X27 : $i]:
% 0.55/0.76         ((r2_hidden @ (sk_B_2 @ X27) @ X27)
% 0.55/0.76          | (v4_ordinal1 @ X27)
% 0.55/0.76          | ~ (v3_ordinal1 @ X27))),
% 0.55/0.76      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.55/0.76  thf(s1_xboole_0__e3_53__ordinal1, axiom,
% 0.55/0.76    (![A:$i]:
% 0.55/0.76     ( ?[B:$i]:
% 0.55/0.76       ( ![C:$i]:
% 0.55/0.76         ( ( r2_hidden @ C @ B ) <=>
% 0.55/0.76           ( ( r2_hidden @ C @ A ) & ( v3_ordinal1 @ C ) ) ) ) ))).
% 0.55/0.76  thf('66', plain,
% 0.55/0.76      (![X13 : $i, X14 : $i]:
% 0.55/0.76         ((r2_hidden @ X14 @ (sk_B @ X13))
% 0.55/0.76          | ~ (v3_ordinal1 @ X14)
% 0.55/0.76          | ~ (r2_hidden @ X14 @ X13))),
% 0.55/0.76      inference('cnf', [status(esa)], [s1_xboole_0__e3_53__ordinal1])).
% 0.55/0.76  thf('67', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         (~ (v3_ordinal1 @ X0)
% 0.55/0.76          | (v4_ordinal1 @ X0)
% 0.55/0.76          | ~ (v3_ordinal1 @ (sk_B_2 @ X0))
% 0.55/0.76          | (r2_hidden @ (sk_B_2 @ X0) @ (sk_B @ X0)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['65', '66'])).
% 0.55/0.76  thf('68', plain,
% 0.55/0.76      (((r2_hidden @ (sk_B_2 @ sk_A) @ (sk_B @ sk_A))
% 0.55/0.76        | (v4_ordinal1 @ sk_A)
% 0.55/0.76        | ~ (v3_ordinal1 @ sk_A))),
% 0.55/0.76      inference('sup-', [status(thm)], ['64', '67'])).
% 0.55/0.76  thf('69', plain, ((v3_ordinal1 @ sk_A)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('70', plain,
% 0.55/0.76      (((r2_hidden @ (sk_B_2 @ sk_A) @ (sk_B @ sk_A)) | (v4_ordinal1 @ sk_A))),
% 0.55/0.76      inference('demod', [status(thm)], ['68', '69'])).
% 0.55/0.76  thf('71', plain, (~ (v4_ordinal1 @ sk_A)),
% 0.55/0.76      inference('simpl_trail', [status(thm)], ['19', '43'])).
% 0.55/0.76  thf('72', plain, ((r2_hidden @ (sk_B_2 @ sk_A) @ (sk_B @ sk_A))),
% 0.55/0.76      inference('clc', [status(thm)], ['70', '71'])).
% 0.55/0.76  thf('73', plain,
% 0.55/0.76      (![X12 : $i, X13 : $i]:
% 0.55/0.76         ((r2_hidden @ X12 @ X13) | ~ (r2_hidden @ X12 @ (sk_B @ X13)))),
% 0.55/0.76      inference('cnf', [status(esa)], [s1_xboole_0__e3_53__ordinal1])).
% 0.55/0.76  thf('74', plain, ((r2_hidden @ (sk_B_2 @ sk_A) @ sk_A)),
% 0.55/0.76      inference('sup-', [status(thm)], ['72', '73'])).
% 0.55/0.76  thf(t33_ordinal1, axiom,
% 0.55/0.76    (![A:$i]:
% 0.55/0.76     ( ( v3_ordinal1 @ A ) =>
% 0.55/0.76       ( ![B:$i]:
% 0.55/0.76         ( ( v3_ordinal1 @ B ) =>
% 0.55/0.76           ( ( r2_hidden @ A @ B ) <=>
% 0.55/0.76             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 0.55/0.76  thf('75', plain,
% 0.55/0.76      (![X22 : $i, X23 : $i]:
% 0.55/0.76         (~ (v3_ordinal1 @ X22)
% 0.55/0.76          | ~ (r2_hidden @ X23 @ X22)
% 0.55/0.76          | (r1_ordinal1 @ (k1_ordinal1 @ X23) @ X22)
% 0.55/0.76          | ~ (v3_ordinal1 @ X23))),
% 0.55/0.76      inference('cnf', [status(esa)], [t33_ordinal1])).
% 0.55/0.76  thf('76', plain,
% 0.55/0.76      ((~ (v3_ordinal1 @ (sk_B_2 @ sk_A))
% 0.55/0.76        | (r1_ordinal1 @ (k1_ordinal1 @ (sk_B_2 @ sk_A)) @ sk_A)
% 0.55/0.76        | ~ (v3_ordinal1 @ sk_A))),
% 0.55/0.76      inference('sup-', [status(thm)], ['74', '75'])).
% 0.55/0.76  thf('77', plain, ((v3_ordinal1 @ (sk_B_2 @ sk_A))),
% 0.55/0.76      inference('demod', [status(thm)], ['62', '63'])).
% 0.55/0.76  thf('78', plain, ((v3_ordinal1 @ sk_A)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('79', plain, ((r1_ordinal1 @ (k1_ordinal1 @ (sk_B_2 @ sk_A)) @ sk_A)),
% 0.55/0.76      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.55/0.76  thf('80', plain,
% 0.55/0.76      (![X24 : $i, X25 : $i]:
% 0.55/0.76         (~ (v3_ordinal1 @ X24)
% 0.55/0.76          | ~ (r1_ordinal1 @ X25 @ X24)
% 0.55/0.76          | (r2_hidden @ X25 @ (k1_ordinal1 @ X24))
% 0.55/0.76          | ~ (v3_ordinal1 @ X25))),
% 0.55/0.76      inference('cnf', [status(esa)], [t34_ordinal1])).
% 0.55/0.76  thf('81', plain,
% 0.55/0.76      ((~ (v3_ordinal1 @ (k1_ordinal1 @ (sk_B_2 @ sk_A)))
% 0.55/0.76        | (r2_hidden @ (k1_ordinal1 @ (sk_B_2 @ sk_A)) @ (k1_ordinal1 @ sk_A))
% 0.55/0.76        | ~ (v3_ordinal1 @ sk_A))),
% 0.55/0.76      inference('sup-', [status(thm)], ['79', '80'])).
% 0.55/0.76  thf('82', plain, ((v3_ordinal1 @ sk_A)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('83', plain,
% 0.55/0.76      ((~ (v3_ordinal1 @ (k1_ordinal1 @ (sk_B_2 @ sk_A)))
% 0.55/0.76        | (r2_hidden @ (k1_ordinal1 @ (sk_B_2 @ sk_A)) @ (k1_ordinal1 @ sk_A)))),
% 0.55/0.76      inference('demod', [status(thm)], ['81', '82'])).
% 0.55/0.76  thf('84', plain,
% 0.55/0.76      ((~ (v3_ordinal1 @ (sk_B_2 @ sk_A))
% 0.55/0.76        | (r2_hidden @ (k1_ordinal1 @ (sk_B_2 @ sk_A)) @ (k1_ordinal1 @ sk_A)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['0', '83'])).
% 0.55/0.76  thf('85', plain, ((v3_ordinal1 @ (sk_B_2 @ sk_A))),
% 0.55/0.76      inference('demod', [status(thm)], ['62', '63'])).
% 0.55/0.76  thf('86', plain,
% 0.55/0.76      ((r2_hidden @ (k1_ordinal1 @ (sk_B_2 @ sk_A)) @ (k1_ordinal1 @ sk_A))),
% 0.55/0.76      inference('demod', [status(thm)], ['84', '85'])).
% 0.55/0.76  thf(t13_ordinal1, axiom,
% 0.55/0.76    (![A:$i,B:$i]:
% 0.55/0.76     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.55/0.76       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.55/0.76  thf('87', plain,
% 0.55/0.76      (![X16 : $i, X17 : $i]:
% 0.55/0.76         (((X17) = (X16))
% 0.55/0.76          | (r2_hidden @ X17 @ X16)
% 0.55/0.76          | ~ (r2_hidden @ X17 @ (k1_ordinal1 @ X16)))),
% 0.55/0.76      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.55/0.76  thf('88', plain,
% 0.55/0.76      (((r2_hidden @ (k1_ordinal1 @ (sk_B_2 @ sk_A)) @ sk_A)
% 0.55/0.76        | ((k1_ordinal1 @ (sk_B_2 @ sk_A)) = (sk_A)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['86', '87'])).
% 0.55/0.76  thf('89', plain,
% 0.55/0.76      (![X27 : $i]:
% 0.55/0.76         (~ (r2_hidden @ (k1_ordinal1 @ (sk_B_2 @ X27)) @ X27)
% 0.55/0.76          | (v4_ordinal1 @ X27)
% 0.55/0.76          | ~ (v3_ordinal1 @ X27))),
% 0.55/0.76      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.55/0.76  thf('90', plain,
% 0.55/0.76      ((((k1_ordinal1 @ (sk_B_2 @ sk_A)) = (sk_A))
% 0.55/0.76        | ~ (v3_ordinal1 @ sk_A)
% 0.55/0.76        | (v4_ordinal1 @ sk_A))),
% 0.55/0.76      inference('sup-', [status(thm)], ['88', '89'])).
% 0.55/0.76  thf('91', plain, ((v3_ordinal1 @ sk_A)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('92', plain,
% 0.55/0.76      ((((k1_ordinal1 @ (sk_B_2 @ sk_A)) = (sk_A)) | (v4_ordinal1 @ sk_A))),
% 0.55/0.76      inference('demod', [status(thm)], ['90', '91'])).
% 0.55/0.76  thf('93', plain, (~ (v4_ordinal1 @ sk_A)),
% 0.55/0.76      inference('simpl_trail', [status(thm)], ['19', '43'])).
% 0.55/0.76  thf('94', plain, (((k1_ordinal1 @ (sk_B_2 @ sk_A)) = (sk_A))),
% 0.55/0.76      inference('clc', [status(thm)], ['92', '93'])).
% 0.55/0.76  thf('95', plain,
% 0.55/0.76      (![X31 : $i]:
% 0.55/0.76         (~ (v3_ordinal1 @ X31)
% 0.55/0.76          | ((sk_A) != (k1_ordinal1 @ X31))
% 0.55/0.76          | (v3_ordinal1 @ sk_B_3))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('96', plain,
% 0.55/0.76      ((![X31 : $i]: (((sk_A) != (k1_ordinal1 @ X31)) | ~ (v3_ordinal1 @ X31)))
% 0.55/0.76         <= ((![X31 : $i]:
% 0.55/0.76                (((sk_A) != (k1_ordinal1 @ X31)) | ~ (v3_ordinal1 @ X31))))),
% 0.55/0.76      inference('split', [status(esa)], ['95'])).
% 0.55/0.76  thf('97', plain,
% 0.55/0.76      ((![X31 : $i]: (((sk_A) != (k1_ordinal1 @ X31)) | ~ (v3_ordinal1 @ X31))) | 
% 0.55/0.76       ((v4_ordinal1 @ sk_A))),
% 0.55/0.76      inference('split', [status(esa)], ['22'])).
% 0.55/0.76  thf('98', plain,
% 0.55/0.76      ((![X31 : $i]: (((sk_A) != (k1_ordinal1 @ X31)) | ~ (v3_ordinal1 @ X31)))),
% 0.55/0.76      inference('sat_resolution*', [status(thm)], ['21', '42', '97'])).
% 0.55/0.76  thf('99', plain,
% 0.55/0.76      (![X31 : $i]: (((sk_A) != (k1_ordinal1 @ X31)) | ~ (v3_ordinal1 @ X31))),
% 0.55/0.76      inference('simpl_trail', [status(thm)], ['96', '98'])).
% 0.55/0.76  thf('100', plain, ((((sk_A) != (sk_A)) | ~ (v3_ordinal1 @ (sk_B_2 @ sk_A)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['94', '99'])).
% 0.55/0.76  thf('101', plain, ((v3_ordinal1 @ (sk_B_2 @ sk_A))),
% 0.55/0.76      inference('demod', [status(thm)], ['62', '63'])).
% 0.55/0.76  thf('102', plain, (((sk_A) != (sk_A))),
% 0.55/0.76      inference('demod', [status(thm)], ['100', '101'])).
% 0.55/0.76  thf('103', plain, ($false), inference('simplify', [status(thm)], ['102'])).
% 0.55/0.76  
% 0.55/0.76  % SZS output end Refutation
% 0.55/0.76  
% 0.55/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
