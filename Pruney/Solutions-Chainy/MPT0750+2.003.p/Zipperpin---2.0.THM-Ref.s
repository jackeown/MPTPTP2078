%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uunOXnkhet

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:09 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 728 expanded)
%              Number of leaves         :   29 ( 201 expanded)
%              Depth                    :   27
%              Number of atoms          : 1442 (7088 expanded)
%              Number of equality atoms :   32 ( 106 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v4_ordinal1_type,type,(
    v4_ordinal1: $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(t41_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v4_ordinal1 @ A )
      <=> ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r2_hidden @ B @ A )
             => ( r2_hidden @ ( k1_ordinal1 @ B ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ( ( v4_ordinal1 @ A )
        <=> ! [B: $i] :
              ( ( v3_ordinal1 @ B )
             => ( ( r2_hidden @ B @ A )
               => ( r2_hidden @ ( k1_ordinal1 @ B ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_ordinal1])).

thf('0',plain,
    ( ( r2_hidden @ sk_B_3 @ sk_A )
    | ~ ( v4_ordinal1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v4_ordinal1 @ sk_A )
   <= ~ ( v4_ordinal1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_B_3 @ sk_A )
    | ~ ( v4_ordinal1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ~ ( r2_hidden @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A )
    | ~ ( v4_ordinal1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( v4_ordinal1 @ sk_A )
    | ~ ( r2_hidden @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( v3_ordinal1 @ sk_B_3 )
    | ~ ( v4_ordinal1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v3_ordinal1 @ sk_B_3 )
    | ~ ( v4_ordinal1 @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,(
    ! [X41: $i] :
      ( ~ ( v3_ordinal1 @ X41 )
      | ( r2_hidden @ ( k1_ordinal1 @ X41 ) @ sk_A )
      | ~ ( r2_hidden @ X41 @ sk_A )
      | ( v4_ordinal1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v4_ordinal1 @ sk_A )
   <= ( v4_ordinal1 @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_B_3 @ sk_A )
   <= ( r2_hidden @ sk_B_3 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(d6_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v4_ordinal1 @ A )
    <=> ( A
        = ( k3_tarski @ A ) ) ) )).

thf('10',plain,(
    ! [X21: $i] :
      ( ( X21
        = ( k3_tarski @ X21 ) )
      | ~ ( v4_ordinal1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d6_ordinal1])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('11',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 ) @ X8 )
      | ( X10
       != ( k3_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('12',plain,(
    ! [X8: $i,X11: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X11 @ X8 ) @ X8 )
      | ~ ( r2_hidden @ X11 @ ( k3_tarski @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v4_ordinal1 @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_B_3 @ sk_A ) @ sk_A )
      | ~ ( v4_ordinal1 @ sk_A ) )
   <= ( r2_hidden @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_B_3 @ sk_A ) @ sk_A )
   <= ( ( v4_ordinal1 @ sk_A )
      & ( r2_hidden @ sk_B_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,
    ( ( v3_ordinal1 @ sk_B_3 )
   <= ( v3_ordinal1 @ sk_B_3 ) ),
    inference(split,[status(esa)],['5'])).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('17',plain,(
    ! [X33: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X33 ) )
      | ~ ( v3_ordinal1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('18',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v3_ordinal1 @ X31 )
      | ( r2_hidden @ X32 @ X31 )
      | ( X32 = X31 )
      | ( r2_hidden @ X31 @ X32 )
      | ~ ( v3_ordinal1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('19',plain,
    ( ~ ( r2_hidden @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A )
   <= ~ ( r2_hidden @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('20',plain,
    ( ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_B_3 ) )
      | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_3 ) )
      | ( ( k1_ordinal1 @ sk_B_3 )
        = sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_B_3 ) )
      | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_3 ) )
      | ( ( k1_ordinal1 @ sk_B_3 )
        = sk_A ) )
   <= ~ ( r2_hidden @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B_3 )
      | ( ( k1_ordinal1 @ sk_B_3 )
        = sk_A )
      | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_3 ) ) )
   <= ~ ( r2_hidden @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_3 ) )
      | ( ( k1_ordinal1 @ sk_B_3 )
        = sk_A ) )
   <= ( ~ ( r2_hidden @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A )
      & ( v3_ordinal1 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['16','23'])).

thf(t34_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
          <=> ( r1_ordinal1 @ A @ B ) ) ) ) )).

thf('25',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( v3_ordinal1 @ X34 )
      | ~ ( r2_hidden @ X35 @ ( k1_ordinal1 @ X34 ) )
      | ( r1_ordinal1 @ X35 @ X34 )
      | ~ ( v3_ordinal1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t34_ordinal1])).

thf('26',plain,
    ( ( ( ( k1_ordinal1 @ sk_B_3 )
        = sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ sk_B_3 )
      | ~ ( v3_ordinal1 @ sk_B_3 ) )
   <= ( ~ ( r2_hidden @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A )
      & ( v3_ordinal1 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v3_ordinal1 @ sk_B_3 )
   <= ( v3_ordinal1 @ sk_B_3 ) ),
    inference(split,[status(esa)],['5'])).

thf('29',plain,
    ( ( ( ( k1_ordinal1 @ sk_B_3 )
        = sk_A )
      | ( r1_ordinal1 @ sk_A @ sk_B_3 ) )
   <= ( ~ ( r2_hidden @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A )
      & ( v3_ordinal1 @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('30',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v3_ordinal1 @ X23 )
      | ~ ( v3_ordinal1 @ X24 )
      | ( r1_tarski @ X23 @ X24 )
      | ~ ( r1_ordinal1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('31',plain,
    ( ( ( ( k1_ordinal1 @ sk_B_3 )
        = sk_A )
      | ( r1_tarski @ sk_A @ sk_B_3 )
      | ~ ( v3_ordinal1 @ sk_B_3 )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A )
      & ( v3_ordinal1 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( v3_ordinal1 @ sk_B_3 )
   <= ( v3_ordinal1 @ sk_B_3 ) ),
    inference(split,[status(esa)],['5'])).

thf('33',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( ( ( k1_ordinal1 @ sk_B_3 )
        = sk_A )
      | ( r1_tarski @ sk_A @ sk_B_3 ) )
   <= ( ~ ( r2_hidden @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A )
      & ( v3_ordinal1 @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ( r2_hidden @ sk_B_3 @ sk_A )
   <= ( r2_hidden @ sk_B_3 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('36',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X39 @ X40 )
      | ~ ( r1_tarski @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('37',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B_3 )
   <= ( r2_hidden @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k1_ordinal1 @ sk_B_3 )
      = sk_A )
   <= ( ~ ( r2_hidden @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A )
      & ( r2_hidden @ sk_B_3 @ sk_A )
      & ( v3_ordinal1 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( v3_ordinal1 @ X34 )
      | ~ ( r2_hidden @ X35 @ ( k1_ordinal1 @ X34 ) )
      | ( r1_ordinal1 @ X35 @ X34 )
      | ~ ( v3_ordinal1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t34_ordinal1])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( v3_ordinal1 @ X0 )
        | ( r1_ordinal1 @ X0 @ sk_B_3 )
        | ~ ( v3_ordinal1 @ sk_B_3 ) )
   <= ( ~ ( r2_hidden @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A )
      & ( r2_hidden @ sk_B_3 @ sk_A )
      & ( v3_ordinal1 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r2_hidden @ sk_B_3 @ sk_A )
   <= ( r2_hidden @ sk_B_3 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t23_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v3_ordinal1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( v3_ordinal1 @ A ) ) ) )).

thf('42',plain,(
    ! [X29: $i,X30: $i] :
      ( ( v3_ordinal1 @ X29 )
      | ~ ( v3_ordinal1 @ X30 )
      | ~ ( r2_hidden @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('43',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( v3_ordinal1 @ sk_B_3 ) )
   <= ( r2_hidden @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v3_ordinal1 @ sk_B_3 )
   <= ( r2_hidden @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( v3_ordinal1 @ X0 )
        | ( r1_ordinal1 @ X0 @ sk_B_3 ) )
   <= ( ~ ( r2_hidden @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A )
      & ( r2_hidden @ sk_B_3 @ sk_A )
      & ( v3_ordinal1 @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['40','45'])).

thf('47',plain,
    ( ( ( r1_ordinal1 @ ( sk_D_1 @ sk_B_3 @ sk_A ) @ sk_B_3 )
      | ~ ( v3_ordinal1 @ ( sk_D_1 @ sk_B_3 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A )
      & ( v4_ordinal1 @ sk_A )
      & ( r2_hidden @ sk_B_3 @ sk_A )
      & ( v3_ordinal1 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['15','46'])).

thf('48',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_B_3 @ sk_A ) @ sk_A )
   <= ( ( v4_ordinal1 @ sk_A )
      & ( r2_hidden @ sk_B_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('49',plain,(
    ! [X29: $i,X30: $i] :
      ( ( v3_ordinal1 @ X29 )
      | ~ ( v3_ordinal1 @ X30 )
      | ~ ( r2_hidden @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('50',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( v3_ordinal1 @ ( sk_D_1 @ sk_B_3 @ sk_A ) ) )
   <= ( ( v4_ordinal1 @ sk_A )
      & ( r2_hidden @ sk_B_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v3_ordinal1 @ ( sk_D_1 @ sk_B_3 @ sk_A ) )
   <= ( ( v4_ordinal1 @ sk_A )
      & ( r2_hidden @ sk_B_3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( r1_ordinal1 @ ( sk_D_1 @ sk_B_3 @ sk_A ) @ sk_B_3 )
   <= ( ~ ( r2_hidden @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A )
      & ( v4_ordinal1 @ sk_A )
      & ( r2_hidden @ sk_B_3 @ sk_A )
      & ( v3_ordinal1 @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v3_ordinal1 @ X23 )
      | ~ ( v3_ordinal1 @ X24 )
      | ( r1_tarski @ X23 @ X24 )
      | ~ ( r1_ordinal1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('55',plain,
    ( ( ( r1_tarski @ ( sk_D_1 @ sk_B_3 @ sk_A ) @ sk_B_3 )
      | ~ ( v3_ordinal1 @ sk_B_3 )
      | ~ ( v3_ordinal1 @ ( sk_D_1 @ sk_B_3 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A )
      & ( v4_ordinal1 @ sk_A )
      & ( r2_hidden @ sk_B_3 @ sk_A )
      & ( v3_ordinal1 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( v3_ordinal1 @ sk_B_3 )
   <= ( r2_hidden @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('57',plain,
    ( ( v3_ordinal1 @ ( sk_D_1 @ sk_B_3 @ sk_A ) )
   <= ( ( v4_ordinal1 @ sk_A )
      & ( r2_hidden @ sk_B_3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('58',plain,
    ( ( r1_tarski @ ( sk_D_1 @ sk_B_3 @ sk_A ) @ sk_B_3 )
   <= ( ~ ( r2_hidden @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A )
      & ( v4_ordinal1 @ sk_A )
      & ( r2_hidden @ sk_B_3 @ sk_A )
      & ( v3_ordinal1 @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ( v4_ordinal1 @ sk_A )
   <= ( v4_ordinal1 @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('60',plain,
    ( ( r2_hidden @ sk_B_3 @ sk_A )
   <= ( r2_hidden @ sk_B_3 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('61',plain,(
    ! [X21: $i] :
      ( ( X21
        = ( k3_tarski @ X21 ) )
      | ~ ( v4_ordinal1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d6_ordinal1])).

thf('62',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( r2_hidden @ X11 @ ( sk_D_1 @ X11 @ X8 ) )
      | ( X10
       != ( k3_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('63',plain,(
    ! [X8: $i,X11: $i] :
      ( ( r2_hidden @ X11 @ ( sk_D_1 @ X11 @ X8 ) )
      | ~ ( r2_hidden @ X11 @ ( k3_tarski @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v4_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ ( sk_D_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','63'])).

thf('65',plain,
    ( ( ( r2_hidden @ sk_B_3 @ ( sk_D_1 @ sk_B_3 @ sk_A ) )
      | ~ ( v4_ordinal1 @ sk_A ) )
   <= ( r2_hidden @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','64'])).

thf('66',plain,
    ( ( r2_hidden @ sk_B_3 @ ( sk_D_1 @ sk_B_3 @ sk_A ) )
   <= ( ( v4_ordinal1 @ sk_A )
      & ( r2_hidden @ sk_B_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','65'])).

thf('67',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X39 @ X40 )
      | ~ ( r1_tarski @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('68',plain,
    ( ~ ( r1_tarski @ ( sk_D_1 @ sk_B_3 @ sk_A ) @ sk_B_3 )
   <= ( ( v4_ordinal1 @ sk_A )
      & ( r2_hidden @ sk_B_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( v4_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ sk_B_3 )
    | ~ ( r2_hidden @ sk_B_3 @ sk_A )
    | ( r2_hidden @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['58','68'])).

thf('70',plain,(
    ~ ( v4_ordinal1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','4','6','69'])).

thf('71',plain,(
    ~ ( v4_ordinal1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','70'])).

thf(t35_ordinal1,axiom,(
    ! [A: $i] :
      ( ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( v3_ordinal1 @ B ) )
     => ( v3_ordinal1 @ ( k3_tarski @ A ) ) ) )).

thf('72',plain,(
    ! [X36: $i] :
      ( ( v3_ordinal1 @ ( k3_tarski @ X36 ) )
      | ( r2_hidden @ ( sk_B_1 @ X36 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[t35_ordinal1])).

thf('73',plain,(
    ! [X29: $i,X30: $i] :
      ( ( v3_ordinal1 @ X29 )
      | ~ ( v3_ordinal1 @ X30 )
      | ~ ( r2_hidden @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v3_ordinal1 @ ( k3_tarski @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v3_ordinal1 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X36: $i] :
      ( ( v3_ordinal1 @ ( k3_tarski @ X36 ) )
      | ~ ( v3_ordinal1 @ ( sk_B_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t35_ordinal1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v3_ordinal1 @ ( k3_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v3_ordinal1 @ ( k3_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('78',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('79',plain,(
    ! [X29: $i,X30: $i] :
      ( ( v3_ordinal1 @ X29 )
      | ~ ( v3_ordinal1 @ X30 )
      | ~ ( r2_hidden @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v3_ordinal1 @ ( sk_C @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('82',plain,
    ( ! [X41: $i] :
        ( ~ ( v3_ordinal1 @ X41 )
        | ( r2_hidden @ ( k1_ordinal1 @ X41 ) @ sk_A )
        | ~ ( r2_hidden @ X41 @ sk_A ) )
   <= ! [X41: $i] :
        ( ~ ( v3_ordinal1 @ X41 )
        | ( r2_hidden @ ( k1_ordinal1 @ X41 ) @ sk_A )
        | ~ ( r2_hidden @ X41 @ sk_A ) ) ),
    inference(split,[status(esa)],['7'])).

thf('83',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_A @ X0 )
        | ( r2_hidden @ ( k1_ordinal1 @ ( sk_C @ X0 @ sk_A ) ) @ sk_A )
        | ~ ( v3_ordinal1 @ ( sk_C @ X0 @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ~ ( v3_ordinal1 @ X41 )
        | ( r2_hidden @ ( k1_ordinal1 @ X41 ) @ sk_A )
        | ~ ( r2_hidden @ X41 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ! [X0: $i] :
        ( ~ ( v3_ordinal1 @ sk_A )
        | ( r1_tarski @ sk_A @ X0 )
        | ( r2_hidden @ ( k1_ordinal1 @ ( sk_C @ X0 @ sk_A ) ) @ sk_A )
        | ( r1_tarski @ sk_A @ X0 ) )
   <= ! [X41: $i] :
        ( ~ ( v3_ordinal1 @ X41 )
        | ( r2_hidden @ ( k1_ordinal1 @ X41 ) @ sk_A )
        | ~ ( r2_hidden @ X41 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_A @ X0 )
        | ( r2_hidden @ ( k1_ordinal1 @ ( sk_C @ X0 @ sk_A ) ) @ sk_A )
        | ( r1_tarski @ sk_A @ X0 ) )
   <= ! [X41: $i] :
        ( ~ ( v3_ordinal1 @ X41 )
        | ( r2_hidden @ ( k1_ordinal1 @ X41 ) @ sk_A )
        | ~ ( r2_hidden @ X41 @ sk_A ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( k1_ordinal1 @ ( sk_C @ X0 @ sk_A ) ) @ sk_A )
        | ( r1_tarski @ sk_A @ X0 ) )
   <= ! [X41: $i] :
        ( ~ ( v3_ordinal1 @ X41 )
        | ( r2_hidden @ ( k1_ordinal1 @ X41 ) @ sk_A )
        | ~ ( r2_hidden @ X41 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('88',plain,(
    ! [X25: $i] :
      ( r2_hidden @ X25 @ ( k1_ordinal1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('89',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ X9 @ X7 )
      | ( r2_hidden @ X9 @ X10 )
      | ( X10
       != ( k3_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('90',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X9 @ ( k3_tarski @ X8 ) )
      | ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k1_ordinal1 @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ ( k3_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['88','90'])).

thf('92',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k3_tarski @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ~ ( v3_ordinal1 @ X41 )
        | ( r2_hidden @ ( k1_ordinal1 @ X41 ) @ sk_A )
        | ~ ( r2_hidden @ X41 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['87','91'])).

thf('93',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('94',plain,
    ( ( ( r1_tarski @ sk_A @ ( k3_tarski @ sk_A ) )
      | ( r1_tarski @ sk_A @ ( k3_tarski @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ~ ( v3_ordinal1 @ X41 )
        | ( r2_hidden @ ( k1_ordinal1 @ X41 ) @ sk_A )
        | ~ ( r2_hidden @ X41 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( r1_tarski @ sk_A @ ( k3_tarski @ sk_A ) )
   <= ! [X41: $i] :
        ( ~ ( v3_ordinal1 @ X41 )
        | ( r2_hidden @ ( k1_ordinal1 @ X41 ) @ sk_A )
        | ~ ( r2_hidden @ X41 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v3_ordinal1 @ X23 )
      | ~ ( v3_ordinal1 @ X24 )
      | ( r1_ordinal1 @ X23 @ X24 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('97',plain,
    ( ( ( r1_ordinal1 @ sk_A @ ( k3_tarski @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( k3_tarski @ sk_A ) )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ! [X41: $i] :
        ( ~ ( v3_ordinal1 @ X41 )
        | ( r2_hidden @ ( k1_ordinal1 @ X41 ) @ sk_A )
        | ~ ( r2_hidden @ X41 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( ( r1_ordinal1 @ sk_A @ ( k3_tarski @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( k3_tarski @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ~ ( v3_ordinal1 @ X41 )
        | ( r2_hidden @ ( k1_ordinal1 @ X41 ) @ sk_A )
        | ~ ( r2_hidden @ X41 @ sk_A ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ ( k3_tarski @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ~ ( v3_ordinal1 @ X41 )
        | ( r2_hidden @ ( k1_ordinal1 @ X41 ) @ sk_A )
        | ~ ( r2_hidden @ X41 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','99'])).

thf('101',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( r1_ordinal1 @ sk_A @ ( k3_tarski @ sk_A ) )
   <= ! [X41: $i] :
        ( ~ ( v3_ordinal1 @ X41 )
        | ( r2_hidden @ ( k1_ordinal1 @ X41 ) @ sk_A )
        | ~ ( r2_hidden @ X41 @ sk_A ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( v3_ordinal1 @ X34 )
      | ~ ( r1_ordinal1 @ X35 @ X34 )
      | ( r2_hidden @ X35 @ ( k1_ordinal1 @ X34 ) )
      | ~ ( v3_ordinal1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t34_ordinal1])).

thf('104',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ ( k3_tarski @ sk_A ) ) )
      | ~ ( v3_ordinal1 @ ( k3_tarski @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ~ ( v3_ordinal1 @ X41 )
        | ( r2_hidden @ ( k1_ordinal1 @ X41 ) @ sk_A )
        | ~ ( r2_hidden @ X41 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ ( k3_tarski @ sk_A ) ) )
      | ~ ( v3_ordinal1 @ ( k3_tarski @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ~ ( v3_ordinal1 @ X41 )
        | ( r2_hidden @ ( k1_ordinal1 @ X41 ) @ sk_A )
        | ~ ( r2_hidden @ X41 @ sk_A ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ ( k3_tarski @ sk_A ) ) ) )
   <= ! [X41: $i] :
        ( ~ ( v3_ordinal1 @ X41 )
        | ( r2_hidden @ ( k1_ordinal1 @ X41 ) @ sk_A )
        | ~ ( r2_hidden @ X41 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','106'])).

thf('108',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ ( k3_tarski @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ~ ( v3_ordinal1 @ X41 )
        | ( r2_hidden @ ( k1_ordinal1 @ X41 ) @ sk_A )
        | ~ ( r2_hidden @ X41 @ sk_A ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('110',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X27 = X26 )
      | ( r2_hidden @ X27 @ X26 )
      | ~ ( r2_hidden @ X27 @ ( k1_ordinal1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('111',plain,
    ( ( ( r2_hidden @ sk_A @ ( k3_tarski @ sk_A ) )
      | ( sk_A
        = ( k3_tarski @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ~ ( v3_ordinal1 @ X41 )
        | ( r2_hidden @ ( k1_ordinal1 @ X41 ) @ sk_A )
        | ~ ( r2_hidden @ X41 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X8: $i,X11: $i] :
      ( ( r2_hidden @ X11 @ ( sk_D_1 @ X11 @ X8 ) )
      | ~ ( r2_hidden @ X11 @ ( k3_tarski @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('113',plain,
    ( ( ( sk_A
        = ( k3_tarski @ sk_A ) )
      | ( r2_hidden @ sk_A @ ( sk_D_1 @ sk_A @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ~ ( v3_ordinal1 @ X41 )
        | ( r2_hidden @ ( k1_ordinal1 @ X41 ) @ sk_A )
        | ~ ( r2_hidden @ X41 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X39 @ X40 )
      | ~ ( r1_tarski @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('115',plain,
    ( ( ( sk_A
        = ( k3_tarski @ sk_A ) )
      | ~ ( r1_tarski @ ( sk_D_1 @ sk_A @ sk_A ) @ sk_A ) )
   <= ! [X41: $i] :
        ( ~ ( v3_ordinal1 @ X41 )
        | ( r2_hidden @ ( k1_ordinal1 @ X41 ) @ sk_A )
        | ~ ( r2_hidden @ X41 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ! [X41: $i] :
        ( ~ ( v3_ordinal1 @ X41 )
        | ( r2_hidden @ ( k1_ordinal1 @ X41 ) @ sk_A )
        | ~ ( r2_hidden @ X41 @ sk_A ) )
    | ( v4_ordinal1 @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('117',plain,(
    ! [X41: $i] :
      ( ~ ( v3_ordinal1 @ X41 )
      | ( r2_hidden @ ( k1_ordinal1 @ X41 ) @ sk_A )
      | ~ ( r2_hidden @ X41 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','6','69','116'])).

thf('118',plain,
    ( ( sk_A
      = ( k3_tarski @ sk_A ) )
    | ~ ( r1_tarski @ ( sk_D_1 @ sk_A @ sk_A ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['115','117'])).

thf('119',plain,
    ( ( ( r2_hidden @ sk_A @ ( k3_tarski @ sk_A ) )
      | ( sk_A
        = ( k3_tarski @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ~ ( v3_ordinal1 @ X41 )
        | ( r2_hidden @ ( k1_ordinal1 @ X41 ) @ sk_A )
        | ~ ( r2_hidden @ X41 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('120',plain,(
    ! [X8: $i,X11: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X11 @ X8 ) @ X8 )
      | ~ ( r2_hidden @ X11 @ ( k3_tarski @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('121',plain,
    ( ( ( sk_A
        = ( k3_tarski @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_A ) @ sk_A ) )
   <= ! [X41: $i] :
        ( ~ ( v3_ordinal1 @ X41 )
        | ( r2_hidden @ ( k1_ordinal1 @ X41 ) @ sk_A )
        | ~ ( r2_hidden @ X41 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('122',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ( r1_tarski @ X18 @ X19 )
      | ~ ( v1_ordinal1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('123',plain,
    ( ( ( sk_A
        = ( k3_tarski @ sk_A ) )
      | ~ ( v1_ordinal1 @ sk_A )
      | ( r1_tarski @ ( sk_D_1 @ sk_A @ sk_A ) @ sk_A ) )
   <= ! [X41: $i] :
        ( ~ ( v3_ordinal1 @ X41 )
        | ( r2_hidden @ ( k1_ordinal1 @ X41 ) @ sk_A )
        | ~ ( r2_hidden @ X41 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('125',plain,(
    ! [X14: $i] :
      ( ( v1_ordinal1 @ X14 )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('126',plain,(
    v1_ordinal1 @ sk_A ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ( ( sk_A
        = ( k3_tarski @ sk_A ) )
      | ( r1_tarski @ ( sk_D_1 @ sk_A @ sk_A ) @ sk_A ) )
   <= ! [X41: $i] :
        ( ~ ( v3_ordinal1 @ X41 )
        | ( r2_hidden @ ( k1_ordinal1 @ X41 ) @ sk_A )
        | ~ ( r2_hidden @ X41 @ sk_A ) ) ),
    inference(demod,[status(thm)],['123','126'])).

thf('128',plain,(
    ! [X41: $i] :
      ( ~ ( v3_ordinal1 @ X41 )
      | ( r2_hidden @ ( k1_ordinal1 @ X41 ) @ sk_A )
      | ~ ( r2_hidden @ X41 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','6','69','116'])).

thf('129',plain,
    ( ( sk_A
      = ( k3_tarski @ sk_A ) )
    | ( r1_tarski @ ( sk_D_1 @ sk_A @ sk_A ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['127','128'])).

thf('130',plain,
    ( sk_A
    = ( k3_tarski @ sk_A ) ),
    inference(clc,[status(thm)],['118','129'])).

thf('131',plain,(
    ! [X22: $i] :
      ( ( v4_ordinal1 @ X22 )
      | ( X22
       != ( k3_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d6_ordinal1])).

thf('132',plain,
    ( ( sk_A != sk_A )
    | ( v4_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    v4_ordinal1 @ sk_A ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    $false ),
    inference(demod,[status(thm)],['71','133'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uunOXnkhet
% 0.16/0.37  % Computer   : n009.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 17:07:26 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 1.29/1.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.29/1.47  % Solved by: fo/fo7.sh
% 1.29/1.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.29/1.47  % done 1625 iterations in 0.979s
% 1.29/1.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.29/1.47  % SZS output start Refutation
% 1.29/1.47  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 1.29/1.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.29/1.47  thf(sk_A_type, type, sk_A: $i).
% 1.29/1.47  thf(sk_B_3_type, type, sk_B_3: $i).
% 1.29/1.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.29/1.47  thf(v4_ordinal1_type, type, v4_ordinal1: $i > $o).
% 1.29/1.47  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 1.29/1.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.29/1.47  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 1.29/1.47  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.29/1.47  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 1.29/1.47  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 1.29/1.47  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 1.29/1.47  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 1.29/1.47  thf(t41_ordinal1, conjecture,
% 1.29/1.47    (![A:$i]:
% 1.29/1.47     ( ( v3_ordinal1 @ A ) =>
% 1.29/1.47       ( ( v4_ordinal1 @ A ) <=>
% 1.29/1.47         ( ![B:$i]:
% 1.29/1.47           ( ( v3_ordinal1 @ B ) =>
% 1.29/1.47             ( ( r2_hidden @ B @ A ) => ( r2_hidden @ ( k1_ordinal1 @ B ) @ A ) ) ) ) ) ))).
% 1.29/1.47  thf(zf_stmt_0, negated_conjecture,
% 1.29/1.47    (~( ![A:$i]:
% 1.29/1.47        ( ( v3_ordinal1 @ A ) =>
% 1.29/1.47          ( ( v4_ordinal1 @ A ) <=>
% 1.29/1.47            ( ![B:$i]:
% 1.29/1.47              ( ( v3_ordinal1 @ B ) =>
% 1.29/1.47                ( ( r2_hidden @ B @ A ) =>
% 1.29/1.47                  ( r2_hidden @ ( k1_ordinal1 @ B ) @ A ) ) ) ) ) ) )),
% 1.29/1.47    inference('cnf.neg', [status(esa)], [t41_ordinal1])).
% 1.29/1.47  thf('0', plain, (((r2_hidden @ sk_B_3 @ sk_A) | ~ (v4_ordinal1 @ sk_A))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('1', plain, ((~ (v4_ordinal1 @ sk_A)) <= (~ ((v4_ordinal1 @ sk_A)))),
% 1.29/1.47      inference('split', [status(esa)], ['0'])).
% 1.29/1.47  thf('2', plain, (((r2_hidden @ sk_B_3 @ sk_A)) | ~ ((v4_ordinal1 @ sk_A))),
% 1.29/1.47      inference('split', [status(esa)], ['0'])).
% 1.29/1.47  thf('3', plain,
% 1.29/1.47      ((~ (r2_hidden @ (k1_ordinal1 @ sk_B_3) @ sk_A) | ~ (v4_ordinal1 @ sk_A))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('4', plain,
% 1.29/1.47      (~ ((v4_ordinal1 @ sk_A)) | 
% 1.29/1.47       ~ ((r2_hidden @ (k1_ordinal1 @ sk_B_3) @ sk_A))),
% 1.29/1.47      inference('split', [status(esa)], ['3'])).
% 1.29/1.47  thf('5', plain, (((v3_ordinal1 @ sk_B_3) | ~ (v4_ordinal1 @ sk_A))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('6', plain, (((v3_ordinal1 @ sk_B_3)) | ~ ((v4_ordinal1 @ sk_A))),
% 1.29/1.47      inference('split', [status(esa)], ['5'])).
% 1.29/1.47  thf('7', plain,
% 1.29/1.47      (![X41 : $i]:
% 1.29/1.47         (~ (v3_ordinal1 @ X41)
% 1.29/1.47          | (r2_hidden @ (k1_ordinal1 @ X41) @ sk_A)
% 1.29/1.47          | ~ (r2_hidden @ X41 @ sk_A)
% 1.29/1.47          | (v4_ordinal1 @ sk_A))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('8', plain, (((v4_ordinal1 @ sk_A)) <= (((v4_ordinal1 @ sk_A)))),
% 1.29/1.47      inference('split', [status(esa)], ['7'])).
% 1.29/1.47  thf('9', plain,
% 1.29/1.47      (((r2_hidden @ sk_B_3 @ sk_A)) <= (((r2_hidden @ sk_B_3 @ sk_A)))),
% 1.29/1.47      inference('split', [status(esa)], ['0'])).
% 1.29/1.47  thf(d6_ordinal1, axiom,
% 1.29/1.47    (![A:$i]: ( ( v4_ordinal1 @ A ) <=> ( ( A ) = ( k3_tarski @ A ) ) ))).
% 1.29/1.47  thf('10', plain,
% 1.29/1.47      (![X21 : $i]: (((X21) = (k3_tarski @ X21)) | ~ (v4_ordinal1 @ X21))),
% 1.29/1.47      inference('cnf', [status(esa)], [d6_ordinal1])).
% 1.29/1.47  thf(d4_tarski, axiom,
% 1.29/1.47    (![A:$i,B:$i]:
% 1.29/1.47     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 1.29/1.47       ( ![C:$i]:
% 1.29/1.47         ( ( r2_hidden @ C @ B ) <=>
% 1.29/1.47           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 1.29/1.47  thf('11', plain,
% 1.29/1.47      (![X8 : $i, X10 : $i, X11 : $i]:
% 1.29/1.47         (~ (r2_hidden @ X11 @ X10)
% 1.29/1.47          | (r2_hidden @ (sk_D_1 @ X11 @ X8) @ X8)
% 1.29/1.47          | ((X10) != (k3_tarski @ X8)))),
% 1.29/1.47      inference('cnf', [status(esa)], [d4_tarski])).
% 1.29/1.47  thf('12', plain,
% 1.29/1.47      (![X8 : $i, X11 : $i]:
% 1.29/1.47         ((r2_hidden @ (sk_D_1 @ X11 @ X8) @ X8)
% 1.29/1.47          | ~ (r2_hidden @ X11 @ (k3_tarski @ X8)))),
% 1.29/1.47      inference('simplify', [status(thm)], ['11'])).
% 1.29/1.47  thf('13', plain,
% 1.29/1.47      (![X0 : $i, X1 : $i]:
% 1.29/1.47         (~ (r2_hidden @ X1 @ X0)
% 1.29/1.47          | ~ (v4_ordinal1 @ X0)
% 1.29/1.47          | (r2_hidden @ (sk_D_1 @ X1 @ X0) @ X0))),
% 1.29/1.47      inference('sup-', [status(thm)], ['10', '12'])).
% 1.29/1.47  thf('14', plain,
% 1.29/1.47      ((((r2_hidden @ (sk_D_1 @ sk_B_3 @ sk_A) @ sk_A) | ~ (v4_ordinal1 @ sk_A)))
% 1.29/1.47         <= (((r2_hidden @ sk_B_3 @ sk_A)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['9', '13'])).
% 1.29/1.47  thf('15', plain,
% 1.29/1.47      (((r2_hidden @ (sk_D_1 @ sk_B_3 @ sk_A) @ sk_A))
% 1.29/1.47         <= (((v4_ordinal1 @ sk_A)) & ((r2_hidden @ sk_B_3 @ sk_A)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['8', '14'])).
% 1.29/1.47  thf('16', plain, (((v3_ordinal1 @ sk_B_3)) <= (((v3_ordinal1 @ sk_B_3)))),
% 1.29/1.47      inference('split', [status(esa)], ['5'])).
% 1.29/1.47  thf(t29_ordinal1, axiom,
% 1.29/1.47    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 1.29/1.47  thf('17', plain,
% 1.29/1.47      (![X33 : $i]:
% 1.29/1.47         ((v3_ordinal1 @ (k1_ordinal1 @ X33)) | ~ (v3_ordinal1 @ X33))),
% 1.29/1.47      inference('cnf', [status(esa)], [t29_ordinal1])).
% 1.29/1.47  thf(t24_ordinal1, axiom,
% 1.29/1.47    (![A:$i]:
% 1.29/1.47     ( ( v3_ordinal1 @ A ) =>
% 1.29/1.47       ( ![B:$i]:
% 1.29/1.47         ( ( v3_ordinal1 @ B ) =>
% 1.29/1.47           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 1.29/1.47                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 1.29/1.47  thf('18', plain,
% 1.29/1.47      (![X31 : $i, X32 : $i]:
% 1.29/1.47         (~ (v3_ordinal1 @ X31)
% 1.29/1.47          | (r2_hidden @ X32 @ X31)
% 1.29/1.47          | ((X32) = (X31))
% 1.29/1.47          | (r2_hidden @ X31 @ X32)
% 1.29/1.47          | ~ (v3_ordinal1 @ X32))),
% 1.29/1.47      inference('cnf', [status(esa)], [t24_ordinal1])).
% 1.29/1.47  thf('19', plain,
% 1.29/1.47      ((~ (r2_hidden @ (k1_ordinal1 @ sk_B_3) @ sk_A))
% 1.29/1.47         <= (~ ((r2_hidden @ (k1_ordinal1 @ sk_B_3) @ sk_A)))),
% 1.29/1.47      inference('split', [status(esa)], ['3'])).
% 1.29/1.47  thf('20', plain,
% 1.29/1.47      (((~ (v3_ordinal1 @ (k1_ordinal1 @ sk_B_3))
% 1.29/1.47         | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_3))
% 1.29/1.47         | ((k1_ordinal1 @ sk_B_3) = (sk_A))
% 1.29/1.47         | ~ (v3_ordinal1 @ sk_A)))
% 1.29/1.47         <= (~ ((r2_hidden @ (k1_ordinal1 @ sk_B_3) @ sk_A)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['18', '19'])).
% 1.29/1.47  thf('21', plain, ((v3_ordinal1 @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('22', plain,
% 1.29/1.47      (((~ (v3_ordinal1 @ (k1_ordinal1 @ sk_B_3))
% 1.29/1.47         | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_3))
% 1.29/1.47         | ((k1_ordinal1 @ sk_B_3) = (sk_A))))
% 1.29/1.47         <= (~ ((r2_hidden @ (k1_ordinal1 @ sk_B_3) @ sk_A)))),
% 1.29/1.47      inference('demod', [status(thm)], ['20', '21'])).
% 1.29/1.47  thf('23', plain,
% 1.29/1.47      (((~ (v3_ordinal1 @ sk_B_3)
% 1.29/1.47         | ((k1_ordinal1 @ sk_B_3) = (sk_A))
% 1.29/1.47         | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_3))))
% 1.29/1.47         <= (~ ((r2_hidden @ (k1_ordinal1 @ sk_B_3) @ sk_A)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['17', '22'])).
% 1.29/1.47  thf('24', plain,
% 1.29/1.47      ((((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_3))
% 1.29/1.47         | ((k1_ordinal1 @ sk_B_3) = (sk_A))))
% 1.29/1.47         <= (~ ((r2_hidden @ (k1_ordinal1 @ sk_B_3) @ sk_A)) & 
% 1.29/1.47             ((v3_ordinal1 @ sk_B_3)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['16', '23'])).
% 1.29/1.47  thf(t34_ordinal1, axiom,
% 1.29/1.47    (![A:$i]:
% 1.29/1.47     ( ( v3_ordinal1 @ A ) =>
% 1.29/1.47       ( ![B:$i]:
% 1.29/1.47         ( ( v3_ordinal1 @ B ) =>
% 1.29/1.47           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 1.29/1.47             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 1.29/1.47  thf('25', plain,
% 1.29/1.47      (![X34 : $i, X35 : $i]:
% 1.29/1.47         (~ (v3_ordinal1 @ X34)
% 1.29/1.47          | ~ (r2_hidden @ X35 @ (k1_ordinal1 @ X34))
% 1.29/1.47          | (r1_ordinal1 @ X35 @ X34)
% 1.29/1.47          | ~ (v3_ordinal1 @ X35))),
% 1.29/1.47      inference('cnf', [status(esa)], [t34_ordinal1])).
% 1.29/1.47  thf('26', plain,
% 1.29/1.47      (((((k1_ordinal1 @ sk_B_3) = (sk_A))
% 1.29/1.47         | ~ (v3_ordinal1 @ sk_A)
% 1.29/1.47         | (r1_ordinal1 @ sk_A @ sk_B_3)
% 1.29/1.47         | ~ (v3_ordinal1 @ sk_B_3)))
% 1.29/1.47         <= (~ ((r2_hidden @ (k1_ordinal1 @ sk_B_3) @ sk_A)) & 
% 1.29/1.47             ((v3_ordinal1 @ sk_B_3)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['24', '25'])).
% 1.29/1.47  thf('27', plain, ((v3_ordinal1 @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('28', plain, (((v3_ordinal1 @ sk_B_3)) <= (((v3_ordinal1 @ sk_B_3)))),
% 1.29/1.47      inference('split', [status(esa)], ['5'])).
% 1.29/1.47  thf('29', plain,
% 1.29/1.47      (((((k1_ordinal1 @ sk_B_3) = (sk_A)) | (r1_ordinal1 @ sk_A @ sk_B_3)))
% 1.29/1.47         <= (~ ((r2_hidden @ (k1_ordinal1 @ sk_B_3) @ sk_A)) & 
% 1.29/1.47             ((v3_ordinal1 @ sk_B_3)))),
% 1.29/1.47      inference('demod', [status(thm)], ['26', '27', '28'])).
% 1.29/1.47  thf(redefinition_r1_ordinal1, axiom,
% 1.29/1.47    (![A:$i,B:$i]:
% 1.29/1.47     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 1.29/1.47       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 1.29/1.47  thf('30', plain,
% 1.29/1.47      (![X23 : $i, X24 : $i]:
% 1.29/1.47         (~ (v3_ordinal1 @ X23)
% 1.29/1.47          | ~ (v3_ordinal1 @ X24)
% 1.29/1.47          | (r1_tarski @ X23 @ X24)
% 1.29/1.47          | ~ (r1_ordinal1 @ X23 @ X24))),
% 1.29/1.47      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 1.29/1.47  thf('31', plain,
% 1.29/1.47      (((((k1_ordinal1 @ sk_B_3) = (sk_A))
% 1.29/1.47         | (r1_tarski @ sk_A @ sk_B_3)
% 1.29/1.47         | ~ (v3_ordinal1 @ sk_B_3)
% 1.29/1.47         | ~ (v3_ordinal1 @ sk_A)))
% 1.29/1.47         <= (~ ((r2_hidden @ (k1_ordinal1 @ sk_B_3) @ sk_A)) & 
% 1.29/1.47             ((v3_ordinal1 @ sk_B_3)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['29', '30'])).
% 1.29/1.47  thf('32', plain, (((v3_ordinal1 @ sk_B_3)) <= (((v3_ordinal1 @ sk_B_3)))),
% 1.29/1.47      inference('split', [status(esa)], ['5'])).
% 1.29/1.47  thf('33', plain, ((v3_ordinal1 @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('34', plain,
% 1.29/1.47      (((((k1_ordinal1 @ sk_B_3) = (sk_A)) | (r1_tarski @ sk_A @ sk_B_3)))
% 1.29/1.47         <= (~ ((r2_hidden @ (k1_ordinal1 @ sk_B_3) @ sk_A)) & 
% 1.29/1.47             ((v3_ordinal1 @ sk_B_3)))),
% 1.29/1.47      inference('demod', [status(thm)], ['31', '32', '33'])).
% 1.29/1.47  thf('35', plain,
% 1.29/1.47      (((r2_hidden @ sk_B_3 @ sk_A)) <= (((r2_hidden @ sk_B_3 @ sk_A)))),
% 1.29/1.47      inference('split', [status(esa)], ['0'])).
% 1.29/1.47  thf(t7_ordinal1, axiom,
% 1.29/1.47    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.29/1.47  thf('36', plain,
% 1.29/1.47      (![X39 : $i, X40 : $i]:
% 1.29/1.47         (~ (r2_hidden @ X39 @ X40) | ~ (r1_tarski @ X40 @ X39))),
% 1.29/1.47      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.29/1.47  thf('37', plain,
% 1.29/1.47      ((~ (r1_tarski @ sk_A @ sk_B_3)) <= (((r2_hidden @ sk_B_3 @ sk_A)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['35', '36'])).
% 1.29/1.47  thf('38', plain,
% 1.29/1.47      ((((k1_ordinal1 @ sk_B_3) = (sk_A)))
% 1.29/1.47         <= (~ ((r2_hidden @ (k1_ordinal1 @ sk_B_3) @ sk_A)) & 
% 1.29/1.47             ((r2_hidden @ sk_B_3 @ sk_A)) & 
% 1.29/1.47             ((v3_ordinal1 @ sk_B_3)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['34', '37'])).
% 1.29/1.47  thf('39', plain,
% 1.29/1.47      (![X34 : $i, X35 : $i]:
% 1.29/1.47         (~ (v3_ordinal1 @ X34)
% 1.29/1.47          | ~ (r2_hidden @ X35 @ (k1_ordinal1 @ X34))
% 1.29/1.47          | (r1_ordinal1 @ X35 @ X34)
% 1.29/1.47          | ~ (v3_ordinal1 @ X35))),
% 1.29/1.47      inference('cnf', [status(esa)], [t34_ordinal1])).
% 1.29/1.47  thf('40', plain,
% 1.29/1.47      ((![X0 : $i]:
% 1.29/1.47          (~ (r2_hidden @ X0 @ sk_A)
% 1.29/1.47           | ~ (v3_ordinal1 @ X0)
% 1.29/1.47           | (r1_ordinal1 @ X0 @ sk_B_3)
% 1.29/1.47           | ~ (v3_ordinal1 @ sk_B_3)))
% 1.29/1.47         <= (~ ((r2_hidden @ (k1_ordinal1 @ sk_B_3) @ sk_A)) & 
% 1.29/1.47             ((r2_hidden @ sk_B_3 @ sk_A)) & 
% 1.29/1.47             ((v3_ordinal1 @ sk_B_3)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['38', '39'])).
% 1.29/1.47  thf('41', plain,
% 1.29/1.47      (((r2_hidden @ sk_B_3 @ sk_A)) <= (((r2_hidden @ sk_B_3 @ sk_A)))),
% 1.29/1.47      inference('split', [status(esa)], ['0'])).
% 1.29/1.47  thf(t23_ordinal1, axiom,
% 1.29/1.47    (![A:$i,B:$i]:
% 1.29/1.47     ( ( v3_ordinal1 @ B ) => ( ( r2_hidden @ A @ B ) => ( v3_ordinal1 @ A ) ) ))).
% 1.29/1.47  thf('42', plain,
% 1.29/1.47      (![X29 : $i, X30 : $i]:
% 1.29/1.47         ((v3_ordinal1 @ X29)
% 1.29/1.47          | ~ (v3_ordinal1 @ X30)
% 1.29/1.47          | ~ (r2_hidden @ X29 @ X30))),
% 1.29/1.47      inference('cnf', [status(esa)], [t23_ordinal1])).
% 1.29/1.47  thf('43', plain,
% 1.29/1.47      (((~ (v3_ordinal1 @ sk_A) | (v3_ordinal1 @ sk_B_3)))
% 1.29/1.47         <= (((r2_hidden @ sk_B_3 @ sk_A)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['41', '42'])).
% 1.29/1.47  thf('44', plain, ((v3_ordinal1 @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('45', plain,
% 1.29/1.47      (((v3_ordinal1 @ sk_B_3)) <= (((r2_hidden @ sk_B_3 @ sk_A)))),
% 1.29/1.47      inference('demod', [status(thm)], ['43', '44'])).
% 1.29/1.47  thf('46', plain,
% 1.29/1.47      ((![X0 : $i]:
% 1.29/1.47          (~ (r2_hidden @ X0 @ sk_A)
% 1.29/1.47           | ~ (v3_ordinal1 @ X0)
% 1.29/1.47           | (r1_ordinal1 @ X0 @ sk_B_3)))
% 1.29/1.47         <= (~ ((r2_hidden @ (k1_ordinal1 @ sk_B_3) @ sk_A)) & 
% 1.29/1.47             ((r2_hidden @ sk_B_3 @ sk_A)) & 
% 1.29/1.47             ((v3_ordinal1 @ sk_B_3)))),
% 1.29/1.47      inference('demod', [status(thm)], ['40', '45'])).
% 1.29/1.47  thf('47', plain,
% 1.29/1.47      ((((r1_ordinal1 @ (sk_D_1 @ sk_B_3 @ sk_A) @ sk_B_3)
% 1.29/1.47         | ~ (v3_ordinal1 @ (sk_D_1 @ sk_B_3 @ sk_A))))
% 1.29/1.47         <= (~ ((r2_hidden @ (k1_ordinal1 @ sk_B_3) @ sk_A)) & 
% 1.29/1.47             ((v4_ordinal1 @ sk_A)) & 
% 1.29/1.47             ((r2_hidden @ sk_B_3 @ sk_A)) & 
% 1.29/1.47             ((v3_ordinal1 @ sk_B_3)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['15', '46'])).
% 1.29/1.47  thf('48', plain,
% 1.29/1.47      (((r2_hidden @ (sk_D_1 @ sk_B_3 @ sk_A) @ sk_A))
% 1.29/1.47         <= (((v4_ordinal1 @ sk_A)) & ((r2_hidden @ sk_B_3 @ sk_A)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['8', '14'])).
% 1.29/1.47  thf('49', plain,
% 1.29/1.47      (![X29 : $i, X30 : $i]:
% 1.29/1.47         ((v3_ordinal1 @ X29)
% 1.29/1.47          | ~ (v3_ordinal1 @ X30)
% 1.29/1.47          | ~ (r2_hidden @ X29 @ X30))),
% 1.29/1.47      inference('cnf', [status(esa)], [t23_ordinal1])).
% 1.29/1.47  thf('50', plain,
% 1.29/1.47      (((~ (v3_ordinal1 @ sk_A) | (v3_ordinal1 @ (sk_D_1 @ sk_B_3 @ sk_A))))
% 1.29/1.47         <= (((v4_ordinal1 @ sk_A)) & ((r2_hidden @ sk_B_3 @ sk_A)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['48', '49'])).
% 1.29/1.47  thf('51', plain, ((v3_ordinal1 @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('52', plain,
% 1.29/1.47      (((v3_ordinal1 @ (sk_D_1 @ sk_B_3 @ sk_A)))
% 1.29/1.47         <= (((v4_ordinal1 @ sk_A)) & ((r2_hidden @ sk_B_3 @ sk_A)))),
% 1.29/1.47      inference('demod', [status(thm)], ['50', '51'])).
% 1.29/1.47  thf('53', plain,
% 1.29/1.47      (((r1_ordinal1 @ (sk_D_1 @ sk_B_3 @ sk_A) @ sk_B_3))
% 1.29/1.47         <= (~ ((r2_hidden @ (k1_ordinal1 @ sk_B_3) @ sk_A)) & 
% 1.29/1.47             ((v4_ordinal1 @ sk_A)) & 
% 1.29/1.47             ((r2_hidden @ sk_B_3 @ sk_A)) & 
% 1.29/1.47             ((v3_ordinal1 @ sk_B_3)))),
% 1.29/1.47      inference('demod', [status(thm)], ['47', '52'])).
% 1.29/1.47  thf('54', plain,
% 1.29/1.47      (![X23 : $i, X24 : $i]:
% 1.29/1.47         (~ (v3_ordinal1 @ X23)
% 1.29/1.47          | ~ (v3_ordinal1 @ X24)
% 1.29/1.47          | (r1_tarski @ X23 @ X24)
% 1.29/1.47          | ~ (r1_ordinal1 @ X23 @ X24))),
% 1.29/1.47      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 1.29/1.47  thf('55', plain,
% 1.29/1.47      ((((r1_tarski @ (sk_D_1 @ sk_B_3 @ sk_A) @ sk_B_3)
% 1.29/1.47         | ~ (v3_ordinal1 @ sk_B_3)
% 1.29/1.47         | ~ (v3_ordinal1 @ (sk_D_1 @ sk_B_3 @ sk_A))))
% 1.29/1.47         <= (~ ((r2_hidden @ (k1_ordinal1 @ sk_B_3) @ sk_A)) & 
% 1.29/1.47             ((v4_ordinal1 @ sk_A)) & 
% 1.29/1.47             ((r2_hidden @ sk_B_3 @ sk_A)) & 
% 1.29/1.47             ((v3_ordinal1 @ sk_B_3)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['53', '54'])).
% 1.29/1.47  thf('56', plain,
% 1.29/1.47      (((v3_ordinal1 @ sk_B_3)) <= (((r2_hidden @ sk_B_3 @ sk_A)))),
% 1.29/1.47      inference('demod', [status(thm)], ['43', '44'])).
% 1.29/1.47  thf('57', plain,
% 1.29/1.47      (((v3_ordinal1 @ (sk_D_1 @ sk_B_3 @ sk_A)))
% 1.29/1.47         <= (((v4_ordinal1 @ sk_A)) & ((r2_hidden @ sk_B_3 @ sk_A)))),
% 1.29/1.47      inference('demod', [status(thm)], ['50', '51'])).
% 1.29/1.47  thf('58', plain,
% 1.29/1.47      (((r1_tarski @ (sk_D_1 @ sk_B_3 @ sk_A) @ sk_B_3))
% 1.29/1.47         <= (~ ((r2_hidden @ (k1_ordinal1 @ sk_B_3) @ sk_A)) & 
% 1.29/1.47             ((v4_ordinal1 @ sk_A)) & 
% 1.29/1.47             ((r2_hidden @ sk_B_3 @ sk_A)) & 
% 1.29/1.47             ((v3_ordinal1 @ sk_B_3)))),
% 1.29/1.47      inference('demod', [status(thm)], ['55', '56', '57'])).
% 1.29/1.47  thf('59', plain, (((v4_ordinal1 @ sk_A)) <= (((v4_ordinal1 @ sk_A)))),
% 1.29/1.47      inference('split', [status(esa)], ['7'])).
% 1.29/1.47  thf('60', plain,
% 1.29/1.47      (((r2_hidden @ sk_B_3 @ sk_A)) <= (((r2_hidden @ sk_B_3 @ sk_A)))),
% 1.29/1.47      inference('split', [status(esa)], ['0'])).
% 1.29/1.47  thf('61', plain,
% 1.29/1.47      (![X21 : $i]: (((X21) = (k3_tarski @ X21)) | ~ (v4_ordinal1 @ X21))),
% 1.29/1.47      inference('cnf', [status(esa)], [d6_ordinal1])).
% 1.29/1.47  thf('62', plain,
% 1.29/1.47      (![X8 : $i, X10 : $i, X11 : $i]:
% 1.29/1.47         (~ (r2_hidden @ X11 @ X10)
% 1.29/1.47          | (r2_hidden @ X11 @ (sk_D_1 @ X11 @ X8))
% 1.29/1.47          | ((X10) != (k3_tarski @ X8)))),
% 1.29/1.47      inference('cnf', [status(esa)], [d4_tarski])).
% 1.29/1.47  thf('63', plain,
% 1.29/1.47      (![X8 : $i, X11 : $i]:
% 1.29/1.47         ((r2_hidden @ X11 @ (sk_D_1 @ X11 @ X8))
% 1.29/1.47          | ~ (r2_hidden @ X11 @ (k3_tarski @ X8)))),
% 1.29/1.47      inference('simplify', [status(thm)], ['62'])).
% 1.29/1.47  thf('64', plain,
% 1.29/1.47      (![X0 : $i, X1 : $i]:
% 1.29/1.47         (~ (r2_hidden @ X1 @ X0)
% 1.29/1.47          | ~ (v4_ordinal1 @ X0)
% 1.29/1.47          | (r2_hidden @ X1 @ (sk_D_1 @ X1 @ X0)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['61', '63'])).
% 1.29/1.47  thf('65', plain,
% 1.29/1.47      ((((r2_hidden @ sk_B_3 @ (sk_D_1 @ sk_B_3 @ sk_A))
% 1.29/1.47         | ~ (v4_ordinal1 @ sk_A))) <= (((r2_hidden @ sk_B_3 @ sk_A)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['60', '64'])).
% 1.29/1.47  thf('66', plain,
% 1.29/1.47      (((r2_hidden @ sk_B_3 @ (sk_D_1 @ sk_B_3 @ sk_A)))
% 1.29/1.47         <= (((v4_ordinal1 @ sk_A)) & ((r2_hidden @ sk_B_3 @ sk_A)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['59', '65'])).
% 1.29/1.47  thf('67', plain,
% 1.29/1.47      (![X39 : $i, X40 : $i]:
% 1.29/1.47         (~ (r2_hidden @ X39 @ X40) | ~ (r1_tarski @ X40 @ X39))),
% 1.29/1.47      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.29/1.47  thf('68', plain,
% 1.29/1.47      ((~ (r1_tarski @ (sk_D_1 @ sk_B_3 @ sk_A) @ sk_B_3))
% 1.29/1.47         <= (((v4_ordinal1 @ sk_A)) & ((r2_hidden @ sk_B_3 @ sk_A)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['66', '67'])).
% 1.29/1.47  thf('69', plain,
% 1.29/1.47      (~ ((v4_ordinal1 @ sk_A)) | ~ ((v3_ordinal1 @ sk_B_3)) | 
% 1.29/1.47       ~ ((r2_hidden @ sk_B_3 @ sk_A)) | 
% 1.29/1.47       ((r2_hidden @ (k1_ordinal1 @ sk_B_3) @ sk_A))),
% 1.29/1.47      inference('sup-', [status(thm)], ['58', '68'])).
% 1.29/1.47  thf('70', plain, (~ ((v4_ordinal1 @ sk_A))),
% 1.29/1.47      inference('sat_resolution*', [status(thm)], ['2', '4', '6', '69'])).
% 1.29/1.47  thf('71', plain, (~ (v4_ordinal1 @ sk_A)),
% 1.29/1.47      inference('simpl_trail', [status(thm)], ['1', '70'])).
% 1.29/1.47  thf(t35_ordinal1, axiom,
% 1.29/1.47    (![A:$i]:
% 1.29/1.47     ( ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( v3_ordinal1 @ B ) ) ) =>
% 1.29/1.47       ( v3_ordinal1 @ ( k3_tarski @ A ) ) ))).
% 1.29/1.47  thf('72', plain,
% 1.29/1.47      (![X36 : $i]:
% 1.29/1.47         ((v3_ordinal1 @ (k3_tarski @ X36))
% 1.29/1.47          | (r2_hidden @ (sk_B_1 @ X36) @ X36))),
% 1.29/1.47      inference('cnf', [status(esa)], [t35_ordinal1])).
% 1.29/1.47  thf('73', plain,
% 1.29/1.47      (![X29 : $i, X30 : $i]:
% 1.29/1.47         ((v3_ordinal1 @ X29)
% 1.29/1.47          | ~ (v3_ordinal1 @ X30)
% 1.29/1.47          | ~ (r2_hidden @ X29 @ X30))),
% 1.29/1.47      inference('cnf', [status(esa)], [t23_ordinal1])).
% 1.29/1.47  thf('74', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         ((v3_ordinal1 @ (k3_tarski @ X0))
% 1.29/1.47          | ~ (v3_ordinal1 @ X0)
% 1.29/1.47          | (v3_ordinal1 @ (sk_B_1 @ X0)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['72', '73'])).
% 1.29/1.47  thf('75', plain,
% 1.29/1.47      (![X36 : $i]:
% 1.29/1.47         ((v3_ordinal1 @ (k3_tarski @ X36)) | ~ (v3_ordinal1 @ (sk_B_1 @ X36)))),
% 1.29/1.47      inference('cnf', [status(esa)], [t35_ordinal1])).
% 1.29/1.47  thf('76', plain,
% 1.29/1.47      (![X0 : $i]: (~ (v3_ordinal1 @ X0) | (v3_ordinal1 @ (k3_tarski @ X0)))),
% 1.29/1.47      inference('clc', [status(thm)], ['74', '75'])).
% 1.29/1.47  thf('77', plain,
% 1.29/1.47      (![X0 : $i]: (~ (v3_ordinal1 @ X0) | (v3_ordinal1 @ (k3_tarski @ X0)))),
% 1.29/1.47      inference('clc', [status(thm)], ['74', '75'])).
% 1.29/1.47  thf(d3_tarski, axiom,
% 1.29/1.47    (![A:$i,B:$i]:
% 1.29/1.47     ( ( r1_tarski @ A @ B ) <=>
% 1.29/1.47       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.29/1.47  thf('78', plain,
% 1.29/1.47      (![X1 : $i, X3 : $i]:
% 1.29/1.47         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.29/1.47      inference('cnf', [status(esa)], [d3_tarski])).
% 1.29/1.47  thf('79', plain,
% 1.29/1.47      (![X29 : $i, X30 : $i]:
% 1.29/1.47         ((v3_ordinal1 @ X29)
% 1.29/1.47          | ~ (v3_ordinal1 @ X30)
% 1.29/1.47          | ~ (r2_hidden @ X29 @ X30))),
% 1.29/1.47      inference('cnf', [status(esa)], [t23_ordinal1])).
% 1.29/1.47  thf('80', plain,
% 1.29/1.47      (![X0 : $i, X1 : $i]:
% 1.29/1.47         ((r1_tarski @ X0 @ X1)
% 1.29/1.47          | ~ (v3_ordinal1 @ X0)
% 1.29/1.47          | (v3_ordinal1 @ (sk_C @ X1 @ X0)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['78', '79'])).
% 1.29/1.47  thf('81', plain,
% 1.29/1.47      (![X1 : $i, X3 : $i]:
% 1.29/1.47         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.29/1.47      inference('cnf', [status(esa)], [d3_tarski])).
% 1.29/1.47  thf('82', plain,
% 1.29/1.47      ((![X41 : $i]:
% 1.29/1.47          (~ (v3_ordinal1 @ X41)
% 1.29/1.47           | (r2_hidden @ (k1_ordinal1 @ X41) @ sk_A)
% 1.29/1.47           | ~ (r2_hidden @ X41 @ sk_A)))
% 1.29/1.47         <= ((![X41 : $i]:
% 1.29/1.47                (~ (v3_ordinal1 @ X41)
% 1.29/1.47                 | (r2_hidden @ (k1_ordinal1 @ X41) @ sk_A)
% 1.29/1.47                 | ~ (r2_hidden @ X41 @ sk_A))))),
% 1.29/1.47      inference('split', [status(esa)], ['7'])).
% 1.29/1.47  thf('83', plain,
% 1.29/1.47      ((![X0 : $i]:
% 1.29/1.47          ((r1_tarski @ sk_A @ X0)
% 1.29/1.47           | (r2_hidden @ (k1_ordinal1 @ (sk_C @ X0 @ sk_A)) @ sk_A)
% 1.29/1.47           | ~ (v3_ordinal1 @ (sk_C @ X0 @ sk_A))))
% 1.29/1.47         <= ((![X41 : $i]:
% 1.29/1.47                (~ (v3_ordinal1 @ X41)
% 1.29/1.47                 | (r2_hidden @ (k1_ordinal1 @ X41) @ sk_A)
% 1.29/1.47                 | ~ (r2_hidden @ X41 @ sk_A))))),
% 1.29/1.47      inference('sup-', [status(thm)], ['81', '82'])).
% 1.29/1.47  thf('84', plain,
% 1.29/1.47      ((![X0 : $i]:
% 1.29/1.47          (~ (v3_ordinal1 @ sk_A)
% 1.29/1.47           | (r1_tarski @ sk_A @ X0)
% 1.29/1.47           | (r2_hidden @ (k1_ordinal1 @ (sk_C @ X0 @ sk_A)) @ sk_A)
% 1.29/1.47           | (r1_tarski @ sk_A @ X0)))
% 1.29/1.47         <= ((![X41 : $i]:
% 1.29/1.47                (~ (v3_ordinal1 @ X41)
% 1.29/1.47                 | (r2_hidden @ (k1_ordinal1 @ X41) @ sk_A)
% 1.29/1.47                 | ~ (r2_hidden @ X41 @ sk_A))))),
% 1.29/1.47      inference('sup-', [status(thm)], ['80', '83'])).
% 1.29/1.47  thf('85', plain, ((v3_ordinal1 @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('86', plain,
% 1.29/1.47      ((![X0 : $i]:
% 1.29/1.47          ((r1_tarski @ sk_A @ X0)
% 1.29/1.47           | (r2_hidden @ (k1_ordinal1 @ (sk_C @ X0 @ sk_A)) @ sk_A)
% 1.29/1.47           | (r1_tarski @ sk_A @ X0)))
% 1.29/1.47         <= ((![X41 : $i]:
% 1.29/1.47                (~ (v3_ordinal1 @ X41)
% 1.29/1.47                 | (r2_hidden @ (k1_ordinal1 @ X41) @ sk_A)
% 1.29/1.47                 | ~ (r2_hidden @ X41 @ sk_A))))),
% 1.29/1.47      inference('demod', [status(thm)], ['84', '85'])).
% 1.29/1.47  thf('87', plain,
% 1.29/1.47      ((![X0 : $i]:
% 1.29/1.47          ((r2_hidden @ (k1_ordinal1 @ (sk_C @ X0 @ sk_A)) @ sk_A)
% 1.29/1.47           | (r1_tarski @ sk_A @ X0)))
% 1.29/1.47         <= ((![X41 : $i]:
% 1.29/1.47                (~ (v3_ordinal1 @ X41)
% 1.29/1.47                 | (r2_hidden @ (k1_ordinal1 @ X41) @ sk_A)
% 1.29/1.47                 | ~ (r2_hidden @ X41 @ sk_A))))),
% 1.29/1.47      inference('simplify', [status(thm)], ['86'])).
% 1.29/1.47  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 1.29/1.47  thf('88', plain, (![X25 : $i]: (r2_hidden @ X25 @ (k1_ordinal1 @ X25))),
% 1.29/1.47      inference('cnf', [status(esa)], [t10_ordinal1])).
% 1.29/1.47  thf('89', plain,
% 1.29/1.47      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.29/1.47         (~ (r2_hidden @ X7 @ X8)
% 1.29/1.47          | ~ (r2_hidden @ X9 @ X7)
% 1.29/1.47          | (r2_hidden @ X9 @ X10)
% 1.29/1.47          | ((X10) != (k3_tarski @ X8)))),
% 1.29/1.47      inference('cnf', [status(esa)], [d4_tarski])).
% 1.29/1.47  thf('90', plain,
% 1.29/1.47      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.29/1.47         ((r2_hidden @ X9 @ (k3_tarski @ X8))
% 1.29/1.47          | ~ (r2_hidden @ X9 @ X7)
% 1.29/1.47          | ~ (r2_hidden @ X7 @ X8))),
% 1.29/1.47      inference('simplify', [status(thm)], ['89'])).
% 1.29/1.47  thf('91', plain,
% 1.29/1.47      (![X0 : $i, X1 : $i]:
% 1.29/1.47         (~ (r2_hidden @ (k1_ordinal1 @ X0) @ X1)
% 1.29/1.47          | (r2_hidden @ X0 @ (k3_tarski @ X1)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['88', '90'])).
% 1.29/1.47  thf('92', plain,
% 1.29/1.47      ((![X0 : $i]:
% 1.29/1.47          ((r1_tarski @ sk_A @ X0)
% 1.29/1.47           | (r2_hidden @ (sk_C @ X0 @ sk_A) @ (k3_tarski @ sk_A))))
% 1.29/1.47         <= ((![X41 : $i]:
% 1.29/1.47                (~ (v3_ordinal1 @ X41)
% 1.29/1.47                 | (r2_hidden @ (k1_ordinal1 @ X41) @ sk_A)
% 1.29/1.47                 | ~ (r2_hidden @ X41 @ sk_A))))),
% 1.29/1.47      inference('sup-', [status(thm)], ['87', '91'])).
% 1.29/1.47  thf('93', plain,
% 1.29/1.47      (![X1 : $i, X3 : $i]:
% 1.29/1.47         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.29/1.47      inference('cnf', [status(esa)], [d3_tarski])).
% 1.29/1.47  thf('94', plain,
% 1.29/1.47      ((((r1_tarski @ sk_A @ (k3_tarski @ sk_A))
% 1.29/1.47         | (r1_tarski @ sk_A @ (k3_tarski @ sk_A))))
% 1.29/1.47         <= ((![X41 : $i]:
% 1.29/1.47                (~ (v3_ordinal1 @ X41)
% 1.29/1.47                 | (r2_hidden @ (k1_ordinal1 @ X41) @ sk_A)
% 1.29/1.47                 | ~ (r2_hidden @ X41 @ sk_A))))),
% 1.29/1.47      inference('sup-', [status(thm)], ['92', '93'])).
% 1.29/1.47  thf('95', plain,
% 1.29/1.47      (((r1_tarski @ sk_A @ (k3_tarski @ sk_A)))
% 1.29/1.47         <= ((![X41 : $i]:
% 1.29/1.47                (~ (v3_ordinal1 @ X41)
% 1.29/1.47                 | (r2_hidden @ (k1_ordinal1 @ X41) @ sk_A)
% 1.29/1.47                 | ~ (r2_hidden @ X41 @ sk_A))))),
% 1.29/1.47      inference('simplify', [status(thm)], ['94'])).
% 1.29/1.47  thf('96', plain,
% 1.29/1.47      (![X23 : $i, X24 : $i]:
% 1.29/1.47         (~ (v3_ordinal1 @ X23)
% 1.29/1.47          | ~ (v3_ordinal1 @ X24)
% 1.29/1.47          | (r1_ordinal1 @ X23 @ X24)
% 1.29/1.47          | ~ (r1_tarski @ X23 @ X24))),
% 1.29/1.47      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 1.29/1.47  thf('97', plain,
% 1.29/1.47      ((((r1_ordinal1 @ sk_A @ (k3_tarski @ sk_A))
% 1.29/1.47         | ~ (v3_ordinal1 @ (k3_tarski @ sk_A))
% 1.29/1.47         | ~ (v3_ordinal1 @ sk_A)))
% 1.29/1.47         <= ((![X41 : $i]:
% 1.29/1.47                (~ (v3_ordinal1 @ X41)
% 1.29/1.47                 | (r2_hidden @ (k1_ordinal1 @ X41) @ sk_A)
% 1.29/1.47                 | ~ (r2_hidden @ X41 @ sk_A))))),
% 1.29/1.47      inference('sup-', [status(thm)], ['95', '96'])).
% 1.29/1.47  thf('98', plain, ((v3_ordinal1 @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('99', plain,
% 1.29/1.47      ((((r1_ordinal1 @ sk_A @ (k3_tarski @ sk_A))
% 1.29/1.47         | ~ (v3_ordinal1 @ (k3_tarski @ sk_A))))
% 1.29/1.47         <= ((![X41 : $i]:
% 1.29/1.47                (~ (v3_ordinal1 @ X41)
% 1.29/1.47                 | (r2_hidden @ (k1_ordinal1 @ X41) @ sk_A)
% 1.29/1.47                 | ~ (r2_hidden @ X41 @ sk_A))))),
% 1.29/1.47      inference('demod', [status(thm)], ['97', '98'])).
% 1.29/1.47  thf('100', plain,
% 1.29/1.47      (((~ (v3_ordinal1 @ sk_A) | (r1_ordinal1 @ sk_A @ (k3_tarski @ sk_A))))
% 1.29/1.47         <= ((![X41 : $i]:
% 1.29/1.47                (~ (v3_ordinal1 @ X41)
% 1.29/1.47                 | (r2_hidden @ (k1_ordinal1 @ X41) @ sk_A)
% 1.29/1.47                 | ~ (r2_hidden @ X41 @ sk_A))))),
% 1.29/1.47      inference('sup-', [status(thm)], ['77', '99'])).
% 1.29/1.47  thf('101', plain, ((v3_ordinal1 @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('102', plain,
% 1.29/1.47      (((r1_ordinal1 @ sk_A @ (k3_tarski @ sk_A)))
% 1.29/1.47         <= ((![X41 : $i]:
% 1.29/1.47                (~ (v3_ordinal1 @ X41)
% 1.29/1.47                 | (r2_hidden @ (k1_ordinal1 @ X41) @ sk_A)
% 1.29/1.47                 | ~ (r2_hidden @ X41 @ sk_A))))),
% 1.29/1.47      inference('demod', [status(thm)], ['100', '101'])).
% 1.29/1.47  thf('103', plain,
% 1.29/1.47      (![X34 : $i, X35 : $i]:
% 1.29/1.47         (~ (v3_ordinal1 @ X34)
% 1.29/1.47          | ~ (r1_ordinal1 @ X35 @ X34)
% 1.29/1.47          | (r2_hidden @ X35 @ (k1_ordinal1 @ X34))
% 1.29/1.47          | ~ (v3_ordinal1 @ X35))),
% 1.29/1.47      inference('cnf', [status(esa)], [t34_ordinal1])).
% 1.29/1.47  thf('104', plain,
% 1.29/1.47      (((~ (v3_ordinal1 @ sk_A)
% 1.29/1.47         | (r2_hidden @ sk_A @ (k1_ordinal1 @ (k3_tarski @ sk_A)))
% 1.29/1.47         | ~ (v3_ordinal1 @ (k3_tarski @ sk_A))))
% 1.29/1.47         <= ((![X41 : $i]:
% 1.29/1.47                (~ (v3_ordinal1 @ X41)
% 1.29/1.47                 | (r2_hidden @ (k1_ordinal1 @ X41) @ sk_A)
% 1.29/1.47                 | ~ (r2_hidden @ X41 @ sk_A))))),
% 1.29/1.47      inference('sup-', [status(thm)], ['102', '103'])).
% 1.29/1.47  thf('105', plain, ((v3_ordinal1 @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('106', plain,
% 1.29/1.47      ((((r2_hidden @ sk_A @ (k1_ordinal1 @ (k3_tarski @ sk_A)))
% 1.29/1.47         | ~ (v3_ordinal1 @ (k3_tarski @ sk_A))))
% 1.29/1.47         <= ((![X41 : $i]:
% 1.29/1.47                (~ (v3_ordinal1 @ X41)
% 1.29/1.47                 | (r2_hidden @ (k1_ordinal1 @ X41) @ sk_A)
% 1.29/1.47                 | ~ (r2_hidden @ X41 @ sk_A))))),
% 1.29/1.47      inference('demod', [status(thm)], ['104', '105'])).
% 1.29/1.47  thf('107', plain,
% 1.29/1.47      (((~ (v3_ordinal1 @ sk_A)
% 1.29/1.47         | (r2_hidden @ sk_A @ (k1_ordinal1 @ (k3_tarski @ sk_A)))))
% 1.29/1.47         <= ((![X41 : $i]:
% 1.29/1.47                (~ (v3_ordinal1 @ X41)
% 1.29/1.47                 | (r2_hidden @ (k1_ordinal1 @ X41) @ sk_A)
% 1.29/1.47                 | ~ (r2_hidden @ X41 @ sk_A))))),
% 1.29/1.47      inference('sup-', [status(thm)], ['76', '106'])).
% 1.29/1.47  thf('108', plain, ((v3_ordinal1 @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('109', plain,
% 1.29/1.47      (((r2_hidden @ sk_A @ (k1_ordinal1 @ (k3_tarski @ sk_A))))
% 1.29/1.47         <= ((![X41 : $i]:
% 1.29/1.47                (~ (v3_ordinal1 @ X41)
% 1.29/1.47                 | (r2_hidden @ (k1_ordinal1 @ X41) @ sk_A)
% 1.29/1.47                 | ~ (r2_hidden @ X41 @ sk_A))))),
% 1.29/1.47      inference('demod', [status(thm)], ['107', '108'])).
% 1.29/1.47  thf(t13_ordinal1, axiom,
% 1.29/1.47    (![A:$i,B:$i]:
% 1.29/1.47     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 1.29/1.47       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 1.29/1.47  thf('110', plain,
% 1.29/1.47      (![X26 : $i, X27 : $i]:
% 1.29/1.47         (((X27) = (X26))
% 1.29/1.47          | (r2_hidden @ X27 @ X26)
% 1.29/1.47          | ~ (r2_hidden @ X27 @ (k1_ordinal1 @ X26)))),
% 1.29/1.47      inference('cnf', [status(esa)], [t13_ordinal1])).
% 1.29/1.47  thf('111', plain,
% 1.29/1.47      ((((r2_hidden @ sk_A @ (k3_tarski @ sk_A))
% 1.29/1.47         | ((sk_A) = (k3_tarski @ sk_A))))
% 1.29/1.47         <= ((![X41 : $i]:
% 1.29/1.47                (~ (v3_ordinal1 @ X41)
% 1.29/1.47                 | (r2_hidden @ (k1_ordinal1 @ X41) @ sk_A)
% 1.29/1.47                 | ~ (r2_hidden @ X41 @ sk_A))))),
% 1.29/1.47      inference('sup-', [status(thm)], ['109', '110'])).
% 1.29/1.47  thf('112', plain,
% 1.29/1.47      (![X8 : $i, X11 : $i]:
% 1.29/1.47         ((r2_hidden @ X11 @ (sk_D_1 @ X11 @ X8))
% 1.29/1.47          | ~ (r2_hidden @ X11 @ (k3_tarski @ X8)))),
% 1.29/1.47      inference('simplify', [status(thm)], ['62'])).
% 1.29/1.47  thf('113', plain,
% 1.29/1.47      (((((sk_A) = (k3_tarski @ sk_A))
% 1.29/1.47         | (r2_hidden @ sk_A @ (sk_D_1 @ sk_A @ sk_A))))
% 1.29/1.47         <= ((![X41 : $i]:
% 1.29/1.47                (~ (v3_ordinal1 @ X41)
% 1.29/1.47                 | (r2_hidden @ (k1_ordinal1 @ X41) @ sk_A)
% 1.29/1.47                 | ~ (r2_hidden @ X41 @ sk_A))))),
% 1.29/1.47      inference('sup-', [status(thm)], ['111', '112'])).
% 1.29/1.47  thf('114', plain,
% 1.29/1.47      (![X39 : $i, X40 : $i]:
% 1.29/1.47         (~ (r2_hidden @ X39 @ X40) | ~ (r1_tarski @ X40 @ X39))),
% 1.29/1.47      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.29/1.47  thf('115', plain,
% 1.29/1.47      (((((sk_A) = (k3_tarski @ sk_A))
% 1.29/1.47         | ~ (r1_tarski @ (sk_D_1 @ sk_A @ sk_A) @ sk_A)))
% 1.29/1.47         <= ((![X41 : $i]:
% 1.29/1.47                (~ (v3_ordinal1 @ X41)
% 1.29/1.47                 | (r2_hidden @ (k1_ordinal1 @ X41) @ sk_A)
% 1.29/1.47                 | ~ (r2_hidden @ X41 @ sk_A))))),
% 1.29/1.47      inference('sup-', [status(thm)], ['113', '114'])).
% 1.29/1.47  thf('116', plain,
% 1.29/1.47      ((![X41 : $i]:
% 1.29/1.47          (~ (v3_ordinal1 @ X41)
% 1.29/1.47           | (r2_hidden @ (k1_ordinal1 @ X41) @ sk_A)
% 1.29/1.47           | ~ (r2_hidden @ X41 @ sk_A))) | 
% 1.29/1.47       ((v4_ordinal1 @ sk_A))),
% 1.29/1.47      inference('split', [status(esa)], ['7'])).
% 1.29/1.47  thf('117', plain,
% 1.29/1.47      ((![X41 : $i]:
% 1.29/1.47          (~ (v3_ordinal1 @ X41)
% 1.29/1.47           | (r2_hidden @ (k1_ordinal1 @ X41) @ sk_A)
% 1.29/1.47           | ~ (r2_hidden @ X41 @ sk_A)))),
% 1.29/1.47      inference('sat_resolution*', [status(thm)], ['2', '4', '6', '69', '116'])).
% 1.29/1.47  thf('118', plain,
% 1.29/1.47      ((((sk_A) = (k3_tarski @ sk_A))
% 1.29/1.47        | ~ (r1_tarski @ (sk_D_1 @ sk_A @ sk_A) @ sk_A))),
% 1.29/1.47      inference('simpl_trail', [status(thm)], ['115', '117'])).
% 1.29/1.47  thf('119', plain,
% 1.29/1.47      ((((r2_hidden @ sk_A @ (k3_tarski @ sk_A))
% 1.29/1.47         | ((sk_A) = (k3_tarski @ sk_A))))
% 1.29/1.47         <= ((![X41 : $i]:
% 1.29/1.47                (~ (v3_ordinal1 @ X41)
% 1.29/1.47                 | (r2_hidden @ (k1_ordinal1 @ X41) @ sk_A)
% 1.29/1.47                 | ~ (r2_hidden @ X41 @ sk_A))))),
% 1.29/1.47      inference('sup-', [status(thm)], ['109', '110'])).
% 1.29/1.47  thf('120', plain,
% 1.29/1.47      (![X8 : $i, X11 : $i]:
% 1.29/1.47         ((r2_hidden @ (sk_D_1 @ X11 @ X8) @ X8)
% 1.29/1.47          | ~ (r2_hidden @ X11 @ (k3_tarski @ X8)))),
% 1.29/1.47      inference('simplify', [status(thm)], ['11'])).
% 1.29/1.47  thf('121', plain,
% 1.29/1.47      (((((sk_A) = (k3_tarski @ sk_A))
% 1.29/1.47         | (r2_hidden @ (sk_D_1 @ sk_A @ sk_A) @ sk_A)))
% 1.29/1.47         <= ((![X41 : $i]:
% 1.29/1.47                (~ (v3_ordinal1 @ X41)
% 1.29/1.47                 | (r2_hidden @ (k1_ordinal1 @ X41) @ sk_A)
% 1.29/1.47                 | ~ (r2_hidden @ X41 @ sk_A))))),
% 1.29/1.47      inference('sup-', [status(thm)], ['119', '120'])).
% 1.29/1.47  thf(d2_ordinal1, axiom,
% 1.29/1.47    (![A:$i]:
% 1.29/1.47     ( ( v1_ordinal1 @ A ) <=>
% 1.29/1.47       ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( r1_tarski @ B @ A ) ) ) ))).
% 1.29/1.47  thf('122', plain,
% 1.29/1.47      (![X18 : $i, X19 : $i]:
% 1.29/1.47         (~ (r2_hidden @ X18 @ X19)
% 1.29/1.47          | (r1_tarski @ X18 @ X19)
% 1.29/1.47          | ~ (v1_ordinal1 @ X19))),
% 1.29/1.47      inference('cnf', [status(esa)], [d2_ordinal1])).
% 1.29/1.47  thf('123', plain,
% 1.29/1.47      (((((sk_A) = (k3_tarski @ sk_A))
% 1.29/1.47         | ~ (v1_ordinal1 @ sk_A)
% 1.29/1.47         | (r1_tarski @ (sk_D_1 @ sk_A @ sk_A) @ sk_A)))
% 1.29/1.47         <= ((![X41 : $i]:
% 1.29/1.47                (~ (v3_ordinal1 @ X41)
% 1.29/1.47                 | (r2_hidden @ (k1_ordinal1 @ X41) @ sk_A)
% 1.29/1.47                 | ~ (r2_hidden @ X41 @ sk_A))))),
% 1.29/1.47      inference('sup-', [status(thm)], ['121', '122'])).
% 1.29/1.47  thf('124', plain, ((v3_ordinal1 @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf(cc1_ordinal1, axiom,
% 1.29/1.47    (![A:$i]:
% 1.29/1.47     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 1.29/1.47  thf('125', plain,
% 1.29/1.47      (![X14 : $i]: ((v1_ordinal1 @ X14) | ~ (v3_ordinal1 @ X14))),
% 1.29/1.47      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 1.29/1.47  thf('126', plain, ((v1_ordinal1 @ sk_A)),
% 1.29/1.47      inference('sup-', [status(thm)], ['124', '125'])).
% 1.29/1.47  thf('127', plain,
% 1.29/1.47      (((((sk_A) = (k3_tarski @ sk_A))
% 1.29/1.47         | (r1_tarski @ (sk_D_1 @ sk_A @ sk_A) @ sk_A)))
% 1.29/1.47         <= ((![X41 : $i]:
% 1.29/1.47                (~ (v3_ordinal1 @ X41)
% 1.29/1.47                 | (r2_hidden @ (k1_ordinal1 @ X41) @ sk_A)
% 1.29/1.47                 | ~ (r2_hidden @ X41 @ sk_A))))),
% 1.29/1.47      inference('demod', [status(thm)], ['123', '126'])).
% 1.29/1.47  thf('128', plain,
% 1.29/1.47      ((![X41 : $i]:
% 1.29/1.47          (~ (v3_ordinal1 @ X41)
% 1.29/1.47           | (r2_hidden @ (k1_ordinal1 @ X41) @ sk_A)
% 1.29/1.47           | ~ (r2_hidden @ X41 @ sk_A)))),
% 1.29/1.47      inference('sat_resolution*', [status(thm)], ['2', '4', '6', '69', '116'])).
% 1.29/1.47  thf('129', plain,
% 1.29/1.47      ((((sk_A) = (k3_tarski @ sk_A))
% 1.29/1.47        | (r1_tarski @ (sk_D_1 @ sk_A @ sk_A) @ sk_A))),
% 1.29/1.47      inference('simpl_trail', [status(thm)], ['127', '128'])).
% 1.29/1.47  thf('130', plain, (((sk_A) = (k3_tarski @ sk_A))),
% 1.29/1.47      inference('clc', [status(thm)], ['118', '129'])).
% 1.29/1.47  thf('131', plain,
% 1.29/1.47      (![X22 : $i]: ((v4_ordinal1 @ X22) | ((X22) != (k3_tarski @ X22)))),
% 1.29/1.47      inference('cnf', [status(esa)], [d6_ordinal1])).
% 1.29/1.47  thf('132', plain, ((((sk_A) != (sk_A)) | (v4_ordinal1 @ sk_A))),
% 1.29/1.47      inference('sup-', [status(thm)], ['130', '131'])).
% 1.29/1.47  thf('133', plain, ((v4_ordinal1 @ sk_A)),
% 1.29/1.47      inference('simplify', [status(thm)], ['132'])).
% 1.29/1.47  thf('134', plain, ($false), inference('demod', [status(thm)], ['71', '133'])).
% 1.29/1.47  
% 1.29/1.47  % SZS output end Refutation
% 1.29/1.47  
% 1.29/1.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
