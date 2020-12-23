%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bQAdn51V5i

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:32 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 329 expanded)
%              Number of leaves         :   28 (  97 expanded)
%              Depth                    :   23
%              Number of atoms          :  911 (4728 expanded)
%              Number of equality atoms :   36 (  88 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v6_relat_2_type,type,(
    v6_relat_2: $i > $o )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(v1_wellord1_type,type,(
    v1_wellord1: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(t37_wellord1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( v2_wellord1 @ C )
          & ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) )
       => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
        <=> ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( ( v2_wellord1 @ C )
            & ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
            & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) )
         => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
          <=> ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t37_wellord1])).

thf('0',plain,
    ( ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_2 @ sk_A ) @ ( k1_wellord1 @ sk_C_2 @ sk_B_2 ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_2 @ sk_A ) @ ( k1_wellord1 @ sk_C_2 @ sk_B_2 ) )
   <= ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_2 @ sk_A ) @ ( k1_wellord1 @ sk_C_2 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_2 @ sk_A ) @ ( k1_wellord1 @ sk_C_2 @ sk_B_2 ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
    r2_hidden @ sk_B_2 @ ( k3_relat_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l4_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v6_relat_2 @ A )
      <=> ! [B: $i,C: $i] :
            ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
              & ( r2_hidden @ C @ ( k3_relat_1 @ A ) )
              & ( B != C )
              & ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
              & ~ ( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) ) ) ) )).

thf('5',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v6_relat_2 @ X21 )
      | ~ ( r2_hidden @ X22 @ ( k3_relat_1 @ X21 ) )
      | ( r2_hidden @ ( k4_tarski @ X23 @ X22 ) @ X21 )
      | ( r2_hidden @ ( k4_tarski @ X22 @ X23 ) @ X21 )
      | ( X22 = X23 )
      | ~ ( r2_hidden @ X23 @ ( k3_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[l4_wellord1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_C_2 ) )
      | ( sk_A = X0 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_2 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ sk_A ) @ sk_C_2 )
      | ~ ( v6_relat_2 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
      <=> ( ( v1_relat_2 @ A )
          & ( v8_relat_2 @ A )
          & ( v4_relat_2 @ A )
          & ( v6_relat_2 @ A )
          & ( v1_wellord1 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X16: $i] :
      ( ~ ( v2_wellord1 @ X16 )
      | ( v6_relat_2 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('10',plain,
    ( ( v6_relat_2 @ sk_C_2 )
    | ~ ( v2_wellord1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_wellord1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v6_relat_2 @ sk_C_2 ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_C_2 ) )
      | ( sk_A = X0 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_2 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ sk_A ) @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['6','7','12'])).

thf('14',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B_2 @ sk_A ) @ sk_C_2 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_2 )
    | ( sk_A = sk_B_2 ) ),
    inference('sup-',[status(thm)],['3','13'])).

thf(d1_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k1_wellord1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ( ( D != B )
                & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) )).

thf('15',plain,(
    ! [X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ( X13
       != ( k1_wellord1 @ X12 @ X11 ) )
      | ( r2_hidden @ X15 @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X11 ) @ X12 )
      | ( X15 = X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('16',plain,(
    ! [X11: $i,X12: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( X15 = X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X11 ) @ X12 )
      | ( r2_hidden @ X15 @ ( k1_wellord1 @ X12 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( sk_A = sk_B_2 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_2 )
    | ( r2_hidden @ sk_B_2 @ ( k1_wellord1 @ sk_C_2 @ sk_A ) )
    | ( sk_B_2 = sk_A )
    | ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( sk_A = sk_B_2 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_2 )
    | ( r2_hidden @ sk_B_2 @ ( k1_wellord1 @ sk_C_2 @ sk_A ) )
    | ( sk_B_2 = sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r2_hidden @ sk_B_2 @ ( k1_wellord1 @ sk_C_2 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_2 )
    | ( sk_A = sk_B_2 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_2 )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ( ( sk_A = sk_B_2 )
      | ( r2_hidden @ sk_B_2 @ ( k1_wellord1 @ sk_C_2 @ sk_A ) ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_2 @ sk_A ) @ ( k1_wellord1 @ sk_C_2 @ sk_B_2 ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_2 @ sk_A ) @ ( k1_wellord1 @ sk_C_2 @ sk_B_2 ) )
   <= ( r1_tarski @ ( k1_wellord1 @ sk_C_2 @ sk_A ) @ ( k1_wellord1 @ sk_C_2 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['23'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k1_wellord1 @ sk_C_2 @ sk_B_2 ) )
        | ~ ( r2_hidden @ X0 @ ( k1_wellord1 @ sk_C_2 @ sk_A ) ) )
   <= ( r1_tarski @ ( k1_wellord1 @ sk_C_2 @ sk_A ) @ ( k1_wellord1 @ sk_C_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( sk_A = sk_B_2 )
      | ( r2_hidden @ sk_B_2 @ ( k1_wellord1 @ sk_C_2 @ sk_B_2 ) ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_2 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_2 @ sk_A ) @ ( k1_wellord1 @ sk_C_2 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['22','26'])).

thf('28',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X13
       != ( k1_wellord1 @ X12 @ X11 ) )
      | ( X14 != X11 )
      | ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('29',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( r2_hidden @ X11 @ ( k1_wellord1 @ X12 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( ( sk_A = sk_B_2 )
      | ~ ( v1_relat_1 @ sk_C_2 ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_2 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_2 @ sk_A ) @ ( k1_wellord1 @ sk_C_2 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_A = sk_B_2 )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_2 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_2 @ sk_A ) @ ( k1_wellord1 @ sk_C_2 @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_2 )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_A ) @ sk_C_2 )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_2 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_2 @ sk_A ) @ ( k1_wellord1 @ sk_C_2 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v1_relat_2 @ A )
      <=> ! [B: $i] :
            ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
           => ( r2_hidden @ ( k4_tarski @ B @ B ) @ A ) ) ) ) )).

thf('36',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_2 @ X19 )
      | ( r2_hidden @ ( k4_tarski @ X20 @ X20 ) @ X19 )
      | ~ ( r2_hidden @ X20 @ ( k3_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l1_wellord1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_A ) @ sk_C_2 )
    | ~ ( v1_relat_2 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X16: $i] :
      ( ~ ( v2_wellord1 @ X16 )
      | ( v1_relat_2 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('41',plain,
    ( ( v1_relat_2 @ sk_C_2 )
    | ~ ( v2_wellord1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_wellord1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_relat_2 @ sk_C_2 ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_A ) @ sk_C_2 ),
    inference(demod,[status(thm)],['37','38','43'])).

thf('45',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_2 )
    | ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_2 @ sk_A ) @ ( k1_wellord1 @ sk_C_2 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['34','44'])).

thf('46',plain,(
    ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_2 @ sk_A ) @ ( k1_wellord1 @ sk_C_2 @ sk_B_2 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','45'])).

thf('47',plain,(
    ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_2 @ sk_A ) @ ( k1_wellord1 @ sk_C_2 @ sk_B_2 ) ) ),
    inference(simpl_trail,[status(thm)],['1','46'])).

thf('48',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_2 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['23'])).

thf('49',plain,(
    ! [X11: $i,X12: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( X15 = X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X11 ) @ X12 )
      | ( r2_hidden @ X15 @ ( k1_wellord1 @ X12 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('50',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_2 @ sk_B_2 ) )
      | ( sk_A = sk_B_2 )
      | ~ ( v1_relat_1 @ sk_C_2 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_2 @ sk_B_2 ) )
      | ( sk_A = sk_B_2 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_2 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_2 )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_2 @ sk_A ) @ ( k1_wellord1 @ sk_C_2 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['23'])).

thf('54',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_2 ),
    inference('sat_resolution*',[status(thm)],['2','45','53'])).

thf('55',plain,
    ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_2 @ sk_B_2 ) )
    | ( sk_A = sk_B_2 ) ),
    inference(simpl_trail,[status(thm)],['52','54'])).

thf(t35_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( v2_wellord1 @ C )
          & ( r2_hidden @ A @ ( k1_wellord1 @ C @ B ) ) )
       => ( ( k1_wellord1 @ ( k2_wellord1 @ C @ ( k1_wellord1 @ C @ B ) ) @ A )
          = ( k1_wellord1 @ C @ A ) ) ) ) )).

thf('56',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v2_wellord1 @ X28 )
      | ~ ( r2_hidden @ X29 @ ( k1_wellord1 @ X28 @ X30 ) )
      | ( ( k1_wellord1 @ ( k2_wellord1 @ X28 @ ( k1_wellord1 @ X28 @ X30 ) ) @ X29 )
        = ( k1_wellord1 @ X28 @ X29 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t35_wellord1])).

thf('57',plain,
    ( ( sk_A = sk_B_2 )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ( ( k1_wellord1 @ ( k2_wellord1 @ sk_C_2 @ ( k1_wellord1 @ sk_C_2 @ sk_B_2 ) ) @ sk_A )
      = ( k1_wellord1 @ sk_C_2 @ sk_A ) )
    | ~ ( v2_wellord1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v2_wellord1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( sk_A = sk_B_2 )
    | ( ( k1_wellord1 @ ( k2_wellord1 @ sk_C_2 @ ( k1_wellord1 @ sk_C_2 @ sk_B_2 ) ) @ sk_A )
      = ( k1_wellord1 @ sk_C_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf(t20_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ ( k3_relat_1 @ B ) )
        & ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ A ) ) ) )).

thf('61',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X26 @ X27 ) ) @ X27 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t20_wellord1])).

thf(t13_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_wellord1 @ B @ A ) @ ( k3_relat_1 @ B ) ) ) )).

thf('62',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X24 @ X25 ) @ ( k3_relat_1 @ X24 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t13_wellord1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('63',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ ( k3_relat_1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_wellord1 @ ( k2_wellord1 @ X1 @ X0 ) @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf(dt_k2_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ) )).

thf('66',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ ( k2_wellord1 @ X1 @ X0 ) @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_2 @ sk_A ) @ ( k1_wellord1 @ sk_C_2 @ sk_B_2 ) )
    | ( sk_A = sk_B_2 )
    | ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['60','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_2 @ sk_A ) @ ( k1_wellord1 @ sk_C_2 @ sk_B_2 ) )
    | ( sk_A = sk_B_2 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_2 @ sk_A ) @ ( k1_wellord1 @ sk_C_2 @ sk_B_2 ) ) ),
    inference(simpl_trail,[status(thm)],['1','46'])).

thf('72',plain,(
    sk_A = sk_B_2 ),
    inference(clc,[status(thm)],['70','71'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('73',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('74',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    $false ),
    inference(demod,[status(thm)],['47','72','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bQAdn51V5i
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:39:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.37/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.61  % Solved by: fo/fo7.sh
% 0.37/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.61  % done 198 iterations in 0.165s
% 0.37/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.61  % SZS output start Refutation
% 0.37/0.61  thf(v4_relat_2_type, type, v4_relat_2: $i > $o).
% 0.37/0.61  thf(v1_relat_2_type, type, v1_relat_2: $i > $o).
% 0.37/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.61  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.37/0.61  thf(v6_relat_2_type, type, v6_relat_2: $i > $o).
% 0.37/0.61  thf(v8_relat_2_type, type, v8_relat_2: $i > $o).
% 0.37/0.61  thf(v1_wellord1_type, type, v1_wellord1: $i > $o).
% 0.37/0.61  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.37/0.61  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.37/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.61  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.37/0.61  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.37/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.61  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.37/0.61  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.37/0.61  thf(t37_wellord1, conjecture,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( v1_relat_1 @ C ) =>
% 0.37/0.61       ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.37/0.61           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) =>
% 0.37/0.61         ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.37/0.61           ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) ))).
% 0.37/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.61        ( ( v1_relat_1 @ C ) =>
% 0.37/0.61          ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.37/0.61              ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) =>
% 0.37/0.61            ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.37/0.61              ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) ) )),
% 0.37/0.61    inference('cnf.neg', [status(esa)], [t37_wellord1])).
% 0.37/0.61  thf('0', plain,
% 0.37/0.61      ((~ (r1_tarski @ (k1_wellord1 @ sk_C_2 @ sk_A) @ 
% 0.37/0.61           (k1_wellord1 @ sk_C_2 @ sk_B_2))
% 0.37/0.61        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_2))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('1', plain,
% 0.37/0.61      ((~ (r1_tarski @ (k1_wellord1 @ sk_C_2 @ sk_A) @ 
% 0.37/0.61           (k1_wellord1 @ sk_C_2 @ sk_B_2)))
% 0.37/0.61         <= (~
% 0.37/0.61             ((r1_tarski @ (k1_wellord1 @ sk_C_2 @ sk_A) @ 
% 0.37/0.61               (k1_wellord1 @ sk_C_2 @ sk_B_2))))),
% 0.37/0.61      inference('split', [status(esa)], ['0'])).
% 0.37/0.61  thf('2', plain,
% 0.37/0.61      (~
% 0.37/0.61       ((r1_tarski @ (k1_wellord1 @ sk_C_2 @ sk_A) @ 
% 0.37/0.61         (k1_wellord1 @ sk_C_2 @ sk_B_2))) | 
% 0.37/0.61       ~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_2))),
% 0.37/0.61      inference('split', [status(esa)], ['0'])).
% 0.37/0.61  thf('3', plain, ((r2_hidden @ sk_B_2 @ (k3_relat_1 @ sk_C_2))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('4', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_2))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(l4_wellord1, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( v1_relat_1 @ A ) =>
% 0.37/0.61       ( ( v6_relat_2 @ A ) <=>
% 0.37/0.61         ( ![B:$i,C:$i]:
% 0.37/0.61           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 0.37/0.61                ( r2_hidden @ C @ ( k3_relat_1 @ A ) ) & ( ( B ) != ( C ) ) & 
% 0.37/0.61                ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) & 
% 0.37/0.61                ( ~( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) ) ) ) ) ) ))).
% 0.37/0.61  thf('5', plain,
% 0.37/0.61      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.37/0.61         (~ (v6_relat_2 @ X21)
% 0.37/0.61          | ~ (r2_hidden @ X22 @ (k3_relat_1 @ X21))
% 0.37/0.61          | (r2_hidden @ (k4_tarski @ X23 @ X22) @ X21)
% 0.37/0.61          | (r2_hidden @ (k4_tarski @ X22 @ X23) @ X21)
% 0.37/0.61          | ((X22) = (X23))
% 0.37/0.61          | ~ (r2_hidden @ X23 @ (k3_relat_1 @ X21))
% 0.37/0.61          | ~ (v1_relat_1 @ X21))),
% 0.37/0.61      inference('cnf', [status(esa)], [l4_wellord1])).
% 0.37/0.61  thf('6', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (~ (v1_relat_1 @ sk_C_2)
% 0.37/0.61          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C_2))
% 0.37/0.61          | ((sk_A) = (X0))
% 0.37/0.61          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_2)
% 0.37/0.61          | (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ sk_C_2)
% 0.37/0.61          | ~ (v6_relat_2 @ sk_C_2))),
% 0.37/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.37/0.61  thf('7', plain, ((v1_relat_1 @ sk_C_2)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('8', plain, ((v1_relat_1 @ sk_C_2)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(d4_wellord1, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( v1_relat_1 @ A ) =>
% 0.37/0.61       ( ( v2_wellord1 @ A ) <=>
% 0.37/0.61         ( ( v1_relat_2 @ A ) & ( v8_relat_2 @ A ) & ( v4_relat_2 @ A ) & 
% 0.37/0.61           ( v6_relat_2 @ A ) & ( v1_wellord1 @ A ) ) ) ))).
% 0.37/0.61  thf('9', plain,
% 0.37/0.61      (![X16 : $i]:
% 0.37/0.61         (~ (v2_wellord1 @ X16) | (v6_relat_2 @ X16) | ~ (v1_relat_1 @ X16))),
% 0.37/0.61      inference('cnf', [status(esa)], [d4_wellord1])).
% 0.37/0.61  thf('10', plain, (((v6_relat_2 @ sk_C_2) | ~ (v2_wellord1 @ sk_C_2))),
% 0.37/0.61      inference('sup-', [status(thm)], ['8', '9'])).
% 0.37/0.61  thf('11', plain, ((v2_wellord1 @ sk_C_2)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('12', plain, ((v6_relat_2 @ sk_C_2)),
% 0.37/0.61      inference('demod', [status(thm)], ['10', '11'])).
% 0.37/0.61  thf('13', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C_2))
% 0.37/0.61          | ((sk_A) = (X0))
% 0.37/0.61          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_2)
% 0.37/0.61          | (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ sk_C_2))),
% 0.37/0.61      inference('demod', [status(thm)], ['6', '7', '12'])).
% 0.37/0.61  thf('14', plain,
% 0.37/0.61      (((r2_hidden @ (k4_tarski @ sk_B_2 @ sk_A) @ sk_C_2)
% 0.37/0.61        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_2)
% 0.37/0.61        | ((sk_A) = (sk_B_2)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['3', '13'])).
% 0.37/0.61  thf(d1_wellord1, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( v1_relat_1 @ A ) =>
% 0.37/0.61       ( ![B:$i,C:$i]:
% 0.37/0.61         ( ( ( C ) = ( k1_wellord1 @ A @ B ) ) <=>
% 0.37/0.61           ( ![D:$i]:
% 0.37/0.61             ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.61               ( ( ( D ) != ( B ) ) & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) ) ))).
% 0.37/0.61  thf('15', plain,
% 0.37/0.61      (![X11 : $i, X12 : $i, X13 : $i, X15 : $i]:
% 0.37/0.61         (((X13) != (k1_wellord1 @ X12 @ X11))
% 0.37/0.61          | (r2_hidden @ X15 @ X13)
% 0.37/0.61          | ~ (r2_hidden @ (k4_tarski @ X15 @ X11) @ X12)
% 0.37/0.61          | ((X15) = (X11))
% 0.37/0.61          | ~ (v1_relat_1 @ X12))),
% 0.37/0.61      inference('cnf', [status(esa)], [d1_wellord1])).
% 0.37/0.61  thf('16', plain,
% 0.37/0.61      (![X11 : $i, X12 : $i, X15 : $i]:
% 0.37/0.61         (~ (v1_relat_1 @ X12)
% 0.37/0.61          | ((X15) = (X11))
% 0.37/0.61          | ~ (r2_hidden @ (k4_tarski @ X15 @ X11) @ X12)
% 0.37/0.61          | (r2_hidden @ X15 @ (k1_wellord1 @ X12 @ X11)))),
% 0.37/0.61      inference('simplify', [status(thm)], ['15'])).
% 0.37/0.61  thf('17', plain,
% 0.37/0.61      ((((sk_A) = (sk_B_2))
% 0.37/0.61        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_2)
% 0.37/0.61        | (r2_hidden @ sk_B_2 @ (k1_wellord1 @ sk_C_2 @ sk_A))
% 0.37/0.61        | ((sk_B_2) = (sk_A))
% 0.37/0.61        | ~ (v1_relat_1 @ sk_C_2))),
% 0.37/0.61      inference('sup-', [status(thm)], ['14', '16'])).
% 0.37/0.61  thf('18', plain, ((v1_relat_1 @ sk_C_2)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('19', plain,
% 0.37/0.61      ((((sk_A) = (sk_B_2))
% 0.37/0.61        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_2)
% 0.37/0.61        | (r2_hidden @ sk_B_2 @ (k1_wellord1 @ sk_C_2 @ sk_A))
% 0.37/0.61        | ((sk_B_2) = (sk_A)))),
% 0.37/0.61      inference('demod', [status(thm)], ['17', '18'])).
% 0.37/0.61  thf('20', plain,
% 0.37/0.61      (((r2_hidden @ sk_B_2 @ (k1_wellord1 @ sk_C_2 @ sk_A))
% 0.37/0.61        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_2)
% 0.37/0.61        | ((sk_A) = (sk_B_2)))),
% 0.37/0.61      inference('simplify', [status(thm)], ['19'])).
% 0.37/0.61  thf('21', plain,
% 0.37/0.61      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_2))
% 0.37/0.61         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_2)))),
% 0.37/0.61      inference('split', [status(esa)], ['0'])).
% 0.37/0.61  thf('22', plain,
% 0.37/0.61      (((((sk_A) = (sk_B_2))
% 0.37/0.61         | (r2_hidden @ sk_B_2 @ (k1_wellord1 @ sk_C_2 @ sk_A))))
% 0.37/0.61         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_2)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['20', '21'])).
% 0.37/0.61  thf('23', plain,
% 0.37/0.61      (((r1_tarski @ (k1_wellord1 @ sk_C_2 @ sk_A) @ 
% 0.37/0.61         (k1_wellord1 @ sk_C_2 @ sk_B_2))
% 0.37/0.61        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_2))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('24', plain,
% 0.37/0.61      (((r1_tarski @ (k1_wellord1 @ sk_C_2 @ sk_A) @ 
% 0.37/0.61         (k1_wellord1 @ sk_C_2 @ sk_B_2)))
% 0.37/0.61         <= (((r1_tarski @ (k1_wellord1 @ sk_C_2 @ sk_A) @ 
% 0.37/0.61               (k1_wellord1 @ sk_C_2 @ sk_B_2))))),
% 0.37/0.61      inference('split', [status(esa)], ['23'])).
% 0.37/0.61  thf(d3_tarski, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( r1_tarski @ A @ B ) <=>
% 0.37/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.37/0.61  thf('25', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         (~ (r2_hidden @ X0 @ X1)
% 0.37/0.61          | (r2_hidden @ X0 @ X2)
% 0.37/0.61          | ~ (r1_tarski @ X1 @ X2))),
% 0.37/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.61  thf('26', plain,
% 0.37/0.61      ((![X0 : $i]:
% 0.37/0.61          ((r2_hidden @ X0 @ (k1_wellord1 @ sk_C_2 @ sk_B_2))
% 0.37/0.61           | ~ (r2_hidden @ X0 @ (k1_wellord1 @ sk_C_2 @ sk_A))))
% 0.37/0.61         <= (((r1_tarski @ (k1_wellord1 @ sk_C_2 @ sk_A) @ 
% 0.37/0.61               (k1_wellord1 @ sk_C_2 @ sk_B_2))))),
% 0.37/0.61      inference('sup-', [status(thm)], ['24', '25'])).
% 0.37/0.61  thf('27', plain,
% 0.37/0.61      (((((sk_A) = (sk_B_2))
% 0.37/0.61         | (r2_hidden @ sk_B_2 @ (k1_wellord1 @ sk_C_2 @ sk_B_2))))
% 0.37/0.61         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_2)) & 
% 0.37/0.61             ((r1_tarski @ (k1_wellord1 @ sk_C_2 @ sk_A) @ 
% 0.37/0.61               (k1_wellord1 @ sk_C_2 @ sk_B_2))))),
% 0.37/0.61      inference('sup-', [status(thm)], ['22', '26'])).
% 0.37/0.61  thf('28', plain,
% 0.37/0.61      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.61         (((X13) != (k1_wellord1 @ X12 @ X11))
% 0.37/0.61          | ((X14) != (X11))
% 0.37/0.61          | ~ (r2_hidden @ X14 @ X13)
% 0.37/0.61          | ~ (v1_relat_1 @ X12))),
% 0.37/0.61      inference('cnf', [status(esa)], [d1_wellord1])).
% 0.37/0.61  thf('29', plain,
% 0.37/0.61      (![X11 : $i, X12 : $i]:
% 0.37/0.61         (~ (v1_relat_1 @ X12)
% 0.37/0.61          | ~ (r2_hidden @ X11 @ (k1_wellord1 @ X12 @ X11)))),
% 0.37/0.61      inference('simplify', [status(thm)], ['28'])).
% 0.37/0.61  thf('30', plain,
% 0.37/0.61      (((((sk_A) = (sk_B_2)) | ~ (v1_relat_1 @ sk_C_2)))
% 0.37/0.61         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_2)) & 
% 0.37/0.61             ((r1_tarski @ (k1_wellord1 @ sk_C_2 @ sk_A) @ 
% 0.37/0.61               (k1_wellord1 @ sk_C_2 @ sk_B_2))))),
% 0.37/0.61      inference('sup-', [status(thm)], ['27', '29'])).
% 0.37/0.61  thf('31', plain, ((v1_relat_1 @ sk_C_2)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('32', plain,
% 0.37/0.61      ((((sk_A) = (sk_B_2)))
% 0.37/0.61         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_2)) & 
% 0.37/0.61             ((r1_tarski @ (k1_wellord1 @ sk_C_2 @ sk_A) @ 
% 0.37/0.61               (k1_wellord1 @ sk_C_2 @ sk_B_2))))),
% 0.37/0.61      inference('demod', [status(thm)], ['30', '31'])).
% 0.37/0.61  thf('33', plain,
% 0.37/0.61      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_2))
% 0.37/0.61         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_2)))),
% 0.37/0.61      inference('split', [status(esa)], ['0'])).
% 0.37/0.61  thf('34', plain,
% 0.37/0.61      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_A) @ sk_C_2))
% 0.37/0.61         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_2)) & 
% 0.37/0.61             ((r1_tarski @ (k1_wellord1 @ sk_C_2 @ sk_A) @ 
% 0.37/0.61               (k1_wellord1 @ sk_C_2 @ sk_B_2))))),
% 0.37/0.61      inference('sup-', [status(thm)], ['32', '33'])).
% 0.37/0.61  thf('35', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_2))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(l1_wellord1, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( v1_relat_1 @ A ) =>
% 0.37/0.61       ( ( v1_relat_2 @ A ) <=>
% 0.37/0.61         ( ![B:$i]:
% 0.37/0.61           ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) =>
% 0.37/0.61             ( r2_hidden @ ( k4_tarski @ B @ B ) @ A ) ) ) ) ))).
% 0.37/0.61  thf('36', plain,
% 0.37/0.61      (![X19 : $i, X20 : $i]:
% 0.37/0.61         (~ (v1_relat_2 @ X19)
% 0.37/0.61          | (r2_hidden @ (k4_tarski @ X20 @ X20) @ X19)
% 0.37/0.61          | ~ (r2_hidden @ X20 @ (k3_relat_1 @ X19))
% 0.37/0.61          | ~ (v1_relat_1 @ X19))),
% 0.37/0.61      inference('cnf', [status(esa)], [l1_wellord1])).
% 0.37/0.61  thf('37', plain,
% 0.37/0.61      ((~ (v1_relat_1 @ sk_C_2)
% 0.37/0.61        | (r2_hidden @ (k4_tarski @ sk_A @ sk_A) @ sk_C_2)
% 0.37/0.61        | ~ (v1_relat_2 @ sk_C_2))),
% 0.37/0.61      inference('sup-', [status(thm)], ['35', '36'])).
% 0.37/0.61  thf('38', plain, ((v1_relat_1 @ sk_C_2)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('39', plain, ((v1_relat_1 @ sk_C_2)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('40', plain,
% 0.37/0.61      (![X16 : $i]:
% 0.37/0.61         (~ (v2_wellord1 @ X16) | (v1_relat_2 @ X16) | ~ (v1_relat_1 @ X16))),
% 0.37/0.61      inference('cnf', [status(esa)], [d4_wellord1])).
% 0.37/0.61  thf('41', plain, (((v1_relat_2 @ sk_C_2) | ~ (v2_wellord1 @ sk_C_2))),
% 0.37/0.61      inference('sup-', [status(thm)], ['39', '40'])).
% 0.37/0.61  thf('42', plain, ((v2_wellord1 @ sk_C_2)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('43', plain, ((v1_relat_2 @ sk_C_2)),
% 0.37/0.61      inference('demod', [status(thm)], ['41', '42'])).
% 0.37/0.61  thf('44', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_A) @ sk_C_2)),
% 0.37/0.61      inference('demod', [status(thm)], ['37', '38', '43'])).
% 0.37/0.61  thf('45', plain,
% 0.37/0.61      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_2)) | 
% 0.37/0.61       ~
% 0.37/0.61       ((r1_tarski @ (k1_wellord1 @ sk_C_2 @ sk_A) @ 
% 0.37/0.61         (k1_wellord1 @ sk_C_2 @ sk_B_2)))),
% 0.37/0.61      inference('demod', [status(thm)], ['34', '44'])).
% 0.37/0.61  thf('46', plain,
% 0.37/0.61      (~
% 0.37/0.61       ((r1_tarski @ (k1_wellord1 @ sk_C_2 @ sk_A) @ 
% 0.37/0.61         (k1_wellord1 @ sk_C_2 @ sk_B_2)))),
% 0.37/0.61      inference('sat_resolution*', [status(thm)], ['2', '45'])).
% 0.37/0.61  thf('47', plain,
% 0.37/0.61      (~ (r1_tarski @ (k1_wellord1 @ sk_C_2 @ sk_A) @ 
% 0.37/0.61          (k1_wellord1 @ sk_C_2 @ sk_B_2))),
% 0.37/0.61      inference('simpl_trail', [status(thm)], ['1', '46'])).
% 0.37/0.61  thf('48', plain,
% 0.37/0.61      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_2))
% 0.37/0.61         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_2)))),
% 0.37/0.61      inference('split', [status(esa)], ['23'])).
% 0.37/0.61  thf('49', plain,
% 0.37/0.61      (![X11 : $i, X12 : $i, X15 : $i]:
% 0.37/0.61         (~ (v1_relat_1 @ X12)
% 0.37/0.61          | ((X15) = (X11))
% 0.37/0.61          | ~ (r2_hidden @ (k4_tarski @ X15 @ X11) @ X12)
% 0.37/0.61          | (r2_hidden @ X15 @ (k1_wellord1 @ X12 @ X11)))),
% 0.37/0.61      inference('simplify', [status(thm)], ['15'])).
% 0.37/0.61  thf('50', plain,
% 0.37/0.61      ((((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_2 @ sk_B_2))
% 0.37/0.61         | ((sk_A) = (sk_B_2))
% 0.37/0.61         | ~ (v1_relat_1 @ sk_C_2)))
% 0.37/0.61         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_2)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['48', '49'])).
% 0.37/0.61  thf('51', plain, ((v1_relat_1 @ sk_C_2)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('52', plain,
% 0.37/0.61      ((((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_2 @ sk_B_2))
% 0.37/0.61         | ((sk_A) = (sk_B_2))))
% 0.37/0.61         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_2)))),
% 0.37/0.61      inference('demod', [status(thm)], ['50', '51'])).
% 0.37/0.61  thf('53', plain,
% 0.37/0.61      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_2)) | 
% 0.37/0.61       ((r1_tarski @ (k1_wellord1 @ sk_C_2 @ sk_A) @ 
% 0.37/0.61         (k1_wellord1 @ sk_C_2 @ sk_B_2)))),
% 0.37/0.61      inference('split', [status(esa)], ['23'])).
% 0.37/0.61  thf('54', plain, (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_2))),
% 0.37/0.61      inference('sat_resolution*', [status(thm)], ['2', '45', '53'])).
% 0.37/0.61  thf('55', plain,
% 0.37/0.61      (((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_2 @ sk_B_2))
% 0.37/0.61        | ((sk_A) = (sk_B_2)))),
% 0.37/0.61      inference('simpl_trail', [status(thm)], ['52', '54'])).
% 0.37/0.61  thf(t35_wellord1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( v1_relat_1 @ C ) =>
% 0.37/0.61       ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k1_wellord1 @ C @ B ) ) ) =>
% 0.37/0.61         ( ( k1_wellord1 @ ( k2_wellord1 @ C @ ( k1_wellord1 @ C @ B ) ) @ A ) =
% 0.37/0.61           ( k1_wellord1 @ C @ A ) ) ) ))).
% 0.37/0.61  thf('56', plain,
% 0.37/0.61      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.37/0.61         (~ (v2_wellord1 @ X28)
% 0.37/0.61          | ~ (r2_hidden @ X29 @ (k1_wellord1 @ X28 @ X30))
% 0.37/0.61          | ((k1_wellord1 @ (k2_wellord1 @ X28 @ (k1_wellord1 @ X28 @ X30)) @ 
% 0.37/0.61              X29) = (k1_wellord1 @ X28 @ X29))
% 0.37/0.61          | ~ (v1_relat_1 @ X28))),
% 0.37/0.61      inference('cnf', [status(esa)], [t35_wellord1])).
% 0.37/0.61  thf('57', plain,
% 0.37/0.61      ((((sk_A) = (sk_B_2))
% 0.37/0.61        | ~ (v1_relat_1 @ sk_C_2)
% 0.37/0.61        | ((k1_wellord1 @ 
% 0.37/0.61            (k2_wellord1 @ sk_C_2 @ (k1_wellord1 @ sk_C_2 @ sk_B_2)) @ sk_A)
% 0.37/0.61            = (k1_wellord1 @ sk_C_2 @ sk_A))
% 0.37/0.61        | ~ (v2_wellord1 @ sk_C_2))),
% 0.37/0.61      inference('sup-', [status(thm)], ['55', '56'])).
% 0.37/0.61  thf('58', plain, ((v1_relat_1 @ sk_C_2)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('59', plain, ((v2_wellord1 @ sk_C_2)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('60', plain,
% 0.37/0.61      ((((sk_A) = (sk_B_2))
% 0.37/0.61        | ((k1_wellord1 @ 
% 0.37/0.61            (k2_wellord1 @ sk_C_2 @ (k1_wellord1 @ sk_C_2 @ sk_B_2)) @ sk_A)
% 0.37/0.61            = (k1_wellord1 @ sk_C_2 @ sk_A)))),
% 0.37/0.61      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.37/0.61  thf(t20_wellord1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( v1_relat_1 @ B ) =>
% 0.37/0.61       ( ( r1_tarski @
% 0.37/0.61           ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ ( k3_relat_1 @ B ) ) & 
% 0.37/0.61         ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ A ) ) ))).
% 0.37/0.61  thf('61', plain,
% 0.37/0.61      (![X26 : $i, X27 : $i]:
% 0.37/0.61         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X26 @ X27)) @ X27)
% 0.37/0.61          | ~ (v1_relat_1 @ X26))),
% 0.37/0.61      inference('cnf', [status(esa)], [t20_wellord1])).
% 0.37/0.61  thf(t13_wellord1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( v1_relat_1 @ B ) =>
% 0.37/0.61       ( r1_tarski @ ( k1_wellord1 @ B @ A ) @ ( k3_relat_1 @ B ) ) ))).
% 0.37/0.61  thf('62', plain,
% 0.37/0.61      (![X24 : $i, X25 : $i]:
% 0.37/0.61         ((r1_tarski @ (k1_wellord1 @ X24 @ X25) @ (k3_relat_1 @ X24))
% 0.37/0.61          | ~ (v1_relat_1 @ X24))),
% 0.37/0.61      inference('cnf', [status(esa)], [t13_wellord1])).
% 0.37/0.61  thf(t1_xboole_1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.37/0.61       ( r1_tarski @ A @ C ) ))).
% 0.37/0.61  thf('63', plain,
% 0.37/0.61      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.37/0.61         (~ (r1_tarski @ X7 @ X8)
% 0.37/0.61          | ~ (r1_tarski @ X8 @ X9)
% 0.37/0.61          | (r1_tarski @ X7 @ X9))),
% 0.37/0.61      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.37/0.61  thf('64', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         (~ (v1_relat_1 @ X0)
% 0.37/0.61          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 0.37/0.61          | ~ (r1_tarski @ (k3_relat_1 @ X0) @ X2))),
% 0.37/0.61      inference('sup-', [status(thm)], ['62', '63'])).
% 0.37/0.61  thf('65', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         (~ (v1_relat_1 @ X1)
% 0.37/0.61          | (r1_tarski @ (k1_wellord1 @ (k2_wellord1 @ X1 @ X0) @ X2) @ X0)
% 0.37/0.61          | ~ (v1_relat_1 @ (k2_wellord1 @ X1 @ X0)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['61', '64'])).
% 0.37/0.61  thf(dt_k2_wellord1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ))).
% 0.37/0.61  thf('66', plain,
% 0.37/0.61      (![X17 : $i, X18 : $i]:
% 0.37/0.61         (~ (v1_relat_1 @ X17) | (v1_relat_1 @ (k2_wellord1 @ X17 @ X18)))),
% 0.37/0.61      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.37/0.61  thf('67', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         ((r1_tarski @ (k1_wellord1 @ (k2_wellord1 @ X1 @ X0) @ X2) @ X0)
% 0.37/0.61          | ~ (v1_relat_1 @ X1))),
% 0.37/0.61      inference('clc', [status(thm)], ['65', '66'])).
% 0.37/0.61  thf('68', plain,
% 0.37/0.61      (((r1_tarski @ (k1_wellord1 @ sk_C_2 @ sk_A) @ 
% 0.37/0.61         (k1_wellord1 @ sk_C_2 @ sk_B_2))
% 0.37/0.61        | ((sk_A) = (sk_B_2))
% 0.37/0.61        | ~ (v1_relat_1 @ sk_C_2))),
% 0.37/0.61      inference('sup+', [status(thm)], ['60', '67'])).
% 0.37/0.61  thf('69', plain, ((v1_relat_1 @ sk_C_2)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('70', plain,
% 0.37/0.61      (((r1_tarski @ (k1_wellord1 @ sk_C_2 @ sk_A) @ 
% 0.37/0.61         (k1_wellord1 @ sk_C_2 @ sk_B_2))
% 0.37/0.61        | ((sk_A) = (sk_B_2)))),
% 0.37/0.61      inference('demod', [status(thm)], ['68', '69'])).
% 0.37/0.61  thf('71', plain,
% 0.37/0.61      (~ (r1_tarski @ (k1_wellord1 @ sk_C_2 @ sk_A) @ 
% 0.37/0.61          (k1_wellord1 @ sk_C_2 @ sk_B_2))),
% 0.37/0.61      inference('simpl_trail', [status(thm)], ['1', '46'])).
% 0.37/0.61  thf('72', plain, (((sk_A) = (sk_B_2))),
% 0.37/0.61      inference('clc', [status(thm)], ['70', '71'])).
% 0.37/0.61  thf(d10_xboole_0, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.61  thf('73', plain,
% 0.37/0.61      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.37/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.61  thf('74', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.37/0.61      inference('simplify', [status(thm)], ['73'])).
% 0.37/0.61  thf('75', plain, ($false),
% 0.37/0.61      inference('demod', [status(thm)], ['47', '72', '74'])).
% 0.37/0.61  
% 0.37/0.61  % SZS output end Refutation
% 0.37/0.61  
% 0.37/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
