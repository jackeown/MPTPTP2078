%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.i77WMSQjfA

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:33 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 351 expanded)
%              Number of leaves         :   31 ( 106 expanded)
%              Depth                    :   22
%              Number of atoms          : 1096 (5015 expanded)
%              Number of equality atoms :   35 (  89 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(v6_relat_2_type,type,(
    v6_relat_2: $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_wellord1_type,type,(
    v1_wellord1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(sk_C_4_type,type,(
    sk_C_4: $i )).

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
    ( ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_2 ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_2 ) )
   <= ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_2 ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_4 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
    r2_hidden @ sk_B_2 @ ( k3_relat_1 @ sk_C_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_4 ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v6_relat_2 @ X13 )
      | ~ ( r2_hidden @ X14 @ ( k3_relat_1 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ X15 @ X14 ) @ X13 )
      | ( r2_hidden @ ( k4_tarski @ X14 @ X15 ) @ X13 )
      | ( X14 = X15 )
      | ~ ( r2_hidden @ X15 @ ( k3_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l4_wellord1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_4 )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_C_4 ) )
      | ( sk_A = X0 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_4 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ sk_A ) @ sk_C_4 )
      | ~ ( v6_relat_2 @ sk_C_4 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_relat_1 @ sk_C_4 ),
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
    ! [X10: $i] :
      ( ~ ( v2_wellord1 @ X10 )
      | ( v6_relat_2 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('10',plain,
    ( ( v6_relat_2 @ sk_C_4 )
    | ~ ( v2_wellord1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_wellord1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v6_relat_2 @ sk_C_4 ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_C_4 ) )
      | ( sk_A = X0 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_4 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ sk_A ) @ sk_C_4 ) ) ),
    inference(demod,[status(thm)],['6','7','12'])).

thf('14',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B_2 @ sk_A ) @ sk_C_4 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_4 )
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
    ! [X5: $i,X6: $i,X7: $i,X9: $i] :
      ( ( X7
       != ( k1_wellord1 @ X6 @ X5 ) )
      | ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X5 ) @ X6 )
      | ( X9 = X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('16',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( X9 = X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X5 ) @ X6 )
      | ( r2_hidden @ X9 @ ( k1_wellord1 @ X6 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( sk_A = sk_B_2 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_4 )
    | ( r2_hidden @ sk_B_2 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) )
    | ( sk_B_2 = sk_A )
    | ~ ( v1_relat_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( sk_A = sk_B_2 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_4 )
    | ( r2_hidden @ sk_B_2 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) )
    | ( sk_B_2 = sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r2_hidden @ sk_B_2 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_4 )
    | ( sk_A = sk_B_2 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_4 )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_4 ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ( ( sk_A = sk_B_2 )
      | ( r2_hidden @ sk_B_2 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_2 ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_2 ) )
   <= ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_2 ) ) ),
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
        ( ( r2_hidden @ X0 @ ( k1_wellord1 @ sk_C_4 @ sk_B_2 ) )
        | ~ ( r2_hidden @ X0 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) ) )
   <= ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( sk_A = sk_B_2 )
      | ( r2_hidden @ sk_B_2 @ ( k1_wellord1 @ sk_C_4 @ sk_B_2 ) ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_4 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['22','26'])).

thf('28',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X7
       != ( k1_wellord1 @ X6 @ X5 ) )
      | ( X8 != X5 )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('29',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( r2_hidden @ X5 @ ( k1_wellord1 @ X6 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( ( sk_A = sk_B_2 )
      | ~ ( v1_relat_1 @ sk_C_4 ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_4 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_A = sk_B_2 )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_4 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_4 )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_4 ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_A ) @ sk_C_4 )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_4 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v1_relat_2 @ A )
      <=> ! [B: $i] :
            ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
           => ( r2_hidden @ ( k4_tarski @ B @ B ) @ A ) ) ) ) )).

thf('36',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_2 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ X12 @ X12 ) @ X11 )
      | ~ ( r2_hidden @ X12 @ ( k3_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l1_wellord1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_C_4 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_A ) @ sk_C_4 )
    | ~ ( v1_relat_2 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X10: $i] :
      ( ~ ( v2_wellord1 @ X10 )
      | ( v1_relat_2 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('41',plain,
    ( ( v1_relat_2 @ sk_C_4 )
    | ~ ( v2_wellord1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_wellord1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_relat_2 @ sk_C_4 ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_A ) @ sk_C_4 ),
    inference(demod,[status(thm)],['37','38','43'])).

thf('45',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_4 )
    | ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['34','44'])).

thf('46',plain,(
    ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_2 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','45'])).

thf('47',plain,(
    ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_2 ) ) ),
    inference(simpl_trail,[status(thm)],['1','46'])).

thf('48',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_4 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_4 ) ),
    inference(split,[status(esa)],['23'])).

thf('49',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( X9 = X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X5 ) @ X6 )
      | ( r2_hidden @ X9 @ ( k1_wellord1 @ X6 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('50',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_4 @ sk_B_2 ) )
      | ( sk_A = sk_B_2 )
      | ~ ( v1_relat_1 @ sk_C_4 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_4 @ sk_B_2 ) )
      | ( sk_A = sk_B_2 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_4 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_4 )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['23'])).

thf('54',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_4 ),
    inference('sat_resolution*',[status(thm)],['2','45','53'])).

thf('55',plain,
    ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_4 @ sk_B_2 ) )
    | ( sk_A = sk_B_2 ) ),
    inference(simpl_trail,[status(thm)],['52','54'])).

thf('56',plain,(
    r2_hidden @ sk_B_2 @ ( k3_relat_1 @ sk_C_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( r1_tarski @ A @ ( k3_relat_1 @ B ) )
          & ( v2_wellord1 @ B ) )
       => ( ~ ( ! [C: $i] :
                  ~ ( ( A
                      = ( k1_wellord1 @ B @ C ) )
                    & ( r2_hidden @ C @ ( k3_relat_1 @ B ) ) )
              & ( A
               != ( k3_relat_1 @ B ) ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ A )
             => ! [D: $i] :
                  ( ( r2_hidden @ ( k4_tarski @ D @ C ) @ B )
                 => ( r2_hidden @ D @ A ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
    <=> ( ( r2_hidden @ C @ ( k3_relat_1 @ B ) )
        & ( A
          = ( k1_wellord1 @ B @ C ) ) ) ) )).

thf('57',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 @ X21 )
      | ( X21
       != ( k1_wellord1 @ X19 @ X18 ) )
      | ~ ( r2_hidden @ X18 @ ( k3_relat_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('58',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k3_relat_1 @ X19 ) )
      | ( zip_tseitin_0 @ X18 @ X19 @ ( k1_wellord1 @ X19 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    zip_tseitin_0 @ sk_B_2 @ sk_C_4 @ ( k1_wellord1 @ sk_C_4 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf(t13_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_wellord1 @ B @ A ) @ ( k3_relat_1 @ B ) ) ) )).

thf('60',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X16 @ X17 ) @ ( k3_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t13_wellord1])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
    <=> ( ( r2_hidden @ C @ A )
       => ! [D: $i] :
            ( ( r2_hidden @ ( k4_tarski @ D @ C ) @ B )
           => ( r2_hidden @ D @ A ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( v2_wellord1 @ B )
          & ( r1_tarski @ A @ ( k3_relat_1 @ B ) ) )
       => ( ~ ( ( A
               != ( k3_relat_1 @ B ) )
              & ! [C: $i] :
                  ~ ( zip_tseitin_0 @ C @ B @ A ) )
        <=> ! [C: $i] :
              ( zip_tseitin_1 @ C @ B @ A ) ) ) ) )).

thf('61',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( v2_wellord1 @ X27 )
      | ~ ( r1_tarski @ X28 @ ( k3_relat_1 @ X27 ) )
      | ~ ( zip_tseitin_0 @ X29 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X30 @ X27 @ X28 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X2 @ X0 @ ( k1_wellord1 @ X0 @ X1 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X0 @ ( k1_wellord1 @ X0 @ X1 ) )
      | ~ ( v2_wellord1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v2_wellord1 @ X0 )
      | ~ ( zip_tseitin_0 @ X3 @ X0 @ ( k1_wellord1 @ X0 @ X1 ) )
      | ( zip_tseitin_1 @ X2 @ X0 @ ( k1_wellord1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_4 )
      | ( zip_tseitin_1 @ X0 @ sk_C_4 @ ( k1_wellord1 @ sk_C_4 @ sk_B_2 ) )
      | ~ ( v2_wellord1 @ sk_C_4 ) ) ),
    inference('sup-',[status(thm)],['59','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v2_wellord1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ X0 @ sk_C_4 @ ( k1_wellord1 @ sk_C_4 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('69',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X7
       != ( k1_wellord1 @ X6 @ X5 ) )
      | ( r2_hidden @ ( k4_tarski @ X8 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('70',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k1_wellord1 @ X6 @ X5 ) )
      | ( r2_hidden @ ( k4_tarski @ X8 @ X5 ) @ X6 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_wellord1 @ X1 @ X0 ) ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['68','70'])).

thf('72',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( r2_hidden @ ( k4_tarski @ X24 @ X22 ) @ X25 )
      | ( r2_hidden @ X24 @ X23 )
      | ~ ( zip_tseitin_1 @ X22 @ X25 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( zip_tseitin_1 @ X1 @ X0 @ X3 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) @ X3 )
      | ~ ( r2_hidden @ X1 @ X3 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_wellord1 @ sk_C_4 @ sk_B_2 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_wellord1 @ sk_C_4 @ X0 ) ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_2 ) )
      | ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ sk_C_4 ) ) ),
    inference('sup-',[status(thm)],['67','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_wellord1 @ sk_C_4 @ sk_B_2 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_wellord1 @ sk_C_4 @ X0 ) ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_2 ) )
      | ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( sk_A = sk_B_2 )
      | ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['55','76'])).

thf('78',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('79',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_2 ) )
    | ( sk_A = sk_B_2 )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( sk_A = sk_B_2 )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_2 ) ) ),
    inference(simpl_trail,[status(thm)],['1','46'])).

thf('82',plain,(
    sk_A = sk_B_2 ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('84',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    $false ),
    inference(demod,[status(thm)],['47','82','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.i77WMSQjfA
% 0.13/0.37  % Computer   : n005.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 18:45:03 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.69/0.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.69/0.89  % Solved by: fo/fo7.sh
% 0.69/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.89  % done 403 iterations in 0.406s
% 0.69/0.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.69/0.89  % SZS output start Refutation
% 0.69/0.89  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.69/0.89  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.69/0.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.69/0.89  thf(v8_relat_2_type, type, v8_relat_2: $i > $o).
% 0.69/0.89  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.69/0.89  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.69/0.89  thf(v6_relat_2_type, type, v6_relat_2: $i > $o).
% 0.69/0.89  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.69/0.89  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.69/0.89  thf(v1_wellord1_type, type, v1_wellord1: $i > $o).
% 0.69/0.89  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.69/0.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.69/0.89  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.69/0.89  thf(v1_relat_2_type, type, v1_relat_2: $i > $o).
% 0.69/0.89  thf(v4_relat_2_type, type, v4_relat_2: $i > $o).
% 0.69/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.89  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.69/0.89  thf(sk_C_4_type, type, sk_C_4: $i).
% 0.69/0.89  thf(t37_wellord1, conjecture,
% 0.69/0.89    (![A:$i,B:$i,C:$i]:
% 0.69/0.89     ( ( v1_relat_1 @ C ) =>
% 0.69/0.89       ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.69/0.89           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) =>
% 0.69/0.89         ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.69/0.89           ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) ))).
% 0.69/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.89    (~( ![A:$i,B:$i,C:$i]:
% 0.69/0.89        ( ( v1_relat_1 @ C ) =>
% 0.69/0.89          ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.69/0.89              ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) =>
% 0.69/0.89            ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.69/0.89              ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) ) )),
% 0.69/0.89    inference('cnf.neg', [status(esa)], [t37_wellord1])).
% 0.69/0.89  thf('0', plain,
% 0.69/0.89      ((~ (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.69/0.89           (k1_wellord1 @ sk_C_4 @ sk_B_2))
% 0.69/0.89        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_4))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('1', plain,
% 0.69/0.89      ((~ (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.69/0.89           (k1_wellord1 @ sk_C_4 @ sk_B_2)))
% 0.69/0.89         <= (~
% 0.69/0.89             ((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.69/0.89               (k1_wellord1 @ sk_C_4 @ sk_B_2))))),
% 0.69/0.89      inference('split', [status(esa)], ['0'])).
% 0.69/0.89  thf('2', plain,
% 0.69/0.89      (~
% 0.69/0.89       ((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.69/0.89         (k1_wellord1 @ sk_C_4 @ sk_B_2))) | 
% 0.69/0.89       ~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_4))),
% 0.69/0.89      inference('split', [status(esa)], ['0'])).
% 0.69/0.89  thf('3', plain, ((r2_hidden @ sk_B_2 @ (k3_relat_1 @ sk_C_4))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('4', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_4))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf(l4_wellord1, axiom,
% 0.69/0.89    (![A:$i]:
% 0.69/0.89     ( ( v1_relat_1 @ A ) =>
% 0.69/0.89       ( ( v6_relat_2 @ A ) <=>
% 0.69/0.89         ( ![B:$i,C:$i]:
% 0.69/0.89           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 0.69/0.89                ( r2_hidden @ C @ ( k3_relat_1 @ A ) ) & ( ( B ) != ( C ) ) & 
% 0.69/0.89                ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) & 
% 0.69/0.89                ( ~( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) ) ) ) ) ) ))).
% 0.69/0.89  thf('5', plain,
% 0.69/0.89      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.69/0.89         (~ (v6_relat_2 @ X13)
% 0.69/0.89          | ~ (r2_hidden @ X14 @ (k3_relat_1 @ X13))
% 0.69/0.89          | (r2_hidden @ (k4_tarski @ X15 @ X14) @ X13)
% 0.69/0.89          | (r2_hidden @ (k4_tarski @ X14 @ X15) @ X13)
% 0.69/0.89          | ((X14) = (X15))
% 0.69/0.89          | ~ (r2_hidden @ X15 @ (k3_relat_1 @ X13))
% 0.69/0.89          | ~ (v1_relat_1 @ X13))),
% 0.69/0.89      inference('cnf', [status(esa)], [l4_wellord1])).
% 0.69/0.89  thf('6', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (~ (v1_relat_1 @ sk_C_4)
% 0.69/0.89          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C_4))
% 0.69/0.89          | ((sk_A) = (X0))
% 0.69/0.89          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_4)
% 0.69/0.89          | (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ sk_C_4)
% 0.69/0.89          | ~ (v6_relat_2 @ sk_C_4))),
% 0.69/0.89      inference('sup-', [status(thm)], ['4', '5'])).
% 0.69/0.89  thf('7', plain, ((v1_relat_1 @ sk_C_4)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('8', plain, ((v1_relat_1 @ sk_C_4)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf(d4_wellord1, axiom,
% 0.69/0.89    (![A:$i]:
% 0.69/0.89     ( ( v1_relat_1 @ A ) =>
% 0.69/0.89       ( ( v2_wellord1 @ A ) <=>
% 0.69/0.89         ( ( v1_relat_2 @ A ) & ( v8_relat_2 @ A ) & ( v4_relat_2 @ A ) & 
% 0.69/0.89           ( v6_relat_2 @ A ) & ( v1_wellord1 @ A ) ) ) ))).
% 0.69/0.89  thf('9', plain,
% 0.69/0.89      (![X10 : $i]:
% 0.69/0.89         (~ (v2_wellord1 @ X10) | (v6_relat_2 @ X10) | ~ (v1_relat_1 @ X10))),
% 0.69/0.89      inference('cnf', [status(esa)], [d4_wellord1])).
% 0.69/0.89  thf('10', plain, (((v6_relat_2 @ sk_C_4) | ~ (v2_wellord1 @ sk_C_4))),
% 0.69/0.89      inference('sup-', [status(thm)], ['8', '9'])).
% 0.69/0.89  thf('11', plain, ((v2_wellord1 @ sk_C_4)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('12', plain, ((v6_relat_2 @ sk_C_4)),
% 0.69/0.89      inference('demod', [status(thm)], ['10', '11'])).
% 0.69/0.89  thf('13', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C_4))
% 0.69/0.89          | ((sk_A) = (X0))
% 0.69/0.89          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_4)
% 0.69/0.89          | (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ sk_C_4))),
% 0.69/0.89      inference('demod', [status(thm)], ['6', '7', '12'])).
% 0.69/0.89  thf('14', plain,
% 0.69/0.89      (((r2_hidden @ (k4_tarski @ sk_B_2 @ sk_A) @ sk_C_4)
% 0.69/0.89        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_4)
% 0.69/0.89        | ((sk_A) = (sk_B_2)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['3', '13'])).
% 0.69/0.89  thf(d1_wellord1, axiom,
% 0.69/0.89    (![A:$i]:
% 0.69/0.89     ( ( v1_relat_1 @ A ) =>
% 0.69/0.89       ( ![B:$i,C:$i]:
% 0.69/0.89         ( ( ( C ) = ( k1_wellord1 @ A @ B ) ) <=>
% 0.69/0.89           ( ![D:$i]:
% 0.69/0.89             ( ( r2_hidden @ D @ C ) <=>
% 0.69/0.89               ( ( ( D ) != ( B ) ) & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) ) ))).
% 0.69/0.89  thf('15', plain,
% 0.69/0.89      (![X5 : $i, X6 : $i, X7 : $i, X9 : $i]:
% 0.69/0.89         (((X7) != (k1_wellord1 @ X6 @ X5))
% 0.69/0.89          | (r2_hidden @ X9 @ X7)
% 0.69/0.89          | ~ (r2_hidden @ (k4_tarski @ X9 @ X5) @ X6)
% 0.69/0.89          | ((X9) = (X5))
% 0.69/0.89          | ~ (v1_relat_1 @ X6))),
% 0.69/0.89      inference('cnf', [status(esa)], [d1_wellord1])).
% 0.69/0.89  thf('16', plain,
% 0.69/0.89      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.69/0.89         (~ (v1_relat_1 @ X6)
% 0.69/0.89          | ((X9) = (X5))
% 0.69/0.89          | ~ (r2_hidden @ (k4_tarski @ X9 @ X5) @ X6)
% 0.69/0.89          | (r2_hidden @ X9 @ (k1_wellord1 @ X6 @ X5)))),
% 0.69/0.89      inference('simplify', [status(thm)], ['15'])).
% 0.69/0.89  thf('17', plain,
% 0.69/0.89      ((((sk_A) = (sk_B_2))
% 0.69/0.89        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_4)
% 0.69/0.89        | (r2_hidden @ sk_B_2 @ (k1_wellord1 @ sk_C_4 @ sk_A))
% 0.69/0.89        | ((sk_B_2) = (sk_A))
% 0.69/0.89        | ~ (v1_relat_1 @ sk_C_4))),
% 0.69/0.89      inference('sup-', [status(thm)], ['14', '16'])).
% 0.69/0.89  thf('18', plain, ((v1_relat_1 @ sk_C_4)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('19', plain,
% 0.69/0.89      ((((sk_A) = (sk_B_2))
% 0.69/0.89        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_4)
% 0.69/0.89        | (r2_hidden @ sk_B_2 @ (k1_wellord1 @ sk_C_4 @ sk_A))
% 0.69/0.89        | ((sk_B_2) = (sk_A)))),
% 0.69/0.89      inference('demod', [status(thm)], ['17', '18'])).
% 0.69/0.89  thf('20', plain,
% 0.69/0.89      (((r2_hidden @ sk_B_2 @ (k1_wellord1 @ sk_C_4 @ sk_A))
% 0.69/0.89        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_4)
% 0.69/0.89        | ((sk_A) = (sk_B_2)))),
% 0.69/0.89      inference('simplify', [status(thm)], ['19'])).
% 0.69/0.89  thf('21', plain,
% 0.69/0.89      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_4))
% 0.69/0.89         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_4)))),
% 0.69/0.89      inference('split', [status(esa)], ['0'])).
% 0.69/0.89  thf('22', plain,
% 0.69/0.89      (((((sk_A) = (sk_B_2))
% 0.69/0.89         | (r2_hidden @ sk_B_2 @ (k1_wellord1 @ sk_C_4 @ sk_A))))
% 0.69/0.89         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_4)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['20', '21'])).
% 0.69/0.89  thf('23', plain,
% 0.69/0.89      (((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.69/0.89         (k1_wellord1 @ sk_C_4 @ sk_B_2))
% 0.69/0.89        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_4))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('24', plain,
% 0.69/0.89      (((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.69/0.89         (k1_wellord1 @ sk_C_4 @ sk_B_2)))
% 0.69/0.89         <= (((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.69/0.89               (k1_wellord1 @ sk_C_4 @ sk_B_2))))),
% 0.69/0.89      inference('split', [status(esa)], ['23'])).
% 0.69/0.89  thf(d3_tarski, axiom,
% 0.69/0.89    (![A:$i,B:$i]:
% 0.69/0.89     ( ( r1_tarski @ A @ B ) <=>
% 0.69/0.89       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.69/0.89  thf('25', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.89         (~ (r2_hidden @ X0 @ X1)
% 0.69/0.89          | (r2_hidden @ X0 @ X2)
% 0.69/0.89          | ~ (r1_tarski @ X1 @ X2))),
% 0.69/0.89      inference('cnf', [status(esa)], [d3_tarski])).
% 0.69/0.89  thf('26', plain,
% 0.69/0.89      ((![X0 : $i]:
% 0.69/0.89          ((r2_hidden @ X0 @ (k1_wellord1 @ sk_C_4 @ sk_B_2))
% 0.69/0.89           | ~ (r2_hidden @ X0 @ (k1_wellord1 @ sk_C_4 @ sk_A))))
% 0.69/0.89         <= (((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.69/0.89               (k1_wellord1 @ sk_C_4 @ sk_B_2))))),
% 0.69/0.89      inference('sup-', [status(thm)], ['24', '25'])).
% 0.69/0.89  thf('27', plain,
% 0.69/0.89      (((((sk_A) = (sk_B_2))
% 0.69/0.89         | (r2_hidden @ sk_B_2 @ (k1_wellord1 @ sk_C_4 @ sk_B_2))))
% 0.69/0.89         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_4)) & 
% 0.69/0.89             ((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.69/0.89               (k1_wellord1 @ sk_C_4 @ sk_B_2))))),
% 0.69/0.89      inference('sup-', [status(thm)], ['22', '26'])).
% 0.69/0.89  thf('28', plain,
% 0.69/0.89      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.69/0.89         (((X7) != (k1_wellord1 @ X6 @ X5))
% 0.69/0.89          | ((X8) != (X5))
% 0.69/0.89          | ~ (r2_hidden @ X8 @ X7)
% 0.69/0.89          | ~ (v1_relat_1 @ X6))),
% 0.69/0.89      inference('cnf', [status(esa)], [d1_wellord1])).
% 0.69/0.89  thf('29', plain,
% 0.69/0.89      (![X5 : $i, X6 : $i]:
% 0.69/0.89         (~ (v1_relat_1 @ X6) | ~ (r2_hidden @ X5 @ (k1_wellord1 @ X6 @ X5)))),
% 0.69/0.89      inference('simplify', [status(thm)], ['28'])).
% 0.69/0.89  thf('30', plain,
% 0.69/0.89      (((((sk_A) = (sk_B_2)) | ~ (v1_relat_1 @ sk_C_4)))
% 0.69/0.89         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_4)) & 
% 0.69/0.89             ((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.69/0.89               (k1_wellord1 @ sk_C_4 @ sk_B_2))))),
% 0.69/0.89      inference('sup-', [status(thm)], ['27', '29'])).
% 0.69/0.89  thf('31', plain, ((v1_relat_1 @ sk_C_4)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('32', plain,
% 0.69/0.89      ((((sk_A) = (sk_B_2)))
% 0.69/0.89         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_4)) & 
% 0.69/0.89             ((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.69/0.89               (k1_wellord1 @ sk_C_4 @ sk_B_2))))),
% 0.69/0.89      inference('demod', [status(thm)], ['30', '31'])).
% 0.69/0.89  thf('33', plain,
% 0.69/0.89      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_4))
% 0.69/0.89         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_4)))),
% 0.69/0.89      inference('split', [status(esa)], ['0'])).
% 0.69/0.89  thf('34', plain,
% 0.69/0.89      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_A) @ sk_C_4))
% 0.69/0.89         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_4)) & 
% 0.69/0.89             ((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.69/0.89               (k1_wellord1 @ sk_C_4 @ sk_B_2))))),
% 0.69/0.89      inference('sup-', [status(thm)], ['32', '33'])).
% 0.69/0.89  thf('35', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_4))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf(l1_wellord1, axiom,
% 0.69/0.89    (![A:$i]:
% 0.69/0.89     ( ( v1_relat_1 @ A ) =>
% 0.69/0.89       ( ( v1_relat_2 @ A ) <=>
% 0.69/0.89         ( ![B:$i]:
% 0.69/0.89           ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) =>
% 0.69/0.89             ( r2_hidden @ ( k4_tarski @ B @ B ) @ A ) ) ) ) ))).
% 0.69/0.89  thf('36', plain,
% 0.69/0.89      (![X11 : $i, X12 : $i]:
% 0.69/0.89         (~ (v1_relat_2 @ X11)
% 0.69/0.89          | (r2_hidden @ (k4_tarski @ X12 @ X12) @ X11)
% 0.69/0.89          | ~ (r2_hidden @ X12 @ (k3_relat_1 @ X11))
% 0.69/0.89          | ~ (v1_relat_1 @ X11))),
% 0.69/0.89      inference('cnf', [status(esa)], [l1_wellord1])).
% 0.69/0.89  thf('37', plain,
% 0.69/0.89      ((~ (v1_relat_1 @ sk_C_4)
% 0.69/0.89        | (r2_hidden @ (k4_tarski @ sk_A @ sk_A) @ sk_C_4)
% 0.69/0.89        | ~ (v1_relat_2 @ sk_C_4))),
% 0.69/0.89      inference('sup-', [status(thm)], ['35', '36'])).
% 0.69/0.89  thf('38', plain, ((v1_relat_1 @ sk_C_4)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('39', plain, ((v1_relat_1 @ sk_C_4)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('40', plain,
% 0.69/0.89      (![X10 : $i]:
% 0.69/0.89         (~ (v2_wellord1 @ X10) | (v1_relat_2 @ X10) | ~ (v1_relat_1 @ X10))),
% 0.69/0.89      inference('cnf', [status(esa)], [d4_wellord1])).
% 0.69/0.89  thf('41', plain, (((v1_relat_2 @ sk_C_4) | ~ (v2_wellord1 @ sk_C_4))),
% 0.69/0.89      inference('sup-', [status(thm)], ['39', '40'])).
% 0.69/0.89  thf('42', plain, ((v2_wellord1 @ sk_C_4)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('43', plain, ((v1_relat_2 @ sk_C_4)),
% 0.69/0.89      inference('demod', [status(thm)], ['41', '42'])).
% 0.69/0.89  thf('44', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_A) @ sk_C_4)),
% 0.69/0.89      inference('demod', [status(thm)], ['37', '38', '43'])).
% 0.69/0.89  thf('45', plain,
% 0.69/0.89      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_4)) | 
% 0.69/0.89       ~
% 0.69/0.89       ((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.69/0.89         (k1_wellord1 @ sk_C_4 @ sk_B_2)))),
% 0.69/0.89      inference('demod', [status(thm)], ['34', '44'])).
% 0.69/0.89  thf('46', plain,
% 0.69/0.89      (~
% 0.69/0.89       ((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.69/0.89         (k1_wellord1 @ sk_C_4 @ sk_B_2)))),
% 0.69/0.89      inference('sat_resolution*', [status(thm)], ['2', '45'])).
% 0.69/0.89  thf('47', plain,
% 0.69/0.89      (~ (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.69/0.89          (k1_wellord1 @ sk_C_4 @ sk_B_2))),
% 0.69/0.89      inference('simpl_trail', [status(thm)], ['1', '46'])).
% 0.69/0.89  thf('48', plain,
% 0.69/0.89      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_4))
% 0.69/0.89         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_4)))),
% 0.69/0.89      inference('split', [status(esa)], ['23'])).
% 0.69/0.89  thf('49', plain,
% 0.69/0.89      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.69/0.89         (~ (v1_relat_1 @ X6)
% 0.69/0.89          | ((X9) = (X5))
% 0.69/0.89          | ~ (r2_hidden @ (k4_tarski @ X9 @ X5) @ X6)
% 0.69/0.89          | (r2_hidden @ X9 @ (k1_wellord1 @ X6 @ X5)))),
% 0.69/0.89      inference('simplify', [status(thm)], ['15'])).
% 0.69/0.89  thf('50', plain,
% 0.69/0.89      ((((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_4 @ sk_B_2))
% 0.69/0.89         | ((sk_A) = (sk_B_2))
% 0.69/0.89         | ~ (v1_relat_1 @ sk_C_4)))
% 0.69/0.89         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_4)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['48', '49'])).
% 0.69/0.89  thf('51', plain, ((v1_relat_1 @ sk_C_4)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('52', plain,
% 0.69/0.89      ((((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_4 @ sk_B_2))
% 0.69/0.89         | ((sk_A) = (sk_B_2))))
% 0.69/0.89         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_4)))),
% 0.69/0.89      inference('demod', [status(thm)], ['50', '51'])).
% 0.69/0.89  thf('53', plain,
% 0.69/0.89      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_4)) | 
% 0.69/0.89       ((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.69/0.89         (k1_wellord1 @ sk_C_4 @ sk_B_2)))),
% 0.69/0.89      inference('split', [status(esa)], ['23'])).
% 0.69/0.89  thf('54', plain, (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_4))),
% 0.69/0.89      inference('sat_resolution*', [status(thm)], ['2', '45', '53'])).
% 0.69/0.89  thf('55', plain,
% 0.69/0.89      (((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_4 @ sk_B_2))
% 0.69/0.89        | ((sk_A) = (sk_B_2)))),
% 0.69/0.89      inference('simpl_trail', [status(thm)], ['52', '54'])).
% 0.69/0.89  thf('56', plain, ((r2_hidden @ sk_B_2 @ (k3_relat_1 @ sk_C_4))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf(t36_wellord1, axiom,
% 0.69/0.89    (![A:$i,B:$i]:
% 0.69/0.89     ( ( v1_relat_1 @ B ) =>
% 0.69/0.89       ( ( ( r1_tarski @ A @ ( k3_relat_1 @ B ) ) & ( v2_wellord1 @ B ) ) =>
% 0.69/0.89         ( ( ~( ( ![C:$i]:
% 0.69/0.89                  ( ~( ( ( A ) = ( k1_wellord1 @ B @ C ) ) & 
% 0.69/0.89                       ( r2_hidden @ C @ ( k3_relat_1 @ B ) ) ) ) ) & 
% 0.69/0.89                ( ( A ) != ( k3_relat_1 @ B ) ) ) ) <=>
% 0.69/0.89           ( ![C:$i]:
% 0.69/0.89             ( ( r2_hidden @ C @ A ) =>
% 0.69/0.89               ( ![D:$i]:
% 0.69/0.89                 ( ( r2_hidden @ ( k4_tarski @ D @ C ) @ B ) =>
% 0.69/0.89                   ( r2_hidden @ D @ A ) ) ) ) ) ) ) ))).
% 0.69/0.89  thf(zf_stmt_1, axiom,
% 0.69/0.89    (![C:$i,B:$i,A:$i]:
% 0.69/0.89     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 0.69/0.89       ( ( r2_hidden @ C @ ( k3_relat_1 @ B ) ) & 
% 0.69/0.89         ( ( A ) = ( k1_wellord1 @ B @ C ) ) ) ))).
% 0.69/0.89  thf('57', plain,
% 0.69/0.89      (![X18 : $i, X19 : $i, X21 : $i]:
% 0.69/0.89         ((zip_tseitin_0 @ X18 @ X19 @ X21)
% 0.69/0.89          | ((X21) != (k1_wellord1 @ X19 @ X18))
% 0.69/0.89          | ~ (r2_hidden @ X18 @ (k3_relat_1 @ X19)))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.69/0.89  thf('58', plain,
% 0.69/0.89      (![X18 : $i, X19 : $i]:
% 0.69/0.89         (~ (r2_hidden @ X18 @ (k3_relat_1 @ X19))
% 0.69/0.89          | (zip_tseitin_0 @ X18 @ X19 @ (k1_wellord1 @ X19 @ X18)))),
% 0.69/0.89      inference('simplify', [status(thm)], ['57'])).
% 0.69/0.89  thf('59', plain,
% 0.69/0.89      ((zip_tseitin_0 @ sk_B_2 @ sk_C_4 @ (k1_wellord1 @ sk_C_4 @ sk_B_2))),
% 0.69/0.89      inference('sup-', [status(thm)], ['56', '58'])).
% 0.69/0.89  thf(t13_wellord1, axiom,
% 0.69/0.89    (![A:$i,B:$i]:
% 0.69/0.89     ( ( v1_relat_1 @ B ) =>
% 0.69/0.89       ( r1_tarski @ ( k1_wellord1 @ B @ A ) @ ( k3_relat_1 @ B ) ) ))).
% 0.69/0.89  thf('60', plain,
% 0.69/0.89      (![X16 : $i, X17 : $i]:
% 0.69/0.89         ((r1_tarski @ (k1_wellord1 @ X16 @ X17) @ (k3_relat_1 @ X16))
% 0.69/0.89          | ~ (v1_relat_1 @ X16))),
% 0.69/0.89      inference('cnf', [status(esa)], [t13_wellord1])).
% 0.69/0.89  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.69/0.89  thf(zf_stmt_3, axiom,
% 0.69/0.89    (![C:$i,B:$i,A:$i]:
% 0.69/0.89     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 0.69/0.89       ( ( r2_hidden @ C @ A ) =>
% 0.69/0.89         ( ![D:$i]:
% 0.69/0.89           ( ( r2_hidden @ ( k4_tarski @ D @ C ) @ B ) => ( r2_hidden @ D @ A ) ) ) ) ))).
% 0.69/0.89  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.69/0.89  thf(zf_stmt_5, axiom,
% 0.69/0.89    (![A:$i,B:$i]:
% 0.69/0.89     ( ( v1_relat_1 @ B ) =>
% 0.69/0.89       ( ( ( v2_wellord1 @ B ) & ( r1_tarski @ A @ ( k3_relat_1 @ B ) ) ) =>
% 0.69/0.89         ( ( ~( ( ( A ) != ( k3_relat_1 @ B ) ) & 
% 0.69/0.89                ( ![C:$i]: ( ~( zip_tseitin_0 @ C @ B @ A ) ) ) ) ) <=>
% 0.69/0.89           ( ![C:$i]: ( zip_tseitin_1 @ C @ B @ A ) ) ) ) ))).
% 0.69/0.89  thf('61', plain,
% 0.69/0.89      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.69/0.89         (~ (v2_wellord1 @ X27)
% 0.69/0.89          | ~ (r1_tarski @ X28 @ (k3_relat_1 @ X27))
% 0.69/0.89          | ~ (zip_tseitin_0 @ X29 @ X27 @ X28)
% 0.69/0.89          | (zip_tseitin_1 @ X30 @ X27 @ X28)
% 0.69/0.89          | ~ (v1_relat_1 @ X27))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.69/0.89  thf('62', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.69/0.89         (~ (v1_relat_1 @ X0)
% 0.69/0.89          | ~ (v1_relat_1 @ X0)
% 0.69/0.89          | (zip_tseitin_1 @ X2 @ X0 @ (k1_wellord1 @ X0 @ X1))
% 0.69/0.89          | ~ (zip_tseitin_0 @ X3 @ X0 @ (k1_wellord1 @ X0 @ X1))
% 0.69/0.89          | ~ (v2_wellord1 @ X0))),
% 0.69/0.89      inference('sup-', [status(thm)], ['60', '61'])).
% 0.69/0.89  thf('63', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.69/0.89         (~ (v2_wellord1 @ X0)
% 0.69/0.89          | ~ (zip_tseitin_0 @ X3 @ X0 @ (k1_wellord1 @ X0 @ X1))
% 0.69/0.89          | (zip_tseitin_1 @ X2 @ X0 @ (k1_wellord1 @ X0 @ X1))
% 0.69/0.89          | ~ (v1_relat_1 @ X0))),
% 0.69/0.89      inference('simplify', [status(thm)], ['62'])).
% 0.69/0.89  thf('64', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (~ (v1_relat_1 @ sk_C_4)
% 0.69/0.89          | (zip_tseitin_1 @ X0 @ sk_C_4 @ (k1_wellord1 @ sk_C_4 @ sk_B_2))
% 0.69/0.89          | ~ (v2_wellord1 @ sk_C_4))),
% 0.69/0.89      inference('sup-', [status(thm)], ['59', '63'])).
% 0.69/0.89  thf('65', plain, ((v1_relat_1 @ sk_C_4)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('66', plain, ((v2_wellord1 @ sk_C_4)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('67', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (zip_tseitin_1 @ X0 @ sk_C_4 @ (k1_wellord1 @ sk_C_4 @ sk_B_2))),
% 0.69/0.89      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.69/0.89  thf('68', plain,
% 0.69/0.89      (![X1 : $i, X3 : $i]:
% 0.69/0.89         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.69/0.89      inference('cnf', [status(esa)], [d3_tarski])).
% 0.69/0.89  thf('69', plain,
% 0.69/0.89      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.69/0.89         (((X7) != (k1_wellord1 @ X6 @ X5))
% 0.69/0.89          | (r2_hidden @ (k4_tarski @ X8 @ X5) @ X6)
% 0.69/0.89          | ~ (r2_hidden @ X8 @ X7)
% 0.69/0.89          | ~ (v1_relat_1 @ X6))),
% 0.69/0.89      inference('cnf', [status(esa)], [d1_wellord1])).
% 0.69/0.89  thf('70', plain,
% 0.69/0.89      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.69/0.89         (~ (v1_relat_1 @ X6)
% 0.69/0.89          | ~ (r2_hidden @ X8 @ (k1_wellord1 @ X6 @ X5))
% 0.69/0.89          | (r2_hidden @ (k4_tarski @ X8 @ X5) @ X6))),
% 0.69/0.89      inference('simplify', [status(thm)], ['69'])).
% 0.69/0.89  thf('71', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.89         ((r1_tarski @ (k1_wellord1 @ X1 @ X0) @ X2)
% 0.69/0.89          | (r2_hidden @ 
% 0.69/0.89             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X1 @ X0)) @ X0) @ X1)
% 0.69/0.89          | ~ (v1_relat_1 @ X1))),
% 0.69/0.89      inference('sup-', [status(thm)], ['68', '70'])).
% 0.69/0.89  thf('72', plain,
% 0.69/0.89      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.69/0.89         (~ (r2_hidden @ X22 @ X23)
% 0.69/0.89          | ~ (r2_hidden @ (k4_tarski @ X24 @ X22) @ X25)
% 0.69/0.89          | (r2_hidden @ X24 @ X23)
% 0.69/0.89          | ~ (zip_tseitin_1 @ X22 @ X25 @ X23))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.69/0.89  thf('73', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.69/0.89         (~ (v1_relat_1 @ X0)
% 0.69/0.89          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 0.69/0.89          | ~ (zip_tseitin_1 @ X1 @ X0 @ X3)
% 0.69/0.89          | (r2_hidden @ (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1)) @ X3)
% 0.69/0.89          | ~ (r2_hidden @ X1 @ X3))),
% 0.69/0.89      inference('sup-', [status(thm)], ['71', '72'])).
% 0.69/0.89  thf('74', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         (~ (r2_hidden @ X0 @ (k1_wellord1 @ sk_C_4 @ sk_B_2))
% 0.69/0.89          | (r2_hidden @ (sk_C @ X1 @ (k1_wellord1 @ sk_C_4 @ X0)) @ 
% 0.69/0.89             (k1_wellord1 @ sk_C_4 @ sk_B_2))
% 0.69/0.89          | (r1_tarski @ (k1_wellord1 @ sk_C_4 @ X0) @ X1)
% 0.69/0.89          | ~ (v1_relat_1 @ sk_C_4))),
% 0.69/0.89      inference('sup-', [status(thm)], ['67', '73'])).
% 0.69/0.89  thf('75', plain, ((v1_relat_1 @ sk_C_4)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('76', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         (~ (r2_hidden @ X0 @ (k1_wellord1 @ sk_C_4 @ sk_B_2))
% 0.69/0.89          | (r2_hidden @ (sk_C @ X1 @ (k1_wellord1 @ sk_C_4 @ X0)) @ 
% 0.69/0.89             (k1_wellord1 @ sk_C_4 @ sk_B_2))
% 0.69/0.89          | (r1_tarski @ (k1_wellord1 @ sk_C_4 @ X0) @ X1))),
% 0.69/0.89      inference('demod', [status(thm)], ['74', '75'])).
% 0.69/0.89  thf('77', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (((sk_A) = (sk_B_2))
% 0.69/0.89          | (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ X0)
% 0.69/0.89          | (r2_hidden @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_4 @ sk_A)) @ 
% 0.69/0.89             (k1_wellord1 @ sk_C_4 @ sk_B_2)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['55', '76'])).
% 0.69/0.89  thf('78', plain,
% 0.69/0.89      (![X1 : $i, X3 : $i]:
% 0.69/0.89         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.69/0.89      inference('cnf', [status(esa)], [d3_tarski])).
% 0.69/0.89  thf('79', plain,
% 0.69/0.89      (((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.69/0.89         (k1_wellord1 @ sk_C_4 @ sk_B_2))
% 0.69/0.89        | ((sk_A) = (sk_B_2))
% 0.69/0.89        | (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.69/0.89           (k1_wellord1 @ sk_C_4 @ sk_B_2)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['77', '78'])).
% 0.69/0.89  thf('80', plain,
% 0.69/0.89      ((((sk_A) = (sk_B_2))
% 0.69/0.89        | (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.69/0.89           (k1_wellord1 @ sk_C_4 @ sk_B_2)))),
% 0.69/0.89      inference('simplify', [status(thm)], ['79'])).
% 0.69/0.89  thf('81', plain,
% 0.69/0.89      (~ (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.69/0.89          (k1_wellord1 @ sk_C_4 @ sk_B_2))),
% 0.69/0.89      inference('simpl_trail', [status(thm)], ['1', '46'])).
% 0.69/0.89  thf('82', plain, (((sk_A) = (sk_B_2))),
% 0.69/0.89      inference('clc', [status(thm)], ['80', '81'])).
% 0.69/0.89  thf('83', plain,
% 0.69/0.89      (![X1 : $i, X3 : $i]:
% 0.69/0.89         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.69/0.89      inference('cnf', [status(esa)], [d3_tarski])).
% 0.69/0.89  thf('84', plain,
% 0.69/0.89      (![X1 : $i, X3 : $i]:
% 0.69/0.89         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.69/0.89      inference('cnf', [status(esa)], [d3_tarski])).
% 0.69/0.89  thf('85', plain,
% 0.69/0.89      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.69/0.89      inference('sup-', [status(thm)], ['83', '84'])).
% 0.69/0.89  thf('86', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.69/0.89      inference('simplify', [status(thm)], ['85'])).
% 0.69/0.89  thf('87', plain, ($false),
% 0.69/0.89      inference('demod', [status(thm)], ['47', '82', '86'])).
% 0.69/0.89  
% 0.69/0.89  % SZS output end Refutation
% 0.69/0.89  
% 0.69/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
