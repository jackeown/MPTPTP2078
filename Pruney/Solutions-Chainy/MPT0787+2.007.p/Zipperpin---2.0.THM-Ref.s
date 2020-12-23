%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.F0hGaj0MvJ

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:33 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 363 expanded)
%              Number of leaves         :   31 ( 109 expanded)
%              Depth                    :   22
%              Number of atoms          : 1184 (5174 expanded)
%              Number of equality atoms :   35 (  92 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(v6_relat_2_type,type,(
    v6_relat_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_wellord1_type,type,(
    v1_wellord1: $i > $o )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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
    ( ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) )
   <= ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
    r2_hidden @ sk_B_3 @ ( k3_relat_1 @ sk_C_5 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_5 ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v6_relat_2 @ X20 )
      | ~ ( r2_hidden @ X21 @ ( k3_relat_1 @ X20 ) )
      | ( r2_hidden @ ( k4_tarski @ X22 @ X21 ) @ X20 )
      | ( r2_hidden @ ( k4_tarski @ X21 @ X22 ) @ X20 )
      | ( X21 = X22 )
      | ~ ( r2_hidden @ X22 @ ( k3_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[l4_wellord1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_5 )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_C_5 ) )
      | ( sk_A = X0 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_5 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ sk_A ) @ sk_C_5 )
      | ~ ( v6_relat_2 @ sk_C_5 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_relat_1 @ sk_C_5 ),
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
    ! [X13: $i] :
      ( ~ ( v2_wellord1 @ X13 )
      | ( v6_relat_2 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('10',plain,
    ( ( v6_relat_2 @ sk_C_5 )
    | ~ ( v2_wellord1 @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_wellord1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v6_relat_2 @ sk_C_5 ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_C_5 ) )
      | ( sk_A = X0 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_5 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ sk_A ) @ sk_C_5 ) ) ),
    inference(demod,[status(thm)],['6','7','12'])).

thf('14',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B_3 @ sk_A ) @ sk_C_5 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 )
    | ( sk_A = sk_B_3 ) ),
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
    ! [X8: $i,X9: $i,X10: $i,X12: $i] :
      ( ( X10
       != ( k1_wellord1 @ X9 @ X8 ) )
      | ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X8 ) @ X9 )
      | ( X12 = X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('16',plain,(
    ! [X8: $i,X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( X12 = X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X8 ) @ X9 )
      | ( r2_hidden @ X12 @ ( k1_wellord1 @ X9 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( sk_A = sk_B_3 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 )
    | ( r2_hidden @ sk_B_3 @ ( k1_wellord1 @ sk_C_5 @ sk_A ) )
    | ( sk_B_3 = sk_A )
    | ~ ( v1_relat_1 @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( sk_A = sk_B_3 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 )
    | ( r2_hidden @ sk_B_3 @ ( k1_wellord1 @ sk_C_5 @ sk_A ) )
    | ( sk_B_3 = sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r2_hidden @ sk_B_3 @ ( k1_wellord1 @ sk_C_5 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 )
    | ( sk_A = sk_B_3 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ( ( sk_A = sk_B_3 )
      | ( r2_hidden @ sk_B_3 @ ( k1_wellord1 @ sk_C_5 @ sk_A ) ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) )
   <= ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) ) ),
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
        ( ( r2_hidden @ X0 @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) )
        | ~ ( r2_hidden @ X0 @ ( k1_wellord1 @ sk_C_5 @ sk_A ) ) )
   <= ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( sk_A = sk_B_3 )
      | ( r2_hidden @ sk_B_3 @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) ) ) ),
    inference('sup-',[status(thm)],['22','26'])).

thf('28',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X10
       != ( k1_wellord1 @ X9 @ X8 ) )
      | ( X11 != X8 )
      | ~ ( r2_hidden @ X11 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('29',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( r2_hidden @ X8 @ ( k1_wellord1 @ X9 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( ( sk_A = sk_B_3 )
      | ~ ( v1_relat_1 @ sk_C_5 ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_A = sk_B_3 )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_A ) @ sk_C_5 )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_5 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v1_relat_2 @ A )
      <=> ! [B: $i] :
            ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
           => ( r2_hidden @ ( k4_tarski @ B @ B ) @ A ) ) ) ) )).

thf('36',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_2 @ X14 )
      | ( r2_hidden @ ( k4_tarski @ X15 @ X15 ) @ X14 )
      | ~ ( r2_hidden @ X15 @ ( k3_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l1_wellord1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_C_5 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_A ) @ sk_C_5 )
    | ~ ( v1_relat_2 @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_relat_1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X13: $i] :
      ( ~ ( v2_wellord1 @ X13 )
      | ( v1_relat_2 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('41',plain,
    ( ( v1_relat_2 @ sk_C_5 )
    | ~ ( v2_wellord1 @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_wellord1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_relat_2 @ sk_C_5 ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_A ) @ sk_C_5 ),
    inference(demod,[status(thm)],['37','38','43'])).

thf('45',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 )
    | ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['34','44'])).

thf('46',plain,(
    ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','45'])).

thf('47',plain,(
    ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) ) ),
    inference(simpl_trail,[status(thm)],['1','46'])).

thf('48',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 ) ),
    inference(split,[status(esa)],['23'])).

thf('49',plain,(
    ! [X8: $i,X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( X12 = X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X8 ) @ X9 )
      | ( r2_hidden @ X12 @ ( k1_wellord1 @ X9 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('50',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) )
      | ( sk_A = sk_B_3 )
      | ~ ( v1_relat_1 @ sk_C_5 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) )
      | ( sk_A = sk_B_3 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) ) ),
    inference(split,[status(esa)],['23'])).

thf('54',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_5 ),
    inference('sat_resolution*',[status(thm)],['2','45','53'])).

thf('55',plain,
    ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) )
    | ( sk_A = sk_B_3 ) ),
    inference(simpl_trail,[status(thm)],['52','54'])).

thf('56',plain,(
    r2_hidden @ sk_B_3 @ ( k3_relat_1 @ sk_C_5 ) ),
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
    ! [X23: $i,X24: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 @ X26 )
      | ( X26
       != ( k1_wellord1 @ X24 @ X23 ) )
      | ~ ( r2_hidden @ X23 @ ( k3_relat_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('58',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X23 @ ( k3_relat_1 @ X24 ) )
      | ( zip_tseitin_0 @ X23 @ X24 @ ( k1_wellord1 @ X24 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    zip_tseitin_0 @ sk_B_3 @ sk_C_5 @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('61',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X10
       != ( k1_wellord1 @ X9 @ X8 ) )
      | ( r2_hidden @ ( k4_tarski @ X11 @ X8 ) @ X9 )
      | ~ ( r2_hidden @ X11 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('62',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k1_wellord1 @ X9 @ X8 ) )
      | ( r2_hidden @ ( k4_tarski @ X11 @ X8 ) @ X9 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_wellord1 @ X1 @ X0 ) ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf(t30_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )).

thf('64',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 )
      | ( r2_hidden @ X4 @ ( k3_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ ( k3_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

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

thf('70',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( v2_wellord1 @ X32 )
      | ~ ( r1_tarski @ X33 @ ( k3_relat_1 @ X32 ) )
      | ~ ( zip_tseitin_0 @ X34 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X35 @ X32 @ X33 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X2 @ X0 @ ( k1_wellord1 @ X0 @ X1 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X0 @ ( k1_wellord1 @ X0 @ X1 ) )
      | ~ ( v2_wellord1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v2_wellord1 @ X0 )
      | ~ ( zip_tseitin_0 @ X3 @ X0 @ ( k1_wellord1 @ X0 @ X1 ) )
      | ( zip_tseitin_1 @ X2 @ X0 @ ( k1_wellord1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_5 )
      | ( zip_tseitin_1 @ X0 @ sk_C_5 @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) )
      | ~ ( v2_wellord1 @ sk_C_5 ) ) ),
    inference('sup-',[status(thm)],['59','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v2_wellord1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ X0 @ sk_C_5 @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_wellord1 @ X1 @ X0 ) ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('78',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ~ ( r2_hidden @ ( k4_tarski @ X29 @ X27 ) @ X30 )
      | ( r2_hidden @ X29 @ X28 )
      | ~ ( zip_tseitin_1 @ X27 @ X30 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( zip_tseitin_1 @ X1 @ X0 @ X3 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) @ X3 )
      | ~ ( r2_hidden @ X1 @ X3 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_wellord1 @ sk_C_5 @ X0 ) ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) )
      | ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ sk_C_5 ) ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,(
    v1_relat_1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_wellord1 @ sk_C_5 @ X0 ) ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) )
      | ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( sk_A = sk_B_3 )
      | ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_5 @ sk_A ) ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) ) ) ),
    inference('sup-',[status(thm)],['55','82'])).

thf('84',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('85',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) )
    | ( sk_A = sk_B_3 )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( sk_A = sk_B_3 )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_5 @ sk_A ) @ ( k1_wellord1 @ sk_C_5 @ sk_B_3 ) ) ),
    inference(simpl_trail,[status(thm)],['1','46'])).

thf('88',plain,(
    sk_A = sk_B_3 ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('90',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    $false ),
    inference(demod,[status(thm)],['47','88','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.F0hGaj0MvJ
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:04:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.75/0.97  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.75/0.97  % Solved by: fo/fo7.sh
% 0.75/0.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.97  % done 481 iterations in 0.518s
% 0.75/0.97  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.75/0.97  % SZS output start Refutation
% 0.75/0.97  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.97  thf(sk_B_3_type, type, sk_B_3: $i).
% 0.75/0.97  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/0.97  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.75/0.97  thf(v1_relat_2_type, type, v1_relat_2: $i > $o).
% 0.75/0.97  thf(v6_relat_2_type, type, v6_relat_2: $i > $o).
% 0.75/0.97  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.75/0.97  thf(sk_C_5_type, type, sk_C_5: $i).
% 0.75/0.97  thf(v4_relat_2_type, type, v4_relat_2: $i > $o).
% 0.75/0.97  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.75/0.97  thf(v8_relat_2_type, type, v8_relat_2: $i > $o).
% 0.75/0.97  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.97  thf(v1_wellord1_type, type, v1_wellord1: $i > $o).
% 0.75/0.97  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.75/0.97  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.75/0.97  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.75/0.97  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.75/0.97  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.75/0.97  thf(t37_wellord1, conjecture,
% 0.75/0.97    (![A:$i,B:$i,C:$i]:
% 0.75/0.97     ( ( v1_relat_1 @ C ) =>
% 0.75/0.97       ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.75/0.97           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) =>
% 0.75/0.97         ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.75/0.97           ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) ))).
% 0.75/0.97  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.97    (~( ![A:$i,B:$i,C:$i]:
% 0.75/0.97        ( ( v1_relat_1 @ C ) =>
% 0.75/0.97          ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.75/0.97              ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) =>
% 0.75/0.97            ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.75/0.97              ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) ) )),
% 0.75/0.97    inference('cnf.neg', [status(esa)], [t37_wellord1])).
% 0.75/0.97  thf('0', plain,
% 0.75/0.97      ((~ (r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 0.75/0.97           (k1_wellord1 @ sk_C_5 @ sk_B_3))
% 0.75/0.97        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('1', plain,
% 0.75/0.97      ((~ (r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 0.75/0.97           (k1_wellord1 @ sk_C_5 @ sk_B_3)))
% 0.75/0.97         <= (~
% 0.75/0.97             ((r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 0.75/0.97               (k1_wellord1 @ sk_C_5 @ sk_B_3))))),
% 0.75/0.97      inference('split', [status(esa)], ['0'])).
% 0.75/0.97  thf('2', plain,
% 0.75/0.97      (~
% 0.75/0.97       ((r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 0.75/0.97         (k1_wellord1 @ sk_C_5 @ sk_B_3))) | 
% 0.75/0.97       ~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5))),
% 0.75/0.97      inference('split', [status(esa)], ['0'])).
% 0.75/0.97  thf('3', plain, ((r2_hidden @ sk_B_3 @ (k3_relat_1 @ sk_C_5))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('4', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_5))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf(l4_wellord1, axiom,
% 0.75/0.97    (![A:$i]:
% 0.75/0.97     ( ( v1_relat_1 @ A ) =>
% 0.75/0.97       ( ( v6_relat_2 @ A ) <=>
% 0.75/0.97         ( ![B:$i,C:$i]:
% 0.75/0.97           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 0.75/0.97                ( r2_hidden @ C @ ( k3_relat_1 @ A ) ) & ( ( B ) != ( C ) ) & 
% 0.75/0.97                ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) & 
% 0.75/0.97                ( ~( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) ) ) ) ) ) ))).
% 0.75/0.97  thf('5', plain,
% 0.75/0.97      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.75/0.97         (~ (v6_relat_2 @ X20)
% 0.75/0.97          | ~ (r2_hidden @ X21 @ (k3_relat_1 @ X20))
% 0.75/0.97          | (r2_hidden @ (k4_tarski @ X22 @ X21) @ X20)
% 0.75/0.97          | (r2_hidden @ (k4_tarski @ X21 @ X22) @ X20)
% 0.75/0.97          | ((X21) = (X22))
% 0.75/0.97          | ~ (r2_hidden @ X22 @ (k3_relat_1 @ X20))
% 0.75/0.97          | ~ (v1_relat_1 @ X20))),
% 0.75/0.97      inference('cnf', [status(esa)], [l4_wellord1])).
% 0.75/0.97  thf('6', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         (~ (v1_relat_1 @ sk_C_5)
% 0.75/0.97          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C_5))
% 0.75/0.97          | ((sk_A) = (X0))
% 0.75/0.97          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_5)
% 0.75/0.97          | (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ sk_C_5)
% 0.75/0.97          | ~ (v6_relat_2 @ sk_C_5))),
% 0.75/0.97      inference('sup-', [status(thm)], ['4', '5'])).
% 0.75/0.97  thf('7', plain, ((v1_relat_1 @ sk_C_5)),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('8', plain, ((v1_relat_1 @ sk_C_5)),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf(d4_wellord1, axiom,
% 0.75/0.97    (![A:$i]:
% 0.75/0.97     ( ( v1_relat_1 @ A ) =>
% 0.75/0.97       ( ( v2_wellord1 @ A ) <=>
% 0.75/0.97         ( ( v1_relat_2 @ A ) & ( v8_relat_2 @ A ) & ( v4_relat_2 @ A ) & 
% 0.75/0.97           ( v6_relat_2 @ A ) & ( v1_wellord1 @ A ) ) ) ))).
% 0.75/0.97  thf('9', plain,
% 0.75/0.97      (![X13 : $i]:
% 0.75/0.97         (~ (v2_wellord1 @ X13) | (v6_relat_2 @ X13) | ~ (v1_relat_1 @ X13))),
% 0.75/0.97      inference('cnf', [status(esa)], [d4_wellord1])).
% 0.75/0.97  thf('10', plain, (((v6_relat_2 @ sk_C_5) | ~ (v2_wellord1 @ sk_C_5))),
% 0.75/0.97      inference('sup-', [status(thm)], ['8', '9'])).
% 0.75/0.97  thf('11', plain, ((v2_wellord1 @ sk_C_5)),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('12', plain, ((v6_relat_2 @ sk_C_5)),
% 0.75/0.97      inference('demod', [status(thm)], ['10', '11'])).
% 0.75/0.97  thf('13', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         (~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C_5))
% 0.75/0.97          | ((sk_A) = (X0))
% 0.75/0.97          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_5)
% 0.75/0.97          | (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ sk_C_5))),
% 0.75/0.97      inference('demod', [status(thm)], ['6', '7', '12'])).
% 0.75/0.97  thf('14', plain,
% 0.75/0.97      (((r2_hidden @ (k4_tarski @ sk_B_3 @ sk_A) @ sk_C_5)
% 0.75/0.97        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)
% 0.75/0.97        | ((sk_A) = (sk_B_3)))),
% 0.75/0.97      inference('sup-', [status(thm)], ['3', '13'])).
% 0.75/0.97  thf(d1_wellord1, axiom,
% 0.75/0.97    (![A:$i]:
% 0.75/0.97     ( ( v1_relat_1 @ A ) =>
% 0.75/0.97       ( ![B:$i,C:$i]:
% 0.75/0.97         ( ( ( C ) = ( k1_wellord1 @ A @ B ) ) <=>
% 0.75/0.97           ( ![D:$i]:
% 0.75/0.97             ( ( r2_hidden @ D @ C ) <=>
% 0.75/0.97               ( ( ( D ) != ( B ) ) & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) ) ))).
% 0.75/0.97  thf('15', plain,
% 0.75/0.97      (![X8 : $i, X9 : $i, X10 : $i, X12 : $i]:
% 0.75/0.97         (((X10) != (k1_wellord1 @ X9 @ X8))
% 0.75/0.97          | (r2_hidden @ X12 @ X10)
% 0.75/0.97          | ~ (r2_hidden @ (k4_tarski @ X12 @ X8) @ X9)
% 0.75/0.97          | ((X12) = (X8))
% 0.75/0.97          | ~ (v1_relat_1 @ X9))),
% 0.75/0.97      inference('cnf', [status(esa)], [d1_wellord1])).
% 0.75/0.97  thf('16', plain,
% 0.75/0.97      (![X8 : $i, X9 : $i, X12 : $i]:
% 0.75/0.97         (~ (v1_relat_1 @ X9)
% 0.75/0.97          | ((X12) = (X8))
% 0.75/0.97          | ~ (r2_hidden @ (k4_tarski @ X12 @ X8) @ X9)
% 0.75/0.97          | (r2_hidden @ X12 @ (k1_wellord1 @ X9 @ X8)))),
% 0.75/0.97      inference('simplify', [status(thm)], ['15'])).
% 0.75/0.97  thf('17', plain,
% 0.75/0.97      ((((sk_A) = (sk_B_3))
% 0.75/0.97        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)
% 0.75/0.97        | (r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_5 @ sk_A))
% 0.75/0.97        | ((sk_B_3) = (sk_A))
% 0.75/0.97        | ~ (v1_relat_1 @ sk_C_5))),
% 0.75/0.97      inference('sup-', [status(thm)], ['14', '16'])).
% 0.75/0.97  thf('18', plain, ((v1_relat_1 @ sk_C_5)),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('19', plain,
% 0.75/0.97      ((((sk_A) = (sk_B_3))
% 0.75/0.97        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)
% 0.75/0.97        | (r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_5 @ sk_A))
% 0.75/0.97        | ((sk_B_3) = (sk_A)))),
% 0.75/0.97      inference('demod', [status(thm)], ['17', '18'])).
% 0.75/0.97  thf('20', plain,
% 0.75/0.97      (((r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_5 @ sk_A))
% 0.75/0.97        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)
% 0.75/0.97        | ((sk_A) = (sk_B_3)))),
% 0.75/0.97      inference('simplify', [status(thm)], ['19'])).
% 0.75/0.97  thf('21', plain,
% 0.75/0.97      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5))
% 0.75/0.97         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)))),
% 0.75/0.97      inference('split', [status(esa)], ['0'])).
% 0.75/0.97  thf('22', plain,
% 0.75/0.97      (((((sk_A) = (sk_B_3))
% 0.75/0.97         | (r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_5 @ sk_A))))
% 0.75/0.97         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)))),
% 0.75/0.97      inference('sup-', [status(thm)], ['20', '21'])).
% 0.75/0.97  thf('23', plain,
% 0.75/0.97      (((r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 0.75/0.97         (k1_wellord1 @ sk_C_5 @ sk_B_3))
% 0.75/0.97        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('24', plain,
% 0.75/0.97      (((r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 0.75/0.97         (k1_wellord1 @ sk_C_5 @ sk_B_3)))
% 0.75/0.97         <= (((r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 0.75/0.97               (k1_wellord1 @ sk_C_5 @ sk_B_3))))),
% 0.75/0.97      inference('split', [status(esa)], ['23'])).
% 0.75/0.97  thf(d3_tarski, axiom,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( r1_tarski @ A @ B ) <=>
% 0.75/0.97       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.75/0.97  thf('25', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.97         (~ (r2_hidden @ X0 @ X1)
% 0.75/0.97          | (r2_hidden @ X0 @ X2)
% 0.75/0.97          | ~ (r1_tarski @ X1 @ X2))),
% 0.75/0.97      inference('cnf', [status(esa)], [d3_tarski])).
% 0.75/0.97  thf('26', plain,
% 0.75/0.97      ((![X0 : $i]:
% 0.75/0.97          ((r2_hidden @ X0 @ (k1_wellord1 @ sk_C_5 @ sk_B_3))
% 0.75/0.97           | ~ (r2_hidden @ X0 @ (k1_wellord1 @ sk_C_5 @ sk_A))))
% 0.75/0.97         <= (((r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 0.75/0.97               (k1_wellord1 @ sk_C_5 @ sk_B_3))))),
% 0.75/0.97      inference('sup-', [status(thm)], ['24', '25'])).
% 0.75/0.97  thf('27', plain,
% 0.75/0.97      (((((sk_A) = (sk_B_3))
% 0.75/0.97         | (r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_5 @ sk_B_3))))
% 0.75/0.97         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)) & 
% 0.75/0.97             ((r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 0.75/0.97               (k1_wellord1 @ sk_C_5 @ sk_B_3))))),
% 0.75/0.97      inference('sup-', [status(thm)], ['22', '26'])).
% 0.75/0.97  thf('28', plain,
% 0.75/0.97      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.75/0.97         (((X10) != (k1_wellord1 @ X9 @ X8))
% 0.75/0.97          | ((X11) != (X8))
% 0.75/0.97          | ~ (r2_hidden @ X11 @ X10)
% 0.75/0.97          | ~ (v1_relat_1 @ X9))),
% 0.75/0.97      inference('cnf', [status(esa)], [d1_wellord1])).
% 0.75/0.97  thf('29', plain,
% 0.75/0.97      (![X8 : $i, X9 : $i]:
% 0.75/0.97         (~ (v1_relat_1 @ X9) | ~ (r2_hidden @ X8 @ (k1_wellord1 @ X9 @ X8)))),
% 0.75/0.97      inference('simplify', [status(thm)], ['28'])).
% 0.75/0.97  thf('30', plain,
% 0.75/0.97      (((((sk_A) = (sk_B_3)) | ~ (v1_relat_1 @ sk_C_5)))
% 0.75/0.97         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)) & 
% 0.75/0.97             ((r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 0.75/0.97               (k1_wellord1 @ sk_C_5 @ sk_B_3))))),
% 0.75/0.97      inference('sup-', [status(thm)], ['27', '29'])).
% 0.75/0.97  thf('31', plain, ((v1_relat_1 @ sk_C_5)),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('32', plain,
% 0.75/0.97      ((((sk_A) = (sk_B_3)))
% 0.75/0.97         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)) & 
% 0.75/0.97             ((r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 0.75/0.97               (k1_wellord1 @ sk_C_5 @ sk_B_3))))),
% 0.75/0.97      inference('demod', [status(thm)], ['30', '31'])).
% 0.75/0.97  thf('33', plain,
% 0.75/0.97      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5))
% 0.75/0.97         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)))),
% 0.75/0.97      inference('split', [status(esa)], ['0'])).
% 0.75/0.97  thf('34', plain,
% 0.75/0.97      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_A) @ sk_C_5))
% 0.75/0.97         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)) & 
% 0.75/0.97             ((r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 0.75/0.97               (k1_wellord1 @ sk_C_5 @ sk_B_3))))),
% 0.75/0.97      inference('sup-', [status(thm)], ['32', '33'])).
% 0.75/0.97  thf('35', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_5))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf(l1_wellord1, axiom,
% 0.75/0.97    (![A:$i]:
% 0.75/0.97     ( ( v1_relat_1 @ A ) =>
% 0.75/0.97       ( ( v1_relat_2 @ A ) <=>
% 0.75/0.97         ( ![B:$i]:
% 0.75/0.97           ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) =>
% 0.75/0.97             ( r2_hidden @ ( k4_tarski @ B @ B ) @ A ) ) ) ) ))).
% 0.75/0.97  thf('36', plain,
% 0.75/0.97      (![X14 : $i, X15 : $i]:
% 0.75/0.97         (~ (v1_relat_2 @ X14)
% 0.75/0.97          | (r2_hidden @ (k4_tarski @ X15 @ X15) @ X14)
% 0.75/0.97          | ~ (r2_hidden @ X15 @ (k3_relat_1 @ X14))
% 0.75/0.97          | ~ (v1_relat_1 @ X14))),
% 0.75/0.97      inference('cnf', [status(esa)], [l1_wellord1])).
% 0.75/0.97  thf('37', plain,
% 0.75/0.97      ((~ (v1_relat_1 @ sk_C_5)
% 0.75/0.97        | (r2_hidden @ (k4_tarski @ sk_A @ sk_A) @ sk_C_5)
% 0.75/0.97        | ~ (v1_relat_2 @ sk_C_5))),
% 0.75/0.97      inference('sup-', [status(thm)], ['35', '36'])).
% 0.75/0.97  thf('38', plain, ((v1_relat_1 @ sk_C_5)),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('39', plain, ((v1_relat_1 @ sk_C_5)),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('40', plain,
% 0.75/0.97      (![X13 : $i]:
% 0.75/0.97         (~ (v2_wellord1 @ X13) | (v1_relat_2 @ X13) | ~ (v1_relat_1 @ X13))),
% 0.75/0.97      inference('cnf', [status(esa)], [d4_wellord1])).
% 0.75/0.97  thf('41', plain, (((v1_relat_2 @ sk_C_5) | ~ (v2_wellord1 @ sk_C_5))),
% 0.75/0.97      inference('sup-', [status(thm)], ['39', '40'])).
% 0.75/0.97  thf('42', plain, ((v2_wellord1 @ sk_C_5)),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('43', plain, ((v1_relat_2 @ sk_C_5)),
% 0.75/0.97      inference('demod', [status(thm)], ['41', '42'])).
% 0.75/0.97  thf('44', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_A) @ sk_C_5)),
% 0.75/0.97      inference('demod', [status(thm)], ['37', '38', '43'])).
% 0.75/0.97  thf('45', plain,
% 0.75/0.97      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)) | 
% 0.75/0.97       ~
% 0.75/0.97       ((r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 0.75/0.97         (k1_wellord1 @ sk_C_5 @ sk_B_3)))),
% 0.75/0.97      inference('demod', [status(thm)], ['34', '44'])).
% 0.75/0.97  thf('46', plain,
% 0.75/0.97      (~
% 0.75/0.97       ((r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 0.75/0.97         (k1_wellord1 @ sk_C_5 @ sk_B_3)))),
% 0.75/0.97      inference('sat_resolution*', [status(thm)], ['2', '45'])).
% 0.75/0.97  thf('47', plain,
% 0.75/0.97      (~ (r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 0.75/0.97          (k1_wellord1 @ sk_C_5 @ sk_B_3))),
% 0.75/0.97      inference('simpl_trail', [status(thm)], ['1', '46'])).
% 0.75/0.97  thf('48', plain,
% 0.75/0.97      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5))
% 0.75/0.97         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)))),
% 0.75/0.97      inference('split', [status(esa)], ['23'])).
% 0.75/0.97  thf('49', plain,
% 0.75/0.97      (![X8 : $i, X9 : $i, X12 : $i]:
% 0.75/0.97         (~ (v1_relat_1 @ X9)
% 0.75/0.97          | ((X12) = (X8))
% 0.75/0.97          | ~ (r2_hidden @ (k4_tarski @ X12 @ X8) @ X9)
% 0.75/0.97          | (r2_hidden @ X12 @ (k1_wellord1 @ X9 @ X8)))),
% 0.75/0.97      inference('simplify', [status(thm)], ['15'])).
% 0.75/0.97  thf('50', plain,
% 0.75/0.97      ((((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_5 @ sk_B_3))
% 0.75/0.97         | ((sk_A) = (sk_B_3))
% 0.75/0.97         | ~ (v1_relat_1 @ sk_C_5)))
% 0.75/0.97         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)))),
% 0.75/0.97      inference('sup-', [status(thm)], ['48', '49'])).
% 0.75/0.97  thf('51', plain, ((v1_relat_1 @ sk_C_5)),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('52', plain,
% 0.75/0.97      ((((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_5 @ sk_B_3))
% 0.75/0.97         | ((sk_A) = (sk_B_3))))
% 0.75/0.97         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)))),
% 0.75/0.97      inference('demod', [status(thm)], ['50', '51'])).
% 0.75/0.97  thf('53', plain,
% 0.75/0.97      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5)) | 
% 0.75/0.97       ((r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 0.75/0.97         (k1_wellord1 @ sk_C_5 @ sk_B_3)))),
% 0.75/0.97      inference('split', [status(esa)], ['23'])).
% 0.75/0.97  thf('54', plain, (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_5))),
% 0.75/0.97      inference('sat_resolution*', [status(thm)], ['2', '45', '53'])).
% 0.75/0.97  thf('55', plain,
% 0.75/0.97      (((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_5 @ sk_B_3))
% 0.75/0.97        | ((sk_A) = (sk_B_3)))),
% 0.75/0.97      inference('simpl_trail', [status(thm)], ['52', '54'])).
% 0.75/0.97  thf('56', plain, ((r2_hidden @ sk_B_3 @ (k3_relat_1 @ sk_C_5))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf(t36_wellord1, axiom,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( v1_relat_1 @ B ) =>
% 0.75/0.97       ( ( ( r1_tarski @ A @ ( k3_relat_1 @ B ) ) & ( v2_wellord1 @ B ) ) =>
% 0.75/0.97         ( ( ~( ( ![C:$i]:
% 0.75/0.97                  ( ~( ( ( A ) = ( k1_wellord1 @ B @ C ) ) & 
% 0.75/0.97                       ( r2_hidden @ C @ ( k3_relat_1 @ B ) ) ) ) ) & 
% 0.75/0.97                ( ( A ) != ( k3_relat_1 @ B ) ) ) ) <=>
% 0.75/0.97           ( ![C:$i]:
% 0.75/0.97             ( ( r2_hidden @ C @ A ) =>
% 0.75/0.97               ( ![D:$i]:
% 0.75/0.97                 ( ( r2_hidden @ ( k4_tarski @ D @ C ) @ B ) =>
% 0.75/0.97                   ( r2_hidden @ D @ A ) ) ) ) ) ) ) ))).
% 0.75/0.97  thf(zf_stmt_1, axiom,
% 0.75/0.97    (![C:$i,B:$i,A:$i]:
% 0.75/0.97     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 0.75/0.97       ( ( r2_hidden @ C @ ( k3_relat_1 @ B ) ) & 
% 0.75/0.97         ( ( A ) = ( k1_wellord1 @ B @ C ) ) ) ))).
% 0.75/0.97  thf('57', plain,
% 0.75/0.97      (![X23 : $i, X24 : $i, X26 : $i]:
% 0.75/0.97         ((zip_tseitin_0 @ X23 @ X24 @ X26)
% 0.75/0.97          | ((X26) != (k1_wellord1 @ X24 @ X23))
% 0.75/0.97          | ~ (r2_hidden @ X23 @ (k3_relat_1 @ X24)))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/0.97  thf('58', plain,
% 0.75/0.97      (![X23 : $i, X24 : $i]:
% 0.75/0.97         (~ (r2_hidden @ X23 @ (k3_relat_1 @ X24))
% 0.75/0.97          | (zip_tseitin_0 @ X23 @ X24 @ (k1_wellord1 @ X24 @ X23)))),
% 0.75/0.97      inference('simplify', [status(thm)], ['57'])).
% 0.75/0.97  thf('59', plain,
% 0.75/0.97      ((zip_tseitin_0 @ sk_B_3 @ sk_C_5 @ (k1_wellord1 @ sk_C_5 @ sk_B_3))),
% 0.75/0.97      inference('sup-', [status(thm)], ['56', '58'])).
% 0.75/0.97  thf('60', plain,
% 0.75/0.97      (![X1 : $i, X3 : $i]:
% 0.75/0.97         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.75/0.97      inference('cnf', [status(esa)], [d3_tarski])).
% 0.75/0.97  thf('61', plain,
% 0.75/0.97      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.75/0.97         (((X10) != (k1_wellord1 @ X9 @ X8))
% 0.75/0.97          | (r2_hidden @ (k4_tarski @ X11 @ X8) @ X9)
% 0.75/0.97          | ~ (r2_hidden @ X11 @ X10)
% 0.75/0.97          | ~ (v1_relat_1 @ X9))),
% 0.75/0.97      inference('cnf', [status(esa)], [d1_wellord1])).
% 0.75/0.97  thf('62', plain,
% 0.75/0.97      (![X8 : $i, X9 : $i, X11 : $i]:
% 0.75/0.97         (~ (v1_relat_1 @ X9)
% 0.75/0.98          | ~ (r2_hidden @ X11 @ (k1_wellord1 @ X9 @ X8))
% 0.75/0.98          | (r2_hidden @ (k4_tarski @ X11 @ X8) @ X9))),
% 0.75/0.98      inference('simplify', [status(thm)], ['61'])).
% 0.75/0.98  thf('63', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.98         ((r1_tarski @ (k1_wellord1 @ X1 @ X0) @ X2)
% 0.75/0.98          | (r2_hidden @ 
% 0.75/0.98             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X1 @ X0)) @ X0) @ X1)
% 0.75/0.98          | ~ (v1_relat_1 @ X1))),
% 0.75/0.98      inference('sup-', [status(thm)], ['60', '62'])).
% 0.75/0.98  thf(t30_relat_1, axiom,
% 0.75/0.98    (![A:$i,B:$i,C:$i]:
% 0.75/0.98     ( ( v1_relat_1 @ C ) =>
% 0.75/0.98       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.75/0.98         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.75/0.98           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ))).
% 0.75/0.98  thf('64', plain,
% 0.75/0.98      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.75/0.98         (~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ X6)
% 0.75/0.98          | (r2_hidden @ X4 @ (k3_relat_1 @ X6))
% 0.75/0.98          | ~ (v1_relat_1 @ X6))),
% 0.75/0.98      inference('cnf', [status(esa)], [t30_relat_1])).
% 0.75/0.98  thf('65', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.98         (~ (v1_relat_1 @ X0)
% 0.75/0.98          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 0.75/0.98          | ~ (v1_relat_1 @ X0)
% 0.75/0.98          | (r2_hidden @ (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1)) @ 
% 0.75/0.98             (k3_relat_1 @ X0)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['63', '64'])).
% 0.75/0.98  thf('66', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.98         ((r2_hidden @ (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1)) @ 
% 0.75/0.98           (k3_relat_1 @ X0))
% 0.75/0.98          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 0.75/0.98          | ~ (v1_relat_1 @ X0))),
% 0.75/0.98      inference('simplify', [status(thm)], ['65'])).
% 0.75/0.98  thf('67', plain,
% 0.75/0.98      (![X1 : $i, X3 : $i]:
% 0.75/0.98         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.75/0.98      inference('cnf', [status(esa)], [d3_tarski])).
% 0.75/0.98  thf('68', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (~ (v1_relat_1 @ X0)
% 0.75/0.98          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ (k3_relat_1 @ X0))
% 0.75/0.98          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ (k3_relat_1 @ X0)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['66', '67'])).
% 0.75/0.98  thf('69', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((r1_tarski @ (k1_wellord1 @ X0 @ X1) @ (k3_relat_1 @ X0))
% 0.75/0.98          | ~ (v1_relat_1 @ X0))),
% 0.75/0.98      inference('simplify', [status(thm)], ['68'])).
% 0.75/0.98  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.75/0.98  thf(zf_stmt_3, axiom,
% 0.75/0.98    (![C:$i,B:$i,A:$i]:
% 0.75/0.98     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 0.75/0.98       ( ( r2_hidden @ C @ A ) =>
% 0.75/0.98         ( ![D:$i]:
% 0.75/0.98           ( ( r2_hidden @ ( k4_tarski @ D @ C ) @ B ) => ( r2_hidden @ D @ A ) ) ) ) ))).
% 0.75/0.98  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.75/0.98  thf(zf_stmt_5, axiom,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( v1_relat_1 @ B ) =>
% 0.75/0.98       ( ( ( v2_wellord1 @ B ) & ( r1_tarski @ A @ ( k3_relat_1 @ B ) ) ) =>
% 0.75/0.98         ( ( ~( ( ( A ) != ( k3_relat_1 @ B ) ) & 
% 0.75/0.98                ( ![C:$i]: ( ~( zip_tseitin_0 @ C @ B @ A ) ) ) ) ) <=>
% 0.75/0.98           ( ![C:$i]: ( zip_tseitin_1 @ C @ B @ A ) ) ) ) ))).
% 0.75/0.98  thf('70', plain,
% 0.75/0.98      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.75/0.98         (~ (v2_wellord1 @ X32)
% 0.75/0.98          | ~ (r1_tarski @ X33 @ (k3_relat_1 @ X32))
% 0.75/0.98          | ~ (zip_tseitin_0 @ X34 @ X32 @ X33)
% 0.75/0.98          | (zip_tseitin_1 @ X35 @ X32 @ X33)
% 0.75/0.98          | ~ (v1_relat_1 @ X32))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.75/0.98  thf('71', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.75/0.98         (~ (v1_relat_1 @ X0)
% 0.75/0.98          | ~ (v1_relat_1 @ X0)
% 0.75/0.98          | (zip_tseitin_1 @ X2 @ X0 @ (k1_wellord1 @ X0 @ X1))
% 0.75/0.98          | ~ (zip_tseitin_0 @ X3 @ X0 @ (k1_wellord1 @ X0 @ X1))
% 0.75/0.98          | ~ (v2_wellord1 @ X0))),
% 0.75/0.98      inference('sup-', [status(thm)], ['69', '70'])).
% 0.75/0.98  thf('72', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.75/0.98         (~ (v2_wellord1 @ X0)
% 0.75/0.98          | ~ (zip_tseitin_0 @ X3 @ X0 @ (k1_wellord1 @ X0 @ X1))
% 0.75/0.98          | (zip_tseitin_1 @ X2 @ X0 @ (k1_wellord1 @ X0 @ X1))
% 0.75/0.98          | ~ (v1_relat_1 @ X0))),
% 0.75/0.98      inference('simplify', [status(thm)], ['71'])).
% 0.75/0.98  thf('73', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (~ (v1_relat_1 @ sk_C_5)
% 0.75/0.98          | (zip_tseitin_1 @ X0 @ sk_C_5 @ (k1_wellord1 @ sk_C_5 @ sk_B_3))
% 0.75/0.98          | ~ (v2_wellord1 @ sk_C_5))),
% 0.75/0.98      inference('sup-', [status(thm)], ['59', '72'])).
% 0.75/0.98  thf('74', plain, ((v1_relat_1 @ sk_C_5)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('75', plain, ((v2_wellord1 @ sk_C_5)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('76', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (zip_tseitin_1 @ X0 @ sk_C_5 @ (k1_wellord1 @ sk_C_5 @ sk_B_3))),
% 0.75/0.98      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.75/0.98  thf('77', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.98         ((r1_tarski @ (k1_wellord1 @ X1 @ X0) @ X2)
% 0.75/0.98          | (r2_hidden @ 
% 0.75/0.98             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X1 @ X0)) @ X0) @ X1)
% 0.75/0.98          | ~ (v1_relat_1 @ X1))),
% 0.75/0.98      inference('sup-', [status(thm)], ['60', '62'])).
% 0.75/0.98  thf('78', plain,
% 0.75/0.98      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.75/0.98         (~ (r2_hidden @ X27 @ X28)
% 0.75/0.98          | ~ (r2_hidden @ (k4_tarski @ X29 @ X27) @ X30)
% 0.75/0.98          | (r2_hidden @ X29 @ X28)
% 0.75/0.98          | ~ (zip_tseitin_1 @ X27 @ X30 @ X28))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.75/0.98  thf('79', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.75/0.98         (~ (v1_relat_1 @ X0)
% 0.75/0.98          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 0.75/0.98          | ~ (zip_tseitin_1 @ X1 @ X0 @ X3)
% 0.75/0.98          | (r2_hidden @ (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1)) @ X3)
% 0.75/0.98          | ~ (r2_hidden @ X1 @ X3))),
% 0.75/0.98      inference('sup-', [status(thm)], ['77', '78'])).
% 0.75/0.98  thf('80', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (~ (r2_hidden @ X0 @ (k1_wellord1 @ sk_C_5 @ sk_B_3))
% 0.75/0.98          | (r2_hidden @ (sk_C @ X1 @ (k1_wellord1 @ sk_C_5 @ X0)) @ 
% 0.75/0.98             (k1_wellord1 @ sk_C_5 @ sk_B_3))
% 0.75/0.98          | (r1_tarski @ (k1_wellord1 @ sk_C_5 @ X0) @ X1)
% 0.75/0.98          | ~ (v1_relat_1 @ sk_C_5))),
% 0.75/0.98      inference('sup-', [status(thm)], ['76', '79'])).
% 0.75/0.98  thf('81', plain, ((v1_relat_1 @ sk_C_5)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('82', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (~ (r2_hidden @ X0 @ (k1_wellord1 @ sk_C_5 @ sk_B_3))
% 0.75/0.98          | (r2_hidden @ (sk_C @ X1 @ (k1_wellord1 @ sk_C_5 @ X0)) @ 
% 0.75/0.98             (k1_wellord1 @ sk_C_5 @ sk_B_3))
% 0.75/0.98          | (r1_tarski @ (k1_wellord1 @ sk_C_5 @ X0) @ X1))),
% 0.75/0.98      inference('demod', [status(thm)], ['80', '81'])).
% 0.75/0.98  thf('83', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (((sk_A) = (sk_B_3))
% 0.75/0.98          | (r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ X0)
% 0.75/0.98          | (r2_hidden @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_5 @ sk_A)) @ 
% 0.75/0.98             (k1_wellord1 @ sk_C_5 @ sk_B_3)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['55', '82'])).
% 0.75/0.98  thf('84', plain,
% 0.75/0.98      (![X1 : $i, X3 : $i]:
% 0.75/0.98         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.75/0.98      inference('cnf', [status(esa)], [d3_tarski])).
% 0.75/0.98  thf('85', plain,
% 0.75/0.98      (((r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 0.75/0.98         (k1_wellord1 @ sk_C_5 @ sk_B_3))
% 0.75/0.98        | ((sk_A) = (sk_B_3))
% 0.75/0.98        | (r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 0.75/0.98           (k1_wellord1 @ sk_C_5 @ sk_B_3)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['83', '84'])).
% 0.75/0.98  thf('86', plain,
% 0.75/0.98      ((((sk_A) = (sk_B_3))
% 0.75/0.98        | (r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 0.75/0.98           (k1_wellord1 @ sk_C_5 @ sk_B_3)))),
% 0.75/0.98      inference('simplify', [status(thm)], ['85'])).
% 0.75/0.98  thf('87', plain,
% 0.75/0.98      (~ (r1_tarski @ (k1_wellord1 @ sk_C_5 @ sk_A) @ 
% 0.75/0.98          (k1_wellord1 @ sk_C_5 @ sk_B_3))),
% 0.75/0.98      inference('simpl_trail', [status(thm)], ['1', '46'])).
% 0.75/0.98  thf('88', plain, (((sk_A) = (sk_B_3))),
% 0.75/0.98      inference('clc', [status(thm)], ['86', '87'])).
% 0.75/0.98  thf('89', plain,
% 0.75/0.98      (![X1 : $i, X3 : $i]:
% 0.75/0.98         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.75/0.98      inference('cnf', [status(esa)], [d3_tarski])).
% 0.75/0.98  thf('90', plain,
% 0.75/0.98      (![X1 : $i, X3 : $i]:
% 0.75/0.98         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.75/0.98      inference('cnf', [status(esa)], [d3_tarski])).
% 0.75/0.98  thf('91', plain,
% 0.75/0.98      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.75/0.98      inference('sup-', [status(thm)], ['89', '90'])).
% 0.75/0.98  thf('92', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.75/0.98      inference('simplify', [status(thm)], ['91'])).
% 0.75/0.98  thf('93', plain, ($false),
% 0.75/0.98      inference('demod', [status(thm)], ['47', '88', '92'])).
% 0.75/0.98  
% 0.75/0.98  % SZS output end Refutation
% 0.75/0.98  
% 0.75/0.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
