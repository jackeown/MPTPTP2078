%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.j5L3l8Av0r

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:33 EST 2020

% Result     : Theorem 11.38s
% Output     : Refutation 11.38s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 369 expanded)
%              Number of leaves         :   37 ( 115 expanded)
%              Depth                    :   24
%              Number of atoms          : 1953 (5115 expanded)
%              Number of equality atoms :   57 (  99 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_C_6_type,type,(
    sk_C_6: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(v6_relat_2_type,type,(
    v6_relat_2: $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_wellord1_type,type,(
    v1_wellord1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ( ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_1 ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_6 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_1 ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_6 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_1 ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_6 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_6 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_6 ) ),
    inference(split,[status(esa)],['2'])).

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

thf('4',plain,(
    ! [X10: $i,X11: $i,X12: $i,X14: $i] :
      ( ( X12
       != ( k1_wellord1 @ X11 @ X10 ) )
      | ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X10 ) @ X11 )
      | ( X14 = X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('5',plain,(
    ! [X10: $i,X11: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( X14 = X10 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X10 ) @ X11 )
      | ( r2_hidden @ X14 @ ( k1_wellord1 @ X11 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_6 @ sk_B_1 ) )
      | ( sk_A = sk_B_1 )
      | ~ ( v1_relat_1 @ sk_C_6 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_6 ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_6 @ sk_B_1 ) )
      | ( sk_A = sk_B_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_6 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X12
       != ( k1_wellord1 @ X11 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ X13 @ X10 ) @ X11 )
      | ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('11',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( r2_hidden @ X13 @ ( k1_wellord1 @ X11 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ X13 @ X10 ) @ X11 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_wellord1 @ X1 @ X0 ) ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf(t30_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )).

thf('13',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 )
      | ( r2_hidden @ X5 @ ( k3_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

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

thf('16',plain,(
    ! [X28: $i,X29: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 @ X31 )
      | ( X31
       != ( k1_wellord1 @ X29 @ X28 ) )
      | ~ ( r2_hidden @ X28 @ ( k3_relat_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('17',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X28 @ ( k3_relat_1 @ X29 ) )
      | ( zip_tseitin_0 @ X28 @ X29 @ ( k1_wellord1 @ X29 @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ( zip_tseitin_0 @ X1 @ X0 @ ( k1_wellord1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf(t13_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_wellord1 @ B @ A ) @ ( k3_relat_1 @ B ) ) ) )).

thf('19',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X26 @ X27 ) @ ( k3_relat_1 @ X26 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
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

thf('20',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( v2_wellord1 @ X37 )
      | ~ ( r1_tarski @ X38 @ ( k3_relat_1 @ X37 ) )
      | ~ ( zip_tseitin_0 @ X39 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X40 @ X37 @ X38 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X2 @ X0 @ ( k1_wellord1 @ X0 @ X1 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X0 @ ( k1_wellord1 @ X0 @ X1 ) )
      | ~ ( v2_wellord1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v2_wellord1 @ X0 )
      | ~ ( zip_tseitin_0 @ X3 @ X0 @ ( k1_wellord1 @ X0 @ X1 ) )
      | ( zip_tseitin_1 @ X2 @ X0 @ ( k1_wellord1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X1 @ X0 ) @ X3 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( zip_tseitin_1 @ X2 @ X1 @ ( k1_wellord1 @ X1 @ X0 ) )
      | ~ ( v2_wellord1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v2_wellord1 @ X1 )
      | ( zip_tseitin_1 @ X2 @ X1 @ ( k1_wellord1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_wellord1 @ X1 @ X0 ) @ X3 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X32: $i,X35: $i,X36: $i] :
      ( ( zip_tseitin_1 @ X32 @ X35 @ X36 )
      | ( r2_hidden @ X32 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('26',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X1 @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( zip_tseitin_1 @ X4 @ X2 @ ( k1_wellord1 @ X2 @ X1 ) )
      | ~ ( v2_wellord1 @ X2 )
      | ( zip_tseitin_1 @ X0 @ X3 @ ( k1_wellord1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X2 @ X1 @ ( k1_wellord1 @ X1 @ X0 ) )
      | ~ ( v2_wellord1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(eq_fact,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_wellord1 @ X1 @ X0 ) ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('31',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X32 @ X33 )
      | ~ ( r2_hidden @ ( k4_tarski @ X34 @ X32 ) @ X35 )
      | ( r2_hidden @ X34 @ X33 )
      | ~ ( zip_tseitin_1 @ X32 @ X35 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( zip_tseitin_1 @ X1 @ X0 @ X3 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) @ X3 )
      | ~ ( r2_hidden @ X1 @ X3 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_wellord1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k1_wellord1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X3 @ ( k1_wellord1 @ X1 @ X2 ) ) @ ( k1_wellord1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord1 @ X1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X1 @ X2 ) @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ ( k1_wellord1 @ X1 @ X2 ) ) @ ( k1_wellord1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_wellord1 @ X1 @ X0 ) )
      | ~ ( v2_wellord1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ( sk_A = sk_B_1 )
        | ~ ( v1_relat_1 @ sk_C_6 )
        | ~ ( v2_wellord1 @ sk_C_6 )
        | ( r2_hidden @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_6 @ sk_A ) ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_1 ) )
        | ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_6 ) ),
    inference('sup-',[status(thm)],['8','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_wellord1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ( sk_A = sk_B_1 )
        | ( r2_hidden @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_6 @ sk_A ) ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_1 ) )
        | ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_6 ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('40',plain,
    ( ( ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_1 ) )
      | ( sk_A = sk_B_1 )
      | ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_1 ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_6 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_1 ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_6 ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_1 ) )
   <= ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('43',plain,
    ( ( sk_A = sk_B_1 )
   <= ( ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_1 ) )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_6 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_1 ) )
   <= ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,
    ( ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_A ) )
   <= ( ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_1 ) )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_6 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('47',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_1 ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_6 ) ),
    inference(demod,[status(thm)],['45','49'])).

thf('51',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_1 ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_6 ) ),
    inference(split,[status(esa)],['2'])).

thf('52',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_6 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(s1_xboole_0__e7_18__wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ? [C: $i] :
        ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ ( k3_relat_1 @ A ) )
            & ~ ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) )).

thf('53',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( r2_hidden @ X20 @ ( sk_C_2 @ X21 @ X19 ) )
      | ( r2_hidden @ ( k4_tarski @ X20 @ X21 ) @ X19 )
      | ~ ( r2_hidden @ X20 @ ( k3_relat_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[s1_xboole_0__e7_18__wellord1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_6 )
      | ( r2_hidden @ sk_A @ ( sk_C_2 @ X0 @ sk_C_6 ) )
      | ~ ( v1_relat_1 @ sk_C_6 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_6 )
      | ( r2_hidden @ sk_A @ ( sk_C_2 @ X0 @ sk_C_6 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    r2_hidden @ sk_B_1 @ ( k3_relat_1 @ sk_C_6 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_6 ) ),
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

thf('59',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v6_relat_2 @ X16 )
      | ~ ( r2_hidden @ X17 @ ( k3_relat_1 @ X16 ) )
      | ( r2_hidden @ ( k4_tarski @ X18 @ X17 ) @ X16 )
      | ( r2_hidden @ ( k4_tarski @ X17 @ X18 ) @ X16 )
      | ( X17 = X18 )
      | ~ ( r2_hidden @ X18 @ ( k3_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l4_wellord1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_6 )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_C_6 ) )
      | ( sk_A = X0 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_6 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ sk_A ) @ sk_C_6 )
      | ~ ( v6_relat_2 @ sk_C_6 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_relat_1 @ sk_C_6 ),
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

thf('63',plain,(
    ! [X15: $i] :
      ( ~ ( v2_wellord1 @ X15 )
      | ( v6_relat_2 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('64',plain,
    ( ( v6_relat_2 @ sk_C_6 )
    | ~ ( v2_wellord1 @ sk_C_6 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v2_wellord1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v6_relat_2 @ sk_C_6 ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_C_6 ) )
      | ( sk_A = X0 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_6 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ sk_A ) @ sk_C_6 ) ) ),
    inference(demod,[status(thm)],['60','61','66'])).

thf('68',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_A ) @ sk_C_6 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_6 )
    | ( sk_A = sk_B_1 ) ),
    inference('sup-',[status(thm)],['57','67'])).

thf('69',plain,(
    ! [X10: $i,X11: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( X14 = X10 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X10 ) @ X11 )
      | ( r2_hidden @ X14 @ ( k1_wellord1 @ X11 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('70',plain,
    ( ( sk_A = sk_B_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_6 )
    | ( r2_hidden @ sk_B_1 @ ( k1_wellord1 @ sk_C_6 @ sk_A ) )
    | ( sk_B_1 = sk_A )
    | ~ ( v1_relat_1 @ sk_C_6 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( sk_A = sk_B_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_6 )
    | ( r2_hidden @ sk_B_1 @ ( k1_wellord1 @ sk_C_6 @ sk_A ) )
    | ( sk_B_1 = sk_A ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( r2_hidden @ sk_B_1 @ ( k1_wellord1 @ sk_C_6 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_6 )
    | ( sk_A = sk_B_1 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_6 )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_6 ) ),
    inference(split,[status(esa)],['0'])).

thf('75',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( r2_hidden @ sk_B_1 @ ( k1_wellord1 @ sk_C_6 @ sk_A ) ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_6 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_1 ) )
   <= ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('78',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k1_wellord1 @ sk_C_6 @ sk_B_1 ) )
        | ~ ( r2_hidden @ X0 @ ( k1_wellord1 @ sk_C_6 @ sk_A ) ) )
   <= ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( r2_hidden @ sk_B_1 @ ( k1_wellord1 @ sk_C_6 @ sk_B_1 ) ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_6 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X12
       != ( k1_wellord1 @ X11 @ X10 ) )
      | ( X13 != X10 )
      | ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('81',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( r2_hidden @ X10 @ ( k1_wellord1 @ X11 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ( ( sk_A = sk_B_1 )
      | ~ ( v1_relat_1 @ sk_C_6 ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_6 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['79','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( sk_A = sk_B_1 )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_6 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_6 )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_6 ) ),
    inference(split,[status(esa)],['0'])).

thf('86',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_A ) @ sk_C_6 )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_6 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( r2_hidden @ sk_A @ ( sk_C_2 @ sk_A @ sk_C_6 ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_6 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['56','86'])).

thf('88',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('89',plain,
    ( ~ ( r1_tarski @ ( sk_C_2 @ sk_A @ sk_C_6 ) @ sk_A )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_6 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('91',plain,(
    ! [X19: $i,X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( r2_hidden @ X22 @ ( k3_relat_1 @ X19 ) )
      | ~ ( r2_hidden @ X22 @ ( sk_C_2 @ X21 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[s1_xboole_0__e7_18__wellord1])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( sk_C_2 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( sk_C_2 @ X1 @ X0 ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( sk_C_2 @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ( r1_tarski @ ( sk_C_2 @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( sk_C_2 @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf(t10_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
       => ! [B: $i] :
            ~ ( ( r1_tarski @ B @ ( k3_relat_1 @ A ) )
              & ( B != k1_xboole_0 )
              & ! [C: $i] :
                  ~ ( ( r2_hidden @ C @ B )
                    & ! [D: $i] :
                        ( ( r2_hidden @ D @ B )
                       => ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ) ) )).

thf('96',plain,(
    ! [X23: $i,X25: $i] :
      ( ~ ( v2_wellord1 @ X23 )
      | ( r2_hidden @ ( sk_C_3 @ X25 @ X23 ) @ X25 )
      | ( X25 = k1_xboole_0 )
      | ~ ( r1_tarski @ X25 @ ( k3_relat_1 @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord1])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( sk_C_2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_3 @ ( sk_C_2 @ X1 @ X0 ) @ X0 ) @ ( sk_C_2 @ X1 @ X0 ) )
      | ~ ( v2_wellord1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_wellord1 @ X0 )
      | ( r2_hidden @ ( sk_C_3 @ ( sk_C_2 @ X1 @ X0 ) @ X0 ) @ ( sk_C_2 @ X1 @ X0 ) )
      | ( ( sk_C_2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( ( r2_hidden @ sk_A @ ( sk_C_2 @ sk_A @ sk_C_6 ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_6 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['56','86'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( sk_C_2 @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('101',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v2_wellord1 @ X23 )
      | ~ ( r2_hidden @ X24 @ X25 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_3 @ X25 @ X23 ) @ X24 ) @ X23 )
      | ( X25 = k1_xboole_0 )
      | ~ ( r1_tarski @ X25 @ ( k3_relat_1 @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord1])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( sk_C_2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_3 @ ( sk_C_2 @ X1 @ X0 ) @ X0 ) @ X2 ) @ X0 )
      | ~ ( r2_hidden @ X2 @ ( sk_C_2 @ X1 @ X0 ) )
      | ~ ( v2_wellord1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v2_wellord1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( sk_C_2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_3 @ ( sk_C_2 @ X1 @ X0 ) @ X0 ) @ X2 ) @ X0 )
      | ( ( sk_C_2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_6 )
      | ( ( sk_C_2 @ sk_A @ sk_C_6 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_3 @ ( sk_C_2 @ sk_A @ sk_C_6 ) @ sk_C_6 ) @ sk_A ) @ sk_C_6 )
      | ~ ( v2_wellord1 @ sk_C_6 ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_6 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['99','103'])).

thf('105',plain,(
    v1_relat_1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v2_wellord1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( ( ( sk_C_2 @ sk_A @ sk_C_6 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_3 @ ( sk_C_2 @ sk_A @ sk_C_6 ) @ sk_C_6 ) @ sk_A ) @ sk_C_6 ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_6 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,(
    ! [X19: $i,X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( r2_hidden @ ( k4_tarski @ X22 @ X21 ) @ X19 )
      | ~ ( r2_hidden @ X22 @ ( sk_C_2 @ X21 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[s1_xboole_0__e7_18__wellord1])).

thf('109',plain,
    ( ( ( ( sk_C_2 @ sk_A @ sk_C_6 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_C_3 @ ( sk_C_2 @ sk_A @ sk_C_6 ) @ sk_C_6 ) @ ( sk_C_2 @ sk_A @ sk_C_6 ) )
      | ~ ( v1_relat_1 @ sk_C_6 ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_6 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v1_relat_1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( ( ( sk_C_2 @ sk_A @ sk_C_6 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_C_3 @ ( sk_C_2 @ sk_A @ sk_C_6 ) @ sk_C_6 ) @ ( sk_C_2 @ sk_A @ sk_C_6 ) ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_6 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_6 )
      | ( ( sk_C_2 @ sk_A @ sk_C_6 )
        = k1_xboole_0 )
      | ~ ( v2_wellord1 @ sk_C_6 )
      | ( ( sk_C_2 @ sk_A @ sk_C_6 )
        = k1_xboole_0 ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_6 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['98','111'])).

thf('113',plain,(
    v1_relat_1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v2_wellord1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( ( ( sk_C_2 @ sk_A @ sk_C_6 )
        = k1_xboole_0 )
      | ( ( sk_C_2 @ sk_A @ sk_C_6 )
        = k1_xboole_0 ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_6 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,
    ( ( ( sk_C_2 @ sk_A @ sk_C_6 )
      = k1_xboole_0 )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_6 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    v1_relat_1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('120',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ ( k3_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['118','121'])).

thf('123',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X26 @ X27 ) @ ( k3_relat_1 @ X26 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t13_wellord1])).

thf('124',plain,(
    ! [X23: $i,X25: $i] :
      ( ~ ( v2_wellord1 @ X23 )
      | ( r2_hidden @ ( sk_C_3 @ X25 @ X23 ) @ X25 )
      | ( X25 = k1_xboole_0 )
      | ~ ( r1_tarski @ X25 @ ( k3_relat_1 @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord1])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_wellord1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_3 @ ( k1_wellord1 @ X0 @ X1 ) @ X0 ) @ ( k1_wellord1 @ X0 @ X1 ) )
      | ~ ( v2_wellord1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_wellord1 @ X0 )
      | ( r2_hidden @ ( sk_C_3 @ ( k1_wellord1 @ X0 @ X1 ) @ X0 ) @ ( k1_wellord1 @ X0 @ X1 ) )
      | ( ( k1_wellord1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_wellord1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_wellord1 @ X1 )
      | ~ ( r1_tarski @ ( k1_wellord1 @ X1 @ X0 ) @ ( sk_C_3 @ ( k1_wellord1 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_wellord1 @ X0 )
      | ( ( k1_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['122','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( ( k1_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['118','121'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_wellord1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_wellord1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v2_wellord1 @ sk_C_6 ) ) ),
    inference('sup-',[status(thm)],['117','133'])).

thf('135',plain,(
    v2_wellord1 @ sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,
    ( ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_6 @ sk_A ) @ ( k1_wellord1 @ sk_C_6 @ sk_B_1 ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_6 ) ),
    inference(demod,[status(thm)],['89','116','136'])).

thf('138',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','50','51','137'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.j5L3l8Av0r
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:47:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.20/0.34  % Running in FO mode
% 11.38/11.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 11.38/11.63  % Solved by: fo/fo7.sh
% 11.38/11.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 11.38/11.63  % done 6753 iterations in 11.182s
% 11.38/11.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 11.38/11.63  % SZS output start Refutation
% 11.38/11.63  thf(v8_relat_2_type, type, v8_relat_2: $i > $o).
% 11.38/11.63  thf(sk_B_1_type, type, sk_B_1: $i).
% 11.38/11.63  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 11.38/11.63  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 11.38/11.63  thf(sk_C_6_type, type, sk_C_6: $i).
% 11.38/11.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 11.38/11.63  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 11.38/11.63  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 11.38/11.63  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 11.38/11.63  thf(v4_relat_2_type, type, v4_relat_2: $i > $o).
% 11.38/11.63  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 11.38/11.63  thf(v1_relat_2_type, type, v1_relat_2: $i > $o).
% 11.38/11.63  thf(v6_relat_2_type, type, v6_relat_2: $i > $o).
% 11.38/11.63  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 11.38/11.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 11.38/11.63  thf(sk_A_type, type, sk_A: $i).
% 11.38/11.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 11.38/11.63  thf(v1_wellord1_type, type, v1_wellord1: $i > $o).
% 11.38/11.63  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 11.38/11.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 11.38/11.63  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 11.38/11.63  thf(t37_wellord1, conjecture,
% 11.38/11.63    (![A:$i,B:$i,C:$i]:
% 11.38/11.63     ( ( v1_relat_1 @ C ) =>
% 11.38/11.63       ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 11.38/11.63           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) =>
% 11.38/11.63         ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 11.38/11.63           ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) ))).
% 11.38/11.63  thf(zf_stmt_0, negated_conjecture,
% 11.38/11.63    (~( ![A:$i,B:$i,C:$i]:
% 11.38/11.63        ( ( v1_relat_1 @ C ) =>
% 11.38/11.63          ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 11.38/11.63              ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) =>
% 11.38/11.63            ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 11.38/11.63              ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) ) )),
% 11.38/11.63    inference('cnf.neg', [status(esa)], [t37_wellord1])).
% 11.38/11.63  thf('0', plain,
% 11.38/11.63      ((~ (r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 11.38/11.63           (k1_wellord1 @ sk_C_6 @ sk_B_1))
% 11.38/11.63        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_6))),
% 11.38/11.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.38/11.63  thf('1', plain,
% 11.38/11.63      (~
% 11.38/11.63       ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 11.38/11.63         (k1_wellord1 @ sk_C_6 @ sk_B_1))) | 
% 11.38/11.63       ~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_6))),
% 11.38/11.63      inference('split', [status(esa)], ['0'])).
% 11.38/11.63  thf('2', plain,
% 11.38/11.63      (((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 11.38/11.63         (k1_wellord1 @ sk_C_6 @ sk_B_1))
% 11.38/11.63        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_6))),
% 11.38/11.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.38/11.63  thf('3', plain,
% 11.38/11.63      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_6))
% 11.38/11.63         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_6)))),
% 11.38/11.63      inference('split', [status(esa)], ['2'])).
% 11.38/11.63  thf(d1_wellord1, axiom,
% 11.38/11.63    (![A:$i]:
% 11.38/11.63     ( ( v1_relat_1 @ A ) =>
% 11.38/11.63       ( ![B:$i,C:$i]:
% 11.38/11.63         ( ( ( C ) = ( k1_wellord1 @ A @ B ) ) <=>
% 11.38/11.63           ( ![D:$i]:
% 11.38/11.63             ( ( r2_hidden @ D @ C ) <=>
% 11.38/11.63               ( ( ( D ) != ( B ) ) & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) ) ))).
% 11.38/11.63  thf('4', plain,
% 11.38/11.63      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 11.38/11.63         (((X12) != (k1_wellord1 @ X11 @ X10))
% 11.38/11.63          | (r2_hidden @ X14 @ X12)
% 11.38/11.63          | ~ (r2_hidden @ (k4_tarski @ X14 @ X10) @ X11)
% 11.38/11.63          | ((X14) = (X10))
% 11.38/11.63          | ~ (v1_relat_1 @ X11))),
% 11.38/11.63      inference('cnf', [status(esa)], [d1_wellord1])).
% 11.38/11.63  thf('5', plain,
% 11.38/11.63      (![X10 : $i, X11 : $i, X14 : $i]:
% 11.38/11.63         (~ (v1_relat_1 @ X11)
% 11.38/11.63          | ((X14) = (X10))
% 11.38/11.63          | ~ (r2_hidden @ (k4_tarski @ X14 @ X10) @ X11)
% 11.38/11.63          | (r2_hidden @ X14 @ (k1_wellord1 @ X11 @ X10)))),
% 11.38/11.63      inference('simplify', [status(thm)], ['4'])).
% 11.38/11.63  thf('6', plain,
% 11.38/11.63      ((((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_6 @ sk_B_1))
% 11.38/11.63         | ((sk_A) = (sk_B_1))
% 11.38/11.63         | ~ (v1_relat_1 @ sk_C_6)))
% 11.38/11.63         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_6)))),
% 11.38/11.63      inference('sup-', [status(thm)], ['3', '5'])).
% 11.38/11.63  thf('7', plain, ((v1_relat_1 @ sk_C_6)),
% 11.38/11.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.38/11.63  thf('8', plain,
% 11.38/11.63      ((((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_6 @ sk_B_1))
% 11.38/11.63         | ((sk_A) = (sk_B_1))))
% 11.38/11.63         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_6)))),
% 11.38/11.63      inference('demod', [status(thm)], ['6', '7'])).
% 11.38/11.63  thf(d3_tarski, axiom,
% 11.38/11.63    (![A:$i,B:$i]:
% 11.38/11.63     ( ( r1_tarski @ A @ B ) <=>
% 11.38/11.63       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 11.38/11.63  thf('9', plain,
% 11.38/11.63      (![X1 : $i, X3 : $i]:
% 11.38/11.63         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 11.38/11.63      inference('cnf', [status(esa)], [d3_tarski])).
% 11.38/11.63  thf('10', plain,
% 11.38/11.63      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 11.38/11.63         (((X12) != (k1_wellord1 @ X11 @ X10))
% 11.38/11.63          | (r2_hidden @ (k4_tarski @ X13 @ X10) @ X11)
% 11.38/11.63          | ~ (r2_hidden @ X13 @ X12)
% 11.38/11.63          | ~ (v1_relat_1 @ X11))),
% 11.38/11.63      inference('cnf', [status(esa)], [d1_wellord1])).
% 11.38/11.63  thf('11', plain,
% 11.38/11.63      (![X10 : $i, X11 : $i, X13 : $i]:
% 11.38/11.63         (~ (v1_relat_1 @ X11)
% 11.38/11.63          | ~ (r2_hidden @ X13 @ (k1_wellord1 @ X11 @ X10))
% 11.38/11.63          | (r2_hidden @ (k4_tarski @ X13 @ X10) @ X11))),
% 11.38/11.63      inference('simplify', [status(thm)], ['10'])).
% 11.38/11.63  thf('12', plain,
% 11.38/11.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.38/11.63         ((r1_tarski @ (k1_wellord1 @ X1 @ X0) @ X2)
% 11.38/11.63          | (r2_hidden @ 
% 11.38/11.63             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X1 @ X0)) @ X0) @ X1)
% 11.38/11.63          | ~ (v1_relat_1 @ X1))),
% 11.38/11.63      inference('sup-', [status(thm)], ['9', '11'])).
% 11.38/11.63  thf(t30_relat_1, axiom,
% 11.38/11.63    (![A:$i,B:$i,C:$i]:
% 11.38/11.63     ( ( v1_relat_1 @ C ) =>
% 11.38/11.63       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 11.38/11.63         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 11.38/11.63           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ))).
% 11.38/11.63  thf('13', plain,
% 11.38/11.63      (![X4 : $i, X5 : $i, X6 : $i]:
% 11.38/11.63         (~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ X6)
% 11.38/11.63          | (r2_hidden @ X5 @ (k3_relat_1 @ X6))
% 11.38/11.63          | ~ (v1_relat_1 @ X6))),
% 11.38/11.63      inference('cnf', [status(esa)], [t30_relat_1])).
% 11.38/11.63  thf('14', plain,
% 11.38/11.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.38/11.63         (~ (v1_relat_1 @ X0)
% 11.38/11.63          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 11.38/11.63          | ~ (v1_relat_1 @ X0)
% 11.38/11.63          | (r2_hidden @ X1 @ (k3_relat_1 @ X0)))),
% 11.38/11.63      inference('sup-', [status(thm)], ['12', '13'])).
% 11.38/11.63  thf('15', plain,
% 11.38/11.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.38/11.63         ((r2_hidden @ X1 @ (k3_relat_1 @ X0))
% 11.38/11.63          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 11.38/11.63          | ~ (v1_relat_1 @ X0))),
% 11.38/11.63      inference('simplify', [status(thm)], ['14'])).
% 11.38/11.63  thf(t36_wellord1, axiom,
% 11.38/11.63    (![A:$i,B:$i]:
% 11.38/11.63     ( ( v1_relat_1 @ B ) =>
% 11.38/11.63       ( ( ( r1_tarski @ A @ ( k3_relat_1 @ B ) ) & ( v2_wellord1 @ B ) ) =>
% 11.38/11.63         ( ( ~( ( ![C:$i]:
% 11.38/11.63                  ( ~( ( ( A ) = ( k1_wellord1 @ B @ C ) ) & 
% 11.38/11.63                       ( r2_hidden @ C @ ( k3_relat_1 @ B ) ) ) ) ) & 
% 11.38/11.63                ( ( A ) != ( k3_relat_1 @ B ) ) ) ) <=>
% 11.38/11.63           ( ![C:$i]:
% 11.38/11.63             ( ( r2_hidden @ C @ A ) =>
% 11.38/11.63               ( ![D:$i]:
% 11.38/11.63                 ( ( r2_hidden @ ( k4_tarski @ D @ C ) @ B ) =>
% 11.38/11.63                   ( r2_hidden @ D @ A ) ) ) ) ) ) ) ))).
% 11.38/11.63  thf(zf_stmt_1, axiom,
% 11.38/11.63    (![C:$i,B:$i,A:$i]:
% 11.38/11.63     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 11.38/11.63       ( ( r2_hidden @ C @ ( k3_relat_1 @ B ) ) & 
% 11.38/11.63         ( ( A ) = ( k1_wellord1 @ B @ C ) ) ) ))).
% 11.38/11.63  thf('16', plain,
% 11.38/11.63      (![X28 : $i, X29 : $i, X31 : $i]:
% 11.38/11.63         ((zip_tseitin_0 @ X28 @ X29 @ X31)
% 11.38/11.63          | ((X31) != (k1_wellord1 @ X29 @ X28))
% 11.38/11.63          | ~ (r2_hidden @ X28 @ (k3_relat_1 @ X29)))),
% 11.38/11.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 11.38/11.63  thf('17', plain,
% 11.38/11.63      (![X28 : $i, X29 : $i]:
% 11.38/11.63         (~ (r2_hidden @ X28 @ (k3_relat_1 @ X29))
% 11.38/11.63          | (zip_tseitin_0 @ X28 @ X29 @ (k1_wellord1 @ X29 @ X28)))),
% 11.38/11.63      inference('simplify', [status(thm)], ['16'])).
% 11.38/11.63  thf('18', plain,
% 11.38/11.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.38/11.63         (~ (v1_relat_1 @ X0)
% 11.38/11.63          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 11.38/11.63          | (zip_tseitin_0 @ X1 @ X0 @ (k1_wellord1 @ X0 @ X1)))),
% 11.38/11.63      inference('sup-', [status(thm)], ['15', '17'])).
% 11.38/11.63  thf(t13_wellord1, axiom,
% 11.38/11.63    (![A:$i,B:$i]:
% 11.38/11.63     ( ( v1_relat_1 @ B ) =>
% 11.38/11.63       ( r1_tarski @ ( k1_wellord1 @ B @ A ) @ ( k3_relat_1 @ B ) ) ))).
% 11.38/11.63  thf('19', plain,
% 11.38/11.63      (![X26 : $i, X27 : $i]:
% 11.38/11.63         ((r1_tarski @ (k1_wellord1 @ X26 @ X27) @ (k3_relat_1 @ X26))
% 11.38/11.63          | ~ (v1_relat_1 @ X26))),
% 11.38/11.63      inference('cnf', [status(esa)], [t13_wellord1])).
% 11.38/11.63  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 11.38/11.63  thf(zf_stmt_3, axiom,
% 11.38/11.63    (![C:$i,B:$i,A:$i]:
% 11.38/11.63     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 11.38/11.63       ( ( r2_hidden @ C @ A ) =>
% 11.38/11.63         ( ![D:$i]:
% 11.38/11.63           ( ( r2_hidden @ ( k4_tarski @ D @ C ) @ B ) => ( r2_hidden @ D @ A ) ) ) ) ))).
% 11.38/11.63  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $i > $o).
% 11.38/11.63  thf(zf_stmt_5, axiom,
% 11.38/11.63    (![A:$i,B:$i]:
% 11.38/11.63     ( ( v1_relat_1 @ B ) =>
% 11.38/11.63       ( ( ( v2_wellord1 @ B ) & ( r1_tarski @ A @ ( k3_relat_1 @ B ) ) ) =>
% 11.38/11.63         ( ( ~( ( ( A ) != ( k3_relat_1 @ B ) ) & 
% 11.38/11.63                ( ![C:$i]: ( ~( zip_tseitin_0 @ C @ B @ A ) ) ) ) ) <=>
% 11.38/11.63           ( ![C:$i]: ( zip_tseitin_1 @ C @ B @ A ) ) ) ) ))).
% 11.38/11.63  thf('20', plain,
% 11.38/11.63      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 11.38/11.63         (~ (v2_wellord1 @ X37)
% 11.38/11.63          | ~ (r1_tarski @ X38 @ (k3_relat_1 @ X37))
% 11.38/11.63          | ~ (zip_tseitin_0 @ X39 @ X37 @ X38)
% 11.38/11.63          | (zip_tseitin_1 @ X40 @ X37 @ X38)
% 11.38/11.63          | ~ (v1_relat_1 @ X37))),
% 11.38/11.63      inference('cnf', [status(esa)], [zf_stmt_5])).
% 11.38/11.63  thf('21', plain,
% 11.38/11.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.38/11.63         (~ (v1_relat_1 @ X0)
% 11.38/11.63          | ~ (v1_relat_1 @ X0)
% 11.38/11.63          | (zip_tseitin_1 @ X2 @ X0 @ (k1_wellord1 @ X0 @ X1))
% 11.38/11.63          | ~ (zip_tseitin_0 @ X3 @ X0 @ (k1_wellord1 @ X0 @ X1))
% 11.38/11.63          | ~ (v2_wellord1 @ X0))),
% 11.38/11.63      inference('sup-', [status(thm)], ['19', '20'])).
% 11.38/11.63  thf('22', plain,
% 11.38/11.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.38/11.63         (~ (v2_wellord1 @ X0)
% 11.38/11.63          | ~ (zip_tseitin_0 @ X3 @ X0 @ (k1_wellord1 @ X0 @ X1))
% 11.38/11.63          | (zip_tseitin_1 @ X2 @ X0 @ (k1_wellord1 @ X0 @ X1))
% 11.38/11.63          | ~ (v1_relat_1 @ X0))),
% 11.38/11.63      inference('simplify', [status(thm)], ['21'])).
% 11.38/11.63  thf('23', plain,
% 11.38/11.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.38/11.63         ((r1_tarski @ (k1_wellord1 @ X1 @ X0) @ X3)
% 11.38/11.63          | ~ (v1_relat_1 @ X1)
% 11.38/11.63          | ~ (v1_relat_1 @ X1)
% 11.38/11.63          | (zip_tseitin_1 @ X2 @ X1 @ (k1_wellord1 @ X1 @ X0))
% 11.38/11.63          | ~ (v2_wellord1 @ X1))),
% 11.38/11.63      inference('sup-', [status(thm)], ['18', '22'])).
% 11.38/11.63  thf('24', plain,
% 11.38/11.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.38/11.63         (~ (v2_wellord1 @ X1)
% 11.38/11.63          | (zip_tseitin_1 @ X2 @ X1 @ (k1_wellord1 @ X1 @ X0))
% 11.38/11.63          | ~ (v1_relat_1 @ X1)
% 11.38/11.63          | (r1_tarski @ (k1_wellord1 @ X1 @ X0) @ X3))),
% 11.38/11.63      inference('simplify', [status(thm)], ['23'])).
% 11.38/11.63  thf('25', plain,
% 11.38/11.63      (![X32 : $i, X35 : $i, X36 : $i]:
% 11.38/11.63         ((zip_tseitin_1 @ X32 @ X35 @ X36) | (r2_hidden @ X32 @ X36))),
% 11.38/11.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 11.38/11.63  thf(t7_ordinal1, axiom,
% 11.38/11.63    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 11.38/11.63  thf('26', plain,
% 11.38/11.63      (![X7 : $i, X8 : $i]: (~ (r2_hidden @ X7 @ X8) | ~ (r1_tarski @ X8 @ X7))),
% 11.38/11.63      inference('cnf', [status(esa)], [t7_ordinal1])).
% 11.38/11.63  thf('27', plain,
% 11.38/11.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.38/11.63         ((zip_tseitin_1 @ X1 @ X2 @ X0) | ~ (r1_tarski @ X0 @ X1))),
% 11.38/11.63      inference('sup-', [status(thm)], ['25', '26'])).
% 11.38/11.63  thf('28', plain,
% 11.38/11.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 11.38/11.63         (~ (v1_relat_1 @ X2)
% 11.38/11.63          | (zip_tseitin_1 @ X4 @ X2 @ (k1_wellord1 @ X2 @ X1))
% 11.38/11.63          | ~ (v2_wellord1 @ X2)
% 11.38/11.63          | (zip_tseitin_1 @ X0 @ X3 @ (k1_wellord1 @ X2 @ X1)))),
% 11.38/11.63      inference('sup-', [status(thm)], ['24', '27'])).
% 11.38/11.63  thf('29', plain,
% 11.38/11.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.38/11.63         ((zip_tseitin_1 @ X2 @ X1 @ (k1_wellord1 @ X1 @ X0))
% 11.38/11.63          | ~ (v2_wellord1 @ X1)
% 11.38/11.63          | ~ (v1_relat_1 @ X1))),
% 11.38/11.63      inference('eq_fact', [status(thm)], ['28'])).
% 11.38/11.63  thf('30', plain,
% 11.38/11.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.38/11.63         ((r1_tarski @ (k1_wellord1 @ X1 @ X0) @ X2)
% 11.38/11.63          | (r2_hidden @ 
% 11.38/11.63             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X1 @ X0)) @ X0) @ X1)
% 11.38/11.63          | ~ (v1_relat_1 @ X1))),
% 11.38/11.63      inference('sup-', [status(thm)], ['9', '11'])).
% 11.38/11.63  thf('31', plain,
% 11.38/11.63      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 11.38/11.63         (~ (r2_hidden @ X32 @ X33)
% 11.38/11.63          | ~ (r2_hidden @ (k4_tarski @ X34 @ X32) @ X35)
% 11.38/11.63          | (r2_hidden @ X34 @ X33)
% 11.38/11.63          | ~ (zip_tseitin_1 @ X32 @ X35 @ X33))),
% 11.38/11.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 11.38/11.63  thf('32', plain,
% 11.38/11.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.38/11.63         (~ (v1_relat_1 @ X0)
% 11.38/11.63          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 11.38/11.63          | ~ (zip_tseitin_1 @ X1 @ X0 @ X3)
% 11.38/11.63          | (r2_hidden @ (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1)) @ X3)
% 11.38/11.63          | ~ (r2_hidden @ X1 @ X3))),
% 11.38/11.63      inference('sup-', [status(thm)], ['30', '31'])).
% 11.38/11.63  thf('33', plain,
% 11.38/11.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.38/11.63         (~ (v1_relat_1 @ X1)
% 11.38/11.63          | ~ (v2_wellord1 @ X1)
% 11.38/11.63          | ~ (r2_hidden @ X2 @ (k1_wellord1 @ X1 @ X0))
% 11.38/11.63          | (r2_hidden @ (sk_C @ X3 @ (k1_wellord1 @ X1 @ X2)) @ 
% 11.38/11.63             (k1_wellord1 @ X1 @ X0))
% 11.38/11.63          | (r1_tarski @ (k1_wellord1 @ X1 @ X2) @ X3)
% 11.38/11.63          | ~ (v1_relat_1 @ X1))),
% 11.38/11.63      inference('sup-', [status(thm)], ['29', '32'])).
% 11.38/11.63  thf('34', plain,
% 11.38/11.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.38/11.63         ((r1_tarski @ (k1_wellord1 @ X1 @ X2) @ X3)
% 11.38/11.63          | (r2_hidden @ (sk_C @ X3 @ (k1_wellord1 @ X1 @ X2)) @ 
% 11.38/11.63             (k1_wellord1 @ X1 @ X0))
% 11.38/11.63          | ~ (r2_hidden @ X2 @ (k1_wellord1 @ X1 @ X0))
% 11.38/11.63          | ~ (v2_wellord1 @ X1)
% 11.38/11.63          | ~ (v1_relat_1 @ X1))),
% 11.38/11.63      inference('simplify', [status(thm)], ['33'])).
% 11.38/11.63  thf('35', plain,
% 11.38/11.63      ((![X0 : $i]:
% 11.38/11.63          (((sk_A) = (sk_B_1))
% 11.38/11.63           | ~ (v1_relat_1 @ sk_C_6)
% 11.38/11.63           | ~ (v2_wellord1 @ sk_C_6)
% 11.38/11.63           | (r2_hidden @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_6 @ sk_A)) @ 
% 11.38/11.63              (k1_wellord1 @ sk_C_6 @ sk_B_1))
% 11.38/11.63           | (r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ X0)))
% 11.38/11.63         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_6)))),
% 11.38/11.63      inference('sup-', [status(thm)], ['8', '34'])).
% 11.38/11.63  thf('36', plain, ((v1_relat_1 @ sk_C_6)),
% 11.38/11.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.38/11.63  thf('37', plain, ((v2_wellord1 @ sk_C_6)),
% 11.38/11.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.38/11.63  thf('38', plain,
% 11.38/11.63      ((![X0 : $i]:
% 11.38/11.63          (((sk_A) = (sk_B_1))
% 11.38/11.63           | (r2_hidden @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_6 @ sk_A)) @ 
% 11.38/11.63              (k1_wellord1 @ sk_C_6 @ sk_B_1))
% 11.38/11.63           | (r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ X0)))
% 11.38/11.63         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_6)))),
% 11.38/11.63      inference('demod', [status(thm)], ['35', '36', '37'])).
% 11.38/11.63  thf('39', plain,
% 11.38/11.63      (![X1 : $i, X3 : $i]:
% 11.38/11.63         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 11.38/11.63      inference('cnf', [status(esa)], [d3_tarski])).
% 11.38/11.63  thf('40', plain,
% 11.38/11.63      ((((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 11.38/11.63          (k1_wellord1 @ sk_C_6 @ sk_B_1))
% 11.38/11.63         | ((sk_A) = (sk_B_1))
% 11.38/11.63         | (r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 11.38/11.63            (k1_wellord1 @ sk_C_6 @ sk_B_1))))
% 11.38/11.63         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_6)))),
% 11.38/11.63      inference('sup-', [status(thm)], ['38', '39'])).
% 11.38/11.63  thf('41', plain,
% 11.38/11.63      (((((sk_A) = (sk_B_1))
% 11.38/11.63         | (r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 11.38/11.63            (k1_wellord1 @ sk_C_6 @ sk_B_1))))
% 11.38/11.63         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_6)))),
% 11.38/11.63      inference('simplify', [status(thm)], ['40'])).
% 11.38/11.63  thf('42', plain,
% 11.38/11.63      ((~ (r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 11.38/11.63           (k1_wellord1 @ sk_C_6 @ sk_B_1)))
% 11.38/11.63         <= (~
% 11.38/11.63             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 11.38/11.63               (k1_wellord1 @ sk_C_6 @ sk_B_1))))),
% 11.38/11.63      inference('split', [status(esa)], ['0'])).
% 11.38/11.63  thf('43', plain,
% 11.38/11.63      ((((sk_A) = (sk_B_1)))
% 11.38/11.63         <= (~
% 11.38/11.63             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 11.38/11.63               (k1_wellord1 @ sk_C_6 @ sk_B_1))) & 
% 11.38/11.63             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_6)))),
% 11.38/11.63      inference('sup-', [status(thm)], ['41', '42'])).
% 11.38/11.63  thf('44', plain,
% 11.38/11.63      ((~ (r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 11.38/11.63           (k1_wellord1 @ sk_C_6 @ sk_B_1)))
% 11.38/11.63         <= (~
% 11.38/11.63             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 11.38/11.63               (k1_wellord1 @ sk_C_6 @ sk_B_1))))),
% 11.38/11.63      inference('split', [status(esa)], ['0'])).
% 11.38/11.63  thf('45', plain,
% 11.38/11.63      ((~ (r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 11.38/11.63           (k1_wellord1 @ sk_C_6 @ sk_A)))
% 11.38/11.63         <= (~
% 11.38/11.63             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 11.38/11.63               (k1_wellord1 @ sk_C_6 @ sk_B_1))) & 
% 11.38/11.63             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_6)))),
% 11.38/11.63      inference('sup-', [status(thm)], ['43', '44'])).
% 11.38/11.63  thf('46', plain,
% 11.38/11.63      (![X1 : $i, X3 : $i]:
% 11.38/11.63         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 11.38/11.63      inference('cnf', [status(esa)], [d3_tarski])).
% 11.38/11.63  thf('47', plain,
% 11.38/11.63      (![X1 : $i, X3 : $i]:
% 11.38/11.63         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 11.38/11.63      inference('cnf', [status(esa)], [d3_tarski])).
% 11.38/11.63  thf('48', plain,
% 11.38/11.63      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 11.38/11.63      inference('sup-', [status(thm)], ['46', '47'])).
% 11.38/11.63  thf('49', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 11.38/11.63      inference('simplify', [status(thm)], ['48'])).
% 11.38/11.63  thf('50', plain,
% 11.38/11.63      (((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 11.38/11.63         (k1_wellord1 @ sk_C_6 @ sk_B_1))) | 
% 11.38/11.63       ~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_6))),
% 11.38/11.63      inference('demod', [status(thm)], ['45', '49'])).
% 11.38/11.63  thf('51', plain,
% 11.38/11.63      (((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 11.38/11.63         (k1_wellord1 @ sk_C_6 @ sk_B_1))) | 
% 11.38/11.63       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_6))),
% 11.38/11.63      inference('split', [status(esa)], ['2'])).
% 11.38/11.63  thf('52', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_6))),
% 11.38/11.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.38/11.63  thf(s1_xboole_0__e7_18__wellord1, axiom,
% 11.38/11.63    (![A:$i,B:$i]:
% 11.38/11.63     ( ( v1_relat_1 @ A ) =>
% 11.38/11.63       ( ?[C:$i]:
% 11.38/11.63         ( ![D:$i]:
% 11.38/11.63           ( ( r2_hidden @ D @ C ) <=>
% 11.38/11.63             ( ( r2_hidden @ D @ ( k3_relat_1 @ A ) ) & 
% 11.38/11.63               ( ~( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) ) ))).
% 11.38/11.63  thf('53', plain,
% 11.38/11.63      (![X19 : $i, X20 : $i, X21 : $i]:
% 11.38/11.63         (~ (v1_relat_1 @ X19)
% 11.38/11.63          | (r2_hidden @ X20 @ (sk_C_2 @ X21 @ X19))
% 11.38/11.63          | (r2_hidden @ (k4_tarski @ X20 @ X21) @ X19)
% 11.38/11.63          | ~ (r2_hidden @ X20 @ (k3_relat_1 @ X19)))),
% 11.38/11.63      inference('cnf', [status(esa)], [s1_xboole_0__e7_18__wellord1])).
% 11.38/11.63  thf('54', plain,
% 11.38/11.63      (![X0 : $i]:
% 11.38/11.63         ((r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_6)
% 11.38/11.63          | (r2_hidden @ sk_A @ (sk_C_2 @ X0 @ sk_C_6))
% 11.38/11.63          | ~ (v1_relat_1 @ sk_C_6))),
% 11.38/11.63      inference('sup-', [status(thm)], ['52', '53'])).
% 11.38/11.63  thf('55', plain, ((v1_relat_1 @ sk_C_6)),
% 11.38/11.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.38/11.63  thf('56', plain,
% 11.38/11.63      (![X0 : $i]:
% 11.38/11.63         ((r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_6)
% 11.38/11.63          | (r2_hidden @ sk_A @ (sk_C_2 @ X0 @ sk_C_6)))),
% 11.38/11.63      inference('demod', [status(thm)], ['54', '55'])).
% 11.38/11.63  thf('57', plain, ((r2_hidden @ sk_B_1 @ (k3_relat_1 @ sk_C_6))),
% 11.38/11.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.38/11.63  thf('58', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_6))),
% 11.38/11.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.38/11.63  thf(l4_wellord1, axiom,
% 11.38/11.63    (![A:$i]:
% 11.38/11.63     ( ( v1_relat_1 @ A ) =>
% 11.38/11.63       ( ( v6_relat_2 @ A ) <=>
% 11.38/11.63         ( ![B:$i,C:$i]:
% 11.38/11.63           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 11.38/11.63                ( r2_hidden @ C @ ( k3_relat_1 @ A ) ) & ( ( B ) != ( C ) ) & 
% 11.38/11.63                ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) & 
% 11.38/11.63                ( ~( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) ) ) ) ) ) ))).
% 11.38/11.63  thf('59', plain,
% 11.38/11.63      (![X16 : $i, X17 : $i, X18 : $i]:
% 11.38/11.63         (~ (v6_relat_2 @ X16)
% 11.38/11.63          | ~ (r2_hidden @ X17 @ (k3_relat_1 @ X16))
% 11.38/11.63          | (r2_hidden @ (k4_tarski @ X18 @ X17) @ X16)
% 11.38/11.63          | (r2_hidden @ (k4_tarski @ X17 @ X18) @ X16)
% 11.38/11.63          | ((X17) = (X18))
% 11.38/11.63          | ~ (r2_hidden @ X18 @ (k3_relat_1 @ X16))
% 11.38/11.63          | ~ (v1_relat_1 @ X16))),
% 11.38/11.63      inference('cnf', [status(esa)], [l4_wellord1])).
% 11.38/11.63  thf('60', plain,
% 11.38/11.63      (![X0 : $i]:
% 11.38/11.63         (~ (v1_relat_1 @ sk_C_6)
% 11.38/11.63          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C_6))
% 11.38/11.63          | ((sk_A) = (X0))
% 11.38/11.63          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_6)
% 11.38/11.63          | (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ sk_C_6)
% 11.38/11.63          | ~ (v6_relat_2 @ sk_C_6))),
% 11.38/11.63      inference('sup-', [status(thm)], ['58', '59'])).
% 11.38/11.63  thf('61', plain, ((v1_relat_1 @ sk_C_6)),
% 11.38/11.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.38/11.63  thf('62', plain, ((v1_relat_1 @ sk_C_6)),
% 11.38/11.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.38/11.63  thf(d4_wellord1, axiom,
% 11.38/11.63    (![A:$i]:
% 11.38/11.63     ( ( v1_relat_1 @ A ) =>
% 11.38/11.63       ( ( v2_wellord1 @ A ) <=>
% 11.38/11.63         ( ( v1_relat_2 @ A ) & ( v8_relat_2 @ A ) & ( v4_relat_2 @ A ) & 
% 11.38/11.63           ( v6_relat_2 @ A ) & ( v1_wellord1 @ A ) ) ) ))).
% 11.38/11.63  thf('63', plain,
% 11.38/11.63      (![X15 : $i]:
% 11.38/11.63         (~ (v2_wellord1 @ X15) | (v6_relat_2 @ X15) | ~ (v1_relat_1 @ X15))),
% 11.38/11.63      inference('cnf', [status(esa)], [d4_wellord1])).
% 11.38/11.63  thf('64', plain, (((v6_relat_2 @ sk_C_6) | ~ (v2_wellord1 @ sk_C_6))),
% 11.38/11.63      inference('sup-', [status(thm)], ['62', '63'])).
% 11.38/11.63  thf('65', plain, ((v2_wellord1 @ sk_C_6)),
% 11.38/11.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.38/11.63  thf('66', plain, ((v6_relat_2 @ sk_C_6)),
% 11.38/11.63      inference('demod', [status(thm)], ['64', '65'])).
% 11.38/11.63  thf('67', plain,
% 11.38/11.63      (![X0 : $i]:
% 11.38/11.63         (~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C_6))
% 11.38/11.63          | ((sk_A) = (X0))
% 11.38/11.63          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_6)
% 11.38/11.63          | (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ sk_C_6))),
% 11.38/11.63      inference('demod', [status(thm)], ['60', '61', '66'])).
% 11.38/11.63  thf('68', plain,
% 11.38/11.63      (((r2_hidden @ (k4_tarski @ sk_B_1 @ sk_A) @ sk_C_6)
% 11.38/11.63        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_6)
% 11.38/11.63        | ((sk_A) = (sk_B_1)))),
% 11.38/11.63      inference('sup-', [status(thm)], ['57', '67'])).
% 11.38/11.63  thf('69', plain,
% 11.38/11.63      (![X10 : $i, X11 : $i, X14 : $i]:
% 11.38/11.63         (~ (v1_relat_1 @ X11)
% 11.38/11.63          | ((X14) = (X10))
% 11.38/11.63          | ~ (r2_hidden @ (k4_tarski @ X14 @ X10) @ X11)
% 11.38/11.63          | (r2_hidden @ X14 @ (k1_wellord1 @ X11 @ X10)))),
% 11.38/11.63      inference('simplify', [status(thm)], ['4'])).
% 11.38/11.63  thf('70', plain,
% 11.38/11.63      ((((sk_A) = (sk_B_1))
% 11.38/11.63        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_6)
% 11.38/11.63        | (r2_hidden @ sk_B_1 @ (k1_wellord1 @ sk_C_6 @ sk_A))
% 11.38/11.63        | ((sk_B_1) = (sk_A))
% 11.38/11.63        | ~ (v1_relat_1 @ sk_C_6))),
% 11.38/11.63      inference('sup-', [status(thm)], ['68', '69'])).
% 11.38/11.63  thf('71', plain, ((v1_relat_1 @ sk_C_6)),
% 11.38/11.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.38/11.63  thf('72', plain,
% 11.38/11.63      ((((sk_A) = (sk_B_1))
% 11.38/11.63        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_6)
% 11.38/11.63        | (r2_hidden @ sk_B_1 @ (k1_wellord1 @ sk_C_6 @ sk_A))
% 11.38/11.63        | ((sk_B_1) = (sk_A)))),
% 11.38/11.63      inference('demod', [status(thm)], ['70', '71'])).
% 11.38/11.63  thf('73', plain,
% 11.38/11.63      (((r2_hidden @ sk_B_1 @ (k1_wellord1 @ sk_C_6 @ sk_A))
% 11.38/11.63        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_6)
% 11.38/11.63        | ((sk_A) = (sk_B_1)))),
% 11.38/11.63      inference('simplify', [status(thm)], ['72'])).
% 11.38/11.63  thf('74', plain,
% 11.38/11.63      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_6))
% 11.38/11.63         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_6)))),
% 11.38/11.63      inference('split', [status(esa)], ['0'])).
% 11.38/11.63  thf('75', plain,
% 11.38/11.63      (((((sk_A) = (sk_B_1))
% 11.38/11.63         | (r2_hidden @ sk_B_1 @ (k1_wellord1 @ sk_C_6 @ sk_A))))
% 11.38/11.63         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_6)))),
% 11.38/11.63      inference('sup-', [status(thm)], ['73', '74'])).
% 11.38/11.63  thf('76', plain,
% 11.38/11.63      (((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 11.38/11.63         (k1_wellord1 @ sk_C_6 @ sk_B_1)))
% 11.38/11.63         <= (((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 11.38/11.63               (k1_wellord1 @ sk_C_6 @ sk_B_1))))),
% 11.38/11.63      inference('split', [status(esa)], ['2'])).
% 11.38/11.63  thf('77', plain,
% 11.38/11.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.38/11.63         (~ (r2_hidden @ X0 @ X1)
% 11.38/11.63          | (r2_hidden @ X0 @ X2)
% 11.38/11.63          | ~ (r1_tarski @ X1 @ X2))),
% 11.38/11.63      inference('cnf', [status(esa)], [d3_tarski])).
% 11.38/11.63  thf('78', plain,
% 11.38/11.63      ((![X0 : $i]:
% 11.38/11.63          ((r2_hidden @ X0 @ (k1_wellord1 @ sk_C_6 @ sk_B_1))
% 11.38/11.63           | ~ (r2_hidden @ X0 @ (k1_wellord1 @ sk_C_6 @ sk_A))))
% 11.38/11.63         <= (((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 11.38/11.63               (k1_wellord1 @ sk_C_6 @ sk_B_1))))),
% 11.38/11.63      inference('sup-', [status(thm)], ['76', '77'])).
% 11.38/11.63  thf('79', plain,
% 11.38/11.63      (((((sk_A) = (sk_B_1))
% 11.38/11.63         | (r2_hidden @ sk_B_1 @ (k1_wellord1 @ sk_C_6 @ sk_B_1))))
% 11.38/11.63         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_6)) & 
% 11.38/11.63             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 11.38/11.63               (k1_wellord1 @ sk_C_6 @ sk_B_1))))),
% 11.38/11.63      inference('sup-', [status(thm)], ['75', '78'])).
% 11.38/11.63  thf('80', plain,
% 11.38/11.63      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 11.38/11.63         (((X12) != (k1_wellord1 @ X11 @ X10))
% 11.38/11.63          | ((X13) != (X10))
% 11.38/11.63          | ~ (r2_hidden @ X13 @ X12)
% 11.38/11.63          | ~ (v1_relat_1 @ X11))),
% 11.38/11.63      inference('cnf', [status(esa)], [d1_wellord1])).
% 11.38/11.63  thf('81', plain,
% 11.38/11.63      (![X10 : $i, X11 : $i]:
% 11.38/11.63         (~ (v1_relat_1 @ X11)
% 11.38/11.63          | ~ (r2_hidden @ X10 @ (k1_wellord1 @ X11 @ X10)))),
% 11.38/11.63      inference('simplify', [status(thm)], ['80'])).
% 11.38/11.63  thf('82', plain,
% 11.38/11.63      (((((sk_A) = (sk_B_1)) | ~ (v1_relat_1 @ sk_C_6)))
% 11.38/11.63         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_6)) & 
% 11.38/11.63             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 11.38/11.63               (k1_wellord1 @ sk_C_6 @ sk_B_1))))),
% 11.38/11.63      inference('sup-', [status(thm)], ['79', '81'])).
% 11.38/11.63  thf('83', plain, ((v1_relat_1 @ sk_C_6)),
% 11.38/11.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.38/11.63  thf('84', plain,
% 11.38/11.63      ((((sk_A) = (sk_B_1)))
% 11.38/11.63         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_6)) & 
% 11.38/11.63             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 11.38/11.63               (k1_wellord1 @ sk_C_6 @ sk_B_1))))),
% 11.38/11.63      inference('demod', [status(thm)], ['82', '83'])).
% 11.38/11.63  thf('85', plain,
% 11.38/11.63      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_6))
% 11.38/11.63         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_6)))),
% 11.38/11.63      inference('split', [status(esa)], ['0'])).
% 11.38/11.63  thf('86', plain,
% 11.38/11.63      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_A) @ sk_C_6))
% 11.38/11.63         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_6)) & 
% 11.38/11.63             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 11.38/11.63               (k1_wellord1 @ sk_C_6 @ sk_B_1))))),
% 11.38/11.63      inference('sup-', [status(thm)], ['84', '85'])).
% 11.38/11.63  thf('87', plain,
% 11.38/11.63      (((r2_hidden @ sk_A @ (sk_C_2 @ sk_A @ sk_C_6)))
% 11.38/11.63         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_6)) & 
% 11.38/11.63             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 11.38/11.63               (k1_wellord1 @ sk_C_6 @ sk_B_1))))),
% 11.38/11.63      inference('sup-', [status(thm)], ['56', '86'])).
% 11.38/11.63  thf('88', plain,
% 11.38/11.63      (![X7 : $i, X8 : $i]: (~ (r2_hidden @ X7 @ X8) | ~ (r1_tarski @ X8 @ X7))),
% 11.38/11.63      inference('cnf', [status(esa)], [t7_ordinal1])).
% 11.38/11.63  thf('89', plain,
% 11.38/11.63      ((~ (r1_tarski @ (sk_C_2 @ sk_A @ sk_C_6) @ sk_A))
% 11.38/11.63         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_6)) & 
% 11.38/11.63             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 11.38/11.63               (k1_wellord1 @ sk_C_6 @ sk_B_1))))),
% 11.38/11.63      inference('sup-', [status(thm)], ['87', '88'])).
% 11.38/11.63  thf('90', plain,
% 11.38/11.63      (![X1 : $i, X3 : $i]:
% 11.38/11.63         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 11.38/11.63      inference('cnf', [status(esa)], [d3_tarski])).
% 11.38/11.63  thf('91', plain,
% 11.38/11.63      (![X19 : $i, X21 : $i, X22 : $i]:
% 11.38/11.63         (~ (v1_relat_1 @ X19)
% 11.38/11.63          | (r2_hidden @ X22 @ (k3_relat_1 @ X19))
% 11.38/11.63          | ~ (r2_hidden @ X22 @ (sk_C_2 @ X21 @ X19)))),
% 11.38/11.63      inference('cnf', [status(esa)], [s1_xboole_0__e7_18__wellord1])).
% 11.38/11.63  thf('92', plain,
% 11.38/11.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.38/11.63         ((r1_tarski @ (sk_C_2 @ X1 @ X0) @ X2)
% 11.38/11.63          | (r2_hidden @ (sk_C @ X2 @ (sk_C_2 @ X1 @ X0)) @ (k3_relat_1 @ X0))
% 11.38/11.63          | ~ (v1_relat_1 @ X0))),
% 11.38/11.63      inference('sup-', [status(thm)], ['90', '91'])).
% 11.38/11.63  thf('93', plain,
% 11.38/11.63      (![X1 : $i, X3 : $i]:
% 11.38/11.63         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 11.38/11.63      inference('cnf', [status(esa)], [d3_tarski])).
% 11.38/11.63  thf('94', plain,
% 11.38/11.63      (![X0 : $i, X1 : $i]:
% 11.38/11.63         (~ (v1_relat_1 @ X0)
% 11.38/11.63          | (r1_tarski @ (sk_C_2 @ X1 @ X0) @ (k3_relat_1 @ X0))
% 11.38/11.63          | (r1_tarski @ (sk_C_2 @ X1 @ X0) @ (k3_relat_1 @ X0)))),
% 11.38/11.63      inference('sup-', [status(thm)], ['92', '93'])).
% 11.38/11.63  thf('95', plain,
% 11.38/11.63      (![X0 : $i, X1 : $i]:
% 11.38/11.63         ((r1_tarski @ (sk_C_2 @ X1 @ X0) @ (k3_relat_1 @ X0))
% 11.38/11.63          | ~ (v1_relat_1 @ X0))),
% 11.38/11.63      inference('simplify', [status(thm)], ['94'])).
% 11.38/11.63  thf(t10_wellord1, axiom,
% 11.38/11.63    (![A:$i]:
% 11.38/11.63     ( ( v1_relat_1 @ A ) =>
% 11.38/11.63       ( ( v2_wellord1 @ A ) =>
% 11.38/11.63         ( ![B:$i]:
% 11.38/11.63           ( ~( ( r1_tarski @ B @ ( k3_relat_1 @ A ) ) & 
% 11.38/11.63                ( ( B ) != ( k1_xboole_0 ) ) & 
% 11.38/11.63                ( ![C:$i]:
% 11.38/11.63                  ( ~( ( r2_hidden @ C @ B ) & 
% 11.38/11.63                       ( ![D:$i]:
% 11.38/11.63                         ( ( r2_hidden @ D @ B ) =>
% 11.38/11.63                           ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ) ) ) ) ) ) ))).
% 11.38/11.63  thf('96', plain,
% 11.38/11.63      (![X23 : $i, X25 : $i]:
% 11.38/11.63         (~ (v2_wellord1 @ X23)
% 11.38/11.63          | (r2_hidden @ (sk_C_3 @ X25 @ X23) @ X25)
% 11.38/11.63          | ((X25) = (k1_xboole_0))
% 11.38/11.63          | ~ (r1_tarski @ X25 @ (k3_relat_1 @ X23))
% 11.38/11.63          | ~ (v1_relat_1 @ X23))),
% 11.38/11.63      inference('cnf', [status(esa)], [t10_wellord1])).
% 11.38/11.63  thf('97', plain,
% 11.38/11.63      (![X0 : $i, X1 : $i]:
% 11.38/11.63         (~ (v1_relat_1 @ X0)
% 11.38/11.63          | ~ (v1_relat_1 @ X0)
% 11.38/11.63          | ((sk_C_2 @ X1 @ X0) = (k1_xboole_0))
% 11.38/11.63          | (r2_hidden @ (sk_C_3 @ (sk_C_2 @ X1 @ X0) @ X0) @ 
% 11.38/11.63             (sk_C_2 @ X1 @ X0))
% 11.38/11.63          | ~ (v2_wellord1 @ X0))),
% 11.38/11.63      inference('sup-', [status(thm)], ['95', '96'])).
% 11.38/11.63  thf('98', plain,
% 11.38/11.63      (![X0 : $i, X1 : $i]:
% 11.38/11.63         (~ (v2_wellord1 @ X0)
% 11.38/11.63          | (r2_hidden @ (sk_C_3 @ (sk_C_2 @ X1 @ X0) @ X0) @ 
% 11.38/11.63             (sk_C_2 @ X1 @ X0))
% 11.38/11.63          | ((sk_C_2 @ X1 @ X0) = (k1_xboole_0))
% 11.38/11.63          | ~ (v1_relat_1 @ X0))),
% 11.38/11.63      inference('simplify', [status(thm)], ['97'])).
% 11.38/11.63  thf('99', plain,
% 11.38/11.63      (((r2_hidden @ sk_A @ (sk_C_2 @ sk_A @ sk_C_6)))
% 11.38/11.63         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_6)) & 
% 11.38/11.63             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 11.38/11.63               (k1_wellord1 @ sk_C_6 @ sk_B_1))))),
% 11.38/11.63      inference('sup-', [status(thm)], ['56', '86'])).
% 11.38/11.63  thf('100', plain,
% 11.38/11.63      (![X0 : $i, X1 : $i]:
% 11.38/11.63         ((r1_tarski @ (sk_C_2 @ X1 @ X0) @ (k3_relat_1 @ X0))
% 11.38/11.63          | ~ (v1_relat_1 @ X0))),
% 11.38/11.63      inference('simplify', [status(thm)], ['94'])).
% 11.38/11.63  thf('101', plain,
% 11.38/11.63      (![X23 : $i, X24 : $i, X25 : $i]:
% 11.38/11.63         (~ (v2_wellord1 @ X23)
% 11.38/11.63          | ~ (r2_hidden @ X24 @ X25)
% 11.38/11.63          | (r2_hidden @ (k4_tarski @ (sk_C_3 @ X25 @ X23) @ X24) @ X23)
% 11.38/11.63          | ((X25) = (k1_xboole_0))
% 11.38/11.63          | ~ (r1_tarski @ X25 @ (k3_relat_1 @ X23))
% 11.38/11.63          | ~ (v1_relat_1 @ X23))),
% 11.38/11.63      inference('cnf', [status(esa)], [t10_wellord1])).
% 11.38/11.63  thf('102', plain,
% 11.38/11.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.38/11.63         (~ (v1_relat_1 @ X0)
% 11.38/11.63          | ~ (v1_relat_1 @ X0)
% 11.38/11.63          | ((sk_C_2 @ X1 @ X0) = (k1_xboole_0))
% 11.38/11.63          | (r2_hidden @ 
% 11.38/11.63             (k4_tarski @ (sk_C_3 @ (sk_C_2 @ X1 @ X0) @ X0) @ X2) @ X0)
% 11.38/11.63          | ~ (r2_hidden @ X2 @ (sk_C_2 @ X1 @ X0))
% 11.38/11.63          | ~ (v2_wellord1 @ X0))),
% 11.38/11.63      inference('sup-', [status(thm)], ['100', '101'])).
% 11.38/11.63  thf('103', plain,
% 11.38/11.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.38/11.63         (~ (v2_wellord1 @ X0)
% 11.38/11.63          | ~ (r2_hidden @ X2 @ (sk_C_2 @ X1 @ X0))
% 11.38/11.63          | (r2_hidden @ 
% 11.38/11.63             (k4_tarski @ (sk_C_3 @ (sk_C_2 @ X1 @ X0) @ X0) @ X2) @ X0)
% 11.38/11.63          | ((sk_C_2 @ X1 @ X0) = (k1_xboole_0))
% 11.38/11.63          | ~ (v1_relat_1 @ X0))),
% 11.38/11.63      inference('simplify', [status(thm)], ['102'])).
% 11.38/11.63  thf('104', plain,
% 11.38/11.63      (((~ (v1_relat_1 @ sk_C_6)
% 11.38/11.63         | ((sk_C_2 @ sk_A @ sk_C_6) = (k1_xboole_0))
% 11.38/11.63         | (r2_hidden @ 
% 11.38/11.63            (k4_tarski @ (sk_C_3 @ (sk_C_2 @ sk_A @ sk_C_6) @ sk_C_6) @ sk_A) @ 
% 11.38/11.63            sk_C_6)
% 11.38/11.63         | ~ (v2_wellord1 @ sk_C_6)))
% 11.38/11.63         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_6)) & 
% 11.38/11.63             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 11.38/11.63               (k1_wellord1 @ sk_C_6 @ sk_B_1))))),
% 11.38/11.63      inference('sup-', [status(thm)], ['99', '103'])).
% 11.38/11.63  thf('105', plain, ((v1_relat_1 @ sk_C_6)),
% 11.38/11.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.38/11.63  thf('106', plain, ((v2_wellord1 @ sk_C_6)),
% 11.38/11.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.38/11.63  thf('107', plain,
% 11.38/11.63      (((((sk_C_2 @ sk_A @ sk_C_6) = (k1_xboole_0))
% 11.38/11.63         | (r2_hidden @ 
% 11.38/11.63            (k4_tarski @ (sk_C_3 @ (sk_C_2 @ sk_A @ sk_C_6) @ sk_C_6) @ sk_A) @ 
% 11.38/11.63            sk_C_6)))
% 11.38/11.63         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_6)) & 
% 11.38/11.63             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 11.38/11.63               (k1_wellord1 @ sk_C_6 @ sk_B_1))))),
% 11.38/11.63      inference('demod', [status(thm)], ['104', '105', '106'])).
% 11.38/11.63  thf('108', plain,
% 11.38/11.63      (![X19 : $i, X21 : $i, X22 : $i]:
% 11.38/11.63         (~ (v1_relat_1 @ X19)
% 11.38/11.63          | ~ (r2_hidden @ (k4_tarski @ X22 @ X21) @ X19)
% 11.38/11.63          | ~ (r2_hidden @ X22 @ (sk_C_2 @ X21 @ X19)))),
% 11.38/11.63      inference('cnf', [status(esa)], [s1_xboole_0__e7_18__wellord1])).
% 11.38/11.63  thf('109', plain,
% 11.38/11.63      (((((sk_C_2 @ sk_A @ sk_C_6) = (k1_xboole_0))
% 11.38/11.63         | ~ (r2_hidden @ (sk_C_3 @ (sk_C_2 @ sk_A @ sk_C_6) @ sk_C_6) @ 
% 11.38/11.63              (sk_C_2 @ sk_A @ sk_C_6))
% 11.38/11.63         | ~ (v1_relat_1 @ sk_C_6)))
% 11.38/11.63         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_6)) & 
% 11.38/11.63             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 11.38/11.63               (k1_wellord1 @ sk_C_6 @ sk_B_1))))),
% 11.38/11.63      inference('sup-', [status(thm)], ['107', '108'])).
% 11.38/11.63  thf('110', plain, ((v1_relat_1 @ sk_C_6)),
% 11.38/11.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.38/11.63  thf('111', plain,
% 11.38/11.63      (((((sk_C_2 @ sk_A @ sk_C_6) = (k1_xboole_0))
% 11.38/11.63         | ~ (r2_hidden @ (sk_C_3 @ (sk_C_2 @ sk_A @ sk_C_6) @ sk_C_6) @ 
% 11.38/11.63              (sk_C_2 @ sk_A @ sk_C_6))))
% 11.38/11.63         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_6)) & 
% 11.38/11.63             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 11.38/11.63               (k1_wellord1 @ sk_C_6 @ sk_B_1))))),
% 11.38/11.63      inference('demod', [status(thm)], ['109', '110'])).
% 11.38/11.63  thf('112', plain,
% 11.38/11.63      (((~ (v1_relat_1 @ sk_C_6)
% 11.38/11.63         | ((sk_C_2 @ sk_A @ sk_C_6) = (k1_xboole_0))
% 11.38/11.63         | ~ (v2_wellord1 @ sk_C_6)
% 11.38/11.63         | ((sk_C_2 @ sk_A @ sk_C_6) = (k1_xboole_0))))
% 11.38/11.63         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_6)) & 
% 11.38/11.63             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 11.38/11.63               (k1_wellord1 @ sk_C_6 @ sk_B_1))))),
% 11.38/11.63      inference('sup-', [status(thm)], ['98', '111'])).
% 11.38/11.63  thf('113', plain, ((v1_relat_1 @ sk_C_6)),
% 11.38/11.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.38/11.63  thf('114', plain, ((v2_wellord1 @ sk_C_6)),
% 11.38/11.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.38/11.63  thf('115', plain,
% 11.38/11.63      (((((sk_C_2 @ sk_A @ sk_C_6) = (k1_xboole_0))
% 11.38/11.63         | ((sk_C_2 @ sk_A @ sk_C_6) = (k1_xboole_0))))
% 11.38/11.63         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_6)) & 
% 11.38/11.64             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 11.38/11.64               (k1_wellord1 @ sk_C_6 @ sk_B_1))))),
% 11.38/11.64      inference('demod', [status(thm)], ['112', '113', '114'])).
% 11.38/11.64  thf('116', plain,
% 11.38/11.64      ((((sk_C_2 @ sk_A @ sk_C_6) = (k1_xboole_0)))
% 11.38/11.64         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_6)) & 
% 11.38/11.64             ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 11.38/11.64               (k1_wellord1 @ sk_C_6 @ sk_B_1))))),
% 11.38/11.64      inference('simplify', [status(thm)], ['115'])).
% 11.38/11.64  thf('117', plain, ((v1_relat_1 @ sk_C_6)),
% 11.38/11.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.38/11.64  thf('118', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 11.38/11.64      inference('simplify', [status(thm)], ['48'])).
% 11.38/11.64  thf('119', plain,
% 11.38/11.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.38/11.64         ((r2_hidden @ X1 @ (k3_relat_1 @ X0))
% 11.38/11.64          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 11.38/11.64          | ~ (v1_relat_1 @ X0))),
% 11.38/11.64      inference('simplify', [status(thm)], ['14'])).
% 11.38/11.64  thf('120', plain,
% 11.38/11.64      (![X7 : $i, X8 : $i]: (~ (r2_hidden @ X7 @ X8) | ~ (r1_tarski @ X8 @ X7))),
% 11.38/11.64      inference('cnf', [status(esa)], [t7_ordinal1])).
% 11.38/11.64  thf('121', plain,
% 11.38/11.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.38/11.64         (~ (v1_relat_1 @ X0)
% 11.38/11.64          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 11.38/11.64          | ~ (r1_tarski @ (k3_relat_1 @ X0) @ X1))),
% 11.38/11.64      inference('sup-', [status(thm)], ['119', '120'])).
% 11.38/11.64  thf('122', plain,
% 11.38/11.64      (![X0 : $i, X1 : $i]:
% 11.38/11.64         ((r1_tarski @ (k1_wellord1 @ X0 @ (k3_relat_1 @ X0)) @ X1)
% 11.38/11.64          | ~ (v1_relat_1 @ X0))),
% 11.38/11.64      inference('sup-', [status(thm)], ['118', '121'])).
% 11.38/11.64  thf('123', plain,
% 11.38/11.64      (![X26 : $i, X27 : $i]:
% 11.38/11.64         ((r1_tarski @ (k1_wellord1 @ X26 @ X27) @ (k3_relat_1 @ X26))
% 11.38/11.64          | ~ (v1_relat_1 @ X26))),
% 11.38/11.64      inference('cnf', [status(esa)], [t13_wellord1])).
% 11.38/11.64  thf('124', plain,
% 11.38/11.64      (![X23 : $i, X25 : $i]:
% 11.38/11.64         (~ (v2_wellord1 @ X23)
% 11.38/11.64          | (r2_hidden @ (sk_C_3 @ X25 @ X23) @ X25)
% 11.38/11.64          | ((X25) = (k1_xboole_0))
% 11.38/11.64          | ~ (r1_tarski @ X25 @ (k3_relat_1 @ X23))
% 11.38/11.64          | ~ (v1_relat_1 @ X23))),
% 11.38/11.64      inference('cnf', [status(esa)], [t10_wellord1])).
% 11.38/11.64  thf('125', plain,
% 11.38/11.64      (![X0 : $i, X1 : $i]:
% 11.38/11.64         (~ (v1_relat_1 @ X0)
% 11.38/11.64          | ~ (v1_relat_1 @ X0)
% 11.38/11.64          | ((k1_wellord1 @ X0 @ X1) = (k1_xboole_0))
% 11.38/11.64          | (r2_hidden @ (sk_C_3 @ (k1_wellord1 @ X0 @ X1) @ X0) @ 
% 11.38/11.64             (k1_wellord1 @ X0 @ X1))
% 11.38/11.64          | ~ (v2_wellord1 @ X0))),
% 11.38/11.64      inference('sup-', [status(thm)], ['123', '124'])).
% 11.38/11.64  thf('126', plain,
% 11.38/11.64      (![X0 : $i, X1 : $i]:
% 11.38/11.64         (~ (v2_wellord1 @ X0)
% 11.38/11.64          | (r2_hidden @ (sk_C_3 @ (k1_wellord1 @ X0 @ X1) @ X0) @ 
% 11.38/11.64             (k1_wellord1 @ X0 @ X1))
% 11.38/11.64          | ((k1_wellord1 @ X0 @ X1) = (k1_xboole_0))
% 11.38/11.64          | ~ (v1_relat_1 @ X0))),
% 11.38/11.64      inference('simplify', [status(thm)], ['125'])).
% 11.38/11.64  thf('127', plain,
% 11.38/11.64      (![X7 : $i, X8 : $i]: (~ (r2_hidden @ X7 @ X8) | ~ (r1_tarski @ X8 @ X7))),
% 11.38/11.64      inference('cnf', [status(esa)], [t7_ordinal1])).
% 11.38/11.64  thf('128', plain,
% 11.38/11.64      (![X0 : $i, X1 : $i]:
% 11.38/11.64         (~ (v1_relat_1 @ X1)
% 11.38/11.64          | ((k1_wellord1 @ X1 @ X0) = (k1_xboole_0))
% 11.38/11.64          | ~ (v2_wellord1 @ X1)
% 11.38/11.64          | ~ (r1_tarski @ (k1_wellord1 @ X1 @ X0) @ 
% 11.38/11.64               (sk_C_3 @ (k1_wellord1 @ X1 @ X0) @ X1)))),
% 11.38/11.64      inference('sup-', [status(thm)], ['126', '127'])).
% 11.38/11.64  thf('129', plain,
% 11.38/11.64      (![X0 : $i]:
% 11.38/11.64         (~ (v1_relat_1 @ X0)
% 11.38/11.64          | ~ (v2_wellord1 @ X0)
% 11.38/11.64          | ((k1_wellord1 @ X0 @ (k3_relat_1 @ X0)) = (k1_xboole_0))
% 11.38/11.64          | ~ (v1_relat_1 @ X0))),
% 11.38/11.64      inference('sup-', [status(thm)], ['122', '128'])).
% 11.38/11.64  thf('130', plain,
% 11.38/11.64      (![X0 : $i]:
% 11.38/11.64         (((k1_wellord1 @ X0 @ (k3_relat_1 @ X0)) = (k1_xboole_0))
% 11.38/11.64          | ~ (v2_wellord1 @ X0)
% 11.38/11.64          | ~ (v1_relat_1 @ X0))),
% 11.38/11.64      inference('simplify', [status(thm)], ['129'])).
% 11.38/11.64  thf('131', plain,
% 11.38/11.64      (![X0 : $i, X1 : $i]:
% 11.38/11.64         ((r1_tarski @ (k1_wellord1 @ X0 @ (k3_relat_1 @ X0)) @ X1)
% 11.38/11.64          | ~ (v1_relat_1 @ X0))),
% 11.38/11.64      inference('sup-', [status(thm)], ['118', '121'])).
% 11.38/11.64  thf('132', plain,
% 11.38/11.64      (![X0 : $i, X1 : $i]:
% 11.38/11.64         ((r1_tarski @ k1_xboole_0 @ X0)
% 11.38/11.64          | ~ (v1_relat_1 @ X1)
% 11.38/11.64          | ~ (v2_wellord1 @ X1)
% 11.38/11.64          | ~ (v1_relat_1 @ X1))),
% 11.38/11.64      inference('sup+', [status(thm)], ['130', '131'])).
% 11.38/11.64  thf('133', plain,
% 11.38/11.64      (![X0 : $i, X1 : $i]:
% 11.38/11.64         (~ (v2_wellord1 @ X1)
% 11.38/11.64          | ~ (v1_relat_1 @ X1)
% 11.38/11.64          | (r1_tarski @ k1_xboole_0 @ X0))),
% 11.38/11.64      inference('simplify', [status(thm)], ['132'])).
% 11.38/11.64  thf('134', plain,
% 11.38/11.64      (![X0 : $i]: ((r1_tarski @ k1_xboole_0 @ X0) | ~ (v2_wellord1 @ sk_C_6))),
% 11.38/11.64      inference('sup-', [status(thm)], ['117', '133'])).
% 11.38/11.64  thf('135', plain, ((v2_wellord1 @ sk_C_6)),
% 11.38/11.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.38/11.64  thf('136', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 11.38/11.64      inference('demod', [status(thm)], ['134', '135'])).
% 11.38/11.64  thf('137', plain,
% 11.38/11.64      (~
% 11.38/11.64       ((r1_tarski @ (k1_wellord1 @ sk_C_6 @ sk_A) @ 
% 11.38/11.64         (k1_wellord1 @ sk_C_6 @ sk_B_1))) | 
% 11.38/11.64       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_6))),
% 11.38/11.64      inference('demod', [status(thm)], ['89', '116', '136'])).
% 11.38/11.64  thf('138', plain, ($false),
% 11.38/11.64      inference('sat_resolution*', [status(thm)], ['1', '50', '51', '137'])).
% 11.38/11.64  
% 11.38/11.64  % SZS output end Refutation
% 11.38/11.64  
% 11.38/11.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
