%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.c1YCiORKrR

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:12 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 928 expanded)
%              Number of leaves         :   29 ( 263 expanded)
%              Depth                    :   30
%              Number of atoms          : 1569 (12158 expanded)
%              Number of equality atoms :   67 ( 532 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t48_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) ) )
           => ( ( v2_funct_1 @ B )
              & ( v2_funct_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
                & ( ( k2_relat_1 @ B )
                  = ( k1_relat_1 @ A ) ) )
             => ( ( v2_funct_1 @ B )
                & ( v2_funct_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_funct_1])).

thf('0',plain,
    ( ~ ( v2_funct_1 @ sk_B_1 )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v2_funct_1 @ sk_A )
   <= ~ ( v2_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) )
           => ( v2_funct_1 @ B ) ) ) ) )).

thf('5',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v1_relat_1 @ X30 )
      | ~ ( v1_funct_1 @ X30 )
      | ( v2_funct_1 @ X30 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X30 ) @ ( k1_relat_1 @ X31 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X30 @ X31 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t47_funct_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ sk_A ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ sk_B_1 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ sk_A ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_funct_1 @ sk_B_1 )
    | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v2_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('15',plain,
    ( ~ ( v2_funct_1 @ sk_B_1 )
   <= ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v2_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','18'])).

thf('20',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
      <=> ! [B: $i,C: $i] :
            ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
              & ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
              & ( ( k1_funct_1 @ A @ B )
                = ( k1_funct_1 @ A @ C ) ) )
           => ( B = C ) ) ) ) )).

thf('21',plain,(
    ! [X22: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X22 ) @ ( k1_relat_1 @ X22 ) )
      | ( v2_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('22',plain,
    ( ( r2_hidden @ ( sk_C_2 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r2_hidden @ ( sk_C_2 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','18'])).

thf('27',plain,(
    r2_hidden @ ( sk_C_2 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['25','26'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('28',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X14 @ X12 ) @ X14 ) @ X12 )
      | ( X13
       != ( k2_relat_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('29',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X14 @ X12 ) @ X14 ) @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k2_relat_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_3 @ ( sk_C_2 @ sk_A ) @ sk_B_1 ) @ ( sk_C_2 @ sk_A ) ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['27','29'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('31',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X32 @ X34 ) @ X33 )
      | ( X34
        = ( k1_funct_1 @ X33 @ X32 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( ( sk_C_2 @ sk_A )
      = ( k1_funct_1 @ sk_B_1 @ ( sk_D_3 @ ( sk_C_2 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( sk_C_2 @ sk_A )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_3 @ ( sk_C_2 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_3 @ ( sk_C_2 @ sk_A ) @ sk_B_1 ) @ ( sk_C_2 @ sk_A ) ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['27','29'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('37',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X5 )
      | ( r2_hidden @ X3 @ X6 )
      | ( X6
       != ( k1_relat_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('38',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X3 @ ( k1_relat_1 @ X5 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X5 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    r2_hidden @ ( sk_D_3 @ ( sk_C_2 @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('40',plain,(
    ! [X19: $i] :
      ( ( ( k10_relat_1 @ X19 @ ( k2_relat_1 @ X19 ) )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('41',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('42',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X21 @ X20 ) )
        = ( k10_relat_1 @ X21 @ ( k1_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('43',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r2_hidden @ ( k4_tarski @ X7 @ ( sk_D_1 @ X7 @ X5 ) ) @ X5 )
      | ( X6
       != ( k1_relat_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('44',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X7 @ ( sk_D_1 @ X7 @ X5 ) ) @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k1_relat_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_D_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ sk_B_1 ) ) )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_D_1 @ X1 @ ( k5_relat_1 @ X0 @ sk_A ) ) ) @ ( k5_relat_1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ sk_B_1 ) ) )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_D_1 @ X1 @ ( k5_relat_1 @ X0 @ sk_A ) ) ) @ ( k5_relat_1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D_1 @ X0 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D_1 @ X0 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_3 @ ( sk_C_2 @ sk_A ) @ sk_B_1 ) @ ( sk_D_1 @ ( sk_D_3 @ ( sk_C_2 @ sk_A ) @ sk_B_1 ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','52'])).

thf('54',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X3 @ ( k1_relat_1 @ X5 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X5 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('55',plain,(
    r2_hidden @ ( sk_D_3 @ ( sk_C_2 @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(fc2_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) )).

thf('56',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_relat_1 @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('57',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('58',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X22: $i] :
      ( ( r2_hidden @ ( sk_B @ X22 ) @ ( k1_relat_1 @ X22 ) )
      | ( v2_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('60',plain,
    ( ( r2_hidden @ ( sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( r2_hidden @ ( sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','18'])).

thf('65',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X14 @ X12 ) @ X14 ) @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k2_relat_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('67',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_3 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( sk_B @ sk_A ) ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X3 @ ( k1_relat_1 @ X5 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X5 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('69',plain,(
    r2_hidden @ ( sk_D_3 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D_1 @ X0 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('71',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_3 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( sk_D_1 @ ( sk_D_3 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X3 @ ( k1_relat_1 @ X5 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X5 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('73',plain,(
    r2_hidden @ ( sk_D_3 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ~ ( r2_hidden @ X23 @ ( k1_relat_1 @ X22 ) )
      | ~ ( r2_hidden @ X24 @ ( k1_relat_1 @ X22 ) )
      | ( ( k1_funct_1 @ X22 @ X23 )
       != ( k1_funct_1 @ X22 @ X24 ) )
      | ( X23 = X24 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ( ( sk_D_3 @ ( sk_B @ sk_A ) @ sk_B_1 )
        = X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_D_3 @ ( sk_B @ sk_A ) @ sk_B_1 ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v2_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ( ( sk_D_3 @ ( sk_B @ sk_A ) @ sk_B_1 )
        = X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_D_3 @ ( sk_B @ sk_A ) @ sk_B_1 ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    r2_hidden @ ( sk_D_3 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf(t22_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A )
              = ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) )).

thf('79',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ~ ( v1_funct_1 @ X27 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X27 @ X28 ) @ X29 )
        = ( k1_funct_1 @ X28 @ ( k1_funct_1 @ X27 @ X29 ) ) )
      | ~ ( r2_hidden @ X29 @ ( k1_relat_1 @ ( k5_relat_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_1])).

thf('80',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_D_3 @ ( sk_B @ sk_A ) @ sk_B_1 ) )
      = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_D_3 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_3 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( sk_B @ sk_A ) ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['65','66'])).

thf('84',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X32 @ X34 ) @ X33 )
      | ( X34
        = ( k1_funct_1 @ X33 @ X32 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('85',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( ( sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B_1 @ ( sk_D_3 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( sk_B @ sk_A )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_3 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_D_3 @ ( sk_B @ sk_A ) @ sk_B_1 ) )
    = ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81','82','88','89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ( ( sk_D_3 @ ( sk_B @ sk_A ) @ sk_B_1 )
        = X0 )
      | ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['77','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ( ( sk_D_3 @ ( sk_B @ sk_A ) @ sk_B_1 )
        = X0 )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['57','92'])).

thf('94',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ( ( sk_D_3 @ ( sk_B @ sk_A ) @ sk_B_1 )
        = X0 )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( ( sk_D_3 @ ( sk_B @ sk_A ) @ sk_B_1 )
        = X0 )
      | ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['56','96'])).

thf('98',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( ( sk_D_3 @ ( sk_B @ sk_A ) @ sk_B_1 )
        = X0 )
      | ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['97','98','99','100','101'])).

thf('103',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_D_3 @ ( sk_C_2 @ sk_A ) @ sk_B_1 ) ) )
    | ( ( sk_D_3 @ ( sk_B @ sk_A ) @ sk_B_1 )
      = ( sk_D_3 @ ( sk_C_2 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['55','102'])).

thf('104',plain,(
    r2_hidden @ ( sk_D_3 @ ( sk_C_2 @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('105',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ~ ( v1_funct_1 @ X27 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X27 @ X28 ) @ X29 )
        = ( k1_funct_1 @ X28 @ ( k1_funct_1 @ X27 @ X29 ) ) )
      | ~ ( r2_hidden @ X29 @ ( k1_relat_1 @ ( k5_relat_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_1])).

thf('106',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_D_3 @ ( sk_C_2 @ sk_A ) @ sk_B_1 ) )
      = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_D_3 @ ( sk_C_2 @ sk_A ) @ sk_B_1 ) ) ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( sk_C_2 @ sk_A )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_3 @ ( sk_C_2 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('110',plain,(
    ! [X22: $i] :
      ( ( ( k1_funct_1 @ X22 @ ( sk_B @ X22 ) )
        = ( k1_funct_1 @ X22 @ ( sk_C_2 @ X22 ) ) )
      | ( v2_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('111',plain,(
    r2_hidden @ ( sk_C_2 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('112',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X32 @ ( k1_relat_1 @ X33 ) )
      | ( X34
       != ( k1_funct_1 @ X33 @ X32 ) )
      | ( r2_hidden @ ( k4_tarski @ X32 @ X34 ) @ X33 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('114',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ~ ( v1_funct_1 @ X33 )
      | ( r2_hidden @ ( k4_tarski @ X32 @ ( k1_funct_1 @ X33 @ X32 ) ) @ X33 )
      | ~ ( r2_hidden @ X32 @ ( k1_relat_1 @ X33 ) ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_A @ X0 ) ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['112','114'])).

thf('116',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_A @ X0 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('119',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C_2 @ sk_A ) @ ( k1_funct_1 @ sk_A @ ( sk_C_2 @ sk_A ) ) ) @ sk_A ),
    inference('sup-',[status(thm)],['111','118'])).

thf('120',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ sk_A ) @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['110','119'])).

thf('121',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ sk_A ) @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) ) @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('124',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','18'])).

thf('125',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C_2 @ sk_A ) @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) ) @ sk_A ),
    inference(clc,[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X32 @ X34 ) @ X33 )
      | ( X34
        = ( k1_funct_1 @ X33 @ X32 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('127',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
      = ( k1_funct_1 @ sk_A @ ( sk_C_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
    = ( k1_funct_1 @ sk_A @ ( sk_C_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('131',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_D_3 @ ( sk_C_2 @ sk_A ) @ sk_B_1 ) )
    = ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['106','107','108','109','130','131','132'])).

thf('134',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
     != ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( ( sk_D_3 @ ( sk_B @ sk_A ) @ sk_B_1 )
      = ( sk_D_3 @ ( sk_C_2 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['103','133'])).

thf('135',plain,
    ( ( sk_D_3 @ ( sk_B @ sk_A ) @ sk_B_1 )
    = ( sk_D_3 @ ( sk_C_2 @ sk_A ) @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,
    ( ( sk_C_2 @ sk_A )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_3 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['35','135'])).

thf('137',plain,
    ( ( sk_B @ sk_A )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_3 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('138',plain,
    ( ( sk_B @ sk_A )
    = ( sk_C_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X22: $i] :
      ( ( ( sk_B @ X22 )
       != ( sk_C_2 @ X22 ) )
      | ( v2_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('140',plain,
    ( ( ( sk_B @ sk_A )
     != ( sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( ( sk_B @ sk_A )
     != ( sk_B @ sk_A ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['140','141','142'])).

thf('144',plain,(
    v2_funct_1 @ sk_A ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,(
    $false ),
    inference(demod,[status(thm)],['19','144'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.c1YCiORKrR
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:17:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.60/0.79  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.60/0.79  % Solved by: fo/fo7.sh
% 0.60/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.79  % done 332 iterations in 0.330s
% 0.60/0.79  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.60/0.79  % SZS output start Refutation
% 0.60/0.79  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.60/0.79  thf(sk_B_type, type, sk_B: $i > $i).
% 0.60/0.79  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.60/0.79  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.60/0.79  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.60/0.79  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.60/0.79  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.60/0.79  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.60/0.79  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.60/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.79  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i).
% 0.60/0.79  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.60/0.79  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.60/0.79  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.60/0.79  thf(sk_C_2_type, type, sk_C_2: $i > $i).
% 0.60/0.79  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.60/0.79  thf(t48_funct_1, conjecture,
% 0.60/0.79    (![A:$i]:
% 0.60/0.79     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.60/0.79       ( ![B:$i]:
% 0.60/0.79         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.60/0.79           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.60/0.79               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.60/0.79             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.60/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.79    (~( ![A:$i]:
% 0.60/0.79        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.60/0.79          ( ![B:$i]:
% 0.60/0.79            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.60/0.79              ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.60/0.79                  ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.60/0.79                ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ) )),
% 0.60/0.79    inference('cnf.neg', [status(esa)], [t48_funct_1])).
% 0.60/0.79  thf('0', plain, ((~ (v2_funct_1 @ sk_B_1) | ~ (v2_funct_1 @ sk_A))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('1', plain, ((~ (v2_funct_1 @ sk_A)) <= (~ ((v2_funct_1 @ sk_A)))),
% 0.60/0.79      inference('split', [status(esa)], ['0'])).
% 0.60/0.79  thf(d10_xboole_0, axiom,
% 0.60/0.79    (![A:$i,B:$i]:
% 0.60/0.79     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.60/0.79  thf('2', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.60/0.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.60/0.79  thf('3', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.60/0.79      inference('simplify', [status(thm)], ['2'])).
% 0.60/0.79  thf('4', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf(t47_funct_1, axiom,
% 0.60/0.79    (![A:$i]:
% 0.60/0.79     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.60/0.79       ( ![B:$i]:
% 0.60/0.79         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.60/0.79           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.60/0.79               ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) =>
% 0.60/0.79             ( v2_funct_1 @ B ) ) ) ) ))).
% 0.60/0.79  thf('5', plain,
% 0.60/0.79      (![X30 : $i, X31 : $i]:
% 0.60/0.79         (~ (v1_relat_1 @ X30)
% 0.60/0.79          | ~ (v1_funct_1 @ X30)
% 0.60/0.79          | (v2_funct_1 @ X30)
% 0.60/0.79          | ~ (r1_tarski @ (k2_relat_1 @ X30) @ (k1_relat_1 @ X31))
% 0.60/0.79          | ~ (v2_funct_1 @ (k5_relat_1 @ X30 @ X31))
% 0.60/0.79          | ~ (v1_funct_1 @ X31)
% 0.60/0.79          | ~ (v1_relat_1 @ X31))),
% 0.60/0.79      inference('cnf', [status(esa)], [t47_funct_1])).
% 0.60/0.79  thf('6', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (~ (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ sk_B_1))
% 0.60/0.79          | ~ (v1_relat_1 @ sk_A)
% 0.60/0.79          | ~ (v1_funct_1 @ sk_A)
% 0.60/0.79          | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_A))
% 0.60/0.79          | (v2_funct_1 @ X0)
% 0.60/0.79          | ~ (v1_funct_1 @ X0)
% 0.60/0.79          | ~ (v1_relat_1 @ X0))),
% 0.60/0.79      inference('sup-', [status(thm)], ['4', '5'])).
% 0.60/0.79  thf('7', plain, ((v1_relat_1 @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('8', plain, ((v1_funct_1 @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('9', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (~ (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ sk_B_1))
% 0.60/0.79          | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_A))
% 0.60/0.79          | (v2_funct_1 @ X0)
% 0.60/0.79          | ~ (v1_funct_1 @ X0)
% 0.60/0.79          | ~ (v1_relat_1 @ X0))),
% 0.60/0.79      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.60/0.79  thf('10', plain,
% 0.60/0.79      ((~ (v1_relat_1 @ sk_B_1)
% 0.60/0.79        | ~ (v1_funct_1 @ sk_B_1)
% 0.60/0.79        | (v2_funct_1 @ sk_B_1)
% 0.60/0.79        | ~ (v2_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['3', '9'])).
% 0.60/0.79  thf('11', plain, ((v1_relat_1 @ sk_B_1)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('12', plain, ((v1_funct_1 @ sk_B_1)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('13', plain, ((v2_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('14', plain, ((v2_funct_1 @ sk_B_1)),
% 0.60/0.79      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.60/0.79  thf('15', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.60/0.79      inference('split', [status(esa)], ['0'])).
% 0.60/0.79  thf('16', plain, (((v2_funct_1 @ sk_B_1))),
% 0.60/0.79      inference('sup-', [status(thm)], ['14', '15'])).
% 0.60/0.79  thf('17', plain, (~ ((v2_funct_1 @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.60/0.79      inference('split', [status(esa)], ['0'])).
% 0.60/0.79  thf('18', plain, (~ ((v2_funct_1 @ sk_A))),
% 0.60/0.79      inference('sat_resolution*', [status(thm)], ['16', '17'])).
% 0.60/0.79  thf('19', plain, (~ (v2_funct_1 @ sk_A)),
% 0.60/0.79      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.60/0.79  thf('20', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf(d8_funct_1, axiom,
% 0.60/0.79    (![A:$i]:
% 0.60/0.79     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.60/0.79       ( ( v2_funct_1 @ A ) <=>
% 0.60/0.79         ( ![B:$i,C:$i]:
% 0.60/0.79           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.60/0.79               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.60/0.79               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.60/0.79             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.60/0.79  thf('21', plain,
% 0.60/0.79      (![X22 : $i]:
% 0.60/0.79         ((r2_hidden @ (sk_C_2 @ X22) @ (k1_relat_1 @ X22))
% 0.60/0.79          | (v2_funct_1 @ X22)
% 0.60/0.79          | ~ (v1_funct_1 @ X22)
% 0.60/0.79          | ~ (v1_relat_1 @ X22))),
% 0.60/0.79      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.60/0.79  thf('22', plain,
% 0.60/0.79      (((r2_hidden @ (sk_C_2 @ sk_A) @ (k2_relat_1 @ sk_B_1))
% 0.60/0.79        | ~ (v1_relat_1 @ sk_A)
% 0.60/0.79        | ~ (v1_funct_1 @ sk_A)
% 0.60/0.79        | (v2_funct_1 @ sk_A))),
% 0.60/0.79      inference('sup+', [status(thm)], ['20', '21'])).
% 0.60/0.79  thf('23', plain, ((v1_relat_1 @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('24', plain, ((v1_funct_1 @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('25', plain,
% 0.60/0.79      (((r2_hidden @ (sk_C_2 @ sk_A) @ (k2_relat_1 @ sk_B_1))
% 0.60/0.79        | (v2_funct_1 @ sk_A))),
% 0.60/0.79      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.60/0.79  thf('26', plain, (~ (v2_funct_1 @ sk_A)),
% 0.60/0.79      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.60/0.79  thf('27', plain, ((r2_hidden @ (sk_C_2 @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 0.60/0.79      inference('clc', [status(thm)], ['25', '26'])).
% 0.60/0.79  thf(d5_relat_1, axiom,
% 0.60/0.79    (![A:$i,B:$i]:
% 0.60/0.79     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.60/0.79       ( ![C:$i]:
% 0.60/0.79         ( ( r2_hidden @ C @ B ) <=>
% 0.60/0.79           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.60/0.79  thf('28', plain,
% 0.60/0.79      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.60/0.79         (~ (r2_hidden @ X14 @ X13)
% 0.60/0.79          | (r2_hidden @ (k4_tarski @ (sk_D_3 @ X14 @ X12) @ X14) @ X12)
% 0.60/0.79          | ((X13) != (k2_relat_1 @ X12)))),
% 0.60/0.79      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.60/0.79  thf('29', plain,
% 0.60/0.79      (![X12 : $i, X14 : $i]:
% 0.60/0.79         ((r2_hidden @ (k4_tarski @ (sk_D_3 @ X14 @ X12) @ X14) @ X12)
% 0.60/0.79          | ~ (r2_hidden @ X14 @ (k2_relat_1 @ X12)))),
% 0.60/0.79      inference('simplify', [status(thm)], ['28'])).
% 0.60/0.79  thf('30', plain,
% 0.60/0.79      ((r2_hidden @ 
% 0.60/0.79        (k4_tarski @ (sk_D_3 @ (sk_C_2 @ sk_A) @ sk_B_1) @ (sk_C_2 @ sk_A)) @ 
% 0.60/0.79        sk_B_1)),
% 0.60/0.79      inference('sup-', [status(thm)], ['27', '29'])).
% 0.60/0.79  thf(t8_funct_1, axiom,
% 0.60/0.79    (![A:$i,B:$i,C:$i]:
% 0.60/0.79     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.60/0.79       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.60/0.79         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.60/0.79           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.60/0.79  thf('31', plain,
% 0.60/0.79      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.60/0.79         (~ (r2_hidden @ (k4_tarski @ X32 @ X34) @ X33)
% 0.60/0.79          | ((X34) = (k1_funct_1 @ X33 @ X32))
% 0.60/0.79          | ~ (v1_funct_1 @ X33)
% 0.60/0.79          | ~ (v1_relat_1 @ X33))),
% 0.60/0.79      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.60/0.79  thf('32', plain,
% 0.60/0.79      ((~ (v1_relat_1 @ sk_B_1)
% 0.60/0.79        | ~ (v1_funct_1 @ sk_B_1)
% 0.60/0.79        | ((sk_C_2 @ sk_A)
% 0.60/0.79            = (k1_funct_1 @ sk_B_1 @ (sk_D_3 @ (sk_C_2 @ sk_A) @ sk_B_1))))),
% 0.60/0.79      inference('sup-', [status(thm)], ['30', '31'])).
% 0.60/0.79  thf('33', plain, ((v1_relat_1 @ sk_B_1)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('34', plain, ((v1_funct_1 @ sk_B_1)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('35', plain,
% 0.60/0.79      (((sk_C_2 @ sk_A)
% 0.60/0.79         = (k1_funct_1 @ sk_B_1 @ (sk_D_3 @ (sk_C_2 @ sk_A) @ sk_B_1)))),
% 0.60/0.79      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.60/0.79  thf('36', plain,
% 0.60/0.79      ((r2_hidden @ 
% 0.60/0.79        (k4_tarski @ (sk_D_3 @ (sk_C_2 @ sk_A) @ sk_B_1) @ (sk_C_2 @ sk_A)) @ 
% 0.60/0.79        sk_B_1)),
% 0.60/0.79      inference('sup-', [status(thm)], ['27', '29'])).
% 0.60/0.79  thf(d4_relat_1, axiom,
% 0.60/0.79    (![A:$i,B:$i]:
% 0.60/0.79     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.60/0.79       ( ![C:$i]:
% 0.60/0.79         ( ( r2_hidden @ C @ B ) <=>
% 0.60/0.79           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.60/0.79  thf('37', plain,
% 0.60/0.79      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.60/0.79         (~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X5)
% 0.60/0.79          | (r2_hidden @ X3 @ X6)
% 0.60/0.79          | ((X6) != (k1_relat_1 @ X5)))),
% 0.60/0.79      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.60/0.79  thf('38', plain,
% 0.60/0.79      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.60/0.79         ((r2_hidden @ X3 @ (k1_relat_1 @ X5))
% 0.60/0.79          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X5))),
% 0.60/0.79      inference('simplify', [status(thm)], ['37'])).
% 0.60/0.79  thf('39', plain,
% 0.60/0.79      ((r2_hidden @ (sk_D_3 @ (sk_C_2 @ sk_A) @ sk_B_1) @ (k1_relat_1 @ sk_B_1))),
% 0.60/0.79      inference('sup-', [status(thm)], ['36', '38'])).
% 0.60/0.79  thf(t169_relat_1, axiom,
% 0.60/0.79    (![A:$i]:
% 0.60/0.79     ( ( v1_relat_1 @ A ) =>
% 0.60/0.79       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.60/0.79  thf('40', plain,
% 0.60/0.79      (![X19 : $i]:
% 0.60/0.79         (((k10_relat_1 @ X19 @ (k2_relat_1 @ X19)) = (k1_relat_1 @ X19))
% 0.60/0.79          | ~ (v1_relat_1 @ X19))),
% 0.60/0.79      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.60/0.79  thf('41', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf(t182_relat_1, axiom,
% 0.60/0.79    (![A:$i]:
% 0.60/0.79     ( ( v1_relat_1 @ A ) =>
% 0.60/0.79       ( ![B:$i]:
% 0.60/0.79         ( ( v1_relat_1 @ B ) =>
% 0.60/0.79           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.60/0.79             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.60/0.79  thf('42', plain,
% 0.60/0.79      (![X20 : $i, X21 : $i]:
% 0.60/0.79         (~ (v1_relat_1 @ X20)
% 0.60/0.79          | ((k1_relat_1 @ (k5_relat_1 @ X21 @ X20))
% 0.60/0.79              = (k10_relat_1 @ X21 @ (k1_relat_1 @ X20)))
% 0.60/0.79          | ~ (v1_relat_1 @ X21))),
% 0.60/0.79      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.60/0.79  thf('43', plain,
% 0.60/0.79      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.60/0.79         (~ (r2_hidden @ X7 @ X6)
% 0.60/0.79          | (r2_hidden @ (k4_tarski @ X7 @ (sk_D_1 @ X7 @ X5)) @ X5)
% 0.60/0.79          | ((X6) != (k1_relat_1 @ X5)))),
% 0.60/0.79      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.60/0.79  thf('44', plain,
% 0.60/0.79      (![X5 : $i, X7 : $i]:
% 0.60/0.79         ((r2_hidden @ (k4_tarski @ X7 @ (sk_D_1 @ X7 @ X5)) @ X5)
% 0.60/0.79          | ~ (r2_hidden @ X7 @ (k1_relat_1 @ X5)))),
% 0.60/0.79      inference('simplify', [status(thm)], ['43'])).
% 0.60/0.79  thf('45', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.79         (~ (r2_hidden @ X2 @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.60/0.79          | ~ (v1_relat_1 @ X1)
% 0.60/0.79          | ~ (v1_relat_1 @ X0)
% 0.60/0.79          | (r2_hidden @ 
% 0.60/0.79             (k4_tarski @ X2 @ (sk_D_1 @ X2 @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.60/0.79             (k5_relat_1 @ X1 @ X0)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['42', '44'])).
% 0.60/0.79  thf('46', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i]:
% 0.60/0.79         (~ (r2_hidden @ X1 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ sk_B_1)))
% 0.60/0.79          | (r2_hidden @ 
% 0.60/0.79             (k4_tarski @ X1 @ (sk_D_1 @ X1 @ (k5_relat_1 @ X0 @ sk_A))) @ 
% 0.60/0.79             (k5_relat_1 @ X0 @ sk_A))
% 0.60/0.79          | ~ (v1_relat_1 @ sk_A)
% 0.60/0.79          | ~ (v1_relat_1 @ X0))),
% 0.60/0.79      inference('sup-', [status(thm)], ['41', '45'])).
% 0.60/0.79  thf('47', plain, ((v1_relat_1 @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('48', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i]:
% 0.60/0.79         (~ (r2_hidden @ X1 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ sk_B_1)))
% 0.60/0.79          | (r2_hidden @ 
% 0.60/0.79             (k4_tarski @ X1 @ (sk_D_1 @ X1 @ (k5_relat_1 @ X0 @ sk_A))) @ 
% 0.60/0.79             (k5_relat_1 @ X0 @ sk_A))
% 0.60/0.79          | ~ (v1_relat_1 @ X0))),
% 0.60/0.79      inference('demod', [status(thm)], ['46', '47'])).
% 0.60/0.79  thf('49', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.60/0.79          | ~ (v1_relat_1 @ sk_B_1)
% 0.60/0.79          | ~ (v1_relat_1 @ sk_B_1)
% 0.60/0.79          | (r2_hidden @ 
% 0.60/0.79             (k4_tarski @ X0 @ (sk_D_1 @ X0 @ (k5_relat_1 @ sk_B_1 @ sk_A))) @ 
% 0.60/0.79             (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['40', '48'])).
% 0.60/0.79  thf('50', plain, ((v1_relat_1 @ sk_B_1)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('51', plain, ((v1_relat_1 @ sk_B_1)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('52', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.60/0.79          | (r2_hidden @ 
% 0.60/0.79             (k4_tarski @ X0 @ (sk_D_1 @ X0 @ (k5_relat_1 @ sk_B_1 @ sk_A))) @ 
% 0.60/0.79             (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.60/0.79      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.60/0.79  thf('53', plain,
% 0.60/0.79      ((r2_hidden @ 
% 0.60/0.79        (k4_tarski @ (sk_D_3 @ (sk_C_2 @ sk_A) @ sk_B_1) @ 
% 0.60/0.79         (sk_D_1 @ (sk_D_3 @ (sk_C_2 @ sk_A) @ sk_B_1) @ 
% 0.60/0.79          (k5_relat_1 @ sk_B_1 @ sk_A))) @ 
% 0.60/0.79        (k5_relat_1 @ sk_B_1 @ sk_A))),
% 0.60/0.79      inference('sup-', [status(thm)], ['39', '52'])).
% 0.60/0.79  thf('54', plain,
% 0.60/0.79      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.60/0.79         ((r2_hidden @ X3 @ (k1_relat_1 @ X5))
% 0.60/0.79          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X5))),
% 0.60/0.79      inference('simplify', [status(thm)], ['37'])).
% 0.60/0.79  thf('55', plain,
% 0.60/0.79      ((r2_hidden @ (sk_D_3 @ (sk_C_2 @ sk_A) @ sk_B_1) @ 
% 0.60/0.79        (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['53', '54'])).
% 0.60/0.79  thf(fc2_funct_1, axiom,
% 0.60/0.79    (![A:$i,B:$i]:
% 0.60/0.79     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v1_relat_1 @ B ) & 
% 0.60/0.79         ( v1_funct_1 @ B ) ) =>
% 0.60/0.79       ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) & 
% 0.60/0.79         ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ))).
% 0.60/0.79  thf('56', plain,
% 0.60/0.79      (![X25 : $i, X26 : $i]:
% 0.60/0.79         (~ (v1_funct_1 @ X25)
% 0.60/0.79          | ~ (v1_relat_1 @ X25)
% 0.60/0.79          | ~ (v1_relat_1 @ X26)
% 0.60/0.79          | ~ (v1_funct_1 @ X26)
% 0.60/0.79          | (v1_funct_1 @ (k5_relat_1 @ X25 @ X26)))),
% 0.60/0.79      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.60/0.79  thf(dt_k5_relat_1, axiom,
% 0.60/0.79    (![A:$i,B:$i]:
% 0.60/0.79     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.60/0.79       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.60/0.79  thf('57', plain,
% 0.60/0.79      (![X17 : $i, X18 : $i]:
% 0.60/0.79         (~ (v1_relat_1 @ X17)
% 0.60/0.79          | ~ (v1_relat_1 @ X18)
% 0.60/0.79          | (v1_relat_1 @ (k5_relat_1 @ X17 @ X18)))),
% 0.60/0.79      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.60/0.79  thf('58', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('59', plain,
% 0.60/0.79      (![X22 : $i]:
% 0.60/0.79         ((r2_hidden @ (sk_B @ X22) @ (k1_relat_1 @ X22))
% 0.60/0.79          | (v2_funct_1 @ X22)
% 0.60/0.79          | ~ (v1_funct_1 @ X22)
% 0.60/0.79          | ~ (v1_relat_1 @ X22))),
% 0.60/0.79      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.60/0.79  thf('60', plain,
% 0.60/0.79      (((r2_hidden @ (sk_B @ sk_A) @ (k2_relat_1 @ sk_B_1))
% 0.60/0.79        | ~ (v1_relat_1 @ sk_A)
% 0.60/0.79        | ~ (v1_funct_1 @ sk_A)
% 0.60/0.79        | (v2_funct_1 @ sk_A))),
% 0.60/0.79      inference('sup+', [status(thm)], ['58', '59'])).
% 0.60/0.79  thf('61', plain, ((v1_relat_1 @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('62', plain, ((v1_funct_1 @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('63', plain,
% 0.60/0.79      (((r2_hidden @ (sk_B @ sk_A) @ (k2_relat_1 @ sk_B_1))
% 0.60/0.79        | (v2_funct_1 @ sk_A))),
% 0.60/0.79      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.60/0.79  thf('64', plain, (~ (v2_funct_1 @ sk_A)),
% 0.60/0.79      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.60/0.79  thf('65', plain, ((r2_hidden @ (sk_B @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 0.60/0.79      inference('clc', [status(thm)], ['63', '64'])).
% 0.60/0.79  thf('66', plain,
% 0.60/0.79      (![X12 : $i, X14 : $i]:
% 0.60/0.79         ((r2_hidden @ (k4_tarski @ (sk_D_3 @ X14 @ X12) @ X14) @ X12)
% 0.60/0.79          | ~ (r2_hidden @ X14 @ (k2_relat_1 @ X12)))),
% 0.60/0.79      inference('simplify', [status(thm)], ['28'])).
% 0.60/0.79  thf('67', plain,
% 0.60/0.79      ((r2_hidden @ 
% 0.60/0.79        (k4_tarski @ (sk_D_3 @ (sk_B @ sk_A) @ sk_B_1) @ (sk_B @ sk_A)) @ 
% 0.60/0.79        sk_B_1)),
% 0.60/0.79      inference('sup-', [status(thm)], ['65', '66'])).
% 0.60/0.79  thf('68', plain,
% 0.60/0.79      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.60/0.79         ((r2_hidden @ X3 @ (k1_relat_1 @ X5))
% 0.60/0.79          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X5))),
% 0.60/0.79      inference('simplify', [status(thm)], ['37'])).
% 0.60/0.79  thf('69', plain,
% 0.60/0.79      ((r2_hidden @ (sk_D_3 @ (sk_B @ sk_A) @ sk_B_1) @ (k1_relat_1 @ sk_B_1))),
% 0.60/0.79      inference('sup-', [status(thm)], ['67', '68'])).
% 0.60/0.79  thf('70', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.60/0.79          | (r2_hidden @ 
% 0.60/0.79             (k4_tarski @ X0 @ (sk_D_1 @ X0 @ (k5_relat_1 @ sk_B_1 @ sk_A))) @ 
% 0.60/0.79             (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.60/0.79      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.60/0.79  thf('71', plain,
% 0.60/0.79      ((r2_hidden @ 
% 0.60/0.79        (k4_tarski @ (sk_D_3 @ (sk_B @ sk_A) @ sk_B_1) @ 
% 0.60/0.79         (sk_D_1 @ (sk_D_3 @ (sk_B @ sk_A) @ sk_B_1) @ 
% 0.60/0.79          (k5_relat_1 @ sk_B_1 @ sk_A))) @ 
% 0.60/0.79        (k5_relat_1 @ sk_B_1 @ sk_A))),
% 0.60/0.79      inference('sup-', [status(thm)], ['69', '70'])).
% 0.60/0.79  thf('72', plain,
% 0.60/0.79      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.60/0.79         ((r2_hidden @ X3 @ (k1_relat_1 @ X5))
% 0.60/0.79          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X5))),
% 0.60/0.79      inference('simplify', [status(thm)], ['37'])).
% 0.60/0.79  thf('73', plain,
% 0.60/0.79      ((r2_hidden @ (sk_D_3 @ (sk_B @ sk_A) @ sk_B_1) @ 
% 0.60/0.79        (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['71', '72'])).
% 0.60/0.79  thf('74', plain,
% 0.60/0.79      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.60/0.79         (~ (v2_funct_1 @ X22)
% 0.60/0.79          | ~ (r2_hidden @ X23 @ (k1_relat_1 @ X22))
% 0.60/0.79          | ~ (r2_hidden @ X24 @ (k1_relat_1 @ X22))
% 0.60/0.79          | ((k1_funct_1 @ X22 @ X23) != (k1_funct_1 @ X22 @ X24))
% 0.60/0.79          | ((X23) = (X24))
% 0.60/0.79          | ~ (v1_funct_1 @ X22)
% 0.60/0.79          | ~ (v1_relat_1 @ X22))),
% 0.60/0.79      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.60/0.79  thf('75', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.60/0.79          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.60/0.79          | ((sk_D_3 @ (sk_B @ sk_A) @ sk_B_1) = (X0))
% 0.60/0.79          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.60/0.79              (sk_D_3 @ (sk_B @ sk_A) @ sk_B_1))
% 0.60/0.79              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.60/0.79          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.60/0.79          | ~ (v2_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['73', '74'])).
% 0.60/0.79  thf('76', plain, ((v2_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('77', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.60/0.79          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.60/0.79          | ((sk_D_3 @ (sk_B @ sk_A) @ sk_B_1) = (X0))
% 0.60/0.79          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.60/0.79              (sk_D_3 @ (sk_B @ sk_A) @ sk_B_1))
% 0.60/0.79              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.60/0.79          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))))),
% 0.60/0.79      inference('demod', [status(thm)], ['75', '76'])).
% 0.60/0.79  thf('78', plain,
% 0.60/0.79      ((r2_hidden @ (sk_D_3 @ (sk_B @ sk_A) @ sk_B_1) @ 
% 0.60/0.79        (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['71', '72'])).
% 0.60/0.79  thf(t22_funct_1, axiom,
% 0.60/0.79    (![A:$i,B:$i]:
% 0.60/0.79     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.60/0.79       ( ![C:$i]:
% 0.60/0.79         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.60/0.79           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) =>
% 0.60/0.79             ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A ) =
% 0.60/0.79               ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) ))).
% 0.60/0.79  thf('79', plain,
% 0.60/0.79      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.60/0.79         (~ (v1_relat_1 @ X27)
% 0.60/0.79          | ~ (v1_funct_1 @ X27)
% 0.60/0.79          | ((k1_funct_1 @ (k5_relat_1 @ X27 @ X28) @ X29)
% 0.60/0.79              = (k1_funct_1 @ X28 @ (k1_funct_1 @ X27 @ X29)))
% 0.60/0.79          | ~ (r2_hidden @ X29 @ (k1_relat_1 @ (k5_relat_1 @ X27 @ X28)))
% 0.60/0.79          | ~ (v1_funct_1 @ X28)
% 0.60/0.79          | ~ (v1_relat_1 @ X28))),
% 0.60/0.79      inference('cnf', [status(esa)], [t22_funct_1])).
% 0.60/0.79  thf('80', plain,
% 0.60/0.79      ((~ (v1_relat_1 @ sk_A)
% 0.60/0.79        | ~ (v1_funct_1 @ sk_A)
% 0.60/0.79        | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.60/0.79            (sk_D_3 @ (sk_B @ sk_A) @ sk_B_1))
% 0.60/0.79            = (k1_funct_1 @ sk_A @ 
% 0.60/0.79               (k1_funct_1 @ sk_B_1 @ (sk_D_3 @ (sk_B @ sk_A) @ sk_B_1))))
% 0.60/0.79        | ~ (v1_funct_1 @ sk_B_1)
% 0.60/0.79        | ~ (v1_relat_1 @ sk_B_1))),
% 0.60/0.79      inference('sup-', [status(thm)], ['78', '79'])).
% 0.60/0.79  thf('81', plain, ((v1_relat_1 @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('82', plain, ((v1_funct_1 @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('83', plain,
% 0.60/0.79      ((r2_hidden @ 
% 0.60/0.79        (k4_tarski @ (sk_D_3 @ (sk_B @ sk_A) @ sk_B_1) @ (sk_B @ sk_A)) @ 
% 0.60/0.79        sk_B_1)),
% 0.60/0.79      inference('sup-', [status(thm)], ['65', '66'])).
% 0.60/0.79  thf('84', plain,
% 0.60/0.79      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.60/0.79         (~ (r2_hidden @ (k4_tarski @ X32 @ X34) @ X33)
% 0.60/0.79          | ((X34) = (k1_funct_1 @ X33 @ X32))
% 0.60/0.79          | ~ (v1_funct_1 @ X33)
% 0.60/0.79          | ~ (v1_relat_1 @ X33))),
% 0.60/0.79      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.60/0.79  thf('85', plain,
% 0.60/0.79      ((~ (v1_relat_1 @ sk_B_1)
% 0.60/0.79        | ~ (v1_funct_1 @ sk_B_1)
% 0.60/0.79        | ((sk_B @ sk_A)
% 0.60/0.79            = (k1_funct_1 @ sk_B_1 @ (sk_D_3 @ (sk_B @ sk_A) @ sk_B_1))))),
% 0.60/0.79      inference('sup-', [status(thm)], ['83', '84'])).
% 0.60/0.79  thf('86', plain, ((v1_relat_1 @ sk_B_1)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('87', plain, ((v1_funct_1 @ sk_B_1)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('88', plain,
% 0.60/0.79      (((sk_B @ sk_A)
% 0.60/0.79         = (k1_funct_1 @ sk_B_1 @ (sk_D_3 @ (sk_B @ sk_A) @ sk_B_1)))),
% 0.60/0.79      inference('demod', [status(thm)], ['85', '86', '87'])).
% 0.60/0.79  thf('89', plain, ((v1_funct_1 @ sk_B_1)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('90', plain, ((v1_relat_1 @ sk_B_1)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('91', plain,
% 0.60/0.79      (((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.60/0.79         (sk_D_3 @ (sk_B @ sk_A) @ sk_B_1))
% 0.60/0.79         = (k1_funct_1 @ sk_A @ (sk_B @ sk_A)))),
% 0.60/0.79      inference('demod', [status(thm)], ['80', '81', '82', '88', '89', '90'])).
% 0.60/0.79  thf('92', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.60/0.79          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.60/0.79          | ((sk_D_3 @ (sk_B @ sk_A) @ sk_B_1) = (X0))
% 0.60/0.79          | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.60/0.79              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.60/0.79          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))))),
% 0.60/0.79      inference('demod', [status(thm)], ['77', '91'])).
% 0.60/0.79  thf('93', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (~ (v1_relat_1 @ sk_A)
% 0.60/0.79          | ~ (v1_relat_1 @ sk_B_1)
% 0.60/0.79          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.60/0.79          | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.60/0.79              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.60/0.79          | ((sk_D_3 @ (sk_B @ sk_A) @ sk_B_1) = (X0))
% 0.60/0.79          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['57', '92'])).
% 0.60/0.79  thf('94', plain, ((v1_relat_1 @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('95', plain, ((v1_relat_1 @ sk_B_1)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('96', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (~ (r2_hidden @ X0 @ (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.60/0.79          | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.60/0.79              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.60/0.79          | ((sk_D_3 @ (sk_B @ sk_A) @ sk_B_1) = (X0))
% 0.60/0.79          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.60/0.79      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.60/0.79  thf('97', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (~ (v1_funct_1 @ sk_A)
% 0.60/0.79          | ~ (v1_relat_1 @ sk_A)
% 0.60/0.79          | ~ (v1_relat_1 @ sk_B_1)
% 0.60/0.79          | ~ (v1_funct_1 @ sk_B_1)
% 0.60/0.79          | ((sk_D_3 @ (sk_B @ sk_A) @ sk_B_1) = (X0))
% 0.60/0.79          | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.60/0.79              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.60/0.79          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))))),
% 0.60/0.79      inference('sup-', [status(thm)], ['56', '96'])).
% 0.60/0.79  thf('98', plain, ((v1_funct_1 @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('99', plain, ((v1_relat_1 @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('100', plain, ((v1_relat_1 @ sk_B_1)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('101', plain, ((v1_funct_1 @ sk_B_1)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('102', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (((sk_D_3 @ (sk_B @ sk_A) @ sk_B_1) = (X0))
% 0.60/0.79          | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.60/0.79              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.60/0.79          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))))),
% 0.60/0.79      inference('demod', [status(thm)], ['97', '98', '99', '100', '101'])).
% 0.60/0.79  thf('103', plain,
% 0.60/0.79      ((((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.60/0.79          != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.60/0.79              (sk_D_3 @ (sk_C_2 @ sk_A) @ sk_B_1)))
% 0.60/0.79        | ((sk_D_3 @ (sk_B @ sk_A) @ sk_B_1)
% 0.60/0.79            = (sk_D_3 @ (sk_C_2 @ sk_A) @ sk_B_1)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['55', '102'])).
% 0.60/0.79  thf('104', plain,
% 0.60/0.79      ((r2_hidden @ (sk_D_3 @ (sk_C_2 @ sk_A) @ sk_B_1) @ 
% 0.60/0.79        (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['53', '54'])).
% 0.60/0.79  thf('105', plain,
% 0.60/0.79      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.60/0.79         (~ (v1_relat_1 @ X27)
% 0.60/0.79          | ~ (v1_funct_1 @ X27)
% 0.60/0.79          | ((k1_funct_1 @ (k5_relat_1 @ X27 @ X28) @ X29)
% 0.60/0.79              = (k1_funct_1 @ X28 @ (k1_funct_1 @ X27 @ X29)))
% 0.60/0.79          | ~ (r2_hidden @ X29 @ (k1_relat_1 @ (k5_relat_1 @ X27 @ X28)))
% 0.60/0.79          | ~ (v1_funct_1 @ X28)
% 0.60/0.79          | ~ (v1_relat_1 @ X28))),
% 0.60/0.79      inference('cnf', [status(esa)], [t22_funct_1])).
% 0.60/0.79  thf('106', plain,
% 0.60/0.79      ((~ (v1_relat_1 @ sk_A)
% 0.60/0.79        | ~ (v1_funct_1 @ sk_A)
% 0.60/0.79        | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.60/0.79            (sk_D_3 @ (sk_C_2 @ sk_A) @ sk_B_1))
% 0.60/0.79            = (k1_funct_1 @ sk_A @ 
% 0.60/0.79               (k1_funct_1 @ sk_B_1 @ (sk_D_3 @ (sk_C_2 @ sk_A) @ sk_B_1))))
% 0.60/0.79        | ~ (v1_funct_1 @ sk_B_1)
% 0.60/0.79        | ~ (v1_relat_1 @ sk_B_1))),
% 0.60/0.79      inference('sup-', [status(thm)], ['104', '105'])).
% 0.60/0.79  thf('107', plain, ((v1_relat_1 @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('108', plain, ((v1_funct_1 @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('109', plain,
% 0.60/0.79      (((sk_C_2 @ sk_A)
% 0.60/0.79         = (k1_funct_1 @ sk_B_1 @ (sk_D_3 @ (sk_C_2 @ sk_A) @ sk_B_1)))),
% 0.60/0.79      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.60/0.79  thf('110', plain,
% 0.60/0.79      (![X22 : $i]:
% 0.60/0.79         (((k1_funct_1 @ X22 @ (sk_B @ X22))
% 0.60/0.79            = (k1_funct_1 @ X22 @ (sk_C_2 @ X22)))
% 0.60/0.79          | (v2_funct_1 @ X22)
% 0.60/0.79          | ~ (v1_funct_1 @ X22)
% 0.60/0.79          | ~ (v1_relat_1 @ X22))),
% 0.60/0.79      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.60/0.79  thf('111', plain, ((r2_hidden @ (sk_C_2 @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 0.60/0.79      inference('clc', [status(thm)], ['25', '26'])).
% 0.60/0.79  thf('112', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('113', plain,
% 0.60/0.79      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.60/0.79         (~ (r2_hidden @ X32 @ (k1_relat_1 @ X33))
% 0.60/0.79          | ((X34) != (k1_funct_1 @ X33 @ X32))
% 0.60/0.79          | (r2_hidden @ (k4_tarski @ X32 @ X34) @ X33)
% 0.60/0.79          | ~ (v1_funct_1 @ X33)
% 0.60/0.79          | ~ (v1_relat_1 @ X33))),
% 0.60/0.79      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.60/0.79  thf('114', plain,
% 0.60/0.79      (![X32 : $i, X33 : $i]:
% 0.60/0.79         (~ (v1_relat_1 @ X33)
% 0.60/0.79          | ~ (v1_funct_1 @ X33)
% 0.60/0.79          | (r2_hidden @ (k4_tarski @ X32 @ (k1_funct_1 @ X33 @ X32)) @ X33)
% 0.60/0.79          | ~ (r2_hidden @ X32 @ (k1_relat_1 @ X33)))),
% 0.60/0.79      inference('simplify', [status(thm)], ['113'])).
% 0.60/0.79  thf('115', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B_1))
% 0.60/0.79          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_A @ X0)) @ sk_A)
% 0.60/0.79          | ~ (v1_funct_1 @ sk_A)
% 0.60/0.79          | ~ (v1_relat_1 @ sk_A))),
% 0.60/0.79      inference('sup-', [status(thm)], ['112', '114'])).
% 0.60/0.79  thf('116', plain, ((v1_funct_1 @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('117', plain, ((v1_relat_1 @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('118', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B_1))
% 0.60/0.79          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_A @ X0)) @ sk_A))),
% 0.60/0.79      inference('demod', [status(thm)], ['115', '116', '117'])).
% 0.60/0.79  thf('119', plain,
% 0.60/0.79      ((r2_hidden @ 
% 0.60/0.79        (k4_tarski @ (sk_C_2 @ sk_A) @ (k1_funct_1 @ sk_A @ (sk_C_2 @ sk_A))) @ 
% 0.60/0.79        sk_A)),
% 0.60/0.79      inference('sup-', [status(thm)], ['111', '118'])).
% 0.60/0.79  thf('120', plain,
% 0.60/0.79      (((r2_hidden @ 
% 0.60/0.79         (k4_tarski @ (sk_C_2 @ sk_A) @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A))) @ 
% 0.60/0.79         sk_A)
% 0.60/0.79        | ~ (v1_relat_1 @ sk_A)
% 0.60/0.79        | ~ (v1_funct_1 @ sk_A)
% 0.60/0.79        | (v2_funct_1 @ sk_A))),
% 0.60/0.79      inference('sup+', [status(thm)], ['110', '119'])).
% 0.60/0.79  thf('121', plain, ((v1_relat_1 @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('122', plain, ((v1_funct_1 @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('123', plain,
% 0.60/0.79      (((r2_hidden @ 
% 0.60/0.79         (k4_tarski @ (sk_C_2 @ sk_A) @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A))) @ 
% 0.60/0.79         sk_A)
% 0.60/0.79        | (v2_funct_1 @ sk_A))),
% 0.60/0.79      inference('demod', [status(thm)], ['120', '121', '122'])).
% 0.60/0.79  thf('124', plain, (~ (v2_funct_1 @ sk_A)),
% 0.60/0.79      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.60/0.79  thf('125', plain,
% 0.60/0.79      ((r2_hidden @ 
% 0.60/0.79        (k4_tarski @ (sk_C_2 @ sk_A) @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A))) @ 
% 0.60/0.79        sk_A)),
% 0.60/0.79      inference('clc', [status(thm)], ['123', '124'])).
% 0.60/0.79  thf('126', plain,
% 0.60/0.79      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.60/0.79         (~ (r2_hidden @ (k4_tarski @ X32 @ X34) @ X33)
% 0.60/0.79          | ((X34) = (k1_funct_1 @ X33 @ X32))
% 0.60/0.79          | ~ (v1_funct_1 @ X33)
% 0.60/0.79          | ~ (v1_relat_1 @ X33))),
% 0.60/0.79      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.60/0.79  thf('127', plain,
% 0.60/0.79      ((~ (v1_relat_1 @ sk_A)
% 0.60/0.79        | ~ (v1_funct_1 @ sk_A)
% 0.60/0.79        | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.60/0.79            = (k1_funct_1 @ sk_A @ (sk_C_2 @ sk_A))))),
% 0.60/0.79      inference('sup-', [status(thm)], ['125', '126'])).
% 0.60/0.79  thf('128', plain, ((v1_relat_1 @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('129', plain, ((v1_funct_1 @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('130', plain,
% 0.60/0.79      (((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.60/0.79         = (k1_funct_1 @ sk_A @ (sk_C_2 @ sk_A)))),
% 0.60/0.79      inference('demod', [status(thm)], ['127', '128', '129'])).
% 0.60/0.79  thf('131', plain, ((v1_funct_1 @ sk_B_1)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('132', plain, ((v1_relat_1 @ sk_B_1)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('133', plain,
% 0.60/0.79      (((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.60/0.79         (sk_D_3 @ (sk_C_2 @ sk_A) @ sk_B_1))
% 0.60/0.79         = (k1_funct_1 @ sk_A @ (sk_B @ sk_A)))),
% 0.60/0.79      inference('demod', [status(thm)],
% 0.60/0.79                ['106', '107', '108', '109', '130', '131', '132'])).
% 0.60/0.79  thf('134', plain,
% 0.60/0.79      ((((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.60/0.79          != (k1_funct_1 @ sk_A @ (sk_B @ sk_A)))
% 0.60/0.79        | ((sk_D_3 @ (sk_B @ sk_A) @ sk_B_1)
% 0.60/0.79            = (sk_D_3 @ (sk_C_2 @ sk_A) @ sk_B_1)))),
% 0.60/0.79      inference('demod', [status(thm)], ['103', '133'])).
% 0.60/0.79  thf('135', plain,
% 0.60/0.79      (((sk_D_3 @ (sk_B @ sk_A) @ sk_B_1) = (sk_D_3 @ (sk_C_2 @ sk_A) @ sk_B_1))),
% 0.60/0.79      inference('simplify', [status(thm)], ['134'])).
% 0.60/0.79  thf('136', plain,
% 0.60/0.79      (((sk_C_2 @ sk_A)
% 0.60/0.79         = (k1_funct_1 @ sk_B_1 @ (sk_D_3 @ (sk_B @ sk_A) @ sk_B_1)))),
% 0.60/0.79      inference('demod', [status(thm)], ['35', '135'])).
% 0.60/0.79  thf('137', plain,
% 0.60/0.79      (((sk_B @ sk_A)
% 0.60/0.79         = (k1_funct_1 @ sk_B_1 @ (sk_D_3 @ (sk_B @ sk_A) @ sk_B_1)))),
% 0.60/0.79      inference('demod', [status(thm)], ['85', '86', '87'])).
% 0.60/0.79  thf('138', plain, (((sk_B @ sk_A) = (sk_C_2 @ sk_A))),
% 0.60/0.79      inference('sup+', [status(thm)], ['136', '137'])).
% 0.60/0.79  thf('139', plain,
% 0.60/0.79      (![X22 : $i]:
% 0.60/0.79         (((sk_B @ X22) != (sk_C_2 @ X22))
% 0.60/0.79          | (v2_funct_1 @ X22)
% 0.60/0.79          | ~ (v1_funct_1 @ X22)
% 0.60/0.79          | ~ (v1_relat_1 @ X22))),
% 0.60/0.79      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.60/0.79  thf('140', plain,
% 0.60/0.79      ((((sk_B @ sk_A) != (sk_B @ sk_A))
% 0.60/0.79        | ~ (v1_relat_1 @ sk_A)
% 0.60/0.79        | ~ (v1_funct_1 @ sk_A)
% 0.60/0.79        | (v2_funct_1 @ sk_A))),
% 0.60/0.79      inference('sup-', [status(thm)], ['138', '139'])).
% 0.60/0.79  thf('141', plain, ((v1_relat_1 @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('142', plain, ((v1_funct_1 @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('143', plain, ((((sk_B @ sk_A) != (sk_B @ sk_A)) | (v2_funct_1 @ sk_A))),
% 0.60/0.79      inference('demod', [status(thm)], ['140', '141', '142'])).
% 0.60/0.79  thf('144', plain, ((v2_funct_1 @ sk_A)),
% 0.60/0.79      inference('simplify', [status(thm)], ['143'])).
% 0.60/0.79  thf('145', plain, ($false), inference('demod', [status(thm)], ['19', '144'])).
% 0.60/0.79  
% 0.60/0.79  % SZS output end Refutation
% 0.60/0.79  
% 0.60/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
