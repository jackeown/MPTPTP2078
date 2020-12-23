%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qIk74WIvn6

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:12 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  247 (2219 expanded)
%              Number of leaves         :   25 ( 621 expanded)
%              Depth                    :   42
%              Number of atoms          : 2425 (30749 expanded)
%              Number of equality atoms :  103 (1354 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ( v2_funct_1 @ X23 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X23 ) @ ( k1_relat_1 @ X24 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X23 @ X24 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
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
    ! [X15: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X15 ) @ ( k1_relat_1 @ X15 ) )
      | ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('22',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) )
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
    ( ( r2_hidden @ ( sk_C_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','18'])).

thf('27',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['25','26'])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('28',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ( X11
       != ( k2_relat_1 @ X9 ) )
      | ( X12
        = ( k1_funct_1 @ X9 @ ( sk_D_1 @ X12 @ X9 ) ) )
      | ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('29',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( X12
        = ( k1_funct_1 @ X9 @ ( sk_D_1 @ X12 @ X9 ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( ( sk_C_1 @ sk_A )
      = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( sk_C_1 @ sk_A )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('35',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ( X11
       != ( k2_relat_1 @ X9 ) )
      | ( r2_hidden @ ( sk_D_1 @ X12 @ X9 ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('36',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( r2_hidden @ ( sk_D_1 @ X12 @ X9 ) @ ( k1_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf(t23_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A )
              = ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) )).

thf('41',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X21 @ X20 ) @ X22 )
        = ( k1_funct_1 @ X20 @ ( k1_funct_1 @ X21 @ X22 ) ) )
      | ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ X0 ) @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( sk_C_1 @ sk_A )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ X0 ) @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) )
        = ( k1_funct_1 @ X0 @ ( sk_C_1 @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('47',plain,(
    ! [X5: $i] :
      ( ( ( k10_relat_1 @ X5 @ ( k2_relat_1 @ X5 ) )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('48',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) )
        = ( k10_relat_1 @ X7 @ ( k1_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('49',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(fc2_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) )).

thf('50',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('51',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('52',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('53',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X15: $i] :
      ( ( r2_hidden @ ( sk_B @ X15 ) @ ( k1_relat_1 @ X15 ) )
      | ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('55',plain,
    ( ( r2_hidden @ ( sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( r2_hidden @ ( sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','18'])).

thf('60',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( r2_hidden @ ( sk_D_1 @ X12 @ X9 ) @ ( k1_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('62',plain,
    ( ( r2_hidden @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X21 @ X20 ) @ X22 )
        = ( k1_funct_1 @ X20 @ ( k1_funct_1 @ X21 @ X22 ) ) )
      | ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ X0 ) @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('71',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( X12
        = ( k1_funct_1 @ X9 @ ( sk_D_1 @ X12 @ X9 ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('72',plain,
    ( ( ( sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( sk_B @ sk_A )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ X0 ) @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) )
        = ( k1_funct_1 @ X0 @ ( sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68','69','75'])).

thf('77',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('78',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('79',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('80',plain,(
    ! [X5: $i] :
      ( ( ( k10_relat_1 @ X5 @ ( k2_relat_1 @ X5 ) )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('81',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) )
        = ( k10_relat_1 @ X7 @ ( k1_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('83',plain,(
    ! [X9: $i,X11: $i,X13: $i,X14: $i] :
      ( ( X11
       != ( k2_relat_1 @ X9 ) )
      | ( r2_hidden @ X13 @ X11 )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X9 ) )
      | ( X13
       != ( k1_funct_1 @ X9 @ X14 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('84',plain,(
    ! [X9: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X9 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X9 @ X14 ) @ ( k2_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['82','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ sk_B_1 ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k5_relat_1 @ X0 @ sk_A ) @ X1 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ sk_B_1 ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k5_relat_1 @ X0 @ sk_A ) @ X1 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ( r2_hidden @ ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['80','88'])).

thf('90',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['79','92'])).

thf('94',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['93','94','95','96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['78','98'])).

thf('100',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,(
    r2_hidden @ ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','102'])).

thf('104',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['76','103'])).

thf('105',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( X12
        = ( k1_funct_1 @ X9 @ ( sk_D_1 @ X12 @ X9 ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('109',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
      = ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
    | ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
      = ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['52','109'])).

thf('111',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
    | ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
      = ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['110','111','112','113','114'])).

thf('116',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
      = ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['51','115'])).

thf('117',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
    = ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) )
        = ( k10_relat_1 @ X7 @ ( k1_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('121',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X15 ) )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X15 ) )
      | ( ( k1_funct_1 @ X15 @ X16 )
       != ( k1_funct_1 @ X15 @ X17 ) )
      | ( X16 = X17 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( X2 = X3 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
       != ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( r2_hidden @ X3 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
        = X0 )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) @ ( k10_relat_1 @ sk_B_1 @ ( k1_relat_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['119','122'])).

thf('124',plain,(
    v2_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) )
        = ( k10_relat_1 @ X7 @ ( k1_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('129',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('130',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('131',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('132',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( r2_hidden @ ( sk_D_1 @ X12 @ X9 ) @ ( k1_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('133',plain,
    ( ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['130','133'])).

thf('135',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['134','135','136','137','138'])).

thf('140',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['129','139'])).

thf('141',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['140','141','142'])).

thf('144',plain,
    ( ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) @ ( k10_relat_1 @ sk_B_1 @ ( k1_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['128','143'])).

thf('145',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) @ ( k10_relat_1 @ sk_B_1 @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['144','145','146','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
        = X0 )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['123','124','125','126','127','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
        = X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','149'])).

thf('151',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
        = X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['150','151','152','153','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['49','155'])).

thf('157',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['156','157','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k10_relat_1 @ sk_B_1 @ ( k1_relat_1 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_A )
      | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
        = X0 )
      | ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','159'])).

thf('161',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k10_relat_1 @ sk_B_1 @ ( k2_relat_1 @ sk_B_1 ) ) )
      | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
        = X0 )
      | ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['160','161','162','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['47','164'])).

thf('166',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
     != ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      = ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) )
    | ~ ( r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['46','167'])).

thf('169',plain,(
    ! [X15: $i] :
      ( ( ( k1_funct_1 @ X15 @ ( sk_B @ X15 ) )
        = ( k1_funct_1 @ X15 @ ( sk_C_1 @ X15 ) ) )
      | ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('170',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('171',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    ! [X9: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X9 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X9 @ X14 ) @ ( k2_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['173','174','175'])).

thf('177',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) ) @ ( k2_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['170','176'])).

thf('178',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( X12
        = ( k1_funct_1 @ X9 @ ( sk_D_1 @ X12 @ X9 ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('179',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) )
      = ( k1_funct_1 @ sk_A @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) )
    = ( k1_funct_1 @ sk_A @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['179','180','181'])).

thf('183',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) )
      = ( k1_funct_1 @ sk_A @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['169','182'])).

thf('184',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['173','174','175'])).

thf('186',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k2_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( X12
        = ( k1_funct_1 @ X9 @ ( sk_D_1 @ X12 @ X9 ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('188',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
      = ( k1_funct_1 @ sk_A @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
    = ( k1_funct_1 @ sk_A @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['188','189','190'])).

thf('192',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) )
      = ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['183','191','192','193'])).

thf('195',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','18'])).

thf('196',plain,
    ( ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) )
    = ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['194','195'])).

thf('197',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('200',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
     != ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      = ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['168','196','197','198','199'])).

thf('201',plain,
    ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
    = ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['200'])).

thf('202',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ X0 ) @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) )
        = ( k1_funct_1 @ X0 @ ( sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68','69','75'])).

thf('203',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('204',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
     != ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      = ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) )
    | ~ ( r2_hidden @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('208',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
     != ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      = ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['204','205','206','207'])).

thf('209',plain,
    ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
    = ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['208'])).

thf('210',plain,
    ( ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 )
    = ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['201','209'])).

thf('211',plain,
    ( ( sk_C_1 @ sk_A )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['33','210'])).

thf('212',plain,
    ( ( sk_B @ sk_A )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('213',plain,
    ( ( sk_B @ sk_A )
    = ( sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['211','212'])).

thf('214',plain,(
    ! [X15: $i] :
      ( ( ( sk_B @ X15 )
       != ( sk_C_1 @ X15 ) )
      | ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('215',plain,
    ( ( ( sk_B @ sk_A )
     != ( sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,
    ( ( ( sk_B @ sk_A )
     != ( sk_B @ sk_A ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['215','216','217'])).

thf('219',plain,(
    v2_funct_1 @ sk_A ),
    inference(simplify,[status(thm)],['218'])).

thf('220',plain,(
    $false ),
    inference(demod,[status(thm)],['19','219'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qIk74WIvn6
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:40:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.90/1.09  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.90/1.09  % Solved by: fo/fo7.sh
% 0.90/1.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.09  % done 601 iterations in 0.647s
% 0.90/1.09  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.90/1.09  % SZS output start Refutation
% 0.90/1.09  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.09  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.90/1.09  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.90/1.09  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.90/1.09  thf(sk_B_type, type, sk_B: $i > $i).
% 0.90/1.09  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.90/1.09  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.90/1.09  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.90/1.09  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.90/1.09  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.09  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.09  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.90/1.09  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.90/1.09  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.90/1.09  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.90/1.09  thf(t48_funct_1, conjecture,
% 0.90/1.09    (![A:$i]:
% 0.90/1.09     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.90/1.09       ( ![B:$i]:
% 0.90/1.09         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.90/1.09           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.90/1.09               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.90/1.09             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.90/1.09  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.09    (~( ![A:$i]:
% 0.90/1.09        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.90/1.09          ( ![B:$i]:
% 0.90/1.09            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.90/1.09              ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.90/1.09                  ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.90/1.09                ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ) )),
% 0.90/1.09    inference('cnf.neg', [status(esa)], [t48_funct_1])).
% 0.90/1.09  thf('0', plain, ((~ (v2_funct_1 @ sk_B_1) | ~ (v2_funct_1 @ sk_A))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('1', plain, ((~ (v2_funct_1 @ sk_A)) <= (~ ((v2_funct_1 @ sk_A)))),
% 0.90/1.09      inference('split', [status(esa)], ['0'])).
% 0.90/1.09  thf(d10_xboole_0, axiom,
% 0.90/1.09    (![A:$i,B:$i]:
% 0.90/1.09     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.90/1.09  thf('2', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.90/1.09      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.09  thf('3', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.90/1.09      inference('simplify', [status(thm)], ['2'])).
% 0.90/1.09  thf('4', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf(t47_funct_1, axiom,
% 0.90/1.09    (![A:$i]:
% 0.90/1.09     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.90/1.09       ( ![B:$i]:
% 0.90/1.09         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.90/1.09           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.90/1.09               ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) =>
% 0.90/1.09             ( v2_funct_1 @ B ) ) ) ) ))).
% 0.90/1.09  thf('5', plain,
% 0.90/1.09      (![X23 : $i, X24 : $i]:
% 0.90/1.09         (~ (v1_relat_1 @ X23)
% 0.90/1.09          | ~ (v1_funct_1 @ X23)
% 0.90/1.09          | (v2_funct_1 @ X23)
% 0.90/1.09          | ~ (r1_tarski @ (k2_relat_1 @ X23) @ (k1_relat_1 @ X24))
% 0.90/1.09          | ~ (v2_funct_1 @ (k5_relat_1 @ X23 @ X24))
% 0.90/1.09          | ~ (v1_funct_1 @ X24)
% 0.90/1.09          | ~ (v1_relat_1 @ X24))),
% 0.90/1.09      inference('cnf', [status(esa)], [t47_funct_1])).
% 0.90/1.09  thf('6', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (~ (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ sk_B_1))
% 0.90/1.09          | ~ (v1_relat_1 @ sk_A)
% 0.90/1.09          | ~ (v1_funct_1 @ sk_A)
% 0.90/1.09          | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_A))
% 0.90/1.09          | (v2_funct_1 @ X0)
% 0.90/1.09          | ~ (v1_funct_1 @ X0)
% 0.90/1.09          | ~ (v1_relat_1 @ X0))),
% 0.90/1.09      inference('sup-', [status(thm)], ['4', '5'])).
% 0.90/1.09  thf('7', plain, ((v1_relat_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('8', plain, ((v1_funct_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('9', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (~ (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ sk_B_1))
% 0.90/1.09          | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_A))
% 0.90/1.09          | (v2_funct_1 @ X0)
% 0.90/1.09          | ~ (v1_funct_1 @ X0)
% 0.90/1.09          | ~ (v1_relat_1 @ X0))),
% 0.90/1.09      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.90/1.09  thf('10', plain,
% 0.90/1.09      ((~ (v1_relat_1 @ sk_B_1)
% 0.90/1.09        | ~ (v1_funct_1 @ sk_B_1)
% 0.90/1.09        | (v2_funct_1 @ sk_B_1)
% 0.90/1.09        | ~ (v2_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['3', '9'])).
% 0.90/1.09  thf('11', plain, ((v1_relat_1 @ sk_B_1)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('12', plain, ((v1_funct_1 @ sk_B_1)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('13', plain, ((v2_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('14', plain, ((v2_funct_1 @ sk_B_1)),
% 0.90/1.09      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.90/1.09  thf('15', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.90/1.09      inference('split', [status(esa)], ['0'])).
% 0.90/1.09  thf('16', plain, (((v2_funct_1 @ sk_B_1))),
% 0.90/1.09      inference('sup-', [status(thm)], ['14', '15'])).
% 0.90/1.09  thf('17', plain, (~ ((v2_funct_1 @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.90/1.09      inference('split', [status(esa)], ['0'])).
% 0.90/1.09  thf('18', plain, (~ ((v2_funct_1 @ sk_A))),
% 0.90/1.09      inference('sat_resolution*', [status(thm)], ['16', '17'])).
% 0.90/1.09  thf('19', plain, (~ (v2_funct_1 @ sk_A)),
% 0.90/1.09      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.90/1.09  thf('20', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf(d8_funct_1, axiom,
% 0.90/1.09    (![A:$i]:
% 0.90/1.09     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.90/1.09       ( ( v2_funct_1 @ A ) <=>
% 0.90/1.09         ( ![B:$i,C:$i]:
% 0.90/1.09           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.90/1.09               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.90/1.09               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.90/1.09             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.90/1.09  thf('21', plain,
% 0.90/1.09      (![X15 : $i]:
% 0.90/1.09         ((r2_hidden @ (sk_C_1 @ X15) @ (k1_relat_1 @ X15))
% 0.90/1.09          | (v2_funct_1 @ X15)
% 0.90/1.09          | ~ (v1_funct_1 @ X15)
% 0.90/1.09          | ~ (v1_relat_1 @ X15))),
% 0.90/1.09      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.90/1.09  thf('22', plain,
% 0.90/1.09      (((r2_hidden @ (sk_C_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))
% 0.90/1.09        | ~ (v1_relat_1 @ sk_A)
% 0.90/1.09        | ~ (v1_funct_1 @ sk_A)
% 0.90/1.09        | (v2_funct_1 @ sk_A))),
% 0.90/1.09      inference('sup+', [status(thm)], ['20', '21'])).
% 0.90/1.09  thf('23', plain, ((v1_relat_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('24', plain, ((v1_funct_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('25', plain,
% 0.90/1.09      (((r2_hidden @ (sk_C_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))
% 0.90/1.09        | (v2_funct_1 @ sk_A))),
% 0.90/1.09      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.90/1.09  thf('26', plain, (~ (v2_funct_1 @ sk_A)),
% 0.90/1.09      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.90/1.09  thf('27', plain, ((r2_hidden @ (sk_C_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 0.90/1.09      inference('clc', [status(thm)], ['25', '26'])).
% 0.90/1.09  thf(d5_funct_1, axiom,
% 0.90/1.09    (![A:$i]:
% 0.90/1.09     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.90/1.09       ( ![B:$i]:
% 0.90/1.09         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.90/1.09           ( ![C:$i]:
% 0.90/1.09             ( ( r2_hidden @ C @ B ) <=>
% 0.90/1.09               ( ?[D:$i]:
% 0.90/1.09                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.90/1.09                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.90/1.09  thf('28', plain,
% 0.90/1.09      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.90/1.09         (((X11) != (k2_relat_1 @ X9))
% 0.90/1.09          | ((X12) = (k1_funct_1 @ X9 @ (sk_D_1 @ X12 @ X9)))
% 0.90/1.09          | ~ (r2_hidden @ X12 @ X11)
% 0.90/1.09          | ~ (v1_funct_1 @ X9)
% 0.90/1.09          | ~ (v1_relat_1 @ X9))),
% 0.90/1.09      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.90/1.09  thf('29', plain,
% 0.90/1.09      (![X9 : $i, X12 : $i]:
% 0.90/1.09         (~ (v1_relat_1 @ X9)
% 0.90/1.09          | ~ (v1_funct_1 @ X9)
% 0.90/1.09          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 0.90/1.09          | ((X12) = (k1_funct_1 @ X9 @ (sk_D_1 @ X12 @ X9))))),
% 0.90/1.09      inference('simplify', [status(thm)], ['28'])).
% 0.90/1.09  thf('30', plain,
% 0.90/1.09      ((((sk_C_1 @ sk_A)
% 0.90/1.09          = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1)))
% 0.90/1.09        | ~ (v1_funct_1 @ sk_B_1)
% 0.90/1.09        | ~ (v1_relat_1 @ sk_B_1))),
% 0.90/1.09      inference('sup-', [status(thm)], ['27', '29'])).
% 0.90/1.09  thf('31', plain, ((v1_funct_1 @ sk_B_1)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('32', plain, ((v1_relat_1 @ sk_B_1)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('33', plain,
% 0.90/1.09      (((sk_C_1 @ sk_A)
% 0.90/1.09         = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1)))),
% 0.90/1.09      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.90/1.09  thf('34', plain, ((r2_hidden @ (sk_C_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 0.90/1.09      inference('clc', [status(thm)], ['25', '26'])).
% 0.90/1.09  thf('35', plain,
% 0.90/1.09      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.90/1.09         (((X11) != (k2_relat_1 @ X9))
% 0.90/1.09          | (r2_hidden @ (sk_D_1 @ X12 @ X9) @ (k1_relat_1 @ X9))
% 0.90/1.09          | ~ (r2_hidden @ X12 @ X11)
% 0.90/1.09          | ~ (v1_funct_1 @ X9)
% 0.90/1.09          | ~ (v1_relat_1 @ X9))),
% 0.90/1.09      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.90/1.09  thf('36', plain,
% 0.90/1.09      (![X9 : $i, X12 : $i]:
% 0.90/1.09         (~ (v1_relat_1 @ X9)
% 0.90/1.09          | ~ (v1_funct_1 @ X9)
% 0.90/1.09          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 0.90/1.09          | (r2_hidden @ (sk_D_1 @ X12 @ X9) @ (k1_relat_1 @ X9)))),
% 0.90/1.09      inference('simplify', [status(thm)], ['35'])).
% 0.90/1.09  thf('37', plain,
% 0.90/1.09      (((r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1) @ 
% 0.90/1.09         (k1_relat_1 @ sk_B_1))
% 0.90/1.09        | ~ (v1_funct_1 @ sk_B_1)
% 0.90/1.09        | ~ (v1_relat_1 @ sk_B_1))),
% 0.90/1.09      inference('sup-', [status(thm)], ['34', '36'])).
% 0.90/1.09  thf('38', plain, ((v1_funct_1 @ sk_B_1)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('39', plain, ((v1_relat_1 @ sk_B_1)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('40', plain,
% 0.90/1.09      ((r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1) @ (k1_relat_1 @ sk_B_1))),
% 0.90/1.09      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.90/1.09  thf(t23_funct_1, axiom,
% 0.90/1.09    (![A:$i,B:$i]:
% 0.90/1.09     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.90/1.09       ( ![C:$i]:
% 0.90/1.09         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.90/1.09           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.90/1.09             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.90/1.09               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 0.90/1.09  thf('41', plain,
% 0.90/1.09      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.90/1.09         (~ (v1_relat_1 @ X20)
% 0.90/1.09          | ~ (v1_funct_1 @ X20)
% 0.90/1.09          | ((k1_funct_1 @ (k5_relat_1 @ X21 @ X20) @ X22)
% 0.90/1.09              = (k1_funct_1 @ X20 @ (k1_funct_1 @ X21 @ X22)))
% 0.90/1.09          | ~ (r2_hidden @ X22 @ (k1_relat_1 @ X21))
% 0.90/1.09          | ~ (v1_funct_1 @ X21)
% 0.90/1.09          | ~ (v1_relat_1 @ X21))),
% 0.90/1.09      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.90/1.09  thf('42', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (~ (v1_relat_1 @ sk_B_1)
% 0.90/1.09          | ~ (v1_funct_1 @ sk_B_1)
% 0.90/1.09          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ X0) @ 
% 0.90/1.09              (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1))
% 0.90/1.09              = (k1_funct_1 @ X0 @ 
% 0.90/1.09                 (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1))))
% 0.90/1.09          | ~ (v1_funct_1 @ X0)
% 0.90/1.09          | ~ (v1_relat_1 @ X0))),
% 0.90/1.09      inference('sup-', [status(thm)], ['40', '41'])).
% 0.90/1.09  thf('43', plain, ((v1_relat_1 @ sk_B_1)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('44', plain, ((v1_funct_1 @ sk_B_1)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('45', plain,
% 0.90/1.09      (((sk_C_1 @ sk_A)
% 0.90/1.09         = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1)))),
% 0.90/1.09      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.90/1.09  thf('46', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ X0) @ 
% 0.90/1.09            (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1))
% 0.90/1.09            = (k1_funct_1 @ X0 @ (sk_C_1 @ sk_A)))
% 0.90/1.09          | ~ (v1_funct_1 @ X0)
% 0.90/1.09          | ~ (v1_relat_1 @ X0))),
% 0.90/1.09      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 0.90/1.09  thf(t169_relat_1, axiom,
% 0.90/1.09    (![A:$i]:
% 0.90/1.09     ( ( v1_relat_1 @ A ) =>
% 0.90/1.09       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.90/1.09  thf('47', plain,
% 0.90/1.09      (![X5 : $i]:
% 0.90/1.09         (((k10_relat_1 @ X5 @ (k2_relat_1 @ X5)) = (k1_relat_1 @ X5))
% 0.90/1.09          | ~ (v1_relat_1 @ X5))),
% 0.90/1.09      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.90/1.09  thf(t182_relat_1, axiom,
% 0.90/1.09    (![A:$i]:
% 0.90/1.09     ( ( v1_relat_1 @ A ) =>
% 0.90/1.09       ( ![B:$i]:
% 0.90/1.09         ( ( v1_relat_1 @ B ) =>
% 0.90/1.09           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.90/1.09             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.90/1.09  thf('48', plain,
% 0.90/1.09      (![X6 : $i, X7 : $i]:
% 0.90/1.09         (~ (v1_relat_1 @ X6)
% 0.90/1.09          | ((k1_relat_1 @ (k5_relat_1 @ X7 @ X6))
% 0.90/1.09              = (k10_relat_1 @ X7 @ (k1_relat_1 @ X6)))
% 0.90/1.09          | ~ (v1_relat_1 @ X7))),
% 0.90/1.09      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.90/1.09  thf(dt_k5_relat_1, axiom,
% 0.90/1.09    (![A:$i,B:$i]:
% 0.90/1.09     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.90/1.09       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.90/1.09  thf('49', plain,
% 0.90/1.09      (![X3 : $i, X4 : $i]:
% 0.90/1.09         (~ (v1_relat_1 @ X3)
% 0.90/1.09          | ~ (v1_relat_1 @ X4)
% 0.90/1.09          | (v1_relat_1 @ (k5_relat_1 @ X3 @ X4)))),
% 0.90/1.09      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.90/1.09  thf(fc2_funct_1, axiom,
% 0.90/1.09    (![A:$i,B:$i]:
% 0.90/1.09     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v1_relat_1 @ B ) & 
% 0.90/1.09         ( v1_funct_1 @ B ) ) =>
% 0.90/1.09       ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) & 
% 0.90/1.09         ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ))).
% 0.90/1.09  thf('50', plain,
% 0.90/1.09      (![X18 : $i, X19 : $i]:
% 0.90/1.09         (~ (v1_funct_1 @ X18)
% 0.90/1.09          | ~ (v1_relat_1 @ X18)
% 0.90/1.09          | ~ (v1_relat_1 @ X19)
% 0.90/1.09          | ~ (v1_funct_1 @ X19)
% 0.90/1.09          | (v1_funct_1 @ (k5_relat_1 @ X18 @ X19)))),
% 0.90/1.09      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.90/1.09  thf('51', plain,
% 0.90/1.09      (![X3 : $i, X4 : $i]:
% 0.90/1.09         (~ (v1_relat_1 @ X3)
% 0.90/1.09          | ~ (v1_relat_1 @ X4)
% 0.90/1.09          | (v1_relat_1 @ (k5_relat_1 @ X3 @ X4)))),
% 0.90/1.09      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.90/1.09  thf('52', plain,
% 0.90/1.09      (![X18 : $i, X19 : $i]:
% 0.90/1.09         (~ (v1_funct_1 @ X18)
% 0.90/1.09          | ~ (v1_relat_1 @ X18)
% 0.90/1.09          | ~ (v1_relat_1 @ X19)
% 0.90/1.09          | ~ (v1_funct_1 @ X19)
% 0.90/1.09          | (v1_funct_1 @ (k5_relat_1 @ X18 @ X19)))),
% 0.90/1.09      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.90/1.09  thf('53', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('54', plain,
% 0.90/1.09      (![X15 : $i]:
% 0.90/1.09         ((r2_hidden @ (sk_B @ X15) @ (k1_relat_1 @ X15))
% 0.90/1.09          | (v2_funct_1 @ X15)
% 0.90/1.09          | ~ (v1_funct_1 @ X15)
% 0.90/1.09          | ~ (v1_relat_1 @ X15))),
% 0.90/1.09      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.90/1.09  thf('55', plain,
% 0.90/1.09      (((r2_hidden @ (sk_B @ sk_A) @ (k2_relat_1 @ sk_B_1))
% 0.90/1.09        | ~ (v1_relat_1 @ sk_A)
% 0.90/1.09        | ~ (v1_funct_1 @ sk_A)
% 0.90/1.09        | (v2_funct_1 @ sk_A))),
% 0.90/1.09      inference('sup+', [status(thm)], ['53', '54'])).
% 0.90/1.09  thf('56', plain, ((v1_relat_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('57', plain, ((v1_funct_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('58', plain,
% 0.90/1.09      (((r2_hidden @ (sk_B @ sk_A) @ (k2_relat_1 @ sk_B_1))
% 0.90/1.09        | (v2_funct_1 @ sk_A))),
% 0.90/1.09      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.90/1.09  thf('59', plain, (~ (v2_funct_1 @ sk_A)),
% 0.90/1.09      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.90/1.09  thf('60', plain, ((r2_hidden @ (sk_B @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 0.90/1.09      inference('clc', [status(thm)], ['58', '59'])).
% 0.90/1.09  thf('61', plain,
% 0.90/1.09      (![X9 : $i, X12 : $i]:
% 0.90/1.09         (~ (v1_relat_1 @ X9)
% 0.90/1.09          | ~ (v1_funct_1 @ X9)
% 0.90/1.09          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 0.90/1.09          | (r2_hidden @ (sk_D_1 @ X12 @ X9) @ (k1_relat_1 @ X9)))),
% 0.90/1.09      inference('simplify', [status(thm)], ['35'])).
% 0.90/1.09  thf('62', plain,
% 0.90/1.09      (((r2_hidden @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) @ (k1_relat_1 @ sk_B_1))
% 0.90/1.09        | ~ (v1_funct_1 @ sk_B_1)
% 0.90/1.09        | ~ (v1_relat_1 @ sk_B_1))),
% 0.90/1.09      inference('sup-', [status(thm)], ['60', '61'])).
% 0.90/1.09  thf('63', plain, ((v1_funct_1 @ sk_B_1)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('64', plain, ((v1_relat_1 @ sk_B_1)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('65', plain,
% 0.90/1.09      ((r2_hidden @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) @ (k1_relat_1 @ sk_B_1))),
% 0.90/1.09      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.90/1.09  thf('66', plain,
% 0.90/1.09      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.90/1.09         (~ (v1_relat_1 @ X20)
% 0.90/1.09          | ~ (v1_funct_1 @ X20)
% 0.90/1.09          | ((k1_funct_1 @ (k5_relat_1 @ X21 @ X20) @ X22)
% 0.90/1.09              = (k1_funct_1 @ X20 @ (k1_funct_1 @ X21 @ X22)))
% 0.90/1.09          | ~ (r2_hidden @ X22 @ (k1_relat_1 @ X21))
% 0.90/1.09          | ~ (v1_funct_1 @ X21)
% 0.90/1.09          | ~ (v1_relat_1 @ X21))),
% 0.90/1.09      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.90/1.09  thf('67', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (~ (v1_relat_1 @ sk_B_1)
% 0.90/1.09          | ~ (v1_funct_1 @ sk_B_1)
% 0.90/1.09          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ X0) @ 
% 0.90/1.09              (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1))
% 0.90/1.09              = (k1_funct_1 @ X0 @ 
% 0.90/1.09                 (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1))))
% 0.90/1.09          | ~ (v1_funct_1 @ X0)
% 0.90/1.09          | ~ (v1_relat_1 @ X0))),
% 0.90/1.09      inference('sup-', [status(thm)], ['65', '66'])).
% 0.90/1.09  thf('68', plain, ((v1_relat_1 @ sk_B_1)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('69', plain, ((v1_funct_1 @ sk_B_1)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('70', plain, ((r2_hidden @ (sk_B @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 0.90/1.09      inference('clc', [status(thm)], ['58', '59'])).
% 0.90/1.09  thf('71', plain,
% 0.90/1.09      (![X9 : $i, X12 : $i]:
% 0.90/1.09         (~ (v1_relat_1 @ X9)
% 0.90/1.09          | ~ (v1_funct_1 @ X9)
% 0.90/1.09          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 0.90/1.09          | ((X12) = (k1_funct_1 @ X9 @ (sk_D_1 @ X12 @ X9))))),
% 0.90/1.09      inference('simplify', [status(thm)], ['28'])).
% 0.90/1.09  thf('72', plain,
% 0.90/1.09      ((((sk_B @ sk_A)
% 0.90/1.09          = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)))
% 0.90/1.09        | ~ (v1_funct_1 @ sk_B_1)
% 0.90/1.09        | ~ (v1_relat_1 @ sk_B_1))),
% 0.90/1.09      inference('sup-', [status(thm)], ['70', '71'])).
% 0.90/1.09  thf('73', plain, ((v1_funct_1 @ sk_B_1)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('74', plain, ((v1_relat_1 @ sk_B_1)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('75', plain,
% 0.90/1.09      (((sk_B @ sk_A)
% 0.90/1.09         = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)))),
% 0.90/1.09      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.90/1.09  thf('76', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ X0) @ 
% 0.90/1.09            (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1))
% 0.90/1.09            = (k1_funct_1 @ X0 @ (sk_B @ sk_A)))
% 0.90/1.09          | ~ (v1_funct_1 @ X0)
% 0.90/1.09          | ~ (v1_relat_1 @ X0))),
% 0.90/1.09      inference('demod', [status(thm)], ['67', '68', '69', '75'])).
% 0.90/1.09  thf('77', plain,
% 0.90/1.09      ((r2_hidden @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) @ (k1_relat_1 @ sk_B_1))),
% 0.90/1.09      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.90/1.09  thf('78', plain,
% 0.90/1.09      (![X3 : $i, X4 : $i]:
% 0.90/1.09         (~ (v1_relat_1 @ X3)
% 0.90/1.09          | ~ (v1_relat_1 @ X4)
% 0.90/1.09          | (v1_relat_1 @ (k5_relat_1 @ X3 @ X4)))),
% 0.90/1.09      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.90/1.09  thf('79', plain,
% 0.90/1.09      (![X18 : $i, X19 : $i]:
% 0.90/1.09         (~ (v1_funct_1 @ X18)
% 0.90/1.09          | ~ (v1_relat_1 @ X18)
% 0.90/1.09          | ~ (v1_relat_1 @ X19)
% 0.90/1.09          | ~ (v1_funct_1 @ X19)
% 0.90/1.09          | (v1_funct_1 @ (k5_relat_1 @ X18 @ X19)))),
% 0.90/1.09      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.90/1.09  thf('80', plain,
% 0.90/1.09      (![X5 : $i]:
% 0.90/1.09         (((k10_relat_1 @ X5 @ (k2_relat_1 @ X5)) = (k1_relat_1 @ X5))
% 0.90/1.09          | ~ (v1_relat_1 @ X5))),
% 0.90/1.09      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.90/1.09  thf('81', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('82', plain,
% 0.90/1.09      (![X6 : $i, X7 : $i]:
% 0.90/1.09         (~ (v1_relat_1 @ X6)
% 0.90/1.09          | ((k1_relat_1 @ (k5_relat_1 @ X7 @ X6))
% 0.90/1.09              = (k10_relat_1 @ X7 @ (k1_relat_1 @ X6)))
% 0.90/1.09          | ~ (v1_relat_1 @ X7))),
% 0.90/1.09      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.90/1.09  thf('83', plain,
% 0.90/1.09      (![X9 : $i, X11 : $i, X13 : $i, X14 : $i]:
% 0.90/1.09         (((X11) != (k2_relat_1 @ X9))
% 0.90/1.09          | (r2_hidden @ X13 @ X11)
% 0.90/1.09          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X9))
% 0.90/1.09          | ((X13) != (k1_funct_1 @ X9 @ X14))
% 0.90/1.09          | ~ (v1_funct_1 @ X9)
% 0.90/1.09          | ~ (v1_relat_1 @ X9))),
% 0.90/1.09      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.90/1.09  thf('84', plain,
% 0.90/1.09      (![X9 : $i, X14 : $i]:
% 0.90/1.09         (~ (v1_relat_1 @ X9)
% 0.90/1.09          | ~ (v1_funct_1 @ X9)
% 0.90/1.09          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X9))
% 0.90/1.09          | (r2_hidden @ (k1_funct_1 @ X9 @ X14) @ (k2_relat_1 @ X9)))),
% 0.90/1.09      inference('simplify', [status(thm)], ['83'])).
% 0.90/1.09  thf('85', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.09         (~ (r2_hidden @ X2 @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.90/1.09          | ~ (v1_relat_1 @ X1)
% 0.90/1.09          | ~ (v1_relat_1 @ X0)
% 0.90/1.09          | (r2_hidden @ (k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 0.90/1.09             (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.90/1.09          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.90/1.09          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['82', '84'])).
% 0.90/1.09  thf('86', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]:
% 0.90/1.09         (~ (r2_hidden @ X1 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ sk_B_1)))
% 0.90/1.09          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ sk_A))
% 0.90/1.09          | ~ (v1_funct_1 @ (k5_relat_1 @ X0 @ sk_A))
% 0.90/1.09          | (r2_hidden @ (k1_funct_1 @ (k5_relat_1 @ X0 @ sk_A) @ X1) @ 
% 0.90/1.09             (k2_relat_1 @ (k5_relat_1 @ X0 @ sk_A)))
% 0.90/1.09          | ~ (v1_relat_1 @ sk_A)
% 0.90/1.09          | ~ (v1_relat_1 @ X0))),
% 0.90/1.09      inference('sup-', [status(thm)], ['81', '85'])).
% 0.90/1.09  thf('87', plain, ((v1_relat_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('88', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]:
% 0.90/1.09         (~ (r2_hidden @ X1 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ sk_B_1)))
% 0.90/1.09          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ sk_A))
% 0.90/1.09          | ~ (v1_funct_1 @ (k5_relat_1 @ X0 @ sk_A))
% 0.90/1.09          | (r2_hidden @ (k1_funct_1 @ (k5_relat_1 @ X0 @ sk_A) @ X1) @ 
% 0.90/1.09             (k2_relat_1 @ (k5_relat_1 @ X0 @ sk_A)))
% 0.90/1.09          | ~ (v1_relat_1 @ X0))),
% 0.90/1.09      inference('demod', [status(thm)], ['86', '87'])).
% 0.90/1.09  thf('89', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.90/1.09          | ~ (v1_relat_1 @ sk_B_1)
% 0.90/1.09          | ~ (v1_relat_1 @ sk_B_1)
% 0.90/1.09          | (r2_hidden @ (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0) @ 
% 0.90/1.09             (k2_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.90/1.09          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.90/1.09          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['80', '88'])).
% 0.90/1.09  thf('90', plain, ((v1_relat_1 @ sk_B_1)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('91', plain, ((v1_relat_1 @ sk_B_1)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('92', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.90/1.09          | (r2_hidden @ (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0) @ 
% 0.90/1.09             (k2_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.90/1.09          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.90/1.09          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.90/1.09      inference('demod', [status(thm)], ['89', '90', '91'])).
% 0.90/1.09  thf('93', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (~ (v1_funct_1 @ sk_A)
% 0.90/1.09          | ~ (v1_relat_1 @ sk_A)
% 0.90/1.09          | ~ (v1_relat_1 @ sk_B_1)
% 0.90/1.09          | ~ (v1_funct_1 @ sk_B_1)
% 0.90/1.09          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.90/1.09          | (r2_hidden @ (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0) @ 
% 0.90/1.09             (k2_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.90/1.09          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['79', '92'])).
% 0.90/1.09  thf('94', plain, ((v1_funct_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('95', plain, ((v1_relat_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('96', plain, ((v1_relat_1 @ sk_B_1)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('97', plain, ((v1_funct_1 @ sk_B_1)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('98', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.90/1.09          | (r2_hidden @ (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0) @ 
% 0.90/1.09             (k2_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.90/1.09          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1)))),
% 0.90/1.09      inference('demod', [status(thm)], ['93', '94', '95', '96', '97'])).
% 0.90/1.09  thf('99', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (~ (v1_relat_1 @ sk_A)
% 0.90/1.09          | ~ (v1_relat_1 @ sk_B_1)
% 0.90/1.09          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.90/1.09          | (r2_hidden @ (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0) @ 
% 0.90/1.09             (k2_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))))),
% 0.90/1.09      inference('sup-', [status(thm)], ['78', '98'])).
% 0.90/1.09  thf('100', plain, ((v1_relat_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('101', plain, ((v1_relat_1 @ sk_B_1)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('102', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.90/1.09          | (r2_hidden @ (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0) @ 
% 0.90/1.09             (k2_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))))),
% 0.90/1.09      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.90/1.09  thf('103', plain,
% 0.90/1.09      ((r2_hidden @ 
% 0.90/1.09        (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.90/1.09         (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)) @ 
% 0.90/1.09        (k2_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['77', '102'])).
% 0.90/1.09  thf('104', plain,
% 0.90/1.09      (((r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.90/1.09         (k2_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.90/1.09        | ~ (v1_relat_1 @ sk_A)
% 0.90/1.09        | ~ (v1_funct_1 @ sk_A))),
% 0.90/1.09      inference('sup+', [status(thm)], ['76', '103'])).
% 0.90/1.09  thf('105', plain, ((v1_relat_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('106', plain, ((v1_funct_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('107', plain,
% 0.90/1.09      ((r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.90/1.09        (k2_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.90/1.09      inference('demod', [status(thm)], ['104', '105', '106'])).
% 0.90/1.09  thf('108', plain,
% 0.90/1.09      (![X9 : $i, X12 : $i]:
% 0.90/1.09         (~ (v1_relat_1 @ X9)
% 0.90/1.09          | ~ (v1_funct_1 @ X9)
% 0.90/1.09          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 0.90/1.09          | ((X12) = (k1_funct_1 @ X9 @ (sk_D_1 @ X12 @ X9))))),
% 0.90/1.09      inference('simplify', [status(thm)], ['28'])).
% 0.90/1.09  thf('109', plain,
% 0.90/1.09      ((((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.90/1.09          = (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.90/1.09             (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.90/1.09              (k5_relat_1 @ sk_B_1 @ sk_A))))
% 0.90/1.09        | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.90/1.09        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['107', '108'])).
% 0.90/1.09  thf('110', plain,
% 0.90/1.09      ((~ (v1_funct_1 @ sk_A)
% 0.90/1.09        | ~ (v1_relat_1 @ sk_A)
% 0.90/1.09        | ~ (v1_relat_1 @ sk_B_1)
% 0.90/1.09        | ~ (v1_funct_1 @ sk_B_1)
% 0.90/1.09        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.90/1.09        | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.90/1.09            = (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.90/1.09               (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.90/1.09                (k5_relat_1 @ sk_B_1 @ sk_A)))))),
% 0.90/1.09      inference('sup-', [status(thm)], ['52', '109'])).
% 0.90/1.09  thf('111', plain, ((v1_funct_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('112', plain, ((v1_relat_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('113', plain, ((v1_relat_1 @ sk_B_1)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('114', plain, ((v1_funct_1 @ sk_B_1)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('115', plain,
% 0.90/1.09      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.90/1.09        | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.90/1.09            = (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.90/1.09               (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.90/1.09                (k5_relat_1 @ sk_B_1 @ sk_A)))))),
% 0.90/1.09      inference('demod', [status(thm)], ['110', '111', '112', '113', '114'])).
% 0.90/1.09  thf('116', plain,
% 0.90/1.09      ((~ (v1_relat_1 @ sk_A)
% 0.90/1.09        | ~ (v1_relat_1 @ sk_B_1)
% 0.90/1.09        | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.90/1.09            = (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.90/1.09               (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.90/1.09                (k5_relat_1 @ sk_B_1 @ sk_A)))))),
% 0.90/1.09      inference('sup-', [status(thm)], ['51', '115'])).
% 0.90/1.09  thf('117', plain, ((v1_relat_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('118', plain, ((v1_relat_1 @ sk_B_1)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('119', plain,
% 0.90/1.09      (((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.90/1.09         = (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.90/1.09            (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.90/1.09             (k5_relat_1 @ sk_B_1 @ sk_A))))),
% 0.90/1.09      inference('demod', [status(thm)], ['116', '117', '118'])).
% 0.90/1.09  thf('120', plain,
% 0.90/1.09      (![X6 : $i, X7 : $i]:
% 0.90/1.09         (~ (v1_relat_1 @ X6)
% 0.90/1.09          | ((k1_relat_1 @ (k5_relat_1 @ X7 @ X6))
% 0.90/1.09              = (k10_relat_1 @ X7 @ (k1_relat_1 @ X6)))
% 0.90/1.09          | ~ (v1_relat_1 @ X7))),
% 0.90/1.09      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.90/1.09  thf('121', plain,
% 0.90/1.09      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.90/1.09         (~ (v2_funct_1 @ X15)
% 0.90/1.09          | ~ (r2_hidden @ X16 @ (k1_relat_1 @ X15))
% 0.90/1.09          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ X15))
% 0.90/1.09          | ((k1_funct_1 @ X15 @ X16) != (k1_funct_1 @ X15 @ X17))
% 0.90/1.09          | ((X16) = (X17))
% 0.90/1.09          | ~ (v1_funct_1 @ X15)
% 0.90/1.09          | ~ (v1_relat_1 @ X15))),
% 0.90/1.09      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.90/1.09  thf('122', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.90/1.09         (~ (r2_hidden @ X2 @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.90/1.09          | ~ (v1_relat_1 @ X1)
% 0.90/1.09          | ~ (v1_relat_1 @ X0)
% 0.90/1.09          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.90/1.09          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.90/1.09          | ((X2) = (X3))
% 0.90/1.09          | ((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.90/1.09              != (k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X3))
% 0.90/1.09          | ~ (r2_hidden @ X3 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.90/1.09          | ~ (v2_funct_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['120', '121'])).
% 0.90/1.09  thf('123', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.90/1.09            != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.90/1.09          | ~ (v2_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.90/1.09          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.90/1.09          | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.90/1.09              (k5_relat_1 @ sk_B_1 @ sk_A)) = (X0))
% 0.90/1.09          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.90/1.09          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.90/1.09          | ~ (v1_relat_1 @ sk_A)
% 0.90/1.09          | ~ (v1_relat_1 @ sk_B_1)
% 0.90/1.09          | ~ (r2_hidden @ 
% 0.90/1.09               (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.90/1.09                (k5_relat_1 @ sk_B_1 @ sk_A)) @ 
% 0.90/1.09               (k10_relat_1 @ sk_B_1 @ (k1_relat_1 @ sk_A))))),
% 0.90/1.09      inference('sup-', [status(thm)], ['119', '122'])).
% 0.90/1.09  thf('124', plain, ((v2_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('125', plain, ((v1_relat_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('126', plain, ((v1_relat_1 @ sk_B_1)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('127', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('128', plain,
% 0.90/1.09      (![X6 : $i, X7 : $i]:
% 0.90/1.09         (~ (v1_relat_1 @ X6)
% 0.90/1.09          | ((k1_relat_1 @ (k5_relat_1 @ X7 @ X6))
% 0.90/1.09              = (k10_relat_1 @ X7 @ (k1_relat_1 @ X6)))
% 0.90/1.09          | ~ (v1_relat_1 @ X7))),
% 0.90/1.09      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.90/1.09  thf('129', plain,
% 0.90/1.09      (![X3 : $i, X4 : $i]:
% 0.90/1.09         (~ (v1_relat_1 @ X3)
% 0.90/1.09          | ~ (v1_relat_1 @ X4)
% 0.90/1.09          | (v1_relat_1 @ (k5_relat_1 @ X3 @ X4)))),
% 0.90/1.09      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.90/1.09  thf('130', plain,
% 0.90/1.09      (![X18 : $i, X19 : $i]:
% 0.90/1.09         (~ (v1_funct_1 @ X18)
% 0.90/1.09          | ~ (v1_relat_1 @ X18)
% 0.90/1.09          | ~ (v1_relat_1 @ X19)
% 0.90/1.09          | ~ (v1_funct_1 @ X19)
% 0.90/1.09          | (v1_funct_1 @ (k5_relat_1 @ X18 @ X19)))),
% 0.90/1.09      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.90/1.09  thf('131', plain,
% 0.90/1.09      ((r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.90/1.09        (k2_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.90/1.09      inference('demod', [status(thm)], ['104', '105', '106'])).
% 0.90/1.09  thf('132', plain,
% 0.90/1.09      (![X9 : $i, X12 : $i]:
% 0.90/1.09         (~ (v1_relat_1 @ X9)
% 0.90/1.09          | ~ (v1_funct_1 @ X9)
% 0.90/1.09          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 0.90/1.09          | (r2_hidden @ (sk_D_1 @ X12 @ X9) @ (k1_relat_1 @ X9)))),
% 0.90/1.09      inference('simplify', [status(thm)], ['35'])).
% 0.90/1.09  thf('133', plain,
% 0.90/1.09      (((r2_hidden @ 
% 0.90/1.09         (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.90/1.09          (k5_relat_1 @ sk_B_1 @ sk_A)) @ 
% 0.90/1.09         (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.90/1.09        | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.90/1.09        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['131', '132'])).
% 0.90/1.09  thf('134', plain,
% 0.90/1.09      ((~ (v1_funct_1 @ sk_A)
% 0.90/1.09        | ~ (v1_relat_1 @ sk_A)
% 0.90/1.09        | ~ (v1_relat_1 @ sk_B_1)
% 0.90/1.09        | ~ (v1_funct_1 @ sk_B_1)
% 0.90/1.09        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.90/1.09        | (r2_hidden @ 
% 0.90/1.09           (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.90/1.09            (k5_relat_1 @ sk_B_1 @ sk_A)) @ 
% 0.90/1.09           (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))))),
% 0.90/1.09      inference('sup-', [status(thm)], ['130', '133'])).
% 0.90/1.09  thf('135', plain, ((v1_funct_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('136', plain, ((v1_relat_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('137', plain, ((v1_relat_1 @ sk_B_1)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('138', plain, ((v1_funct_1 @ sk_B_1)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('139', plain,
% 0.90/1.09      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.90/1.09        | (r2_hidden @ 
% 0.90/1.09           (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.90/1.09            (k5_relat_1 @ sk_B_1 @ sk_A)) @ 
% 0.90/1.09           (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))))),
% 0.90/1.09      inference('demod', [status(thm)], ['134', '135', '136', '137', '138'])).
% 0.90/1.09  thf('140', plain,
% 0.90/1.09      ((~ (v1_relat_1 @ sk_A)
% 0.90/1.09        | ~ (v1_relat_1 @ sk_B_1)
% 0.90/1.09        | (r2_hidden @ 
% 0.90/1.09           (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.90/1.09            (k5_relat_1 @ sk_B_1 @ sk_A)) @ 
% 0.90/1.09           (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))))),
% 0.90/1.09      inference('sup-', [status(thm)], ['129', '139'])).
% 0.90/1.09  thf('141', plain, ((v1_relat_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('142', plain, ((v1_relat_1 @ sk_B_1)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('143', plain,
% 0.90/1.09      ((r2_hidden @ 
% 0.90/1.09        (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.90/1.09         (k5_relat_1 @ sk_B_1 @ sk_A)) @ 
% 0.90/1.09        (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.90/1.09      inference('demod', [status(thm)], ['140', '141', '142'])).
% 0.90/1.09  thf('144', plain,
% 0.90/1.09      (((r2_hidden @ 
% 0.90/1.09         (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.90/1.09          (k5_relat_1 @ sk_B_1 @ sk_A)) @ 
% 0.90/1.09         (k10_relat_1 @ sk_B_1 @ (k1_relat_1 @ sk_A)))
% 0.90/1.09        | ~ (v1_relat_1 @ sk_B_1)
% 0.90/1.09        | ~ (v1_relat_1 @ sk_A))),
% 0.90/1.09      inference('sup+', [status(thm)], ['128', '143'])).
% 0.90/1.09  thf('145', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('146', plain, ((v1_relat_1 @ sk_B_1)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('147', plain, ((v1_relat_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('148', plain,
% 0.90/1.09      ((r2_hidden @ 
% 0.90/1.09        (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.90/1.09         (k5_relat_1 @ sk_B_1 @ sk_A)) @ 
% 0.90/1.09        (k10_relat_1 @ sk_B_1 @ (k2_relat_1 @ sk_B_1)))),
% 0.90/1.09      inference('demod', [status(thm)], ['144', '145', '146', '147'])).
% 0.90/1.09  thf('149', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.90/1.09            != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.90/1.09          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.90/1.09          | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.90/1.09              (k5_relat_1 @ sk_B_1 @ sk_A)) = (X0))
% 0.90/1.09          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.90/1.09          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.90/1.09      inference('demod', [status(thm)],
% 0.90/1.09                ['123', '124', '125', '126', '127', '148'])).
% 0.90/1.09  thf('150', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (~ (v1_funct_1 @ sk_A)
% 0.90/1.09          | ~ (v1_relat_1 @ sk_A)
% 0.90/1.09          | ~ (v1_relat_1 @ sk_B_1)
% 0.90/1.09          | ~ (v1_funct_1 @ sk_B_1)
% 0.90/1.09          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.90/1.09          | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.90/1.09              (k5_relat_1 @ sk_B_1 @ sk_A)) = (X0))
% 0.90/1.09          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.90/1.09          | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.90/1.09              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['50', '149'])).
% 0.90/1.09  thf('151', plain, ((v1_funct_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('152', plain, ((v1_relat_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('153', plain, ((v1_relat_1 @ sk_B_1)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('154', plain, ((v1_funct_1 @ sk_B_1)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('155', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.90/1.09          | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.90/1.09              (k5_relat_1 @ sk_B_1 @ sk_A)) = (X0))
% 0.90/1.09          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.90/1.09          | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.90/1.09              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)))),
% 0.90/1.09      inference('demod', [status(thm)], ['150', '151', '152', '153', '154'])).
% 0.90/1.09  thf('156', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (~ (v1_relat_1 @ sk_A)
% 0.90/1.09          | ~ (v1_relat_1 @ sk_B_1)
% 0.90/1.09          | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.90/1.09              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.90/1.09          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.90/1.09          | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.90/1.09              (k5_relat_1 @ sk_B_1 @ sk_A)) = (X0)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['49', '155'])).
% 0.90/1.09  thf('157', plain, ((v1_relat_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('158', plain, ((v1_relat_1 @ sk_B_1)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('159', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.90/1.09            != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.90/1.09          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.90/1.09          | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.90/1.09              (k5_relat_1 @ sk_B_1 @ sk_A)) = (X0)))),
% 0.90/1.09      inference('demod', [status(thm)], ['156', '157', '158'])).
% 0.90/1.09  thf('160', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (~ (r2_hidden @ X0 @ (k10_relat_1 @ sk_B_1 @ (k1_relat_1 @ sk_A)))
% 0.90/1.09          | ~ (v1_relat_1 @ sk_B_1)
% 0.90/1.09          | ~ (v1_relat_1 @ sk_A)
% 0.90/1.09          | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.90/1.09              (k5_relat_1 @ sk_B_1 @ sk_A)) = (X0))
% 0.90/1.09          | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.90/1.09              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['48', '159'])).
% 0.90/1.09  thf('161', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('162', plain, ((v1_relat_1 @ sk_B_1)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('163', plain, ((v1_relat_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('164', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (~ (r2_hidden @ X0 @ (k10_relat_1 @ sk_B_1 @ (k2_relat_1 @ sk_B_1)))
% 0.90/1.09          | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.90/1.09              (k5_relat_1 @ sk_B_1 @ sk_A)) = (X0))
% 0.90/1.09          | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.90/1.09              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)))),
% 0.90/1.09      inference('demod', [status(thm)], ['160', '161', '162', '163'])).
% 0.90/1.09  thf('165', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.90/1.09          | ~ (v1_relat_1 @ sk_B_1)
% 0.90/1.09          | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.90/1.09              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.90/1.09          | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.90/1.09              (k5_relat_1 @ sk_B_1 @ sk_A)) = (X0)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['47', '164'])).
% 0.90/1.09  thf('166', plain, ((v1_relat_1 @ sk_B_1)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('167', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.90/1.09          | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.90/1.09              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.90/1.09          | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.90/1.09              (k5_relat_1 @ sk_B_1 @ sk_A)) = (X0)))),
% 0.90/1.09      inference('demod', [status(thm)], ['165', '166'])).
% 0.90/1.09  thf('168', plain,
% 0.90/1.09      ((((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.90/1.09          != (k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A)))
% 0.90/1.09        | ~ (v1_relat_1 @ sk_A)
% 0.90/1.09        | ~ (v1_funct_1 @ sk_A)
% 0.90/1.09        | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.90/1.09            (k5_relat_1 @ sk_B_1 @ sk_A)) = (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1))
% 0.90/1.09        | ~ (r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1) @ 
% 0.90/1.09             (k1_relat_1 @ sk_B_1)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['46', '167'])).
% 0.90/1.09  thf('169', plain,
% 0.90/1.09      (![X15 : $i]:
% 0.90/1.09         (((k1_funct_1 @ X15 @ (sk_B @ X15))
% 0.90/1.09            = (k1_funct_1 @ X15 @ (sk_C_1 @ X15)))
% 0.90/1.09          | (v2_funct_1 @ X15)
% 0.90/1.09          | ~ (v1_funct_1 @ X15)
% 0.90/1.09          | ~ (v1_relat_1 @ X15))),
% 0.90/1.09      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.90/1.09  thf('170', plain, ((r2_hidden @ (sk_C_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 0.90/1.09      inference('clc', [status(thm)], ['25', '26'])).
% 0.90/1.09  thf('171', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('172', plain,
% 0.90/1.09      (![X9 : $i, X14 : $i]:
% 0.90/1.09         (~ (v1_relat_1 @ X9)
% 0.90/1.09          | ~ (v1_funct_1 @ X9)
% 0.90/1.09          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X9))
% 0.90/1.09          | (r2_hidden @ (k1_funct_1 @ X9 @ X14) @ (k2_relat_1 @ X9)))),
% 0.90/1.09      inference('simplify', [status(thm)], ['83'])).
% 0.90/1.09  thf('173', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B_1))
% 0.90/1.09          | (r2_hidden @ (k1_funct_1 @ sk_A @ X0) @ (k2_relat_1 @ sk_A))
% 0.90/1.09          | ~ (v1_funct_1 @ sk_A)
% 0.90/1.09          | ~ (v1_relat_1 @ sk_A))),
% 0.90/1.09      inference('sup-', [status(thm)], ['171', '172'])).
% 0.90/1.09  thf('174', plain, ((v1_funct_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('175', plain, ((v1_relat_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('176', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B_1))
% 0.90/1.09          | (r2_hidden @ (k1_funct_1 @ sk_A @ X0) @ (k2_relat_1 @ sk_A)))),
% 0.90/1.09      inference('demod', [status(thm)], ['173', '174', '175'])).
% 0.90/1.09  thf('177', plain,
% 0.90/1.09      ((r2_hidden @ (k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A)) @ (k2_relat_1 @ sk_A))),
% 0.90/1.09      inference('sup-', [status(thm)], ['170', '176'])).
% 0.90/1.09  thf('178', plain,
% 0.90/1.09      (![X9 : $i, X12 : $i]:
% 0.90/1.09         (~ (v1_relat_1 @ X9)
% 0.90/1.09          | ~ (v1_funct_1 @ X9)
% 0.90/1.09          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 0.90/1.09          | ((X12) = (k1_funct_1 @ X9 @ (sk_D_1 @ X12 @ X9))))),
% 0.90/1.09      inference('simplify', [status(thm)], ['28'])).
% 0.90/1.09  thf('179', plain,
% 0.90/1.09      ((((k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A))
% 0.90/1.09          = (k1_funct_1 @ sk_A @ 
% 0.90/1.09             (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A)) @ sk_A)))
% 0.90/1.09        | ~ (v1_funct_1 @ sk_A)
% 0.90/1.09        | ~ (v1_relat_1 @ sk_A))),
% 0.90/1.09      inference('sup-', [status(thm)], ['177', '178'])).
% 0.90/1.09  thf('180', plain, ((v1_funct_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('181', plain, ((v1_relat_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('182', plain,
% 0.90/1.09      (((k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A))
% 0.90/1.09         = (k1_funct_1 @ sk_A @ 
% 0.90/1.09            (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A)) @ sk_A)))),
% 0.90/1.09      inference('demod', [status(thm)], ['179', '180', '181'])).
% 0.90/1.09  thf('183', plain,
% 0.90/1.09      ((((k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A))
% 0.90/1.09          = (k1_funct_1 @ sk_A @ 
% 0.90/1.09             (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A)))
% 0.90/1.09        | ~ (v1_relat_1 @ sk_A)
% 0.90/1.09        | ~ (v1_funct_1 @ sk_A)
% 0.90/1.09        | (v2_funct_1 @ sk_A))),
% 0.90/1.09      inference('sup+', [status(thm)], ['169', '182'])).
% 0.90/1.09  thf('184', plain, ((r2_hidden @ (sk_B @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 0.90/1.09      inference('clc', [status(thm)], ['58', '59'])).
% 0.90/1.09  thf('185', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B_1))
% 0.90/1.09          | (r2_hidden @ (k1_funct_1 @ sk_A @ X0) @ (k2_relat_1 @ sk_A)))),
% 0.90/1.09      inference('demod', [status(thm)], ['173', '174', '175'])).
% 0.90/1.09  thf('186', plain,
% 0.90/1.09      ((r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ (k2_relat_1 @ sk_A))),
% 0.90/1.09      inference('sup-', [status(thm)], ['184', '185'])).
% 0.90/1.09  thf('187', plain,
% 0.90/1.09      (![X9 : $i, X12 : $i]:
% 0.90/1.09         (~ (v1_relat_1 @ X9)
% 0.90/1.09          | ~ (v1_funct_1 @ X9)
% 0.90/1.09          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 0.90/1.09          | ((X12) = (k1_funct_1 @ X9 @ (sk_D_1 @ X12 @ X9))))),
% 0.90/1.09      inference('simplify', [status(thm)], ['28'])).
% 0.90/1.09  thf('188', plain,
% 0.90/1.09      ((((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.90/1.09          = (k1_funct_1 @ sk_A @ 
% 0.90/1.09             (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A)))
% 0.90/1.09        | ~ (v1_funct_1 @ sk_A)
% 0.90/1.09        | ~ (v1_relat_1 @ sk_A))),
% 0.90/1.09      inference('sup-', [status(thm)], ['186', '187'])).
% 0.90/1.09  thf('189', plain, ((v1_funct_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('190', plain, ((v1_relat_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('191', plain,
% 0.90/1.09      (((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.90/1.09         = (k1_funct_1 @ sk_A @ 
% 0.90/1.09            (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A)))),
% 0.90/1.09      inference('demod', [status(thm)], ['188', '189', '190'])).
% 0.90/1.09  thf('192', plain, ((v1_relat_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('193', plain, ((v1_funct_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('194', plain,
% 0.90/1.09      ((((k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A))
% 0.90/1.09          = (k1_funct_1 @ sk_A @ (sk_B @ sk_A)))
% 0.90/1.09        | (v2_funct_1 @ sk_A))),
% 0.90/1.09      inference('demod', [status(thm)], ['183', '191', '192', '193'])).
% 0.90/1.09  thf('195', plain, (~ (v2_funct_1 @ sk_A)),
% 0.90/1.09      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.90/1.09  thf('196', plain,
% 0.90/1.09      (((k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A))
% 0.90/1.09         = (k1_funct_1 @ sk_A @ (sk_B @ sk_A)))),
% 0.90/1.09      inference('clc', [status(thm)], ['194', '195'])).
% 0.90/1.09  thf('197', plain, ((v1_relat_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('198', plain, ((v1_funct_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('199', plain,
% 0.90/1.09      ((r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1) @ (k1_relat_1 @ sk_B_1))),
% 0.90/1.09      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.90/1.09  thf('200', plain,
% 0.90/1.09      ((((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.90/1.09          != (k1_funct_1 @ sk_A @ (sk_B @ sk_A)))
% 0.90/1.09        | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.90/1.09            (k5_relat_1 @ sk_B_1 @ sk_A)) = (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1)))),
% 0.90/1.09      inference('demod', [status(thm)], ['168', '196', '197', '198', '199'])).
% 0.90/1.09  thf('201', plain,
% 0.90/1.09      (((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.90/1.09         (k5_relat_1 @ sk_B_1 @ sk_A)) = (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1))),
% 0.90/1.09      inference('simplify', [status(thm)], ['200'])).
% 0.90/1.09  thf('202', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ X0) @ 
% 0.90/1.09            (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1))
% 0.90/1.09            = (k1_funct_1 @ X0 @ (sk_B @ sk_A)))
% 0.90/1.09          | ~ (v1_funct_1 @ X0)
% 0.90/1.09          | ~ (v1_relat_1 @ X0))),
% 0.90/1.09      inference('demod', [status(thm)], ['67', '68', '69', '75'])).
% 0.90/1.09  thf('203', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.90/1.09          | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.90/1.09              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.90/1.09          | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.90/1.09              (k5_relat_1 @ sk_B_1 @ sk_A)) = (X0)))),
% 0.90/1.09      inference('demod', [status(thm)], ['165', '166'])).
% 0.90/1.09  thf('204', plain,
% 0.90/1.09      ((((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.90/1.09          != (k1_funct_1 @ sk_A @ (sk_B @ sk_A)))
% 0.90/1.09        | ~ (v1_relat_1 @ sk_A)
% 0.90/1.09        | ~ (v1_funct_1 @ sk_A)
% 0.90/1.09        | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.90/1.09            (k5_relat_1 @ sk_B_1 @ sk_A)) = (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1))
% 0.90/1.09        | ~ (r2_hidden @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) @ 
% 0.90/1.09             (k1_relat_1 @ sk_B_1)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['202', '203'])).
% 0.90/1.09  thf('205', plain, ((v1_relat_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('206', plain, ((v1_funct_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('207', plain,
% 0.90/1.09      ((r2_hidden @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) @ (k1_relat_1 @ sk_B_1))),
% 0.90/1.09      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.90/1.09  thf('208', plain,
% 0.90/1.09      ((((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.90/1.09          != (k1_funct_1 @ sk_A @ (sk_B @ sk_A)))
% 0.90/1.09        | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.90/1.09            (k5_relat_1 @ sk_B_1 @ sk_A)) = (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)))),
% 0.90/1.09      inference('demod', [status(thm)], ['204', '205', '206', '207'])).
% 0.90/1.09  thf('209', plain,
% 0.90/1.09      (((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.90/1.09         (k5_relat_1 @ sk_B_1 @ sk_A)) = (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1))),
% 0.90/1.09      inference('simplify', [status(thm)], ['208'])).
% 0.90/1.09  thf('210', plain,
% 0.90/1.09      (((sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1) = (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1))),
% 0.90/1.09      inference('sup+', [status(thm)], ['201', '209'])).
% 0.90/1.09  thf('211', plain,
% 0.90/1.09      (((sk_C_1 @ sk_A)
% 0.90/1.09         = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)))),
% 0.90/1.09      inference('demod', [status(thm)], ['33', '210'])).
% 0.90/1.09  thf('212', plain,
% 0.90/1.09      (((sk_B @ sk_A)
% 0.90/1.09         = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)))),
% 0.90/1.09      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.90/1.09  thf('213', plain, (((sk_B @ sk_A) = (sk_C_1 @ sk_A))),
% 0.90/1.09      inference('sup+', [status(thm)], ['211', '212'])).
% 0.90/1.09  thf('214', plain,
% 0.90/1.09      (![X15 : $i]:
% 0.90/1.09         (((sk_B @ X15) != (sk_C_1 @ X15))
% 0.90/1.09          | (v2_funct_1 @ X15)
% 0.90/1.09          | ~ (v1_funct_1 @ X15)
% 0.90/1.09          | ~ (v1_relat_1 @ X15))),
% 0.90/1.09      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.90/1.09  thf('215', plain,
% 0.90/1.09      ((((sk_B @ sk_A) != (sk_B @ sk_A))
% 0.90/1.09        | ~ (v1_relat_1 @ sk_A)
% 0.90/1.09        | ~ (v1_funct_1 @ sk_A)
% 0.90/1.09        | (v2_funct_1 @ sk_A))),
% 0.90/1.09      inference('sup-', [status(thm)], ['213', '214'])).
% 0.90/1.09  thf('216', plain, ((v1_relat_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('217', plain, ((v1_funct_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('218', plain, ((((sk_B @ sk_A) != (sk_B @ sk_A)) | (v2_funct_1 @ sk_A))),
% 0.90/1.09      inference('demod', [status(thm)], ['215', '216', '217'])).
% 0.90/1.09  thf('219', plain, ((v2_funct_1 @ sk_A)),
% 0.90/1.09      inference('simplify', [status(thm)], ['218'])).
% 0.90/1.09  thf('220', plain, ($false), inference('demod', [status(thm)], ['19', '219'])).
% 0.90/1.09  
% 0.90/1.09  % SZS output end Refutation
% 0.90/1.09  
% 0.90/1.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
