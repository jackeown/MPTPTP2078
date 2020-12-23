%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RDNsYEvMQ8

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:13 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 911 expanded)
%              Number of leaves         :   25 ( 257 expanded)
%              Depth                    :   26
%              Number of atoms          : 1441 (11888 expanded)
%              Number of equality atoms :   72 ( 542 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

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
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ( v2_funct_1 @ X22 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X22 ) @ ( k1_relat_1 @ X23 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X22 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
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
    ! [X14: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X14 ) @ ( k1_relat_1 @ X14 ) )
      | ( v2_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('28',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X7 @ X5 ) @ X7 ) @ X5 )
      | ( X6
       != ( k2_relat_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('29',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X7 @ X5 ) @ X7 ) @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k2_relat_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) @ ( sk_C_1 @ sk_A ) ) @ sk_B_1 ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X24 @ X26 ) @ X25 )
      | ( X26
        = ( k1_funct_1 @ X25 @ X24 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( ( sk_C_1 @ sk_A )
      = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( sk_C_1 @ sk_A )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) @ ( sk_C_1 @ sk_A ) ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['27','29'])).

thf('37',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X24 @ X26 ) @ X25 )
      | ( r2_hidden @ X24 @ ( k1_relat_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('43',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('44',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X13 ) @ ( k1_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ sk_A ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ sk_A ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      = ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['48','49'])).

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

thf('51',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X19 @ X20 ) @ X21 )
        = ( k1_funct_1 @ X20 @ ( k1_funct_1 @ X19 @ X21 ) ) )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ ( k5_relat_1 @ X19 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
        = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
        = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['52','53','54','55','56'])).

thf('58',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) )
    = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['41','57'])).

thf('59',plain,
    ( ( sk_C_1 @ sk_A )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('60',plain,(
    ! [X14: $i] :
      ( ( ( k1_funct_1 @ X14 @ ( sk_B @ X14 ) )
        = ( k1_funct_1 @ X14 @ ( sk_C_1 @ X14 ) ) )
      | ( v2_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('61',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('62',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X24 @ ( k1_relat_1 @ X25 ) )
      | ( X26
       != ( k1_funct_1 @ X25 @ X24 ) )
      | ( r2_hidden @ ( k4_tarski @ X24 @ X26 ) @ X25 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('64',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_funct_1 @ X25 )
      | ( r2_hidden @ ( k4_tarski @ X24 @ ( k1_funct_1 @ X25 @ X24 ) ) @ X25 )
      | ~ ( r2_hidden @ X24 @ ( k1_relat_1 @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_A @ X0 ) ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','64'])).

thf('66',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_A @ X0 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_A ) @ ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) ) ) @ sk_A ),
    inference('sup-',[status(thm)],['61','68'])).

thf('70',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_A ) @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['60','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_A ) @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) ) @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','18'])).

thf('75',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_A ) @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) ) @ sk_A ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X24 @ X26 ) @ X25 )
      | ( X26
        = ( k1_funct_1 @ X25 @ X24 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('77',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
      = ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
    = ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) )
    = ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59','80'])).

thf('82',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X14: $i] :
      ( ( r2_hidden @ ( sk_B @ X14 ) @ ( k1_relat_1 @ X14 ) )
      | ( v2_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('84',plain,
    ( ( r2_hidden @ ( sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( r2_hidden @ ( sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','18'])).

thf('89',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X7 @ X5 ) @ X7 ) @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k2_relat_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('91',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( sk_B @ sk_A ) ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X24 @ X26 ) @ X25 )
      | ( r2_hidden @ X24 @ ( k1_relat_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('93',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
        = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['52','53','54','55','56'])).

thf('98',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) )
    = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( sk_B @ sk_A ) ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['89','90'])).

thf('100',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X24 @ X26 ) @ X25 )
      | ( X26
        = ( k1_funct_1 @ X25 @ X24 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('101',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( ( sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( sk_B @ sk_A )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) )
    = ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','104'])).

thf(fc2_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) )).

thf('106',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('107',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('108',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('109',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X14 ) )
      | ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X14 ) )
      | ( ( k1_funct_1 @ X14 @ X15 )
       != ( k1_funct_1 @ X14 @ X16 ) )
      | ( X15 = X16 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('112',plain,(
    v2_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X1 )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ( X1 = X0 )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['107','113'])).

thf('115',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X1 )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ( X1 = X0 )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['106','117'])).

thf('119',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['118','119','120','121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 )
        = X0 )
      | ~ ( r2_hidden @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['105','123'])).

thf('125',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
     != ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 )
      = ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) )
    | ~ ( r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['81','126'])).

thf('128',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('129',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
     != ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 )
      = ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,
    ( ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 )
    = ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,
    ( ( sk_C_1 @ sk_A )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['35','130'])).

thf('132',plain,
    ( ( sk_B @ sk_A )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('133',plain,
    ( ( sk_B @ sk_A )
    = ( sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X14: $i] :
      ( ( ( sk_B @ X14 )
       != ( sk_C_1 @ X14 ) )
      | ( v2_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('135',plain,
    ( ( ( sk_B @ sk_A )
     != ( sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( ( sk_B @ sk_A )
     != ( sk_B @ sk_A ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['135','136','137'])).

thf('139',plain,(
    v2_funct_1 @ sk_A ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,(
    $false ),
    inference(demod,[status(thm)],['19','139'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RDNsYEvMQ8
% 0.15/0.35  % Computer   : n020.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 14:40:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.42/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.62  % Solved by: fo/fo7.sh
% 0.42/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.62  % done 141 iterations in 0.151s
% 0.42/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.62  % SZS output start Refutation
% 0.42/0.62  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.42/0.62  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.42/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.42/0.62  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.42/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.42/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.62  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.42/0.62  thf(sk_B_type, type, sk_B: $i > $i).
% 0.42/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.62  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.42/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.42/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.42/0.62  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.42/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.42/0.62  thf(t48_funct_1, conjecture,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.42/0.62       ( ![B:$i]:
% 0.42/0.62         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.42/0.62           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.42/0.62               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.42/0.62             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.42/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.62    (~( ![A:$i]:
% 0.42/0.62        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.42/0.62          ( ![B:$i]:
% 0.42/0.62            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.42/0.62              ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.42/0.62                  ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.42/0.62                ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ) )),
% 0.42/0.62    inference('cnf.neg', [status(esa)], [t48_funct_1])).
% 0.42/0.62  thf('0', plain, ((~ (v2_funct_1 @ sk_B_1) | ~ (v2_funct_1 @ sk_A))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('1', plain, ((~ (v2_funct_1 @ sk_A)) <= (~ ((v2_funct_1 @ sk_A)))),
% 0.42/0.62      inference('split', [status(esa)], ['0'])).
% 0.42/0.62  thf(d10_xboole_0, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.42/0.62  thf('2', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.42/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.42/0.62  thf('3', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.42/0.62      inference('simplify', [status(thm)], ['2'])).
% 0.42/0.62  thf('4', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(t47_funct_1, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.42/0.62       ( ![B:$i]:
% 0.42/0.62         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.42/0.62           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.42/0.62               ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) =>
% 0.42/0.62             ( v2_funct_1 @ B ) ) ) ) ))).
% 0.42/0.62  thf('5', plain,
% 0.42/0.62      (![X22 : $i, X23 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ X22)
% 0.42/0.62          | ~ (v1_funct_1 @ X22)
% 0.42/0.62          | (v2_funct_1 @ X22)
% 0.42/0.62          | ~ (r1_tarski @ (k2_relat_1 @ X22) @ (k1_relat_1 @ X23))
% 0.42/0.62          | ~ (v2_funct_1 @ (k5_relat_1 @ X22 @ X23))
% 0.42/0.62          | ~ (v1_funct_1 @ X23)
% 0.42/0.62          | ~ (v1_relat_1 @ X23))),
% 0.42/0.62      inference('cnf', [status(esa)], [t47_funct_1])).
% 0.42/0.62  thf('6', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ sk_B_1))
% 0.42/0.62          | ~ (v1_relat_1 @ sk_A)
% 0.42/0.62          | ~ (v1_funct_1 @ sk_A)
% 0.42/0.62          | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_A))
% 0.42/0.62          | (v2_funct_1 @ X0)
% 0.42/0.62          | ~ (v1_funct_1 @ X0)
% 0.42/0.62          | ~ (v1_relat_1 @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['4', '5'])).
% 0.42/0.62  thf('7', plain, ((v1_relat_1 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('8', plain, ((v1_funct_1 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('9', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ sk_B_1))
% 0.42/0.62          | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_A))
% 0.42/0.62          | (v2_funct_1 @ X0)
% 0.42/0.62          | ~ (v1_funct_1 @ X0)
% 0.42/0.62          | ~ (v1_relat_1 @ X0))),
% 0.42/0.62      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.42/0.62  thf('10', plain,
% 0.42/0.62      ((~ (v1_relat_1 @ sk_B_1)
% 0.42/0.62        | ~ (v1_funct_1 @ sk_B_1)
% 0.42/0.62        | (v2_funct_1 @ sk_B_1)
% 0.42/0.62        | ~ (v2_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['3', '9'])).
% 0.42/0.62  thf('11', plain, ((v1_relat_1 @ sk_B_1)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('12', plain, ((v1_funct_1 @ sk_B_1)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('13', plain, ((v2_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('14', plain, ((v2_funct_1 @ sk_B_1)),
% 0.42/0.62      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.42/0.62  thf('15', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.42/0.62      inference('split', [status(esa)], ['0'])).
% 0.42/0.62  thf('16', plain, (((v2_funct_1 @ sk_B_1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['14', '15'])).
% 0.42/0.62  thf('17', plain, (~ ((v2_funct_1 @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.42/0.62      inference('split', [status(esa)], ['0'])).
% 0.42/0.62  thf('18', plain, (~ ((v2_funct_1 @ sk_A))),
% 0.42/0.62      inference('sat_resolution*', [status(thm)], ['16', '17'])).
% 0.42/0.62  thf('19', plain, (~ (v2_funct_1 @ sk_A)),
% 0.42/0.62      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.42/0.62  thf('20', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(d8_funct_1, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.42/0.62       ( ( v2_funct_1 @ A ) <=>
% 0.42/0.62         ( ![B:$i,C:$i]:
% 0.42/0.62           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.42/0.62               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.42/0.62               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.42/0.62             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.42/0.62  thf('21', plain,
% 0.42/0.62      (![X14 : $i]:
% 0.42/0.62         ((r2_hidden @ (sk_C_1 @ X14) @ (k1_relat_1 @ X14))
% 0.42/0.62          | (v2_funct_1 @ X14)
% 0.42/0.62          | ~ (v1_funct_1 @ X14)
% 0.42/0.62          | ~ (v1_relat_1 @ X14))),
% 0.42/0.62      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.42/0.62  thf('22', plain,
% 0.42/0.62      (((r2_hidden @ (sk_C_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))
% 0.42/0.62        | ~ (v1_relat_1 @ sk_A)
% 0.42/0.62        | ~ (v1_funct_1 @ sk_A)
% 0.42/0.62        | (v2_funct_1 @ sk_A))),
% 0.42/0.62      inference('sup+', [status(thm)], ['20', '21'])).
% 0.42/0.62  thf('23', plain, ((v1_relat_1 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('24', plain, ((v1_funct_1 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('25', plain,
% 0.42/0.62      (((r2_hidden @ (sk_C_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))
% 0.42/0.62        | (v2_funct_1 @ sk_A))),
% 0.42/0.62      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.42/0.62  thf('26', plain, (~ (v2_funct_1 @ sk_A)),
% 0.42/0.62      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.42/0.62  thf('27', plain, ((r2_hidden @ (sk_C_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 0.42/0.62      inference('clc', [status(thm)], ['25', '26'])).
% 0.42/0.62  thf(d5_relat_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.42/0.62       ( ![C:$i]:
% 0.42/0.62         ( ( r2_hidden @ C @ B ) <=>
% 0.42/0.62           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.42/0.62  thf('28', plain,
% 0.42/0.62      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X7 @ X6)
% 0.42/0.62          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X7 @ X5) @ X7) @ X5)
% 0.42/0.62          | ((X6) != (k2_relat_1 @ X5)))),
% 0.42/0.62      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.42/0.62  thf('29', plain,
% 0.42/0.62      (![X5 : $i, X7 : $i]:
% 0.42/0.62         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X7 @ X5) @ X7) @ X5)
% 0.42/0.62          | ~ (r2_hidden @ X7 @ (k2_relat_1 @ X5)))),
% 0.42/0.62      inference('simplify', [status(thm)], ['28'])).
% 0.42/0.62  thf('30', plain,
% 0.42/0.62      ((r2_hidden @ 
% 0.42/0.62        (k4_tarski @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1) @ (sk_C_1 @ sk_A)) @ 
% 0.42/0.62        sk_B_1)),
% 0.42/0.62      inference('sup-', [status(thm)], ['27', '29'])).
% 0.42/0.62  thf(t8_funct_1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i]:
% 0.42/0.62     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.42/0.62       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.42/0.62         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.42/0.62           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.42/0.62  thf('31', plain,
% 0.42/0.62      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.42/0.62         (~ (r2_hidden @ (k4_tarski @ X24 @ X26) @ X25)
% 0.42/0.62          | ((X26) = (k1_funct_1 @ X25 @ X24))
% 0.42/0.62          | ~ (v1_funct_1 @ X25)
% 0.42/0.62          | ~ (v1_relat_1 @ X25))),
% 0.42/0.62      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.42/0.62  thf('32', plain,
% 0.42/0.62      ((~ (v1_relat_1 @ sk_B_1)
% 0.42/0.62        | ~ (v1_funct_1 @ sk_B_1)
% 0.42/0.62        | ((sk_C_1 @ sk_A)
% 0.42/0.62            = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['30', '31'])).
% 0.42/0.62  thf('33', plain, ((v1_relat_1 @ sk_B_1)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('34', plain, ((v1_funct_1 @ sk_B_1)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('35', plain,
% 0.42/0.62      (((sk_C_1 @ sk_A)
% 0.42/0.62         = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1)))),
% 0.42/0.62      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.42/0.62  thf('36', plain,
% 0.42/0.62      ((r2_hidden @ 
% 0.42/0.62        (k4_tarski @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1) @ (sk_C_1 @ sk_A)) @ 
% 0.42/0.62        sk_B_1)),
% 0.42/0.62      inference('sup-', [status(thm)], ['27', '29'])).
% 0.42/0.62  thf('37', plain,
% 0.42/0.62      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.42/0.62         (~ (r2_hidden @ (k4_tarski @ X24 @ X26) @ X25)
% 0.42/0.62          | (r2_hidden @ X24 @ (k1_relat_1 @ X25))
% 0.42/0.62          | ~ (v1_funct_1 @ X25)
% 0.42/0.62          | ~ (v1_relat_1 @ X25))),
% 0.42/0.62      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.42/0.62  thf('38', plain,
% 0.42/0.62      ((~ (v1_relat_1 @ sk_B_1)
% 0.42/0.62        | ~ (v1_funct_1 @ sk_B_1)
% 0.42/0.62        | (r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62           (k1_relat_1 @ sk_B_1)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['36', '37'])).
% 0.42/0.62  thf('39', plain, ((v1_relat_1 @ sk_B_1)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('40', plain, ((v1_funct_1 @ sk_B_1)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('41', plain,
% 0.42/0.62      ((r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1) @ (k1_relat_1 @ sk_B_1))),
% 0.42/0.62      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.42/0.62  thf('42', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.42/0.62      inference('simplify', [status(thm)], ['2'])).
% 0.42/0.62  thf('43', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(t46_relat_1, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( v1_relat_1 @ A ) =>
% 0.42/0.62       ( ![B:$i]:
% 0.42/0.62         ( ( v1_relat_1 @ B ) =>
% 0.42/0.62           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.42/0.62             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.42/0.62  thf('44', plain,
% 0.42/0.62      (![X12 : $i, X13 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ X12)
% 0.42/0.62          | ((k1_relat_1 @ (k5_relat_1 @ X13 @ X12)) = (k1_relat_1 @ X13))
% 0.42/0.62          | ~ (r1_tarski @ (k2_relat_1 @ X13) @ (k1_relat_1 @ X12))
% 0.42/0.62          | ~ (v1_relat_1 @ X13))),
% 0.42/0.62      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.42/0.62  thf('45', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ sk_B_1))
% 0.42/0.62          | ~ (v1_relat_1 @ X0)
% 0.42/0.62          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ sk_A)) = (k1_relat_1 @ X0))
% 0.42/0.62          | ~ (v1_relat_1 @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['43', '44'])).
% 0.42/0.62  thf('46', plain, ((v1_relat_1 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('47', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ sk_B_1))
% 0.42/0.62          | ~ (v1_relat_1 @ X0)
% 0.42/0.62          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ sk_A)) = (k1_relat_1 @ X0)))),
% 0.42/0.62      inference('demod', [status(thm)], ['45', '46'])).
% 0.42/0.62  thf('48', plain,
% 0.42/0.62      ((((k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)) = (k1_relat_1 @ sk_B_1))
% 0.42/0.62        | ~ (v1_relat_1 @ sk_B_1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['42', '47'])).
% 0.42/0.62  thf('49', plain, ((v1_relat_1 @ sk_B_1)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('50', plain,
% 0.42/0.62      (((k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)) = (k1_relat_1 @ sk_B_1))),
% 0.42/0.62      inference('demod', [status(thm)], ['48', '49'])).
% 0.42/0.62  thf(t22_funct_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.42/0.62       ( ![C:$i]:
% 0.42/0.62         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.42/0.62           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) =>
% 0.42/0.62             ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A ) =
% 0.42/0.62               ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) ))).
% 0.42/0.62  thf('51', plain,
% 0.42/0.62      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ X19)
% 0.42/0.62          | ~ (v1_funct_1 @ X19)
% 0.42/0.62          | ((k1_funct_1 @ (k5_relat_1 @ X19 @ X20) @ X21)
% 0.42/0.62              = (k1_funct_1 @ X20 @ (k1_funct_1 @ X19 @ X21)))
% 0.42/0.62          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ (k5_relat_1 @ X19 @ X20)))
% 0.42/0.62          | ~ (v1_funct_1 @ X20)
% 0.42/0.62          | ~ (v1_relat_1 @ X20))),
% 0.42/0.62      inference('cnf', [status(esa)], [t22_funct_1])).
% 0.42/0.62  thf('52', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.42/0.62          | ~ (v1_relat_1 @ sk_A)
% 0.42/0.62          | ~ (v1_funct_1 @ sk_A)
% 0.42/0.62          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.42/0.62              = (k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B_1 @ X0)))
% 0.42/0.62          | ~ (v1_funct_1 @ sk_B_1)
% 0.42/0.62          | ~ (v1_relat_1 @ sk_B_1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['50', '51'])).
% 0.42/0.62  thf('53', plain, ((v1_relat_1 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('54', plain, ((v1_funct_1 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('55', plain, ((v1_funct_1 @ sk_B_1)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('56', plain, ((v1_relat_1 @ sk_B_1)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('57', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.42/0.62          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.42/0.62              = (k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B_1 @ X0))))),
% 0.42/0.62      inference('demod', [status(thm)], ['52', '53', '54', '55', '56'])).
% 0.42/0.62  thf('58', plain,
% 0.42/0.62      (((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.42/0.62         (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1))
% 0.42/0.62         = (k1_funct_1 @ sk_A @ 
% 0.42/0.62            (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['41', '57'])).
% 0.42/0.62  thf('59', plain,
% 0.42/0.62      (((sk_C_1 @ sk_A)
% 0.42/0.62         = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1)))),
% 0.42/0.62      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.42/0.62  thf('60', plain,
% 0.42/0.62      (![X14 : $i]:
% 0.42/0.62         (((k1_funct_1 @ X14 @ (sk_B @ X14))
% 0.42/0.62            = (k1_funct_1 @ X14 @ (sk_C_1 @ X14)))
% 0.42/0.62          | (v2_funct_1 @ X14)
% 0.42/0.62          | ~ (v1_funct_1 @ X14)
% 0.42/0.62          | ~ (v1_relat_1 @ X14))),
% 0.42/0.62      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.42/0.62  thf('61', plain, ((r2_hidden @ (sk_C_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 0.42/0.62      inference('clc', [status(thm)], ['25', '26'])).
% 0.42/0.62  thf('62', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('63', plain,
% 0.42/0.62      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X24 @ (k1_relat_1 @ X25))
% 0.42/0.62          | ((X26) != (k1_funct_1 @ X25 @ X24))
% 0.42/0.62          | (r2_hidden @ (k4_tarski @ X24 @ X26) @ X25)
% 0.42/0.62          | ~ (v1_funct_1 @ X25)
% 0.42/0.62          | ~ (v1_relat_1 @ X25))),
% 0.42/0.62      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.42/0.62  thf('64', plain,
% 0.42/0.62      (![X24 : $i, X25 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ X25)
% 0.42/0.62          | ~ (v1_funct_1 @ X25)
% 0.42/0.62          | (r2_hidden @ (k4_tarski @ X24 @ (k1_funct_1 @ X25 @ X24)) @ X25)
% 0.42/0.62          | ~ (r2_hidden @ X24 @ (k1_relat_1 @ X25)))),
% 0.42/0.62      inference('simplify', [status(thm)], ['63'])).
% 0.42/0.62  thf('65', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B_1))
% 0.42/0.62          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_A @ X0)) @ sk_A)
% 0.42/0.62          | ~ (v1_funct_1 @ sk_A)
% 0.42/0.62          | ~ (v1_relat_1 @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['62', '64'])).
% 0.42/0.62  thf('66', plain, ((v1_funct_1 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('67', plain, ((v1_relat_1 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('68', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B_1))
% 0.42/0.62          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_A @ X0)) @ sk_A))),
% 0.42/0.62      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.42/0.62  thf('69', plain,
% 0.42/0.62      ((r2_hidden @ 
% 0.42/0.62        (k4_tarski @ (sk_C_1 @ sk_A) @ (k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A))) @ 
% 0.42/0.62        sk_A)),
% 0.42/0.62      inference('sup-', [status(thm)], ['61', '68'])).
% 0.42/0.62  thf('70', plain,
% 0.42/0.62      (((r2_hidden @ 
% 0.42/0.62         (k4_tarski @ (sk_C_1 @ sk_A) @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A))) @ 
% 0.42/0.62         sk_A)
% 0.42/0.62        | ~ (v1_relat_1 @ sk_A)
% 0.42/0.62        | ~ (v1_funct_1 @ sk_A)
% 0.42/0.62        | (v2_funct_1 @ sk_A))),
% 0.42/0.62      inference('sup+', [status(thm)], ['60', '69'])).
% 0.42/0.62  thf('71', plain, ((v1_relat_1 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('72', plain, ((v1_funct_1 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('73', plain,
% 0.42/0.62      (((r2_hidden @ 
% 0.42/0.62         (k4_tarski @ (sk_C_1 @ sk_A) @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A))) @ 
% 0.42/0.62         sk_A)
% 0.42/0.62        | (v2_funct_1 @ sk_A))),
% 0.42/0.62      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.42/0.62  thf('74', plain, (~ (v2_funct_1 @ sk_A)),
% 0.42/0.62      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.42/0.62  thf('75', plain,
% 0.42/0.62      ((r2_hidden @ 
% 0.42/0.62        (k4_tarski @ (sk_C_1 @ sk_A) @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A))) @ 
% 0.42/0.62        sk_A)),
% 0.42/0.62      inference('clc', [status(thm)], ['73', '74'])).
% 0.42/0.62  thf('76', plain,
% 0.42/0.62      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.42/0.62         (~ (r2_hidden @ (k4_tarski @ X24 @ X26) @ X25)
% 0.42/0.62          | ((X26) = (k1_funct_1 @ X25 @ X24))
% 0.42/0.62          | ~ (v1_funct_1 @ X25)
% 0.42/0.62          | ~ (v1_relat_1 @ X25))),
% 0.42/0.62      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.42/0.62  thf('77', plain,
% 0.42/0.62      ((~ (v1_relat_1 @ sk_A)
% 0.42/0.62        | ~ (v1_funct_1 @ sk_A)
% 0.42/0.62        | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.42/0.62            = (k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['75', '76'])).
% 0.42/0.62  thf('78', plain, ((v1_relat_1 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('79', plain, ((v1_funct_1 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('80', plain,
% 0.42/0.62      (((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.42/0.62         = (k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A)))),
% 0.42/0.62      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.42/0.62  thf('81', plain,
% 0.42/0.62      (((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.42/0.62         (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1))
% 0.42/0.62         = (k1_funct_1 @ sk_A @ (sk_B @ sk_A)))),
% 0.42/0.62      inference('demod', [status(thm)], ['58', '59', '80'])).
% 0.42/0.62  thf('82', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('83', plain,
% 0.42/0.62      (![X14 : $i]:
% 0.42/0.62         ((r2_hidden @ (sk_B @ X14) @ (k1_relat_1 @ X14))
% 0.42/0.62          | (v2_funct_1 @ X14)
% 0.42/0.62          | ~ (v1_funct_1 @ X14)
% 0.42/0.62          | ~ (v1_relat_1 @ X14))),
% 0.42/0.62      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.42/0.62  thf('84', plain,
% 0.42/0.62      (((r2_hidden @ (sk_B @ sk_A) @ (k2_relat_1 @ sk_B_1))
% 0.42/0.62        | ~ (v1_relat_1 @ sk_A)
% 0.42/0.62        | ~ (v1_funct_1 @ sk_A)
% 0.42/0.62        | (v2_funct_1 @ sk_A))),
% 0.42/0.62      inference('sup+', [status(thm)], ['82', '83'])).
% 0.42/0.62  thf('85', plain, ((v1_relat_1 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('86', plain, ((v1_funct_1 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('87', plain,
% 0.42/0.62      (((r2_hidden @ (sk_B @ sk_A) @ (k2_relat_1 @ sk_B_1))
% 0.42/0.62        | (v2_funct_1 @ sk_A))),
% 0.42/0.62      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.42/0.62  thf('88', plain, (~ (v2_funct_1 @ sk_A)),
% 0.42/0.62      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.42/0.62  thf('89', plain, ((r2_hidden @ (sk_B @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 0.42/0.62      inference('clc', [status(thm)], ['87', '88'])).
% 0.42/0.62  thf('90', plain,
% 0.42/0.62      (![X5 : $i, X7 : $i]:
% 0.42/0.62         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X7 @ X5) @ X7) @ X5)
% 0.42/0.62          | ~ (r2_hidden @ X7 @ (k2_relat_1 @ X5)))),
% 0.42/0.62      inference('simplify', [status(thm)], ['28'])).
% 0.42/0.62  thf('91', plain,
% 0.42/0.62      ((r2_hidden @ 
% 0.42/0.62        (k4_tarski @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) @ (sk_B @ sk_A)) @ 
% 0.42/0.62        sk_B_1)),
% 0.42/0.62      inference('sup-', [status(thm)], ['89', '90'])).
% 0.42/0.62  thf('92', plain,
% 0.42/0.62      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.42/0.62         (~ (r2_hidden @ (k4_tarski @ X24 @ X26) @ X25)
% 0.42/0.62          | (r2_hidden @ X24 @ (k1_relat_1 @ X25))
% 0.42/0.62          | ~ (v1_funct_1 @ X25)
% 0.42/0.62          | ~ (v1_relat_1 @ X25))),
% 0.42/0.62      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.42/0.62  thf('93', plain,
% 0.42/0.62      ((~ (v1_relat_1 @ sk_B_1)
% 0.42/0.62        | ~ (v1_funct_1 @ sk_B_1)
% 0.42/0.62        | (r2_hidden @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) @ 
% 0.42/0.62           (k1_relat_1 @ sk_B_1)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['91', '92'])).
% 0.42/0.62  thf('94', plain, ((v1_relat_1 @ sk_B_1)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('95', plain, ((v1_funct_1 @ sk_B_1)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('96', plain,
% 0.42/0.62      ((r2_hidden @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) @ (k1_relat_1 @ sk_B_1))),
% 0.42/0.62      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.42/0.62  thf('97', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.42/0.62          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.42/0.62              = (k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B_1 @ X0))))),
% 0.42/0.62      inference('demod', [status(thm)], ['52', '53', '54', '55', '56'])).
% 0.42/0.62  thf('98', plain,
% 0.42/0.62      (((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.42/0.62         (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1))
% 0.42/0.62         = (k1_funct_1 @ sk_A @ 
% 0.42/0.62            (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['96', '97'])).
% 0.42/0.62  thf('99', plain,
% 0.42/0.62      ((r2_hidden @ 
% 0.42/0.62        (k4_tarski @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) @ (sk_B @ sk_A)) @ 
% 0.42/0.62        sk_B_1)),
% 0.42/0.62      inference('sup-', [status(thm)], ['89', '90'])).
% 0.42/0.62  thf('100', plain,
% 0.42/0.62      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.42/0.62         (~ (r2_hidden @ (k4_tarski @ X24 @ X26) @ X25)
% 0.42/0.62          | ((X26) = (k1_funct_1 @ X25 @ X24))
% 0.42/0.62          | ~ (v1_funct_1 @ X25)
% 0.42/0.62          | ~ (v1_relat_1 @ X25))),
% 0.42/0.62      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.42/0.62  thf('101', plain,
% 0.42/0.62      ((~ (v1_relat_1 @ sk_B_1)
% 0.42/0.62        | ~ (v1_funct_1 @ sk_B_1)
% 0.42/0.62        | ((sk_B @ sk_A)
% 0.42/0.62            = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['99', '100'])).
% 0.42/0.62  thf('102', plain, ((v1_relat_1 @ sk_B_1)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('103', plain, ((v1_funct_1 @ sk_B_1)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('104', plain,
% 0.42/0.62      (((sk_B @ sk_A)
% 0.42/0.62         = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)))),
% 0.42/0.62      inference('demod', [status(thm)], ['101', '102', '103'])).
% 0.42/0.62  thf('105', plain,
% 0.42/0.62      (((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.42/0.62         (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1))
% 0.42/0.62         = (k1_funct_1 @ sk_A @ (sk_B @ sk_A)))),
% 0.42/0.62      inference('demod', [status(thm)], ['98', '104'])).
% 0.42/0.62  thf(fc2_funct_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v1_relat_1 @ B ) & 
% 0.42/0.62         ( v1_funct_1 @ B ) ) =>
% 0.42/0.62       ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) & 
% 0.42/0.62         ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ))).
% 0.42/0.62  thf('106', plain,
% 0.42/0.62      (![X17 : $i, X18 : $i]:
% 0.42/0.62         (~ (v1_funct_1 @ X17)
% 0.42/0.62          | ~ (v1_relat_1 @ X17)
% 0.42/0.62          | ~ (v1_relat_1 @ X18)
% 0.42/0.62          | ~ (v1_funct_1 @ X18)
% 0.42/0.62          | (v1_funct_1 @ (k5_relat_1 @ X17 @ X18)))),
% 0.42/0.62      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.42/0.62  thf(dt_k5_relat_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.42/0.62       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.42/0.62  thf('107', plain,
% 0.42/0.62      (![X10 : $i, X11 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ X10)
% 0.42/0.62          | ~ (v1_relat_1 @ X11)
% 0.42/0.62          | (v1_relat_1 @ (k5_relat_1 @ X10 @ X11)))),
% 0.42/0.62      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.42/0.62  thf('108', plain,
% 0.42/0.62      (((k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)) = (k1_relat_1 @ sk_B_1))),
% 0.42/0.62      inference('demod', [status(thm)], ['48', '49'])).
% 0.42/0.62  thf('109', plain,
% 0.42/0.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.42/0.62         (~ (v2_funct_1 @ X14)
% 0.42/0.62          | ~ (r2_hidden @ X15 @ (k1_relat_1 @ X14))
% 0.42/0.62          | ~ (r2_hidden @ X16 @ (k1_relat_1 @ X14))
% 0.42/0.62          | ((k1_funct_1 @ X14 @ X15) != (k1_funct_1 @ X14 @ X16))
% 0.42/0.62          | ((X15) = (X16))
% 0.42/0.62          | ~ (v1_funct_1 @ X14)
% 0.42/0.62          | ~ (v1_relat_1 @ X14))),
% 0.42/0.62      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.42/0.62  thf('110', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.42/0.62          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.42/0.62          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.42/0.62          | ((X0) = (X1))
% 0.42/0.62          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.42/0.62              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X1))
% 0.42/0.62          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.42/0.62          | ~ (v2_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['108', '109'])).
% 0.42/0.62  thf('111', plain,
% 0.42/0.62      (((k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)) = (k1_relat_1 @ sk_B_1))),
% 0.42/0.62      inference('demod', [status(thm)], ['48', '49'])).
% 0.42/0.62  thf('112', plain, ((v2_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('113', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.42/0.62          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.42/0.62          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.42/0.62          | ((X0) = (X1))
% 0.42/0.62          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.42/0.62              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X1))
% 0.42/0.62          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1)))),
% 0.42/0.62      inference('demod', [status(thm)], ['110', '111', '112'])).
% 0.42/0.62  thf('114', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ sk_A)
% 0.42/0.62          | ~ (v1_relat_1 @ sk_B_1)
% 0.42/0.62          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.42/0.62          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X1)
% 0.42/0.62              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.42/0.62          | ((X1) = (X0))
% 0.42/0.62          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.42/0.62          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['107', '113'])).
% 0.42/0.62  thf('115', plain, ((v1_relat_1 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('116', plain, ((v1_relat_1 @ sk_B_1)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('117', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.42/0.62          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X1)
% 0.42/0.62              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.42/0.62          | ((X1) = (X0))
% 0.42/0.62          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.42/0.62          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1)))),
% 0.42/0.62      inference('demod', [status(thm)], ['114', '115', '116'])).
% 0.42/0.62  thf('118', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (v1_funct_1 @ sk_A)
% 0.42/0.62          | ~ (v1_relat_1 @ sk_A)
% 0.42/0.62          | ~ (v1_relat_1 @ sk_B_1)
% 0.42/0.62          | ~ (v1_funct_1 @ sk_B_1)
% 0.42/0.62          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.42/0.62          | ((X0) = (X1))
% 0.42/0.62          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.42/0.62              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X1))
% 0.42/0.62          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['106', '117'])).
% 0.42/0.62  thf('119', plain, ((v1_funct_1 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('120', plain, ((v1_relat_1 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('121', plain, ((v1_relat_1 @ sk_B_1)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('122', plain, ((v1_funct_1 @ sk_B_1)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('123', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.42/0.62          | ((X0) = (X1))
% 0.42/0.62          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.42/0.62              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X1))
% 0.42/0.62          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1)))),
% 0.42/0.62      inference('demod', [status(thm)], ['118', '119', '120', '121', '122'])).
% 0.42/0.62  thf('124', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.42/0.62            != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.42/0.62          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.42/0.62          | ((sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) = (X0))
% 0.42/0.62          | ~ (r2_hidden @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (k1_relat_1 @ sk_B_1)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['105', '123'])).
% 0.42/0.62  thf('125', plain,
% 0.42/0.62      ((r2_hidden @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) @ (k1_relat_1 @ sk_B_1))),
% 0.42/0.62      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.42/0.62  thf('126', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.42/0.62            != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.42/0.62          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.42/0.62          | ((sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) = (X0)))),
% 0.42/0.62      inference('demod', [status(thm)], ['124', '125'])).
% 0.42/0.62  thf('127', plain,
% 0.42/0.62      ((((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.42/0.62          != (k1_funct_1 @ sk_A @ (sk_B @ sk_A)))
% 0.42/0.62        | ((sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)
% 0.42/0.62            = (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1))
% 0.42/0.62        | ~ (r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62             (k1_relat_1 @ sk_B_1)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['81', '126'])).
% 0.42/0.62  thf('128', plain,
% 0.42/0.62      ((r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1) @ (k1_relat_1 @ sk_B_1))),
% 0.42/0.62      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.42/0.62  thf('129', plain,
% 0.42/0.62      ((((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.42/0.62          != (k1_funct_1 @ sk_A @ (sk_B @ sk_A)))
% 0.42/0.62        | ((sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)
% 0.42/0.62            = (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1)))),
% 0.42/0.62      inference('demod', [status(thm)], ['127', '128'])).
% 0.42/0.62  thf('130', plain,
% 0.42/0.62      (((sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) = (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1))),
% 0.42/0.62      inference('simplify', [status(thm)], ['129'])).
% 0.42/0.62  thf('131', plain,
% 0.42/0.62      (((sk_C_1 @ sk_A)
% 0.42/0.62         = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)))),
% 0.42/0.62      inference('demod', [status(thm)], ['35', '130'])).
% 0.42/0.62  thf('132', plain,
% 0.42/0.62      (((sk_B @ sk_A)
% 0.42/0.62         = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)))),
% 0.42/0.62      inference('demod', [status(thm)], ['101', '102', '103'])).
% 0.42/0.62  thf('133', plain, (((sk_B @ sk_A) = (sk_C_1 @ sk_A))),
% 0.42/0.62      inference('sup+', [status(thm)], ['131', '132'])).
% 0.42/0.62  thf('134', plain,
% 0.42/0.62      (![X14 : $i]:
% 0.42/0.62         (((sk_B @ X14) != (sk_C_1 @ X14))
% 0.42/0.62          | (v2_funct_1 @ X14)
% 0.42/0.62          | ~ (v1_funct_1 @ X14)
% 0.42/0.62          | ~ (v1_relat_1 @ X14))),
% 0.42/0.62      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.42/0.62  thf('135', plain,
% 0.42/0.62      ((((sk_B @ sk_A) != (sk_B @ sk_A))
% 0.42/0.62        | ~ (v1_relat_1 @ sk_A)
% 0.42/0.62        | ~ (v1_funct_1 @ sk_A)
% 0.42/0.62        | (v2_funct_1 @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['133', '134'])).
% 0.42/0.62  thf('136', plain, ((v1_relat_1 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('137', plain, ((v1_funct_1 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('138', plain, ((((sk_B @ sk_A) != (sk_B @ sk_A)) | (v2_funct_1 @ sk_A))),
% 0.42/0.62      inference('demod', [status(thm)], ['135', '136', '137'])).
% 0.42/0.62  thf('139', plain, ((v2_funct_1 @ sk_A)),
% 0.42/0.62      inference('simplify', [status(thm)], ['138'])).
% 0.42/0.62  thf('140', plain, ($false), inference('demod', [status(thm)], ['19', '139'])).
% 0.42/0.62  
% 0.42/0.62  % SZS output end Refutation
% 0.42/0.62  
% 0.42/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
