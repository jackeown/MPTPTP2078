%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.s6tcCf20zX

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:13 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 871 expanded)
%              Number of leaves         :   25 ( 247 expanded)
%              Depth                    :   26
%              Number of atoms          : 1440 (11374 expanded)
%              Number of equality atoms :   69 ( 508 expanded)
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

thf('42',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X20 @ X19 ) @ X21 )
        = ( k1_funct_1 @ X19 @ ( k1_funct_1 @ X20 @ X21 ) ) )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ X0 ) @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( sk_C_1 @ sk_A )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ X0 ) @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) )
        = ( k1_funct_1 @ X0 @ ( sk_C_1 @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44','45','46'])).

thf('48',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X14: $i] :
      ( ( r2_hidden @ ( sk_B @ X14 ) @ ( k1_relat_1 @ X14 ) )
      | ( v2_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('50',plain,
    ( ( r2_hidden @ ( sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( r2_hidden @ ( sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','18'])).

thf('55',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X7 @ X5 ) @ X7 ) @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k2_relat_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('57',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( sk_B @ sk_A ) ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X24 @ X26 ) @ X25 )
      | ( r2_hidden @ X24 @ ( k1_relat_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X20 @ X19 ) @ X21 )
        = ( k1_funct_1 @ X19 @ ( k1_funct_1 @ X20 @ X21 ) ) )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ X0 ) @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( sk_B @ sk_A ) ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['55','56'])).

thf('68',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X24 @ X26 ) @ X25 )
      | ( X26
        = ( k1_funct_1 @ X25 @ X24 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('69',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( ( sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( sk_B @ sk_A )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ X0 ) @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) )
        = ( k1_funct_1 @ X0 @ ( sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65','66','72'])).

thf(fc2_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) )).

thf('74',plain,(
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

thf('75',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('76',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('77',plain,
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

thf('78',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X13 ) @ ( k1_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ sk_A ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ sk_A ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      = ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['76','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
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

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('88',plain,(
    v2_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X1 )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ( X1 = X0 )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['75','89'])).

thf('91',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X1 )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ( X1 = X0 )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,(
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
    inference('sup-',[status(thm)],['74','93'])).

thf('95',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['94','95','96','97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 )
        = X0 )
      | ~ ( r2_hidden @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['73','99'])).

thf('101',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['100','101','102','103'])).

thf('105',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
     != ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 )
      = ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) )
    | ~ ( r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['47','104'])).

thf('106',plain,(
    ! [X14: $i] :
      ( ( ( k1_funct_1 @ X14 @ ( sk_B @ X14 ) )
        = ( k1_funct_1 @ X14 @ ( sk_C_1 @ X14 ) ) )
      | ( v2_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('107',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('108',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X24 @ ( k1_relat_1 @ X25 ) )
      | ( X26
       != ( k1_funct_1 @ X25 @ X24 ) )
      | ( r2_hidden @ ( k4_tarski @ X24 @ X26 ) @ X25 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('110',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_funct_1 @ X25 )
      | ( r2_hidden @ ( k4_tarski @ X24 @ ( k1_funct_1 @ X25 @ X24 ) ) @ X25 )
      | ~ ( r2_hidden @ X24 @ ( k1_relat_1 @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_A @ X0 ) ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['108','110'])).

thf('112',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_A @ X0 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_A ) @ ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) ) ) @ sk_A ),
    inference('sup-',[status(thm)],['107','114'])).

thf('116',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_A ) @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['106','115'])).

thf('117',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_A ) @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) ) @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','18'])).

thf('121',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_A ) @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) ) @ sk_A ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X24 @ X26 ) @ X25 )
      | ( X26
        = ( k1_funct_1 @ X25 @ X24 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('123',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
      = ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
    = ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('130',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
     != ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 )
      = ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['105','126','127','128','129'])).

thf('131',plain,
    ( ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 )
    = ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,
    ( ( sk_C_1 @ sk_A )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['35','131'])).

thf('133',plain,
    ( ( sk_B @ sk_A )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('134',plain,
    ( ( sk_B @ sk_A )
    = ( sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X14: $i] :
      ( ( ( sk_B @ X14 )
       != ( sk_C_1 @ X14 ) )
      | ( v2_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('136',plain,
    ( ( ( sk_B @ sk_A )
     != ( sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( ( sk_B @ sk_A )
     != ( sk_B @ sk_A ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('140',plain,(
    v2_funct_1 @ sk_A ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,(
    $false ),
    inference(demod,[status(thm)],['19','140'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.s6tcCf20zX
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:57:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.59  % Solved by: fo/fo7.sh
% 0.35/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.59  % done 140 iterations in 0.133s
% 0.35/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.59  % SZS output start Refutation
% 0.35/0.59  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.35/0.59  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.35/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.35/0.59  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.35/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.35/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.59  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.35/0.59  thf(sk_B_type, type, sk_B: $i > $i).
% 0.35/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.59  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.35/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.35/0.59  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.35/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.59  thf(t48_funct_1, conjecture,
% 0.35/0.59    (![A:$i]:
% 0.35/0.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.35/0.59       ( ![B:$i]:
% 0.35/0.59         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.35/0.59           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.35/0.59               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.35/0.59             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.35/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.59    (~( ![A:$i]:
% 0.35/0.59        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.35/0.59          ( ![B:$i]:
% 0.35/0.59            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.35/0.59              ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.35/0.59                  ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.35/0.59                ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ) )),
% 0.35/0.59    inference('cnf.neg', [status(esa)], [t48_funct_1])).
% 0.35/0.59  thf('0', plain, ((~ (v2_funct_1 @ sk_B_1) | ~ (v2_funct_1 @ sk_A))),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('1', plain, ((~ (v2_funct_1 @ sk_A)) <= (~ ((v2_funct_1 @ sk_A)))),
% 0.35/0.59      inference('split', [status(esa)], ['0'])).
% 0.35/0.59  thf(d10_xboole_0, axiom,
% 0.35/0.59    (![A:$i,B:$i]:
% 0.35/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.35/0.59  thf('2', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.35/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.35/0.59  thf('3', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.35/0.59      inference('simplify', [status(thm)], ['2'])).
% 0.35/0.59  thf('4', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf(t47_funct_1, axiom,
% 0.35/0.59    (![A:$i]:
% 0.35/0.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.35/0.59       ( ![B:$i]:
% 0.35/0.59         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.35/0.59           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.35/0.59               ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) =>
% 0.35/0.59             ( v2_funct_1 @ B ) ) ) ) ))).
% 0.35/0.59  thf('5', plain,
% 0.35/0.59      (![X22 : $i, X23 : $i]:
% 0.35/0.59         (~ (v1_relat_1 @ X22)
% 0.35/0.59          | ~ (v1_funct_1 @ X22)
% 0.35/0.59          | (v2_funct_1 @ X22)
% 0.35/0.59          | ~ (r1_tarski @ (k2_relat_1 @ X22) @ (k1_relat_1 @ X23))
% 0.35/0.59          | ~ (v2_funct_1 @ (k5_relat_1 @ X22 @ X23))
% 0.35/0.59          | ~ (v1_funct_1 @ X23)
% 0.35/0.59          | ~ (v1_relat_1 @ X23))),
% 0.35/0.59      inference('cnf', [status(esa)], [t47_funct_1])).
% 0.35/0.59  thf('6', plain,
% 0.35/0.59      (![X0 : $i]:
% 0.35/0.59         (~ (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ sk_B_1))
% 0.35/0.59          | ~ (v1_relat_1 @ sk_A)
% 0.35/0.59          | ~ (v1_funct_1 @ sk_A)
% 0.35/0.59          | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_A))
% 0.35/0.59          | (v2_funct_1 @ X0)
% 0.35/0.59          | ~ (v1_funct_1 @ X0)
% 0.35/0.59          | ~ (v1_relat_1 @ X0))),
% 0.35/0.59      inference('sup-', [status(thm)], ['4', '5'])).
% 0.35/0.59  thf('7', plain, ((v1_relat_1 @ sk_A)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('8', plain, ((v1_funct_1 @ sk_A)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('9', plain,
% 0.35/0.59      (![X0 : $i]:
% 0.35/0.59         (~ (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ sk_B_1))
% 0.35/0.59          | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_A))
% 0.35/0.59          | (v2_funct_1 @ X0)
% 0.35/0.59          | ~ (v1_funct_1 @ X0)
% 0.35/0.59          | ~ (v1_relat_1 @ X0))),
% 0.35/0.59      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.35/0.59  thf('10', plain,
% 0.35/0.59      ((~ (v1_relat_1 @ sk_B_1)
% 0.35/0.59        | ~ (v1_funct_1 @ sk_B_1)
% 0.35/0.59        | (v2_funct_1 @ sk_B_1)
% 0.35/0.59        | ~ (v2_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.35/0.59      inference('sup-', [status(thm)], ['3', '9'])).
% 0.35/0.59  thf('11', plain, ((v1_relat_1 @ sk_B_1)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('12', plain, ((v1_funct_1 @ sk_B_1)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('13', plain, ((v2_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('14', plain, ((v2_funct_1 @ sk_B_1)),
% 0.35/0.59      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.35/0.59  thf('15', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.35/0.59      inference('split', [status(esa)], ['0'])).
% 0.35/0.59  thf('16', plain, (((v2_funct_1 @ sk_B_1))),
% 0.35/0.59      inference('sup-', [status(thm)], ['14', '15'])).
% 0.35/0.59  thf('17', plain, (~ ((v2_funct_1 @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.35/0.59      inference('split', [status(esa)], ['0'])).
% 0.35/0.59  thf('18', plain, (~ ((v2_funct_1 @ sk_A))),
% 0.35/0.59      inference('sat_resolution*', [status(thm)], ['16', '17'])).
% 0.35/0.59  thf('19', plain, (~ (v2_funct_1 @ sk_A)),
% 0.35/0.59      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.35/0.59  thf('20', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf(d8_funct_1, axiom,
% 0.35/0.59    (![A:$i]:
% 0.35/0.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.35/0.59       ( ( v2_funct_1 @ A ) <=>
% 0.35/0.59         ( ![B:$i,C:$i]:
% 0.35/0.59           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.35/0.59               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.35/0.59               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.35/0.59             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.35/0.59  thf('21', plain,
% 0.35/0.59      (![X14 : $i]:
% 0.35/0.59         ((r2_hidden @ (sk_C_1 @ X14) @ (k1_relat_1 @ X14))
% 0.35/0.59          | (v2_funct_1 @ X14)
% 0.35/0.59          | ~ (v1_funct_1 @ X14)
% 0.35/0.59          | ~ (v1_relat_1 @ X14))),
% 0.35/0.59      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.35/0.59  thf('22', plain,
% 0.35/0.59      (((r2_hidden @ (sk_C_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))
% 0.35/0.59        | ~ (v1_relat_1 @ sk_A)
% 0.35/0.59        | ~ (v1_funct_1 @ sk_A)
% 0.35/0.59        | (v2_funct_1 @ sk_A))),
% 0.35/0.59      inference('sup+', [status(thm)], ['20', '21'])).
% 0.35/0.59  thf('23', plain, ((v1_relat_1 @ sk_A)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('24', plain, ((v1_funct_1 @ sk_A)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('25', plain,
% 0.35/0.59      (((r2_hidden @ (sk_C_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))
% 0.35/0.59        | (v2_funct_1 @ sk_A))),
% 0.35/0.59      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.35/0.59  thf('26', plain, (~ (v2_funct_1 @ sk_A)),
% 0.35/0.59      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.35/0.59  thf('27', plain, ((r2_hidden @ (sk_C_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 0.35/0.59      inference('clc', [status(thm)], ['25', '26'])).
% 0.35/0.59  thf(d5_relat_1, axiom,
% 0.35/0.59    (![A:$i,B:$i]:
% 0.35/0.59     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.35/0.59       ( ![C:$i]:
% 0.35/0.59         ( ( r2_hidden @ C @ B ) <=>
% 0.35/0.59           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.35/0.59  thf('28', plain,
% 0.35/0.59      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.35/0.59         (~ (r2_hidden @ X7 @ X6)
% 0.35/0.59          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X7 @ X5) @ X7) @ X5)
% 0.35/0.59          | ((X6) != (k2_relat_1 @ X5)))),
% 0.35/0.59      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.35/0.59  thf('29', plain,
% 0.35/0.59      (![X5 : $i, X7 : $i]:
% 0.35/0.59         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X7 @ X5) @ X7) @ X5)
% 0.35/0.59          | ~ (r2_hidden @ X7 @ (k2_relat_1 @ X5)))),
% 0.35/0.59      inference('simplify', [status(thm)], ['28'])).
% 0.35/0.59  thf('30', plain,
% 0.35/0.59      ((r2_hidden @ 
% 0.35/0.59        (k4_tarski @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1) @ (sk_C_1 @ sk_A)) @ 
% 0.35/0.59        sk_B_1)),
% 0.35/0.59      inference('sup-', [status(thm)], ['27', '29'])).
% 0.35/0.59  thf(t8_funct_1, axiom,
% 0.35/0.59    (![A:$i,B:$i,C:$i]:
% 0.35/0.59     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.35/0.59       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.35/0.59         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.35/0.59           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.35/0.59  thf('31', plain,
% 0.35/0.59      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.35/0.59         (~ (r2_hidden @ (k4_tarski @ X24 @ X26) @ X25)
% 0.35/0.59          | ((X26) = (k1_funct_1 @ X25 @ X24))
% 0.35/0.59          | ~ (v1_funct_1 @ X25)
% 0.35/0.59          | ~ (v1_relat_1 @ X25))),
% 0.35/0.59      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.35/0.59  thf('32', plain,
% 0.35/0.59      ((~ (v1_relat_1 @ sk_B_1)
% 0.35/0.59        | ~ (v1_funct_1 @ sk_B_1)
% 0.35/0.59        | ((sk_C_1 @ sk_A)
% 0.35/0.59            = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1))))),
% 0.35/0.59      inference('sup-', [status(thm)], ['30', '31'])).
% 0.35/0.59  thf('33', plain, ((v1_relat_1 @ sk_B_1)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('34', plain, ((v1_funct_1 @ sk_B_1)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('35', plain,
% 0.35/0.59      (((sk_C_1 @ sk_A)
% 0.35/0.59         = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1)))),
% 0.35/0.59      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.35/0.59  thf('36', plain,
% 0.35/0.59      ((r2_hidden @ 
% 0.35/0.59        (k4_tarski @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1) @ (sk_C_1 @ sk_A)) @ 
% 0.35/0.59        sk_B_1)),
% 0.35/0.59      inference('sup-', [status(thm)], ['27', '29'])).
% 0.35/0.59  thf('37', plain,
% 0.35/0.59      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.35/0.59         (~ (r2_hidden @ (k4_tarski @ X24 @ X26) @ X25)
% 0.35/0.59          | (r2_hidden @ X24 @ (k1_relat_1 @ X25))
% 0.35/0.59          | ~ (v1_funct_1 @ X25)
% 0.35/0.59          | ~ (v1_relat_1 @ X25))),
% 0.35/0.59      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.35/0.59  thf('38', plain,
% 0.35/0.59      ((~ (v1_relat_1 @ sk_B_1)
% 0.35/0.59        | ~ (v1_funct_1 @ sk_B_1)
% 0.35/0.59        | (r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1) @ 
% 0.35/0.59           (k1_relat_1 @ sk_B_1)))),
% 0.35/0.59      inference('sup-', [status(thm)], ['36', '37'])).
% 0.35/0.59  thf('39', plain, ((v1_relat_1 @ sk_B_1)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('40', plain, ((v1_funct_1 @ sk_B_1)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('41', plain,
% 0.35/0.59      ((r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1) @ (k1_relat_1 @ sk_B_1))),
% 0.35/0.59      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.35/0.59  thf(t23_funct_1, axiom,
% 0.35/0.59    (![A:$i,B:$i]:
% 0.35/0.59     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.35/0.59       ( ![C:$i]:
% 0.35/0.59         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.35/0.59           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.35/0.59             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.35/0.59               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 0.35/0.59  thf('42', plain,
% 0.35/0.59      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.35/0.59         (~ (v1_relat_1 @ X19)
% 0.35/0.59          | ~ (v1_funct_1 @ X19)
% 0.35/0.59          | ((k1_funct_1 @ (k5_relat_1 @ X20 @ X19) @ X21)
% 0.35/0.59              = (k1_funct_1 @ X19 @ (k1_funct_1 @ X20 @ X21)))
% 0.35/0.59          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X20))
% 0.35/0.59          | ~ (v1_funct_1 @ X20)
% 0.35/0.59          | ~ (v1_relat_1 @ X20))),
% 0.35/0.59      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.35/0.59  thf('43', plain,
% 0.35/0.59      (![X0 : $i]:
% 0.35/0.59         (~ (v1_relat_1 @ sk_B_1)
% 0.35/0.59          | ~ (v1_funct_1 @ sk_B_1)
% 0.35/0.59          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ X0) @ 
% 0.35/0.59              (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1))
% 0.35/0.59              = (k1_funct_1 @ X0 @ 
% 0.35/0.59                 (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1))))
% 0.35/0.59          | ~ (v1_funct_1 @ X0)
% 0.35/0.59          | ~ (v1_relat_1 @ X0))),
% 0.35/0.59      inference('sup-', [status(thm)], ['41', '42'])).
% 0.35/0.59  thf('44', plain, ((v1_relat_1 @ sk_B_1)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('45', plain, ((v1_funct_1 @ sk_B_1)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('46', plain,
% 0.35/0.59      (((sk_C_1 @ sk_A)
% 0.35/0.59         = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1)))),
% 0.35/0.59      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.35/0.59  thf('47', plain,
% 0.35/0.59      (![X0 : $i]:
% 0.35/0.59         (((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ X0) @ 
% 0.35/0.59            (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1))
% 0.35/0.59            = (k1_funct_1 @ X0 @ (sk_C_1 @ sk_A)))
% 0.35/0.59          | ~ (v1_funct_1 @ X0)
% 0.35/0.59          | ~ (v1_relat_1 @ X0))),
% 0.35/0.59      inference('demod', [status(thm)], ['43', '44', '45', '46'])).
% 0.35/0.59  thf('48', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('49', plain,
% 0.35/0.59      (![X14 : $i]:
% 0.35/0.59         ((r2_hidden @ (sk_B @ X14) @ (k1_relat_1 @ X14))
% 0.35/0.59          | (v2_funct_1 @ X14)
% 0.35/0.59          | ~ (v1_funct_1 @ X14)
% 0.35/0.59          | ~ (v1_relat_1 @ X14))),
% 0.35/0.59      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.35/0.59  thf('50', plain,
% 0.35/0.59      (((r2_hidden @ (sk_B @ sk_A) @ (k2_relat_1 @ sk_B_1))
% 0.35/0.59        | ~ (v1_relat_1 @ sk_A)
% 0.35/0.59        | ~ (v1_funct_1 @ sk_A)
% 0.35/0.59        | (v2_funct_1 @ sk_A))),
% 0.35/0.59      inference('sup+', [status(thm)], ['48', '49'])).
% 0.35/0.59  thf('51', plain, ((v1_relat_1 @ sk_A)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('52', plain, ((v1_funct_1 @ sk_A)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('53', plain,
% 0.35/0.59      (((r2_hidden @ (sk_B @ sk_A) @ (k2_relat_1 @ sk_B_1))
% 0.35/0.59        | (v2_funct_1 @ sk_A))),
% 0.35/0.59      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.35/0.59  thf('54', plain, (~ (v2_funct_1 @ sk_A)),
% 0.35/0.59      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.35/0.59  thf('55', plain, ((r2_hidden @ (sk_B @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 0.35/0.59      inference('clc', [status(thm)], ['53', '54'])).
% 0.35/0.59  thf('56', plain,
% 0.35/0.59      (![X5 : $i, X7 : $i]:
% 0.35/0.59         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X7 @ X5) @ X7) @ X5)
% 0.35/0.59          | ~ (r2_hidden @ X7 @ (k2_relat_1 @ X5)))),
% 0.35/0.59      inference('simplify', [status(thm)], ['28'])).
% 0.35/0.59  thf('57', plain,
% 0.35/0.59      ((r2_hidden @ 
% 0.35/0.59        (k4_tarski @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) @ (sk_B @ sk_A)) @ 
% 0.35/0.59        sk_B_1)),
% 0.35/0.59      inference('sup-', [status(thm)], ['55', '56'])).
% 0.35/0.59  thf('58', plain,
% 0.35/0.59      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.35/0.59         (~ (r2_hidden @ (k4_tarski @ X24 @ X26) @ X25)
% 0.35/0.59          | (r2_hidden @ X24 @ (k1_relat_1 @ X25))
% 0.35/0.59          | ~ (v1_funct_1 @ X25)
% 0.35/0.59          | ~ (v1_relat_1 @ X25))),
% 0.35/0.59      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.35/0.59  thf('59', plain,
% 0.35/0.59      ((~ (v1_relat_1 @ sk_B_1)
% 0.35/0.59        | ~ (v1_funct_1 @ sk_B_1)
% 0.35/0.59        | (r2_hidden @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) @ 
% 0.35/0.59           (k1_relat_1 @ sk_B_1)))),
% 0.35/0.59      inference('sup-', [status(thm)], ['57', '58'])).
% 0.35/0.59  thf('60', plain, ((v1_relat_1 @ sk_B_1)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('61', plain, ((v1_funct_1 @ sk_B_1)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('62', plain,
% 0.35/0.59      ((r2_hidden @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) @ (k1_relat_1 @ sk_B_1))),
% 0.35/0.59      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.35/0.59  thf('63', plain,
% 0.35/0.59      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.35/0.59         (~ (v1_relat_1 @ X19)
% 0.35/0.59          | ~ (v1_funct_1 @ X19)
% 0.35/0.59          | ((k1_funct_1 @ (k5_relat_1 @ X20 @ X19) @ X21)
% 0.35/0.59              = (k1_funct_1 @ X19 @ (k1_funct_1 @ X20 @ X21)))
% 0.35/0.59          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X20))
% 0.35/0.59          | ~ (v1_funct_1 @ X20)
% 0.35/0.59          | ~ (v1_relat_1 @ X20))),
% 0.35/0.59      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.35/0.59  thf('64', plain,
% 0.35/0.59      (![X0 : $i]:
% 0.35/0.59         (~ (v1_relat_1 @ sk_B_1)
% 0.35/0.59          | ~ (v1_funct_1 @ sk_B_1)
% 0.35/0.59          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ X0) @ 
% 0.35/0.59              (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1))
% 0.35/0.59              = (k1_funct_1 @ X0 @ 
% 0.35/0.59                 (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1))))
% 0.35/0.59          | ~ (v1_funct_1 @ X0)
% 0.35/0.59          | ~ (v1_relat_1 @ X0))),
% 0.35/0.59      inference('sup-', [status(thm)], ['62', '63'])).
% 0.35/0.59  thf('65', plain, ((v1_relat_1 @ sk_B_1)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('66', plain, ((v1_funct_1 @ sk_B_1)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('67', plain,
% 0.35/0.59      ((r2_hidden @ 
% 0.35/0.59        (k4_tarski @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) @ (sk_B @ sk_A)) @ 
% 0.35/0.59        sk_B_1)),
% 0.35/0.59      inference('sup-', [status(thm)], ['55', '56'])).
% 0.35/0.59  thf('68', plain,
% 0.35/0.59      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.35/0.59         (~ (r2_hidden @ (k4_tarski @ X24 @ X26) @ X25)
% 0.35/0.59          | ((X26) = (k1_funct_1 @ X25 @ X24))
% 0.35/0.59          | ~ (v1_funct_1 @ X25)
% 0.35/0.59          | ~ (v1_relat_1 @ X25))),
% 0.35/0.59      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.35/0.59  thf('69', plain,
% 0.35/0.59      ((~ (v1_relat_1 @ sk_B_1)
% 0.35/0.59        | ~ (v1_funct_1 @ sk_B_1)
% 0.35/0.59        | ((sk_B @ sk_A)
% 0.35/0.59            = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1))))),
% 0.35/0.59      inference('sup-', [status(thm)], ['67', '68'])).
% 0.35/0.59  thf('70', plain, ((v1_relat_1 @ sk_B_1)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('71', plain, ((v1_funct_1 @ sk_B_1)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('72', plain,
% 0.35/0.59      (((sk_B @ sk_A)
% 0.35/0.59         = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)))),
% 0.35/0.59      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.35/0.59  thf('73', plain,
% 0.35/0.59      (![X0 : $i]:
% 0.35/0.59         (((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ X0) @ 
% 0.35/0.59            (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1))
% 0.35/0.59            = (k1_funct_1 @ X0 @ (sk_B @ sk_A)))
% 0.35/0.59          | ~ (v1_funct_1 @ X0)
% 0.35/0.59          | ~ (v1_relat_1 @ X0))),
% 0.35/0.59      inference('demod', [status(thm)], ['64', '65', '66', '72'])).
% 0.35/0.59  thf(fc2_funct_1, axiom,
% 0.35/0.59    (![A:$i,B:$i]:
% 0.35/0.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v1_relat_1 @ B ) & 
% 0.35/0.59         ( v1_funct_1 @ B ) ) =>
% 0.35/0.59       ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) & 
% 0.35/0.59         ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ))).
% 0.35/0.59  thf('74', plain,
% 0.35/0.59      (![X17 : $i, X18 : $i]:
% 0.35/0.59         (~ (v1_funct_1 @ X17)
% 0.35/0.59          | ~ (v1_relat_1 @ X17)
% 0.35/0.59          | ~ (v1_relat_1 @ X18)
% 0.35/0.59          | ~ (v1_funct_1 @ X18)
% 0.35/0.59          | (v1_funct_1 @ (k5_relat_1 @ X17 @ X18)))),
% 0.35/0.59      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.35/0.59  thf(dt_k5_relat_1, axiom,
% 0.35/0.59    (![A:$i,B:$i]:
% 0.35/0.59     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.35/0.59       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.35/0.59  thf('75', plain,
% 0.35/0.59      (![X10 : $i, X11 : $i]:
% 0.35/0.59         (~ (v1_relat_1 @ X10)
% 0.35/0.59          | ~ (v1_relat_1 @ X11)
% 0.35/0.59          | (v1_relat_1 @ (k5_relat_1 @ X10 @ X11)))),
% 0.35/0.59      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.35/0.59  thf('76', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.35/0.59      inference('simplify', [status(thm)], ['2'])).
% 0.35/0.59  thf('77', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf(t46_relat_1, axiom,
% 0.35/0.59    (![A:$i]:
% 0.35/0.59     ( ( v1_relat_1 @ A ) =>
% 0.35/0.59       ( ![B:$i]:
% 0.35/0.59         ( ( v1_relat_1 @ B ) =>
% 0.35/0.59           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.35/0.59             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.35/0.59  thf('78', plain,
% 0.35/0.59      (![X12 : $i, X13 : $i]:
% 0.35/0.59         (~ (v1_relat_1 @ X12)
% 0.35/0.59          | ((k1_relat_1 @ (k5_relat_1 @ X13 @ X12)) = (k1_relat_1 @ X13))
% 0.35/0.59          | ~ (r1_tarski @ (k2_relat_1 @ X13) @ (k1_relat_1 @ X12))
% 0.35/0.59          | ~ (v1_relat_1 @ X13))),
% 0.35/0.59      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.35/0.59  thf('79', plain,
% 0.35/0.59      (![X0 : $i]:
% 0.35/0.59         (~ (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ sk_B_1))
% 0.35/0.59          | ~ (v1_relat_1 @ X0)
% 0.35/0.59          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ sk_A)) = (k1_relat_1 @ X0))
% 0.35/0.59          | ~ (v1_relat_1 @ sk_A))),
% 0.35/0.59      inference('sup-', [status(thm)], ['77', '78'])).
% 0.35/0.59  thf('80', plain, ((v1_relat_1 @ sk_A)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('81', plain,
% 0.35/0.59      (![X0 : $i]:
% 0.35/0.59         (~ (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ sk_B_1))
% 0.35/0.59          | ~ (v1_relat_1 @ X0)
% 0.35/0.59          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ sk_A)) = (k1_relat_1 @ X0)))),
% 0.35/0.59      inference('demod', [status(thm)], ['79', '80'])).
% 0.35/0.59  thf('82', plain,
% 0.35/0.59      ((((k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)) = (k1_relat_1 @ sk_B_1))
% 0.35/0.59        | ~ (v1_relat_1 @ sk_B_1))),
% 0.35/0.59      inference('sup-', [status(thm)], ['76', '81'])).
% 0.35/0.59  thf('83', plain, ((v1_relat_1 @ sk_B_1)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('84', plain,
% 0.35/0.59      (((k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)) = (k1_relat_1 @ sk_B_1))),
% 0.35/0.59      inference('demod', [status(thm)], ['82', '83'])).
% 0.35/0.59  thf('85', plain,
% 0.35/0.59      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.35/0.59         (~ (v2_funct_1 @ X14)
% 0.35/0.59          | ~ (r2_hidden @ X15 @ (k1_relat_1 @ X14))
% 0.35/0.59          | ~ (r2_hidden @ X16 @ (k1_relat_1 @ X14))
% 0.35/0.59          | ((k1_funct_1 @ X14 @ X15) != (k1_funct_1 @ X14 @ X16))
% 0.35/0.59          | ((X15) = (X16))
% 0.35/0.59          | ~ (v1_funct_1 @ X14)
% 0.35/0.59          | ~ (v1_relat_1 @ X14))),
% 0.35/0.59      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.35/0.59  thf('86', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]:
% 0.35/0.59         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.35/0.59          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.35/0.59          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.35/0.59          | ((X0) = (X1))
% 0.35/0.59          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.35/0.59              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X1))
% 0.35/0.59          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.35/0.59          | ~ (v2_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.35/0.59      inference('sup-', [status(thm)], ['84', '85'])).
% 0.35/0.59  thf('87', plain,
% 0.35/0.59      (((k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)) = (k1_relat_1 @ sk_B_1))),
% 0.35/0.59      inference('demod', [status(thm)], ['82', '83'])).
% 0.35/0.59  thf('88', plain, ((v2_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('89', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]:
% 0.35/0.59         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.35/0.59          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.35/0.59          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.35/0.59          | ((X0) = (X1))
% 0.35/0.59          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.35/0.59              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X1))
% 0.35/0.59          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1)))),
% 0.35/0.59      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.35/0.59  thf('90', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]:
% 0.35/0.59         (~ (v1_relat_1 @ sk_A)
% 0.35/0.59          | ~ (v1_relat_1 @ sk_B_1)
% 0.35/0.59          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.35/0.59          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X1)
% 0.35/0.59              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.35/0.59          | ((X1) = (X0))
% 0.35/0.59          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.35/0.59          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1)))),
% 0.35/0.59      inference('sup-', [status(thm)], ['75', '89'])).
% 0.35/0.59  thf('91', plain, ((v1_relat_1 @ sk_A)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('92', plain, ((v1_relat_1 @ sk_B_1)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('93', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]:
% 0.35/0.59         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.35/0.59          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X1)
% 0.35/0.59              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.35/0.59          | ((X1) = (X0))
% 0.35/0.59          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.35/0.59          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1)))),
% 0.35/0.59      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.35/0.59  thf('94', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]:
% 0.35/0.59         (~ (v1_funct_1 @ sk_A)
% 0.35/0.59          | ~ (v1_relat_1 @ sk_A)
% 0.35/0.59          | ~ (v1_relat_1 @ sk_B_1)
% 0.35/0.59          | ~ (v1_funct_1 @ sk_B_1)
% 0.35/0.59          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.35/0.59          | ((X0) = (X1))
% 0.35/0.59          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.35/0.59              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X1))
% 0.35/0.59          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1)))),
% 0.35/0.59      inference('sup-', [status(thm)], ['74', '93'])).
% 0.35/0.59  thf('95', plain, ((v1_funct_1 @ sk_A)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('96', plain, ((v1_relat_1 @ sk_A)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('97', plain, ((v1_relat_1 @ sk_B_1)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('98', plain, ((v1_funct_1 @ sk_B_1)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('99', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]:
% 0.35/0.59         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.35/0.59          | ((X0) = (X1))
% 0.35/0.59          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.35/0.59              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X1))
% 0.35/0.59          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1)))),
% 0.35/0.59      inference('demod', [status(thm)], ['94', '95', '96', '97', '98'])).
% 0.35/0.59  thf('100', plain,
% 0.35/0.59      (![X0 : $i]:
% 0.35/0.59         (((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.35/0.59            != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.35/0.59          | ~ (v1_relat_1 @ sk_A)
% 0.35/0.59          | ~ (v1_funct_1 @ sk_A)
% 0.35/0.59          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.35/0.59          | ((sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) = (X0))
% 0.35/0.59          | ~ (r2_hidden @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) @ 
% 0.35/0.59               (k1_relat_1 @ sk_B_1)))),
% 0.35/0.59      inference('sup-', [status(thm)], ['73', '99'])).
% 0.35/0.59  thf('101', plain, ((v1_relat_1 @ sk_A)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('102', plain, ((v1_funct_1 @ sk_A)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('103', plain,
% 0.35/0.59      ((r2_hidden @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) @ (k1_relat_1 @ sk_B_1))),
% 0.35/0.59      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.35/0.59  thf('104', plain,
% 0.35/0.59      (![X0 : $i]:
% 0.35/0.59         (((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.35/0.59            != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.35/0.59          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.35/0.59          | ((sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) = (X0)))),
% 0.35/0.59      inference('demod', [status(thm)], ['100', '101', '102', '103'])).
% 0.35/0.59  thf('105', plain,
% 0.35/0.59      ((((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.35/0.59          != (k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A)))
% 0.35/0.59        | ~ (v1_relat_1 @ sk_A)
% 0.35/0.59        | ~ (v1_funct_1 @ sk_A)
% 0.35/0.59        | ((sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)
% 0.35/0.59            = (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1))
% 0.35/0.59        | ~ (r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1) @ 
% 0.35/0.59             (k1_relat_1 @ sk_B_1)))),
% 0.35/0.59      inference('sup-', [status(thm)], ['47', '104'])).
% 0.35/0.59  thf('106', plain,
% 0.35/0.59      (![X14 : $i]:
% 0.35/0.59         (((k1_funct_1 @ X14 @ (sk_B @ X14))
% 0.35/0.59            = (k1_funct_1 @ X14 @ (sk_C_1 @ X14)))
% 0.35/0.59          | (v2_funct_1 @ X14)
% 0.35/0.59          | ~ (v1_funct_1 @ X14)
% 0.35/0.59          | ~ (v1_relat_1 @ X14))),
% 0.35/0.59      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.35/0.59  thf('107', plain, ((r2_hidden @ (sk_C_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 0.35/0.59      inference('clc', [status(thm)], ['25', '26'])).
% 0.35/0.59  thf('108', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('109', plain,
% 0.35/0.59      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.35/0.59         (~ (r2_hidden @ X24 @ (k1_relat_1 @ X25))
% 0.35/0.59          | ((X26) != (k1_funct_1 @ X25 @ X24))
% 0.35/0.59          | (r2_hidden @ (k4_tarski @ X24 @ X26) @ X25)
% 0.35/0.59          | ~ (v1_funct_1 @ X25)
% 0.35/0.59          | ~ (v1_relat_1 @ X25))),
% 0.35/0.59      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.35/0.59  thf('110', plain,
% 0.35/0.59      (![X24 : $i, X25 : $i]:
% 0.35/0.59         (~ (v1_relat_1 @ X25)
% 0.35/0.59          | ~ (v1_funct_1 @ X25)
% 0.35/0.59          | (r2_hidden @ (k4_tarski @ X24 @ (k1_funct_1 @ X25 @ X24)) @ X25)
% 0.35/0.59          | ~ (r2_hidden @ X24 @ (k1_relat_1 @ X25)))),
% 0.35/0.59      inference('simplify', [status(thm)], ['109'])).
% 0.35/0.59  thf('111', plain,
% 0.35/0.59      (![X0 : $i]:
% 0.35/0.59         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B_1))
% 0.35/0.59          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_A @ X0)) @ sk_A)
% 0.35/0.59          | ~ (v1_funct_1 @ sk_A)
% 0.35/0.59          | ~ (v1_relat_1 @ sk_A))),
% 0.35/0.59      inference('sup-', [status(thm)], ['108', '110'])).
% 0.35/0.59  thf('112', plain, ((v1_funct_1 @ sk_A)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('113', plain, ((v1_relat_1 @ sk_A)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('114', plain,
% 0.35/0.59      (![X0 : $i]:
% 0.35/0.59         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B_1))
% 0.35/0.59          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_A @ X0)) @ sk_A))),
% 0.35/0.59      inference('demod', [status(thm)], ['111', '112', '113'])).
% 0.35/0.59  thf('115', plain,
% 0.35/0.59      ((r2_hidden @ 
% 0.35/0.59        (k4_tarski @ (sk_C_1 @ sk_A) @ (k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A))) @ 
% 0.35/0.59        sk_A)),
% 0.35/0.59      inference('sup-', [status(thm)], ['107', '114'])).
% 0.35/0.59  thf('116', plain,
% 0.35/0.59      (((r2_hidden @ 
% 0.35/0.59         (k4_tarski @ (sk_C_1 @ sk_A) @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A))) @ 
% 0.35/0.59         sk_A)
% 0.35/0.59        | ~ (v1_relat_1 @ sk_A)
% 0.35/0.59        | ~ (v1_funct_1 @ sk_A)
% 0.35/0.59        | (v2_funct_1 @ sk_A))),
% 0.35/0.59      inference('sup+', [status(thm)], ['106', '115'])).
% 0.35/0.59  thf('117', plain, ((v1_relat_1 @ sk_A)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('118', plain, ((v1_funct_1 @ sk_A)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('119', plain,
% 0.35/0.59      (((r2_hidden @ 
% 0.35/0.59         (k4_tarski @ (sk_C_1 @ sk_A) @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A))) @ 
% 0.35/0.59         sk_A)
% 0.35/0.59        | (v2_funct_1 @ sk_A))),
% 0.35/0.59      inference('demod', [status(thm)], ['116', '117', '118'])).
% 0.35/0.59  thf('120', plain, (~ (v2_funct_1 @ sk_A)),
% 0.35/0.59      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.35/0.59  thf('121', plain,
% 0.35/0.59      ((r2_hidden @ 
% 0.35/0.59        (k4_tarski @ (sk_C_1 @ sk_A) @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A))) @ 
% 0.35/0.59        sk_A)),
% 0.35/0.59      inference('clc', [status(thm)], ['119', '120'])).
% 0.35/0.59  thf('122', plain,
% 0.35/0.59      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.35/0.59         (~ (r2_hidden @ (k4_tarski @ X24 @ X26) @ X25)
% 0.35/0.59          | ((X26) = (k1_funct_1 @ X25 @ X24))
% 0.35/0.59          | ~ (v1_funct_1 @ X25)
% 0.35/0.59          | ~ (v1_relat_1 @ X25))),
% 0.35/0.59      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.35/0.59  thf('123', plain,
% 0.35/0.59      ((~ (v1_relat_1 @ sk_A)
% 0.35/0.59        | ~ (v1_funct_1 @ sk_A)
% 0.35/0.59        | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.35/0.59            = (k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A))))),
% 0.35/0.59      inference('sup-', [status(thm)], ['121', '122'])).
% 0.35/0.59  thf('124', plain, ((v1_relat_1 @ sk_A)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('125', plain, ((v1_funct_1 @ sk_A)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('126', plain,
% 0.35/0.59      (((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.35/0.59         = (k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A)))),
% 0.35/0.59      inference('demod', [status(thm)], ['123', '124', '125'])).
% 0.35/0.59  thf('127', plain, ((v1_relat_1 @ sk_A)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('128', plain, ((v1_funct_1 @ sk_A)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('129', plain,
% 0.35/0.59      ((r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1) @ (k1_relat_1 @ sk_B_1))),
% 0.35/0.59      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.35/0.59  thf('130', plain,
% 0.35/0.59      ((((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.35/0.59          != (k1_funct_1 @ sk_A @ (sk_B @ sk_A)))
% 0.35/0.59        | ((sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)
% 0.35/0.59            = (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1)))),
% 0.35/0.59      inference('demod', [status(thm)], ['105', '126', '127', '128', '129'])).
% 0.35/0.59  thf('131', plain,
% 0.35/0.59      (((sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) = (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1))),
% 0.35/0.59      inference('simplify', [status(thm)], ['130'])).
% 0.35/0.59  thf('132', plain,
% 0.35/0.59      (((sk_C_1 @ sk_A)
% 0.35/0.59         = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)))),
% 0.35/0.59      inference('demod', [status(thm)], ['35', '131'])).
% 0.35/0.59  thf('133', plain,
% 0.35/0.59      (((sk_B @ sk_A)
% 0.35/0.59         = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)))),
% 0.35/0.59      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.35/0.59  thf('134', plain, (((sk_B @ sk_A) = (sk_C_1 @ sk_A))),
% 0.35/0.59      inference('sup+', [status(thm)], ['132', '133'])).
% 0.35/0.59  thf('135', plain,
% 0.35/0.59      (![X14 : $i]:
% 0.35/0.59         (((sk_B @ X14) != (sk_C_1 @ X14))
% 0.35/0.59          | (v2_funct_1 @ X14)
% 0.35/0.59          | ~ (v1_funct_1 @ X14)
% 0.35/0.59          | ~ (v1_relat_1 @ X14))),
% 0.35/0.59      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.35/0.59  thf('136', plain,
% 0.35/0.59      ((((sk_B @ sk_A) != (sk_B @ sk_A))
% 0.35/0.59        | ~ (v1_relat_1 @ sk_A)
% 0.35/0.59        | ~ (v1_funct_1 @ sk_A)
% 0.35/0.59        | (v2_funct_1 @ sk_A))),
% 0.35/0.59      inference('sup-', [status(thm)], ['134', '135'])).
% 0.35/0.59  thf('137', plain, ((v1_relat_1 @ sk_A)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('138', plain, ((v1_funct_1 @ sk_A)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('139', plain, ((((sk_B @ sk_A) != (sk_B @ sk_A)) | (v2_funct_1 @ sk_A))),
% 0.35/0.59      inference('demod', [status(thm)], ['136', '137', '138'])).
% 0.35/0.59  thf('140', plain, ((v2_funct_1 @ sk_A)),
% 0.35/0.59      inference('simplify', [status(thm)], ['139'])).
% 0.35/0.59  thf('141', plain, ($false), inference('demod', [status(thm)], ['19', '140'])).
% 0.35/0.59  
% 0.35/0.59  % SZS output end Refutation
% 0.35/0.59  
% 0.35/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
