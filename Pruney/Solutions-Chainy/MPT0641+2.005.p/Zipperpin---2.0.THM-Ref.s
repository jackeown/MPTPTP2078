%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BSEPKw19su

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:12 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 969 expanded)
%              Number of leaves         :   23 ( 270 expanded)
%              Depth                    :   26
%              Number of atoms          : 1489 (12827 expanded)
%              Number of equality atoms :   81 ( 606 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ! [X8: $i,X10: $i,X11: $i] :
      ( ( X10
       != ( k2_relat_1 @ X8 ) )
      | ( X11
        = ( k1_funct_1 @ X8 @ ( sk_D_1 @ X11 @ X8 ) ) )
      | ~ ( r2_hidden @ X11 @ X10 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('29',plain,(
    ! [X8: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( r2_hidden @ X11 @ ( k2_relat_1 @ X8 ) )
      | ( X11
        = ( k1_funct_1 @ X8 @ ( sk_D_1 @ X11 @ X8 ) ) ) ) ),
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
    ! [X8: $i,X10: $i,X11: $i] :
      ( ( X10
       != ( k2_relat_1 @ X8 ) )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 ) @ ( k1_relat_1 @ X8 ) )
      | ~ ( r2_hidden @ X11 @ X10 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('36',plain,(
    ! [X8: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( r2_hidden @ X11 @ ( k2_relat_1 @ X8 ) )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 ) @ ( k1_relat_1 @ X8 ) ) ) ),
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

thf('41',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('42',plain,
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

thf('43',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X6 ) @ ( k1_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ sk_A ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ sk_A ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      = ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['47','48'])).

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

thf('50',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X19 @ X20 ) @ X21 )
        = ( k1_funct_1 @ X20 @ ( k1_funct_1 @ X19 @ X21 ) ) )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ ( k5_relat_1 @ X19 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
        = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
        = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['51','52','53','54','55'])).

thf('57',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) )
    = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['40','56'])).

thf('58',plain,
    ( ( sk_C_1 @ sk_A )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('59',plain,(
    ! [X14: $i] :
      ( ( ( k1_funct_1 @ X14 @ ( sk_B @ X14 ) )
        = ( k1_funct_1 @ X14 @ ( sk_C_1 @ X14 ) ) )
      | ( v2_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('60',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('61',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X8: $i,X10: $i,X12: $i,X13: $i] :
      ( ( X10
       != ( k2_relat_1 @ X8 ) )
      | ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X8 ) )
      | ( X12
       != ( k1_funct_1 @ X8 @ X13 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('63',plain,(
    ! [X8: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X8 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X8 @ X13 ) @ ( k2_relat_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','63'])).

thf('65',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) ) @ ( k2_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','67'])).

thf('69',plain,(
    ! [X8: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( r2_hidden @ X11 @ ( k2_relat_1 @ X8 ) )
      | ( X11
        = ( k1_funct_1 @ X8 @ ( sk_D_1 @ X11 @ X8 ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('70',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) )
      = ( k1_funct_1 @ sk_A @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) )
    = ( k1_funct_1 @ sk_A @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) )
      = ( k1_funct_1 @ sk_A @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['59','73'])).

thf('75',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X14: $i] :
      ( ( r2_hidden @ ( sk_B @ X14 ) @ ( k1_relat_1 @ X14 ) )
      | ( v2_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('77',plain,
    ( ( r2_hidden @ ( sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( r2_hidden @ ( sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','18'])).

thf('82',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('84',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k2_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X8: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( r2_hidden @ X11 @ ( k2_relat_1 @ X8 ) )
      | ( X11
        = ( k1_funct_1 @ X8 @ ( sk_D_1 @ X11 @ X8 ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('86',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
      = ( k1_funct_1 @ sk_A @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
    = ( k1_funct_1 @ sk_A @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) )
      = ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['74','89','90','91'])).

thf('93',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','18'])).

thf('94',plain,
    ( ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) )
    = ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) )
    = ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58','94'])).

thf('96',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('97',plain,(
    ! [X8: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( r2_hidden @ X11 @ ( k2_relat_1 @ X8 ) )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 ) @ ( k1_relat_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('98',plain,
    ( ( r2_hidden @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
        = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['51','52','53','54','55'])).

thf('103',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) )
    = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('105',plain,(
    ! [X8: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( r2_hidden @ X11 @ ( k2_relat_1 @ X8 ) )
      | ( X11
        = ( k1_funct_1 @ X8 @ ( sk_D_1 @ X11 @ X8 ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('106',plain,
    ( ( ( sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( sk_B @ sk_A )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) )
    = ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['103','109'])).

thf(fc2_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) )).

thf('111',plain,(
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

thf('112',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('113',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('114',plain,(
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

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('117',plain,(
    v2_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X1 )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ( X1 = X0 )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['112','118'])).

thf('120',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X1 )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ( X1 = X0 )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('123',plain,(
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
    inference('sup-',[status(thm)],['111','122'])).

thf('124',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['123','124','125','126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 )
        = X0 )
      | ~ ( r2_hidden @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['110','128'])).

thf('130',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
     != ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 )
      = ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) )
    | ~ ( r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['95','131'])).

thf('133',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('134',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
     != ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 )
      = ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 )
    = ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,
    ( ( sk_C_1 @ sk_A )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['33','135'])).

thf('137',plain,
    ( ( sk_B @ sk_A )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('138',plain,
    ( ( sk_B @ sk_A )
    = ( sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X14: $i] :
      ( ( ( sk_B @ X14 )
       != ( sk_C_1 @ X14 ) )
      | ( v2_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BSEPKw19su
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:12:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.66  % Solved by: fo/fo7.sh
% 0.45/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.66  % done 255 iterations in 0.207s
% 0.45/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.66  % SZS output start Refutation
% 0.45/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.66  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.45/0.66  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.45/0.66  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.45/0.66  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.45/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.66  thf(sk_B_type, type, sk_B: $i > $i).
% 0.45/0.66  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.45/0.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.66  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.45/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.66  thf(t48_funct_1, conjecture,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.45/0.66           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.45/0.66               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.45/0.66             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.45/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.66    (~( ![A:$i]:
% 0.45/0.66        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.66          ( ![B:$i]:
% 0.45/0.66            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.45/0.66              ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.45/0.66                  ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.45/0.66                ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ) )),
% 0.45/0.66    inference('cnf.neg', [status(esa)], [t48_funct_1])).
% 0.45/0.66  thf('0', plain, ((~ (v2_funct_1 @ sk_B_1) | ~ (v2_funct_1 @ sk_A))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('1', plain, ((~ (v2_funct_1 @ sk_A)) <= (~ ((v2_funct_1 @ sk_A)))),
% 0.45/0.66      inference('split', [status(esa)], ['0'])).
% 0.45/0.66  thf(d10_xboole_0, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.66  thf('2', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.45/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.66  thf('3', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.45/0.66      inference('simplify', [status(thm)], ['2'])).
% 0.45/0.66  thf('4', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(t47_funct_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.45/0.66           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.45/0.66               ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) =>
% 0.45/0.66             ( v2_funct_1 @ B ) ) ) ) ))).
% 0.45/0.66  thf('5', plain,
% 0.45/0.66      (![X22 : $i, X23 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X22)
% 0.45/0.66          | ~ (v1_funct_1 @ X22)
% 0.45/0.66          | (v2_funct_1 @ X22)
% 0.45/0.66          | ~ (r1_tarski @ (k2_relat_1 @ X22) @ (k1_relat_1 @ X23))
% 0.45/0.66          | ~ (v2_funct_1 @ (k5_relat_1 @ X22 @ X23))
% 0.45/0.66          | ~ (v1_funct_1 @ X23)
% 0.45/0.66          | ~ (v1_relat_1 @ X23))),
% 0.45/0.66      inference('cnf', [status(esa)], [t47_funct_1])).
% 0.45/0.66  thf('6', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ sk_B_1))
% 0.45/0.66          | ~ (v1_relat_1 @ sk_A)
% 0.45/0.66          | ~ (v1_funct_1 @ sk_A)
% 0.45/0.66          | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_A))
% 0.45/0.66          | (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['4', '5'])).
% 0.45/0.66  thf('7', plain, ((v1_relat_1 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('8', plain, ((v1_funct_1 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('9', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ sk_B_1))
% 0.45/0.66          | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_A))
% 0.45/0.66          | (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0))),
% 0.45/0.66      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.45/0.66  thf('10', plain,
% 0.45/0.66      ((~ (v1_relat_1 @ sk_B_1)
% 0.45/0.66        | ~ (v1_funct_1 @ sk_B_1)
% 0.45/0.66        | (v2_funct_1 @ sk_B_1)
% 0.45/0.66        | ~ (v2_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['3', '9'])).
% 0.45/0.66  thf('11', plain, ((v1_relat_1 @ sk_B_1)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('12', plain, ((v1_funct_1 @ sk_B_1)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('13', plain, ((v2_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('14', plain, ((v2_funct_1 @ sk_B_1)),
% 0.45/0.66      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.45/0.66  thf('15', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.45/0.66      inference('split', [status(esa)], ['0'])).
% 0.45/0.66  thf('16', plain, (((v2_funct_1 @ sk_B_1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['14', '15'])).
% 0.45/0.66  thf('17', plain, (~ ((v2_funct_1 @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.45/0.66      inference('split', [status(esa)], ['0'])).
% 0.45/0.66  thf('18', plain, (~ ((v2_funct_1 @ sk_A))),
% 0.45/0.66      inference('sat_resolution*', [status(thm)], ['16', '17'])).
% 0.45/0.66  thf('19', plain, (~ (v2_funct_1 @ sk_A)),
% 0.45/0.66      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.45/0.66  thf('20', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(d8_funct_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.66       ( ( v2_funct_1 @ A ) <=>
% 0.45/0.66         ( ![B:$i,C:$i]:
% 0.45/0.66           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.45/0.66               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.45/0.66               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.45/0.66             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.45/0.66  thf('21', plain,
% 0.45/0.66      (![X14 : $i]:
% 0.45/0.66         ((r2_hidden @ (sk_C_1 @ X14) @ (k1_relat_1 @ X14))
% 0.45/0.66          | (v2_funct_1 @ X14)
% 0.45/0.66          | ~ (v1_funct_1 @ X14)
% 0.45/0.66          | ~ (v1_relat_1 @ X14))),
% 0.45/0.66      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.45/0.66  thf('22', plain,
% 0.45/0.66      (((r2_hidden @ (sk_C_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))
% 0.45/0.66        | ~ (v1_relat_1 @ sk_A)
% 0.45/0.66        | ~ (v1_funct_1 @ sk_A)
% 0.45/0.66        | (v2_funct_1 @ sk_A))),
% 0.45/0.66      inference('sup+', [status(thm)], ['20', '21'])).
% 0.45/0.66  thf('23', plain, ((v1_relat_1 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('24', plain, ((v1_funct_1 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('25', plain,
% 0.45/0.66      (((r2_hidden @ (sk_C_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))
% 0.45/0.66        | (v2_funct_1 @ sk_A))),
% 0.45/0.66      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.45/0.66  thf('26', plain, (~ (v2_funct_1 @ sk_A)),
% 0.45/0.66      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.45/0.66  thf('27', plain, ((r2_hidden @ (sk_C_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 0.45/0.66      inference('clc', [status(thm)], ['25', '26'])).
% 0.45/0.66  thf(d5_funct_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.45/0.66           ( ![C:$i]:
% 0.45/0.66             ( ( r2_hidden @ C @ B ) <=>
% 0.45/0.66               ( ?[D:$i]:
% 0.45/0.66                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.45/0.66                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.45/0.66  thf('28', plain,
% 0.45/0.66      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.45/0.66         (((X10) != (k2_relat_1 @ X8))
% 0.45/0.66          | ((X11) = (k1_funct_1 @ X8 @ (sk_D_1 @ X11 @ X8)))
% 0.45/0.66          | ~ (r2_hidden @ X11 @ X10)
% 0.45/0.66          | ~ (v1_funct_1 @ X8)
% 0.45/0.66          | ~ (v1_relat_1 @ X8))),
% 0.45/0.66      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.45/0.66  thf('29', plain,
% 0.45/0.66      (![X8 : $i, X11 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X8)
% 0.45/0.66          | ~ (v1_funct_1 @ X8)
% 0.45/0.66          | ~ (r2_hidden @ X11 @ (k2_relat_1 @ X8))
% 0.45/0.66          | ((X11) = (k1_funct_1 @ X8 @ (sk_D_1 @ X11 @ X8))))),
% 0.45/0.66      inference('simplify', [status(thm)], ['28'])).
% 0.45/0.66  thf('30', plain,
% 0.45/0.66      ((((sk_C_1 @ sk_A)
% 0.45/0.66          = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1)))
% 0.45/0.66        | ~ (v1_funct_1 @ sk_B_1)
% 0.45/0.66        | ~ (v1_relat_1 @ sk_B_1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['27', '29'])).
% 0.45/0.66  thf('31', plain, ((v1_funct_1 @ sk_B_1)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('32', plain, ((v1_relat_1 @ sk_B_1)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('33', plain,
% 0.45/0.66      (((sk_C_1 @ sk_A)
% 0.45/0.66         = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1)))),
% 0.45/0.66      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.45/0.66  thf('34', plain, ((r2_hidden @ (sk_C_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 0.45/0.66      inference('clc', [status(thm)], ['25', '26'])).
% 0.45/0.66  thf('35', plain,
% 0.45/0.66      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.45/0.66         (((X10) != (k2_relat_1 @ X8))
% 0.45/0.66          | (r2_hidden @ (sk_D_1 @ X11 @ X8) @ (k1_relat_1 @ X8))
% 0.45/0.66          | ~ (r2_hidden @ X11 @ X10)
% 0.45/0.66          | ~ (v1_funct_1 @ X8)
% 0.45/0.66          | ~ (v1_relat_1 @ X8))),
% 0.45/0.66      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.45/0.66  thf('36', plain,
% 0.45/0.66      (![X8 : $i, X11 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X8)
% 0.45/0.66          | ~ (v1_funct_1 @ X8)
% 0.45/0.66          | ~ (r2_hidden @ X11 @ (k2_relat_1 @ X8))
% 0.45/0.66          | (r2_hidden @ (sk_D_1 @ X11 @ X8) @ (k1_relat_1 @ X8)))),
% 0.45/0.66      inference('simplify', [status(thm)], ['35'])).
% 0.45/0.66  thf('37', plain,
% 0.45/0.66      (((r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1) @ 
% 0.45/0.66         (k1_relat_1 @ sk_B_1))
% 0.45/0.66        | ~ (v1_funct_1 @ sk_B_1)
% 0.45/0.66        | ~ (v1_relat_1 @ sk_B_1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['34', '36'])).
% 0.45/0.66  thf('38', plain, ((v1_funct_1 @ sk_B_1)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('39', plain, ((v1_relat_1 @ sk_B_1)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('40', plain,
% 0.45/0.66      ((r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1) @ (k1_relat_1 @ sk_B_1))),
% 0.45/0.66      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.45/0.66  thf('41', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.45/0.66      inference('simplify', [status(thm)], ['2'])).
% 0.45/0.66  thf('42', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(t46_relat_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( v1_relat_1 @ A ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( v1_relat_1 @ B ) =>
% 0.45/0.66           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.45/0.66             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.45/0.66  thf('43', plain,
% 0.45/0.66      (![X5 : $i, X6 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X5)
% 0.45/0.66          | ((k1_relat_1 @ (k5_relat_1 @ X6 @ X5)) = (k1_relat_1 @ X6))
% 0.45/0.66          | ~ (r1_tarski @ (k2_relat_1 @ X6) @ (k1_relat_1 @ X5))
% 0.45/0.66          | ~ (v1_relat_1 @ X6))),
% 0.45/0.66      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.45/0.66  thf('44', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ sk_B_1))
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ sk_A)) = (k1_relat_1 @ X0))
% 0.45/0.66          | ~ (v1_relat_1 @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['42', '43'])).
% 0.45/0.66  thf('45', plain, ((v1_relat_1 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('46', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ sk_B_1))
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ sk_A)) = (k1_relat_1 @ X0)))),
% 0.45/0.66      inference('demod', [status(thm)], ['44', '45'])).
% 0.45/0.66  thf('47', plain,
% 0.45/0.66      ((((k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)) = (k1_relat_1 @ sk_B_1))
% 0.45/0.66        | ~ (v1_relat_1 @ sk_B_1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['41', '46'])).
% 0.45/0.66  thf('48', plain, ((v1_relat_1 @ sk_B_1)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('49', plain,
% 0.45/0.66      (((k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)) = (k1_relat_1 @ sk_B_1))),
% 0.45/0.66      inference('demod', [status(thm)], ['47', '48'])).
% 0.45/0.66  thf(t22_funct_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.45/0.66       ( ![C:$i]:
% 0.45/0.66         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.45/0.66           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) =>
% 0.45/0.66             ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A ) =
% 0.45/0.66               ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) ))).
% 0.45/0.66  thf('50', plain,
% 0.45/0.66      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X19)
% 0.45/0.66          | ~ (v1_funct_1 @ X19)
% 0.45/0.66          | ((k1_funct_1 @ (k5_relat_1 @ X19 @ X20) @ X21)
% 0.45/0.66              = (k1_funct_1 @ X20 @ (k1_funct_1 @ X19 @ X21)))
% 0.45/0.66          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ (k5_relat_1 @ X19 @ X20)))
% 0.45/0.66          | ~ (v1_funct_1 @ X20)
% 0.45/0.66          | ~ (v1_relat_1 @ X20))),
% 0.45/0.66      inference('cnf', [status(esa)], [t22_funct_1])).
% 0.45/0.66  thf('51', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.45/0.66          | ~ (v1_relat_1 @ sk_A)
% 0.45/0.66          | ~ (v1_funct_1 @ sk_A)
% 0.45/0.66          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.45/0.66              = (k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B_1 @ X0)))
% 0.45/0.66          | ~ (v1_funct_1 @ sk_B_1)
% 0.45/0.66          | ~ (v1_relat_1 @ sk_B_1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['49', '50'])).
% 0.45/0.66  thf('52', plain, ((v1_relat_1 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('53', plain, ((v1_funct_1 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('54', plain, ((v1_funct_1 @ sk_B_1)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('55', plain, ((v1_relat_1 @ sk_B_1)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('56', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.45/0.66          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.45/0.66              = (k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B_1 @ X0))))),
% 0.45/0.66      inference('demod', [status(thm)], ['51', '52', '53', '54', '55'])).
% 0.45/0.66  thf('57', plain,
% 0.45/0.66      (((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.45/0.66         (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1))
% 0.45/0.66         = (k1_funct_1 @ sk_A @ 
% 0.45/0.66            (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['40', '56'])).
% 0.45/0.66  thf('58', plain,
% 0.45/0.66      (((sk_C_1 @ sk_A)
% 0.45/0.66         = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1)))),
% 0.45/0.66      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.45/0.66  thf('59', plain,
% 0.45/0.66      (![X14 : $i]:
% 0.45/0.66         (((k1_funct_1 @ X14 @ (sk_B @ X14))
% 0.45/0.66            = (k1_funct_1 @ X14 @ (sk_C_1 @ X14)))
% 0.45/0.66          | (v2_funct_1 @ X14)
% 0.45/0.66          | ~ (v1_funct_1 @ X14)
% 0.45/0.66          | ~ (v1_relat_1 @ X14))),
% 0.45/0.66      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.45/0.66  thf('60', plain, ((r2_hidden @ (sk_C_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 0.45/0.66      inference('clc', [status(thm)], ['25', '26'])).
% 0.45/0.66  thf('61', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('62', plain,
% 0.45/0.66      (![X8 : $i, X10 : $i, X12 : $i, X13 : $i]:
% 0.45/0.66         (((X10) != (k2_relat_1 @ X8))
% 0.45/0.66          | (r2_hidden @ X12 @ X10)
% 0.45/0.66          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X8))
% 0.45/0.66          | ((X12) != (k1_funct_1 @ X8 @ X13))
% 0.45/0.66          | ~ (v1_funct_1 @ X8)
% 0.45/0.66          | ~ (v1_relat_1 @ X8))),
% 0.45/0.66      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.45/0.66  thf('63', plain,
% 0.45/0.66      (![X8 : $i, X13 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X8)
% 0.45/0.66          | ~ (v1_funct_1 @ X8)
% 0.45/0.66          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X8))
% 0.45/0.66          | (r2_hidden @ (k1_funct_1 @ X8 @ X13) @ (k2_relat_1 @ X8)))),
% 0.45/0.66      inference('simplify', [status(thm)], ['62'])).
% 0.45/0.66  thf('64', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B_1))
% 0.45/0.66          | (r2_hidden @ (k1_funct_1 @ sk_A @ X0) @ (k2_relat_1 @ sk_A))
% 0.45/0.66          | ~ (v1_funct_1 @ sk_A)
% 0.45/0.66          | ~ (v1_relat_1 @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['61', '63'])).
% 0.45/0.66  thf('65', plain, ((v1_funct_1 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('66', plain, ((v1_relat_1 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('67', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B_1))
% 0.45/0.66          | (r2_hidden @ (k1_funct_1 @ sk_A @ X0) @ (k2_relat_1 @ sk_A)))),
% 0.45/0.66      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.45/0.66  thf('68', plain,
% 0.45/0.66      ((r2_hidden @ (k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A)) @ (k2_relat_1 @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['60', '67'])).
% 0.45/0.66  thf('69', plain,
% 0.45/0.66      (![X8 : $i, X11 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X8)
% 0.45/0.66          | ~ (v1_funct_1 @ X8)
% 0.45/0.66          | ~ (r2_hidden @ X11 @ (k2_relat_1 @ X8))
% 0.45/0.66          | ((X11) = (k1_funct_1 @ X8 @ (sk_D_1 @ X11 @ X8))))),
% 0.45/0.66      inference('simplify', [status(thm)], ['28'])).
% 0.45/0.66  thf('70', plain,
% 0.45/0.66      ((((k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A))
% 0.45/0.66          = (k1_funct_1 @ sk_A @ 
% 0.45/0.66             (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A)) @ sk_A)))
% 0.45/0.66        | ~ (v1_funct_1 @ sk_A)
% 0.45/0.66        | ~ (v1_relat_1 @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['68', '69'])).
% 0.45/0.66  thf('71', plain, ((v1_funct_1 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('72', plain, ((v1_relat_1 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('73', plain,
% 0.45/0.66      (((k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A))
% 0.45/0.66         = (k1_funct_1 @ sk_A @ 
% 0.45/0.66            (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A)) @ sk_A)))),
% 0.45/0.66      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.45/0.66  thf('74', plain,
% 0.45/0.66      ((((k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A))
% 0.45/0.66          = (k1_funct_1 @ sk_A @ 
% 0.45/0.66             (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A)))
% 0.45/0.66        | ~ (v1_relat_1 @ sk_A)
% 0.45/0.66        | ~ (v1_funct_1 @ sk_A)
% 0.45/0.66        | (v2_funct_1 @ sk_A))),
% 0.45/0.66      inference('sup+', [status(thm)], ['59', '73'])).
% 0.45/0.66  thf('75', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('76', plain,
% 0.45/0.66      (![X14 : $i]:
% 0.45/0.66         ((r2_hidden @ (sk_B @ X14) @ (k1_relat_1 @ X14))
% 0.45/0.66          | (v2_funct_1 @ X14)
% 0.45/0.66          | ~ (v1_funct_1 @ X14)
% 0.45/0.66          | ~ (v1_relat_1 @ X14))),
% 0.45/0.66      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.45/0.66  thf('77', plain,
% 0.45/0.66      (((r2_hidden @ (sk_B @ sk_A) @ (k2_relat_1 @ sk_B_1))
% 0.45/0.66        | ~ (v1_relat_1 @ sk_A)
% 0.45/0.66        | ~ (v1_funct_1 @ sk_A)
% 0.45/0.66        | (v2_funct_1 @ sk_A))),
% 0.45/0.66      inference('sup+', [status(thm)], ['75', '76'])).
% 0.45/0.66  thf('78', plain, ((v1_relat_1 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('79', plain, ((v1_funct_1 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('80', plain,
% 0.45/0.66      (((r2_hidden @ (sk_B @ sk_A) @ (k2_relat_1 @ sk_B_1))
% 0.45/0.66        | (v2_funct_1 @ sk_A))),
% 0.45/0.66      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.45/0.66  thf('81', plain, (~ (v2_funct_1 @ sk_A)),
% 0.45/0.66      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.45/0.66  thf('82', plain, ((r2_hidden @ (sk_B @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 0.45/0.66      inference('clc', [status(thm)], ['80', '81'])).
% 0.45/0.66  thf('83', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B_1))
% 0.45/0.66          | (r2_hidden @ (k1_funct_1 @ sk_A @ X0) @ (k2_relat_1 @ sk_A)))),
% 0.45/0.66      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.45/0.66  thf('84', plain,
% 0.45/0.66      ((r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ (k2_relat_1 @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['82', '83'])).
% 0.45/0.66  thf('85', plain,
% 0.45/0.66      (![X8 : $i, X11 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X8)
% 0.45/0.66          | ~ (v1_funct_1 @ X8)
% 0.45/0.66          | ~ (r2_hidden @ X11 @ (k2_relat_1 @ X8))
% 0.45/0.66          | ((X11) = (k1_funct_1 @ X8 @ (sk_D_1 @ X11 @ X8))))),
% 0.45/0.66      inference('simplify', [status(thm)], ['28'])).
% 0.45/0.66  thf('86', plain,
% 0.45/0.66      ((((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.45/0.66          = (k1_funct_1 @ sk_A @ 
% 0.45/0.66             (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A)))
% 0.45/0.66        | ~ (v1_funct_1 @ sk_A)
% 0.45/0.66        | ~ (v1_relat_1 @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['84', '85'])).
% 0.45/0.66  thf('87', plain, ((v1_funct_1 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('88', plain, ((v1_relat_1 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('89', plain,
% 0.45/0.66      (((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.45/0.66         = (k1_funct_1 @ sk_A @ 
% 0.45/0.66            (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A)))),
% 0.45/0.66      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.45/0.66  thf('90', plain, ((v1_relat_1 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('91', plain, ((v1_funct_1 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('92', plain,
% 0.45/0.66      ((((k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A))
% 0.45/0.66          = (k1_funct_1 @ sk_A @ (sk_B @ sk_A)))
% 0.45/0.66        | (v2_funct_1 @ sk_A))),
% 0.45/0.66      inference('demod', [status(thm)], ['74', '89', '90', '91'])).
% 0.45/0.66  thf('93', plain, (~ (v2_funct_1 @ sk_A)),
% 0.45/0.66      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.45/0.66  thf('94', plain,
% 0.45/0.66      (((k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A))
% 0.45/0.66         = (k1_funct_1 @ sk_A @ (sk_B @ sk_A)))),
% 0.45/0.66      inference('clc', [status(thm)], ['92', '93'])).
% 0.45/0.66  thf('95', plain,
% 0.45/0.66      (((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.45/0.66         (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1))
% 0.45/0.66         = (k1_funct_1 @ sk_A @ (sk_B @ sk_A)))),
% 0.45/0.66      inference('demod', [status(thm)], ['57', '58', '94'])).
% 0.45/0.66  thf('96', plain, ((r2_hidden @ (sk_B @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 0.45/0.66      inference('clc', [status(thm)], ['80', '81'])).
% 0.45/0.66  thf('97', plain,
% 0.45/0.66      (![X8 : $i, X11 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X8)
% 0.45/0.66          | ~ (v1_funct_1 @ X8)
% 0.45/0.66          | ~ (r2_hidden @ X11 @ (k2_relat_1 @ X8))
% 0.45/0.66          | (r2_hidden @ (sk_D_1 @ X11 @ X8) @ (k1_relat_1 @ X8)))),
% 0.45/0.66      inference('simplify', [status(thm)], ['35'])).
% 0.45/0.66  thf('98', plain,
% 0.45/0.66      (((r2_hidden @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) @ (k1_relat_1 @ sk_B_1))
% 0.45/0.66        | ~ (v1_funct_1 @ sk_B_1)
% 0.45/0.66        | ~ (v1_relat_1 @ sk_B_1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['96', '97'])).
% 0.45/0.66  thf('99', plain, ((v1_funct_1 @ sk_B_1)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('100', plain, ((v1_relat_1 @ sk_B_1)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('101', plain,
% 0.45/0.66      ((r2_hidden @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) @ (k1_relat_1 @ sk_B_1))),
% 0.45/0.66      inference('demod', [status(thm)], ['98', '99', '100'])).
% 0.45/0.66  thf('102', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.45/0.66          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.45/0.66              = (k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B_1 @ X0))))),
% 0.45/0.66      inference('demod', [status(thm)], ['51', '52', '53', '54', '55'])).
% 0.45/0.66  thf('103', plain,
% 0.45/0.66      (((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.45/0.66         (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1))
% 0.45/0.66         = (k1_funct_1 @ sk_A @ 
% 0.45/0.66            (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['101', '102'])).
% 0.45/0.66  thf('104', plain, ((r2_hidden @ (sk_B @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 0.45/0.66      inference('clc', [status(thm)], ['80', '81'])).
% 0.45/0.66  thf('105', plain,
% 0.45/0.66      (![X8 : $i, X11 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X8)
% 0.45/0.66          | ~ (v1_funct_1 @ X8)
% 0.45/0.66          | ~ (r2_hidden @ X11 @ (k2_relat_1 @ X8))
% 0.45/0.66          | ((X11) = (k1_funct_1 @ X8 @ (sk_D_1 @ X11 @ X8))))),
% 0.45/0.66      inference('simplify', [status(thm)], ['28'])).
% 0.45/0.66  thf('106', plain,
% 0.45/0.66      ((((sk_B @ sk_A)
% 0.45/0.66          = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)))
% 0.45/0.66        | ~ (v1_funct_1 @ sk_B_1)
% 0.45/0.66        | ~ (v1_relat_1 @ sk_B_1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['104', '105'])).
% 0.45/0.66  thf('107', plain, ((v1_funct_1 @ sk_B_1)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('108', plain, ((v1_relat_1 @ sk_B_1)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('109', plain,
% 0.45/0.66      (((sk_B @ sk_A)
% 0.45/0.66         = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)))),
% 0.45/0.66      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.45/0.66  thf('110', plain,
% 0.45/0.66      (((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.45/0.66         (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1))
% 0.45/0.66         = (k1_funct_1 @ sk_A @ (sk_B @ sk_A)))),
% 0.45/0.66      inference('demod', [status(thm)], ['103', '109'])).
% 0.45/0.66  thf(fc2_funct_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v1_relat_1 @ B ) & 
% 0.45/0.66         ( v1_funct_1 @ B ) ) =>
% 0.45/0.66       ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) & 
% 0.45/0.66         ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ))).
% 0.45/0.66  thf('111', plain,
% 0.45/0.66      (![X17 : $i, X18 : $i]:
% 0.45/0.66         (~ (v1_funct_1 @ X17)
% 0.45/0.66          | ~ (v1_relat_1 @ X17)
% 0.45/0.66          | ~ (v1_relat_1 @ X18)
% 0.45/0.66          | ~ (v1_funct_1 @ X18)
% 0.45/0.66          | (v1_funct_1 @ (k5_relat_1 @ X17 @ X18)))),
% 0.45/0.66      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.45/0.66  thf(dt_k5_relat_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.45/0.66       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.45/0.66  thf('112', plain,
% 0.45/0.66      (![X3 : $i, X4 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X3)
% 0.45/0.66          | ~ (v1_relat_1 @ X4)
% 0.45/0.66          | (v1_relat_1 @ (k5_relat_1 @ X3 @ X4)))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.45/0.66  thf('113', plain,
% 0.45/0.66      (((k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)) = (k1_relat_1 @ sk_B_1))),
% 0.45/0.66      inference('demod', [status(thm)], ['47', '48'])).
% 0.45/0.66  thf('114', plain,
% 0.45/0.66      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.45/0.66         (~ (v2_funct_1 @ X14)
% 0.45/0.66          | ~ (r2_hidden @ X15 @ (k1_relat_1 @ X14))
% 0.45/0.66          | ~ (r2_hidden @ X16 @ (k1_relat_1 @ X14))
% 0.45/0.66          | ((k1_funct_1 @ X14 @ X15) != (k1_funct_1 @ X14 @ X16))
% 0.45/0.66          | ((X15) = (X16))
% 0.45/0.66          | ~ (v1_funct_1 @ X14)
% 0.45/0.66          | ~ (v1_relat_1 @ X14))),
% 0.45/0.66      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.45/0.66  thf('115', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.45/0.66          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.45/0.66          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.45/0.66          | ((X0) = (X1))
% 0.45/0.66          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.45/0.66              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X1))
% 0.45/0.66          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.45/0.66          | ~ (v2_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['113', '114'])).
% 0.45/0.66  thf('116', plain,
% 0.45/0.66      (((k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)) = (k1_relat_1 @ sk_B_1))),
% 0.45/0.66      inference('demod', [status(thm)], ['47', '48'])).
% 0.45/0.66  thf('117', plain, ((v2_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('118', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.45/0.66          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.45/0.66          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.45/0.66          | ((X0) = (X1))
% 0.45/0.66          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.45/0.66              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X1))
% 0.45/0.66          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1)))),
% 0.45/0.66      inference('demod', [status(thm)], ['115', '116', '117'])).
% 0.45/0.66  thf('119', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ sk_A)
% 0.45/0.66          | ~ (v1_relat_1 @ sk_B_1)
% 0.45/0.66          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.45/0.66          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X1)
% 0.45/0.66              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.45/0.66          | ((X1) = (X0))
% 0.45/0.66          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.45/0.66          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['112', '118'])).
% 0.45/0.66  thf('120', plain, ((v1_relat_1 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('121', plain, ((v1_relat_1 @ sk_B_1)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('122', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.45/0.66          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X1)
% 0.45/0.66              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.45/0.66          | ((X1) = (X0))
% 0.45/0.66          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.45/0.66          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1)))),
% 0.45/0.66      inference('demod', [status(thm)], ['119', '120', '121'])).
% 0.45/0.66  thf('123', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_funct_1 @ sk_A)
% 0.45/0.66          | ~ (v1_relat_1 @ sk_A)
% 0.45/0.66          | ~ (v1_relat_1 @ sk_B_1)
% 0.45/0.66          | ~ (v1_funct_1 @ sk_B_1)
% 0.45/0.66          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.45/0.66          | ((X0) = (X1))
% 0.45/0.66          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.45/0.66              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X1))
% 0.45/0.66          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['111', '122'])).
% 0.45/0.66  thf('124', plain, ((v1_funct_1 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('125', plain, ((v1_relat_1 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('126', plain, ((v1_relat_1 @ sk_B_1)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('127', plain, ((v1_funct_1 @ sk_B_1)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('128', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.45/0.66          | ((X0) = (X1))
% 0.45/0.66          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.45/0.66              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X1))
% 0.45/0.66          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1)))),
% 0.45/0.66      inference('demod', [status(thm)], ['123', '124', '125', '126', '127'])).
% 0.45/0.66  thf('129', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.45/0.66            != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.45/0.66          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.45/0.66          | ((sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) = (X0))
% 0.45/0.66          | ~ (r2_hidden @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) @ 
% 0.45/0.66               (k1_relat_1 @ sk_B_1)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['110', '128'])).
% 0.45/0.66  thf('130', plain,
% 0.45/0.66      ((r2_hidden @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) @ (k1_relat_1 @ sk_B_1))),
% 0.45/0.66      inference('demod', [status(thm)], ['98', '99', '100'])).
% 0.45/0.66  thf('131', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.45/0.66            != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.45/0.66          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.45/0.66          | ((sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) = (X0)))),
% 0.45/0.66      inference('demod', [status(thm)], ['129', '130'])).
% 0.45/0.66  thf('132', plain,
% 0.45/0.66      ((((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.45/0.66          != (k1_funct_1 @ sk_A @ (sk_B @ sk_A)))
% 0.45/0.66        | ((sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)
% 0.45/0.66            = (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1))
% 0.45/0.66        | ~ (r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1) @ 
% 0.45/0.66             (k1_relat_1 @ sk_B_1)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['95', '131'])).
% 0.45/0.66  thf('133', plain,
% 0.45/0.66      ((r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1) @ (k1_relat_1 @ sk_B_1))),
% 0.45/0.66      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.45/0.66  thf('134', plain,
% 0.45/0.66      ((((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.45/0.66          != (k1_funct_1 @ sk_A @ (sk_B @ sk_A)))
% 0.45/0.66        | ((sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)
% 0.45/0.66            = (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1)))),
% 0.45/0.66      inference('demod', [status(thm)], ['132', '133'])).
% 0.45/0.66  thf('135', plain,
% 0.45/0.66      (((sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) = (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1))),
% 0.45/0.66      inference('simplify', [status(thm)], ['134'])).
% 0.45/0.66  thf('136', plain,
% 0.45/0.66      (((sk_C_1 @ sk_A)
% 0.45/0.66         = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)))),
% 0.45/0.66      inference('demod', [status(thm)], ['33', '135'])).
% 0.45/0.66  thf('137', plain,
% 0.45/0.66      (((sk_B @ sk_A)
% 0.45/0.66         = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)))),
% 0.45/0.66      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.45/0.66  thf('138', plain, (((sk_B @ sk_A) = (sk_C_1 @ sk_A))),
% 0.45/0.66      inference('sup+', [status(thm)], ['136', '137'])).
% 0.45/0.66  thf('139', plain,
% 0.45/0.66      (![X14 : $i]:
% 0.45/0.66         (((sk_B @ X14) != (sk_C_1 @ X14))
% 0.45/0.66          | (v2_funct_1 @ X14)
% 0.45/0.66          | ~ (v1_funct_1 @ X14)
% 0.45/0.66          | ~ (v1_relat_1 @ X14))),
% 0.45/0.66      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.45/0.66  thf('140', plain,
% 0.45/0.66      ((((sk_B @ sk_A) != (sk_B @ sk_A))
% 0.45/0.66        | ~ (v1_relat_1 @ sk_A)
% 0.45/0.66        | ~ (v1_funct_1 @ sk_A)
% 0.45/0.66        | (v2_funct_1 @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['138', '139'])).
% 0.45/0.66  thf('141', plain, ((v1_relat_1 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('142', plain, ((v1_funct_1 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('143', plain, ((((sk_B @ sk_A) != (sk_B @ sk_A)) | (v2_funct_1 @ sk_A))),
% 0.45/0.66      inference('demod', [status(thm)], ['140', '141', '142'])).
% 0.45/0.66  thf('144', plain, ((v2_funct_1 @ sk_A)),
% 0.45/0.66      inference('simplify', [status(thm)], ['143'])).
% 0.45/0.66  thf('145', plain, ($false), inference('demod', [status(thm)], ['19', '144'])).
% 0.45/0.66  
% 0.45/0.66  % SZS output end Refutation
% 0.45/0.66  
% 0.45/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
