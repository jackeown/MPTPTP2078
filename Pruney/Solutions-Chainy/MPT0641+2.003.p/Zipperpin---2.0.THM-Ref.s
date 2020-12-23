%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.C526ek3vVA

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:12 EST 2020

% Result     : Theorem 0.84s
% Output     : Refutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :  282 (4991 expanded)
%              Number of leaves         :   25 (1381 expanded)
%              Depth                    :   51
%              Number of atoms          : 2923 (70747 expanded)
%              Number of equality atoms :  125 (3160 expanded)
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

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('41',plain,(
    ! [X5: $i] :
      ( ( ( k10_relat_1 @ X5 @ ( k2_relat_1 @ X5 ) )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('42',plain,
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

thf('43',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) )
        = ( k10_relat_1 @ X7 @ ( k1_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

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

thf('44',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X20 @ X21 ) @ X22 )
        = ( k1_funct_1 @ X21 @ ( k1_funct_1 @ X20 @ X22 ) ) )
      | ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ ( k5_relat_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ sk_B_1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ sk_A ) @ X1 )
        = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ sk_B_1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ sk_A ) @ X1 )
        = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
        = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['41','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
        = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('56',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) )
    = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['40','55'])).

thf('57',plain,
    ( ( sk_C_1 @ sk_A )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('58',plain,(
    ! [X15: $i] :
      ( ( ( k1_funct_1 @ X15 @ ( sk_B @ X15 ) )
        = ( k1_funct_1 @ X15 @ ( sk_C_1 @ X15 ) ) )
      | ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('59',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('60',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
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

thf('62',plain,(
    ! [X9: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X9 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X9 @ X14 ) @ ( k2_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) ) @ ( k2_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['59','66'])).

thf('68',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( X12
        = ( k1_funct_1 @ X9 @ ( sk_D_1 @ X12 @ X9 ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('69',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) )
      = ( k1_funct_1 @ sk_A @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) )
    = ( k1_funct_1 @ sk_A @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) )
      = ( k1_funct_1 @ sk_A @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['58','72'])).

thf('74',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X15: $i] :
      ( ( r2_hidden @ ( sk_B @ X15 ) @ ( k1_relat_1 @ X15 ) )
      | ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('76',plain,
    ( ( r2_hidden @ ( sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( r2_hidden @ ( sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','18'])).

thf('81',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('83',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k2_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( X12
        = ( k1_funct_1 @ X9 @ ( sk_D_1 @ X12 @ X9 ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('85',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
      = ( k1_funct_1 @ sk_A @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
    = ( k1_funct_1 @ sk_A @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) )
      = ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['73','88','89','90'])).

thf('92',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','18'])).

thf('93',plain,
    ( ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) )
    = ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) )
    = ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57','93'])).

thf('95',plain,(
    ! [X5: $i] :
      ( ( ( k10_relat_1 @ X5 @ ( k2_relat_1 @ X5 ) )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('96',plain,(
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

thf('97',plain,(
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

thf('98',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('99',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('100',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('101',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k2_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('102',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( r2_hidden @ ( sk_D_1 @ X12 @ X9 ) @ ( k1_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('103',plain,
    ( ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['103','104','105','106'])).

thf('108',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( r2_hidden @ ( sk_D_1 @ X12 @ X9 ) @ ( k1_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('109',plain,
    ( ( r2_hidden @ ( sk_D_1 @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('114',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('115',plain,(
    ! [X5: $i] :
      ( ( ( k10_relat_1 @ X5 @ ( k2_relat_1 @ X5 ) )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('116',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) )
        = ( k10_relat_1 @ X7 @ ( k1_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('118',plain,(
    ! [X9: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X9 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X9 @ X14 ) @ ( k2_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ sk_B_1 ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k5_relat_1 @ X0 @ sk_A ) @ X1 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['116','119'])).

thf('121',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ sk_B_1 ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k5_relat_1 @ X0 @ sk_A ) @ X1 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ( r2_hidden @ ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['115','122'])).

thf('124',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['114','126'])).

thf('128',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['127','128','129','130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['113','132'])).

thf('134',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['133','134','135'])).

thf('137',plain,(
    r2_hidden @ ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) @ sk_B_1 ) ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['112','136'])).

thf('138',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
        = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('140',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) @ sk_B_1 ) )
    = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['103','104','105','106'])).

thf('142',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( X12
        = ( k1_funct_1 @ X9 @ ( sk_D_1 @ X12 @ X9 ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('143',plain,
    ( ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A )
      = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['143','144','145'])).

thf('147',plain,
    ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
    = ( k1_funct_1 @ sk_A @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('148',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) @ sk_B_1 ) )
    = ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['140','146','147'])).

thf('149',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['137','148'])).

thf('150',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( r2_hidden @ ( sk_D_1 @ X12 @ X9 ) @ ( k1_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('151',plain,
    ( ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['100','151'])).

thf('153',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['152','153','154','155','156'])).

thf('158',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['99','157'])).

thf('159',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['158','159','160'])).

thf('162',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X20 @ X21 ) @ X22 )
        = ( k1_funct_1 @ X21 @ ( k1_funct_1 @ X20 @ X22 ) ) )
      | ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ ( k5_relat_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_1])).

thf('163',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
      = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
    = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['163','164','165','166','167'])).

thf('169',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('170',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('171',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['137','148'])).

thf('172',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( X12
        = ( k1_funct_1 @ X9 @ ( sk_D_1 @ X12 @ X9 ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('173',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
      = ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
    = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['163','164','165','166','167'])).

thf('175',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
      = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ) )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('176',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
    | ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
      = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['170','175'])).

thf('177',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
    | ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
      = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['176','177','178','179','180'])).

thf('182',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
      = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['169','181'])).

thf('183',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
    = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['182','183','184'])).

thf('186',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
    = ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['168','185'])).

thf('187',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) )
        = ( k10_relat_1 @ X7 @ ( k1_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('188',plain,(
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

thf('189',plain,(
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
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,(
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
    inference('sup-',[status(thm)],['186','189'])).

thf('191',plain,(
    v2_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) )
        = ( k10_relat_1 @ X7 @ ( k1_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('196',plain,(
    r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['158','159','160'])).

thf('197',plain,
    ( ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) @ ( k10_relat_1 @ sk_B_1 @ ( k1_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['195','196'])).

thf('198',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) @ ( k10_relat_1 @ sk_B_1 @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['197','198','199','200'])).

thf('202',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
        = X0 )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['190','191','192','193','194','201'])).

thf('203',plain,(
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
    inference('sup-',[status(thm)],['98','202'])).

thf('204',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
        = X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['203','204','205','206','207'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['97','208'])).

thf('210',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['209','210','211'])).

thf('213',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k10_relat_1 @ sk_B_1 @ ( k1_relat_1 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_A )
      | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
        = X0 )
      | ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['96','212'])).

thf('214',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k10_relat_1 @ sk_B_1 @ ( k2_relat_1 @ sk_B_1 ) ) )
      | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
        = X0 )
      | ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['213','214','215','216'])).

thf('218',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['95','217'])).

thf('219',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['218','219'])).

thf('221',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
     != ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      = ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) )
    | ~ ( r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['94','220'])).

thf('222',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('223',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
     != ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      = ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['221','222'])).

thf('224',plain,
    ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
    = ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['223'])).

thf('225',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('226',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( r2_hidden @ ( sk_D_1 @ X12 @ X9 ) @ ( k1_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('227',plain,
    ( ( r2_hidden @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['225','226'])).

thf('228',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['227','228','229'])).

thf('231',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
        = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('232',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) )
    = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['230','231'])).

thf('233',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('234',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( X12
        = ( k1_funct_1 @ X9 @ ( sk_D_1 @ X12 @ X9 ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('235',plain,
    ( ( ( sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['233','234'])).

thf('236',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,
    ( ( sk_B @ sk_A )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['235','236','237'])).

thf('239',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) )
    = ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['232','238'])).

thf('240',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['218','219'])).

thf('241',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
     != ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      = ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) )
    | ~ ( r2_hidden @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['239','240'])).

thf('242',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['227','228','229'])).

thf('243',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
     != ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      = ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['241','242'])).

thf('244',plain,
    ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
    = ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['243'])).

thf('245',plain,
    ( ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 )
    = ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['224','244'])).

thf('246',plain,
    ( ( sk_C_1 @ sk_A )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['33','245'])).

thf('247',plain,
    ( ( sk_B @ sk_A )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['235','236','237'])).

thf('248',plain,
    ( ( sk_B @ sk_A )
    = ( sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['246','247'])).

thf('249',plain,(
    ! [X15: $i] :
      ( ( ( sk_B @ X15 )
       != ( sk_C_1 @ X15 ) )
      | ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('250',plain,
    ( ( ( sk_B @ sk_A )
     != ( sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['248','249'])).

thf('251',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,
    ( ( ( sk_B @ sk_A )
     != ( sk_B @ sk_A ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['250','251','252'])).

thf('254',plain,(
    v2_funct_1 @ sk_A ),
    inference(simplify,[status(thm)],['253'])).

thf('255',plain,(
    $false ),
    inference(demod,[status(thm)],['19','254'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.C526ek3vVA
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:02:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.84/1.04  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.84/1.04  % Solved by: fo/fo7.sh
% 0.84/1.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.84/1.04  % done 544 iterations in 0.589s
% 0.84/1.04  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.84/1.04  % SZS output start Refutation
% 0.84/1.04  thf(sk_A_type, type, sk_A: $i).
% 0.84/1.04  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.84/1.04  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.84/1.04  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.84/1.04  thf(sk_B_type, type, sk_B: $i > $i).
% 0.84/1.04  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.84/1.04  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.84/1.04  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.84/1.04  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.84/1.04  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.84/1.04  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.84/1.04  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.84/1.04  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.84/1.04  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.84/1.04  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.84/1.04  thf(t48_funct_1, conjecture,
% 0.84/1.04    (![A:$i]:
% 0.84/1.04     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.84/1.04       ( ![B:$i]:
% 0.84/1.04         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.84/1.04           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.84/1.04               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.84/1.04             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.84/1.04  thf(zf_stmt_0, negated_conjecture,
% 0.84/1.04    (~( ![A:$i]:
% 0.84/1.04        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.84/1.04          ( ![B:$i]:
% 0.84/1.04            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.84/1.04              ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.84/1.04                  ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.84/1.04                ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ) )),
% 0.84/1.04    inference('cnf.neg', [status(esa)], [t48_funct_1])).
% 0.84/1.04  thf('0', plain, ((~ (v2_funct_1 @ sk_B_1) | ~ (v2_funct_1 @ sk_A))),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('1', plain, ((~ (v2_funct_1 @ sk_A)) <= (~ ((v2_funct_1 @ sk_A)))),
% 0.84/1.04      inference('split', [status(esa)], ['0'])).
% 0.84/1.04  thf(d10_xboole_0, axiom,
% 0.84/1.04    (![A:$i,B:$i]:
% 0.84/1.04     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.84/1.04  thf('2', plain,
% 0.84/1.04      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.84/1.04      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.84/1.04  thf('3', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.84/1.04      inference('simplify', [status(thm)], ['2'])).
% 0.84/1.04  thf('4', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf(t47_funct_1, axiom,
% 0.84/1.04    (![A:$i]:
% 0.84/1.04     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.84/1.04       ( ![B:$i]:
% 0.84/1.04         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.84/1.04           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.84/1.04               ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) =>
% 0.84/1.04             ( v2_funct_1 @ B ) ) ) ) ))).
% 0.84/1.04  thf('5', plain,
% 0.84/1.04      (![X23 : $i, X24 : $i]:
% 0.84/1.04         (~ (v1_relat_1 @ X23)
% 0.84/1.04          | ~ (v1_funct_1 @ X23)
% 0.84/1.04          | (v2_funct_1 @ X23)
% 0.84/1.04          | ~ (r1_tarski @ (k2_relat_1 @ X23) @ (k1_relat_1 @ X24))
% 0.84/1.04          | ~ (v2_funct_1 @ (k5_relat_1 @ X23 @ X24))
% 0.84/1.04          | ~ (v1_funct_1 @ X24)
% 0.84/1.04          | ~ (v1_relat_1 @ X24))),
% 0.84/1.04      inference('cnf', [status(esa)], [t47_funct_1])).
% 0.84/1.04  thf('6', plain,
% 0.84/1.04      (![X0 : $i]:
% 0.84/1.04         (~ (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ sk_B_1))
% 0.84/1.04          | ~ (v1_relat_1 @ sk_A)
% 0.84/1.04          | ~ (v1_funct_1 @ sk_A)
% 0.84/1.04          | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_A))
% 0.84/1.04          | (v2_funct_1 @ X0)
% 0.84/1.04          | ~ (v1_funct_1 @ X0)
% 0.84/1.04          | ~ (v1_relat_1 @ X0))),
% 0.84/1.04      inference('sup-', [status(thm)], ['4', '5'])).
% 0.84/1.04  thf('7', plain, ((v1_relat_1 @ sk_A)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('8', plain, ((v1_funct_1 @ sk_A)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('9', plain,
% 0.84/1.04      (![X0 : $i]:
% 0.84/1.04         (~ (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ sk_B_1))
% 0.84/1.04          | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_A))
% 0.84/1.04          | (v2_funct_1 @ X0)
% 0.84/1.04          | ~ (v1_funct_1 @ X0)
% 0.84/1.04          | ~ (v1_relat_1 @ X0))),
% 0.84/1.04      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.84/1.04  thf('10', plain,
% 0.84/1.04      ((~ (v1_relat_1 @ sk_B_1)
% 0.84/1.04        | ~ (v1_funct_1 @ sk_B_1)
% 0.84/1.04        | (v2_funct_1 @ sk_B_1)
% 0.84/1.04        | ~ (v2_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.84/1.04      inference('sup-', [status(thm)], ['3', '9'])).
% 0.84/1.04  thf('11', plain, ((v1_relat_1 @ sk_B_1)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('12', plain, ((v1_funct_1 @ sk_B_1)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('13', plain, ((v2_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('14', plain, ((v2_funct_1 @ sk_B_1)),
% 0.84/1.04      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.84/1.04  thf('15', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.84/1.04      inference('split', [status(esa)], ['0'])).
% 0.84/1.04  thf('16', plain, (((v2_funct_1 @ sk_B_1))),
% 0.84/1.04      inference('sup-', [status(thm)], ['14', '15'])).
% 0.84/1.04  thf('17', plain, (~ ((v2_funct_1 @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.84/1.04      inference('split', [status(esa)], ['0'])).
% 0.84/1.04  thf('18', plain, (~ ((v2_funct_1 @ sk_A))),
% 0.84/1.04      inference('sat_resolution*', [status(thm)], ['16', '17'])).
% 0.84/1.04  thf('19', plain, (~ (v2_funct_1 @ sk_A)),
% 0.84/1.04      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.84/1.04  thf('20', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf(d8_funct_1, axiom,
% 0.84/1.04    (![A:$i]:
% 0.84/1.04     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.84/1.04       ( ( v2_funct_1 @ A ) <=>
% 0.84/1.04         ( ![B:$i,C:$i]:
% 0.84/1.04           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.84/1.04               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.84/1.04               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.84/1.04             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.84/1.04  thf('21', plain,
% 0.84/1.04      (![X15 : $i]:
% 0.84/1.04         ((r2_hidden @ (sk_C_1 @ X15) @ (k1_relat_1 @ X15))
% 0.84/1.04          | (v2_funct_1 @ X15)
% 0.84/1.04          | ~ (v1_funct_1 @ X15)
% 0.84/1.04          | ~ (v1_relat_1 @ X15))),
% 0.84/1.04      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.84/1.04  thf('22', plain,
% 0.84/1.04      (((r2_hidden @ (sk_C_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))
% 0.84/1.04        | ~ (v1_relat_1 @ sk_A)
% 0.84/1.04        | ~ (v1_funct_1 @ sk_A)
% 0.84/1.04        | (v2_funct_1 @ sk_A))),
% 0.84/1.04      inference('sup+', [status(thm)], ['20', '21'])).
% 0.84/1.04  thf('23', plain, ((v1_relat_1 @ sk_A)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('24', plain, ((v1_funct_1 @ sk_A)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('25', plain,
% 0.84/1.04      (((r2_hidden @ (sk_C_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))
% 0.84/1.04        | (v2_funct_1 @ sk_A))),
% 0.84/1.04      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.84/1.04  thf('26', plain, (~ (v2_funct_1 @ sk_A)),
% 0.84/1.04      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.84/1.04  thf('27', plain, ((r2_hidden @ (sk_C_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 0.84/1.04      inference('clc', [status(thm)], ['25', '26'])).
% 0.84/1.04  thf(d5_funct_1, axiom,
% 0.84/1.04    (![A:$i]:
% 0.84/1.04     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.84/1.04       ( ![B:$i]:
% 0.84/1.04         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.84/1.04           ( ![C:$i]:
% 0.84/1.04             ( ( r2_hidden @ C @ B ) <=>
% 0.84/1.04               ( ?[D:$i]:
% 0.84/1.04                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.84/1.04                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.84/1.04  thf('28', plain,
% 0.84/1.04      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.84/1.04         (((X11) != (k2_relat_1 @ X9))
% 0.84/1.04          | ((X12) = (k1_funct_1 @ X9 @ (sk_D_1 @ X12 @ X9)))
% 0.84/1.04          | ~ (r2_hidden @ X12 @ X11)
% 0.84/1.04          | ~ (v1_funct_1 @ X9)
% 0.84/1.04          | ~ (v1_relat_1 @ X9))),
% 0.84/1.04      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.84/1.04  thf('29', plain,
% 0.84/1.04      (![X9 : $i, X12 : $i]:
% 0.84/1.04         (~ (v1_relat_1 @ X9)
% 0.84/1.04          | ~ (v1_funct_1 @ X9)
% 0.84/1.04          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 0.84/1.04          | ((X12) = (k1_funct_1 @ X9 @ (sk_D_1 @ X12 @ X9))))),
% 0.84/1.04      inference('simplify', [status(thm)], ['28'])).
% 0.84/1.04  thf('30', plain,
% 0.84/1.04      ((((sk_C_1 @ sk_A)
% 0.84/1.04          = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1)))
% 0.84/1.04        | ~ (v1_funct_1 @ sk_B_1)
% 0.84/1.04        | ~ (v1_relat_1 @ sk_B_1))),
% 0.84/1.04      inference('sup-', [status(thm)], ['27', '29'])).
% 0.84/1.04  thf('31', plain, ((v1_funct_1 @ sk_B_1)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('32', plain, ((v1_relat_1 @ sk_B_1)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('33', plain,
% 0.84/1.04      (((sk_C_1 @ sk_A)
% 0.84/1.04         = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1)))),
% 0.84/1.04      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.84/1.04  thf('34', plain, ((r2_hidden @ (sk_C_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 0.84/1.04      inference('clc', [status(thm)], ['25', '26'])).
% 0.84/1.04  thf('35', plain,
% 0.84/1.04      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.84/1.04         (((X11) != (k2_relat_1 @ X9))
% 0.84/1.04          | (r2_hidden @ (sk_D_1 @ X12 @ X9) @ (k1_relat_1 @ X9))
% 0.84/1.04          | ~ (r2_hidden @ X12 @ X11)
% 0.84/1.04          | ~ (v1_funct_1 @ X9)
% 0.84/1.04          | ~ (v1_relat_1 @ X9))),
% 0.84/1.04      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.84/1.04  thf('36', plain,
% 0.84/1.04      (![X9 : $i, X12 : $i]:
% 0.84/1.04         (~ (v1_relat_1 @ X9)
% 0.84/1.04          | ~ (v1_funct_1 @ X9)
% 0.84/1.04          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 0.84/1.04          | (r2_hidden @ (sk_D_1 @ X12 @ X9) @ (k1_relat_1 @ X9)))),
% 0.84/1.04      inference('simplify', [status(thm)], ['35'])).
% 0.84/1.04  thf('37', plain,
% 0.84/1.04      (((r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1) @ 
% 0.84/1.04         (k1_relat_1 @ sk_B_1))
% 0.84/1.04        | ~ (v1_funct_1 @ sk_B_1)
% 0.84/1.04        | ~ (v1_relat_1 @ sk_B_1))),
% 0.84/1.04      inference('sup-', [status(thm)], ['34', '36'])).
% 0.84/1.04  thf('38', plain, ((v1_funct_1 @ sk_B_1)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('39', plain, ((v1_relat_1 @ sk_B_1)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('40', plain,
% 0.84/1.05      ((r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1) @ (k1_relat_1 @ sk_B_1))),
% 0.84/1.05      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.84/1.05  thf(t169_relat_1, axiom,
% 0.84/1.05    (![A:$i]:
% 0.84/1.05     ( ( v1_relat_1 @ A ) =>
% 0.84/1.05       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.84/1.05  thf('41', plain,
% 0.84/1.05      (![X5 : $i]:
% 0.84/1.05         (((k10_relat_1 @ X5 @ (k2_relat_1 @ X5)) = (k1_relat_1 @ X5))
% 0.84/1.05          | ~ (v1_relat_1 @ X5))),
% 0.84/1.05      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.84/1.05  thf('42', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf(t182_relat_1, axiom,
% 0.84/1.05    (![A:$i]:
% 0.84/1.05     ( ( v1_relat_1 @ A ) =>
% 0.84/1.05       ( ![B:$i]:
% 0.84/1.05         ( ( v1_relat_1 @ B ) =>
% 0.84/1.05           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.84/1.05             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.84/1.05  thf('43', plain,
% 0.84/1.05      (![X6 : $i, X7 : $i]:
% 0.84/1.05         (~ (v1_relat_1 @ X6)
% 0.84/1.05          | ((k1_relat_1 @ (k5_relat_1 @ X7 @ X6))
% 0.84/1.05              = (k10_relat_1 @ X7 @ (k1_relat_1 @ X6)))
% 0.84/1.05          | ~ (v1_relat_1 @ X7))),
% 0.84/1.05      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.84/1.05  thf(t22_funct_1, axiom,
% 0.84/1.05    (![A:$i,B:$i]:
% 0.84/1.05     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.84/1.05       ( ![C:$i]:
% 0.84/1.05         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.84/1.05           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) =>
% 0.84/1.05             ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A ) =
% 0.84/1.05               ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) ))).
% 0.84/1.05  thf('44', plain,
% 0.84/1.05      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.84/1.05         (~ (v1_relat_1 @ X20)
% 0.84/1.05          | ~ (v1_funct_1 @ X20)
% 0.84/1.05          | ((k1_funct_1 @ (k5_relat_1 @ X20 @ X21) @ X22)
% 0.84/1.05              = (k1_funct_1 @ X21 @ (k1_funct_1 @ X20 @ X22)))
% 0.84/1.05          | ~ (r2_hidden @ X22 @ (k1_relat_1 @ (k5_relat_1 @ X20 @ X21)))
% 0.84/1.05          | ~ (v1_funct_1 @ X21)
% 0.84/1.05          | ~ (v1_relat_1 @ X21))),
% 0.84/1.05      inference('cnf', [status(esa)], [t22_funct_1])).
% 0.84/1.05  thf('45', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.05         (~ (r2_hidden @ X2 @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.84/1.05          | ~ (v1_relat_1 @ X1)
% 0.84/1.05          | ~ (v1_relat_1 @ X0)
% 0.84/1.05          | ~ (v1_relat_1 @ X0)
% 0.84/1.05          | ~ (v1_funct_1 @ X0)
% 0.84/1.05          | ((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.84/1.05              = (k1_funct_1 @ X0 @ (k1_funct_1 @ X1 @ X2)))
% 0.84/1.05          | ~ (v1_funct_1 @ X1)
% 0.84/1.05          | ~ (v1_relat_1 @ X1))),
% 0.84/1.05      inference('sup-', [status(thm)], ['43', '44'])).
% 0.84/1.05  thf('46', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.05         (~ (v1_funct_1 @ X1)
% 0.84/1.05          | ((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.84/1.05              = (k1_funct_1 @ X0 @ (k1_funct_1 @ X1 @ X2)))
% 0.84/1.05          | ~ (v1_funct_1 @ X0)
% 0.84/1.05          | ~ (v1_relat_1 @ X0)
% 0.84/1.05          | ~ (v1_relat_1 @ X1)
% 0.84/1.05          | ~ (r2_hidden @ X2 @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0))))),
% 0.84/1.05      inference('simplify', [status(thm)], ['45'])).
% 0.84/1.05  thf('47', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         (~ (r2_hidden @ X1 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ sk_B_1)))
% 0.84/1.05          | ~ (v1_relat_1 @ X0)
% 0.84/1.05          | ~ (v1_relat_1 @ sk_A)
% 0.84/1.05          | ~ (v1_funct_1 @ sk_A)
% 0.84/1.05          | ((k1_funct_1 @ (k5_relat_1 @ X0 @ sk_A) @ X1)
% 0.84/1.05              = (k1_funct_1 @ sk_A @ (k1_funct_1 @ X0 @ X1)))
% 0.84/1.05          | ~ (v1_funct_1 @ X0))),
% 0.84/1.05      inference('sup-', [status(thm)], ['42', '46'])).
% 0.84/1.05  thf('48', plain, ((v1_relat_1 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('49', plain, ((v1_funct_1 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('50', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         (~ (r2_hidden @ X1 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ sk_B_1)))
% 0.84/1.05          | ~ (v1_relat_1 @ X0)
% 0.84/1.05          | ((k1_funct_1 @ (k5_relat_1 @ X0 @ sk_A) @ X1)
% 0.84/1.05              = (k1_funct_1 @ sk_A @ (k1_funct_1 @ X0 @ X1)))
% 0.84/1.05          | ~ (v1_funct_1 @ X0))),
% 0.84/1.05      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.84/1.05  thf('51', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.84/1.05          | ~ (v1_relat_1 @ sk_B_1)
% 0.84/1.05          | ~ (v1_funct_1 @ sk_B_1)
% 0.84/1.05          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.84/1.05              = (k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B_1 @ X0)))
% 0.84/1.05          | ~ (v1_relat_1 @ sk_B_1))),
% 0.84/1.05      inference('sup-', [status(thm)], ['41', '50'])).
% 0.84/1.05  thf('52', plain, ((v1_relat_1 @ sk_B_1)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('53', plain, ((v1_funct_1 @ sk_B_1)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('54', plain, ((v1_relat_1 @ sk_B_1)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('55', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.84/1.05          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.84/1.05              = (k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B_1 @ X0))))),
% 0.84/1.05      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 0.84/1.05  thf('56', plain,
% 0.84/1.05      (((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.84/1.05         (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1))
% 0.84/1.05         = (k1_funct_1 @ sk_A @ 
% 0.84/1.05            (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1))))),
% 0.84/1.05      inference('sup-', [status(thm)], ['40', '55'])).
% 0.84/1.05  thf('57', plain,
% 0.84/1.05      (((sk_C_1 @ sk_A)
% 0.84/1.05         = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1)))),
% 0.84/1.05      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.84/1.05  thf('58', plain,
% 0.84/1.05      (![X15 : $i]:
% 0.84/1.05         (((k1_funct_1 @ X15 @ (sk_B @ X15))
% 0.84/1.05            = (k1_funct_1 @ X15 @ (sk_C_1 @ X15)))
% 0.84/1.05          | (v2_funct_1 @ X15)
% 0.84/1.05          | ~ (v1_funct_1 @ X15)
% 0.84/1.05          | ~ (v1_relat_1 @ X15))),
% 0.84/1.05      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.84/1.05  thf('59', plain, ((r2_hidden @ (sk_C_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 0.84/1.05      inference('clc', [status(thm)], ['25', '26'])).
% 0.84/1.05  thf('60', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('61', plain,
% 0.84/1.05      (![X9 : $i, X11 : $i, X13 : $i, X14 : $i]:
% 0.84/1.05         (((X11) != (k2_relat_1 @ X9))
% 0.84/1.05          | (r2_hidden @ X13 @ X11)
% 0.84/1.05          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X9))
% 0.84/1.05          | ((X13) != (k1_funct_1 @ X9 @ X14))
% 0.84/1.05          | ~ (v1_funct_1 @ X9)
% 0.84/1.05          | ~ (v1_relat_1 @ X9))),
% 0.84/1.05      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.84/1.05  thf('62', plain,
% 0.84/1.05      (![X9 : $i, X14 : $i]:
% 0.84/1.05         (~ (v1_relat_1 @ X9)
% 0.84/1.05          | ~ (v1_funct_1 @ X9)
% 0.84/1.05          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X9))
% 0.84/1.05          | (r2_hidden @ (k1_funct_1 @ X9 @ X14) @ (k2_relat_1 @ X9)))),
% 0.84/1.05      inference('simplify', [status(thm)], ['61'])).
% 0.84/1.05  thf('63', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B_1))
% 0.84/1.05          | (r2_hidden @ (k1_funct_1 @ sk_A @ X0) @ (k2_relat_1 @ sk_A))
% 0.84/1.05          | ~ (v1_funct_1 @ sk_A)
% 0.84/1.05          | ~ (v1_relat_1 @ sk_A))),
% 0.84/1.05      inference('sup-', [status(thm)], ['60', '62'])).
% 0.84/1.05  thf('64', plain, ((v1_funct_1 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('65', plain, ((v1_relat_1 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('66', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B_1))
% 0.84/1.05          | (r2_hidden @ (k1_funct_1 @ sk_A @ X0) @ (k2_relat_1 @ sk_A)))),
% 0.84/1.05      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.84/1.05  thf('67', plain,
% 0.84/1.05      ((r2_hidden @ (k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A)) @ (k2_relat_1 @ sk_A))),
% 0.84/1.05      inference('sup-', [status(thm)], ['59', '66'])).
% 0.84/1.05  thf('68', plain,
% 0.84/1.05      (![X9 : $i, X12 : $i]:
% 0.84/1.05         (~ (v1_relat_1 @ X9)
% 0.84/1.05          | ~ (v1_funct_1 @ X9)
% 0.84/1.05          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 0.84/1.05          | ((X12) = (k1_funct_1 @ X9 @ (sk_D_1 @ X12 @ X9))))),
% 0.84/1.05      inference('simplify', [status(thm)], ['28'])).
% 0.84/1.05  thf('69', plain,
% 0.84/1.05      ((((k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A))
% 0.84/1.05          = (k1_funct_1 @ sk_A @ 
% 0.84/1.05             (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A)) @ sk_A)))
% 0.84/1.05        | ~ (v1_funct_1 @ sk_A)
% 0.84/1.05        | ~ (v1_relat_1 @ sk_A))),
% 0.84/1.05      inference('sup-', [status(thm)], ['67', '68'])).
% 0.84/1.05  thf('70', plain, ((v1_funct_1 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('71', plain, ((v1_relat_1 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('72', plain,
% 0.84/1.05      (((k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A))
% 0.84/1.05         = (k1_funct_1 @ sk_A @ 
% 0.84/1.05            (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A)) @ sk_A)))),
% 0.84/1.05      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.84/1.05  thf('73', plain,
% 0.84/1.05      ((((k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A))
% 0.84/1.05          = (k1_funct_1 @ sk_A @ 
% 0.84/1.05             (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A)))
% 0.84/1.05        | ~ (v1_relat_1 @ sk_A)
% 0.84/1.05        | ~ (v1_funct_1 @ sk_A)
% 0.84/1.05        | (v2_funct_1 @ sk_A))),
% 0.84/1.05      inference('sup+', [status(thm)], ['58', '72'])).
% 0.84/1.05  thf('74', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('75', plain,
% 0.84/1.05      (![X15 : $i]:
% 0.84/1.05         ((r2_hidden @ (sk_B @ X15) @ (k1_relat_1 @ X15))
% 0.84/1.05          | (v2_funct_1 @ X15)
% 0.84/1.05          | ~ (v1_funct_1 @ X15)
% 0.84/1.05          | ~ (v1_relat_1 @ X15))),
% 0.84/1.05      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.84/1.05  thf('76', plain,
% 0.84/1.05      (((r2_hidden @ (sk_B @ sk_A) @ (k2_relat_1 @ sk_B_1))
% 0.84/1.05        | ~ (v1_relat_1 @ sk_A)
% 0.84/1.05        | ~ (v1_funct_1 @ sk_A)
% 0.84/1.05        | (v2_funct_1 @ sk_A))),
% 0.84/1.05      inference('sup+', [status(thm)], ['74', '75'])).
% 0.84/1.05  thf('77', plain, ((v1_relat_1 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('78', plain, ((v1_funct_1 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('79', plain,
% 0.84/1.05      (((r2_hidden @ (sk_B @ sk_A) @ (k2_relat_1 @ sk_B_1))
% 0.84/1.05        | (v2_funct_1 @ sk_A))),
% 0.84/1.05      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.84/1.05  thf('80', plain, (~ (v2_funct_1 @ sk_A)),
% 0.84/1.05      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.84/1.05  thf('81', plain, ((r2_hidden @ (sk_B @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 0.84/1.05      inference('clc', [status(thm)], ['79', '80'])).
% 0.84/1.05  thf('82', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B_1))
% 0.84/1.05          | (r2_hidden @ (k1_funct_1 @ sk_A @ X0) @ (k2_relat_1 @ sk_A)))),
% 0.84/1.05      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.84/1.05  thf('83', plain,
% 0.84/1.05      ((r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ (k2_relat_1 @ sk_A))),
% 0.84/1.05      inference('sup-', [status(thm)], ['81', '82'])).
% 0.84/1.05  thf('84', plain,
% 0.84/1.05      (![X9 : $i, X12 : $i]:
% 0.84/1.05         (~ (v1_relat_1 @ X9)
% 0.84/1.05          | ~ (v1_funct_1 @ X9)
% 0.84/1.05          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 0.84/1.05          | ((X12) = (k1_funct_1 @ X9 @ (sk_D_1 @ X12 @ X9))))),
% 0.84/1.05      inference('simplify', [status(thm)], ['28'])).
% 0.84/1.05  thf('85', plain,
% 0.84/1.05      ((((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.84/1.05          = (k1_funct_1 @ sk_A @ 
% 0.84/1.05             (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A)))
% 0.84/1.05        | ~ (v1_funct_1 @ sk_A)
% 0.84/1.05        | ~ (v1_relat_1 @ sk_A))),
% 0.84/1.05      inference('sup-', [status(thm)], ['83', '84'])).
% 0.84/1.05  thf('86', plain, ((v1_funct_1 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('87', plain, ((v1_relat_1 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('88', plain,
% 0.84/1.05      (((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.84/1.05         = (k1_funct_1 @ sk_A @ 
% 0.84/1.05            (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A)))),
% 0.84/1.05      inference('demod', [status(thm)], ['85', '86', '87'])).
% 0.84/1.05  thf('89', plain, ((v1_relat_1 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('90', plain, ((v1_funct_1 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('91', plain,
% 0.84/1.05      ((((k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A))
% 0.84/1.05          = (k1_funct_1 @ sk_A @ (sk_B @ sk_A)))
% 0.84/1.05        | (v2_funct_1 @ sk_A))),
% 0.84/1.05      inference('demod', [status(thm)], ['73', '88', '89', '90'])).
% 0.84/1.05  thf('92', plain, (~ (v2_funct_1 @ sk_A)),
% 0.84/1.05      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.84/1.05  thf('93', plain,
% 0.84/1.05      (((k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A))
% 0.84/1.05         = (k1_funct_1 @ sk_A @ (sk_B @ sk_A)))),
% 0.84/1.05      inference('clc', [status(thm)], ['91', '92'])).
% 0.84/1.05  thf('94', plain,
% 0.84/1.05      (((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.84/1.05         (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1))
% 0.84/1.05         = (k1_funct_1 @ sk_A @ (sk_B @ sk_A)))),
% 0.84/1.05      inference('demod', [status(thm)], ['56', '57', '93'])).
% 0.84/1.05  thf('95', plain,
% 0.84/1.05      (![X5 : $i]:
% 0.84/1.05         (((k10_relat_1 @ X5 @ (k2_relat_1 @ X5)) = (k1_relat_1 @ X5))
% 0.84/1.05          | ~ (v1_relat_1 @ X5))),
% 0.84/1.05      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.84/1.05  thf('96', plain,
% 0.84/1.05      (![X6 : $i, X7 : $i]:
% 0.84/1.05         (~ (v1_relat_1 @ X6)
% 0.84/1.05          | ((k1_relat_1 @ (k5_relat_1 @ X7 @ X6))
% 0.84/1.05              = (k10_relat_1 @ X7 @ (k1_relat_1 @ X6)))
% 0.84/1.05          | ~ (v1_relat_1 @ X7))),
% 0.84/1.05      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.84/1.05  thf(dt_k5_relat_1, axiom,
% 0.84/1.05    (![A:$i,B:$i]:
% 0.84/1.05     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.84/1.05       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.84/1.05  thf('97', plain,
% 0.84/1.05      (![X3 : $i, X4 : $i]:
% 0.84/1.05         (~ (v1_relat_1 @ X3)
% 0.84/1.05          | ~ (v1_relat_1 @ X4)
% 0.84/1.05          | (v1_relat_1 @ (k5_relat_1 @ X3 @ X4)))),
% 0.84/1.05      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.84/1.05  thf(fc2_funct_1, axiom,
% 0.84/1.05    (![A:$i,B:$i]:
% 0.84/1.05     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v1_relat_1 @ B ) & 
% 0.84/1.05         ( v1_funct_1 @ B ) ) =>
% 0.84/1.05       ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) & 
% 0.84/1.05         ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ))).
% 0.84/1.05  thf('98', plain,
% 0.84/1.05      (![X18 : $i, X19 : $i]:
% 0.84/1.05         (~ (v1_funct_1 @ X18)
% 0.84/1.05          | ~ (v1_relat_1 @ X18)
% 0.84/1.05          | ~ (v1_relat_1 @ X19)
% 0.84/1.05          | ~ (v1_funct_1 @ X19)
% 0.84/1.05          | (v1_funct_1 @ (k5_relat_1 @ X18 @ X19)))),
% 0.84/1.05      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.84/1.05  thf('99', plain,
% 0.84/1.05      (![X3 : $i, X4 : $i]:
% 0.84/1.05         (~ (v1_relat_1 @ X3)
% 0.84/1.05          | ~ (v1_relat_1 @ X4)
% 0.84/1.05          | (v1_relat_1 @ (k5_relat_1 @ X3 @ X4)))),
% 0.84/1.05      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.84/1.05  thf('100', plain,
% 0.84/1.05      (![X18 : $i, X19 : $i]:
% 0.84/1.05         (~ (v1_funct_1 @ X18)
% 0.84/1.05          | ~ (v1_relat_1 @ X18)
% 0.84/1.05          | ~ (v1_relat_1 @ X19)
% 0.84/1.05          | ~ (v1_funct_1 @ X19)
% 0.84/1.05          | (v1_funct_1 @ (k5_relat_1 @ X18 @ X19)))),
% 0.84/1.05      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.84/1.05  thf('101', plain,
% 0.84/1.05      ((r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ (k2_relat_1 @ sk_A))),
% 0.84/1.05      inference('sup-', [status(thm)], ['81', '82'])).
% 0.84/1.05  thf('102', plain,
% 0.84/1.05      (![X9 : $i, X12 : $i]:
% 0.84/1.05         (~ (v1_relat_1 @ X9)
% 0.84/1.05          | ~ (v1_funct_1 @ X9)
% 0.84/1.05          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 0.84/1.05          | (r2_hidden @ (sk_D_1 @ X12 @ X9) @ (k1_relat_1 @ X9)))),
% 0.84/1.05      inference('simplify', [status(thm)], ['35'])).
% 0.84/1.05  thf('103', plain,
% 0.84/1.05      (((r2_hidden @ (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A) @ 
% 0.84/1.05         (k1_relat_1 @ sk_A))
% 0.84/1.05        | ~ (v1_funct_1 @ sk_A)
% 0.84/1.05        | ~ (v1_relat_1 @ sk_A))),
% 0.84/1.05      inference('sup-', [status(thm)], ['101', '102'])).
% 0.84/1.05  thf('104', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('105', plain, ((v1_funct_1 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('106', plain, ((v1_relat_1 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('107', plain,
% 0.84/1.05      ((r2_hidden @ (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A) @ 
% 0.84/1.05        (k2_relat_1 @ sk_B_1))),
% 0.84/1.05      inference('demod', [status(thm)], ['103', '104', '105', '106'])).
% 0.84/1.05  thf('108', plain,
% 0.84/1.05      (![X9 : $i, X12 : $i]:
% 0.84/1.05         (~ (v1_relat_1 @ X9)
% 0.84/1.05          | ~ (v1_funct_1 @ X9)
% 0.84/1.05          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 0.84/1.05          | (r2_hidden @ (sk_D_1 @ X12 @ X9) @ (k1_relat_1 @ X9)))),
% 0.84/1.05      inference('simplify', [status(thm)], ['35'])).
% 0.84/1.05  thf('109', plain,
% 0.84/1.05      (((r2_hidden @ 
% 0.84/1.05         (sk_D_1 @ (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A) @ 
% 0.84/1.05          sk_B_1) @ 
% 0.84/1.05         (k1_relat_1 @ sk_B_1))
% 0.84/1.05        | ~ (v1_funct_1 @ sk_B_1)
% 0.84/1.05        | ~ (v1_relat_1 @ sk_B_1))),
% 0.84/1.05      inference('sup-', [status(thm)], ['107', '108'])).
% 0.84/1.05  thf('110', plain, ((v1_funct_1 @ sk_B_1)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('111', plain, ((v1_relat_1 @ sk_B_1)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('112', plain,
% 0.84/1.05      ((r2_hidden @ 
% 0.84/1.05        (sk_D_1 @ (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A) @ 
% 0.84/1.05         sk_B_1) @ 
% 0.84/1.05        (k1_relat_1 @ sk_B_1))),
% 0.84/1.05      inference('demod', [status(thm)], ['109', '110', '111'])).
% 0.84/1.05  thf('113', plain,
% 0.84/1.05      (![X3 : $i, X4 : $i]:
% 0.84/1.05         (~ (v1_relat_1 @ X3)
% 0.84/1.05          | ~ (v1_relat_1 @ X4)
% 0.84/1.05          | (v1_relat_1 @ (k5_relat_1 @ X3 @ X4)))),
% 0.84/1.05      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.84/1.05  thf('114', plain,
% 0.84/1.05      (![X18 : $i, X19 : $i]:
% 0.84/1.05         (~ (v1_funct_1 @ X18)
% 0.84/1.05          | ~ (v1_relat_1 @ X18)
% 0.84/1.05          | ~ (v1_relat_1 @ X19)
% 0.84/1.05          | ~ (v1_funct_1 @ X19)
% 0.84/1.05          | (v1_funct_1 @ (k5_relat_1 @ X18 @ X19)))),
% 0.84/1.05      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.84/1.05  thf('115', plain,
% 0.84/1.05      (![X5 : $i]:
% 0.84/1.05         (((k10_relat_1 @ X5 @ (k2_relat_1 @ X5)) = (k1_relat_1 @ X5))
% 0.84/1.05          | ~ (v1_relat_1 @ X5))),
% 0.84/1.05      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.84/1.05  thf('116', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('117', plain,
% 0.84/1.05      (![X6 : $i, X7 : $i]:
% 0.84/1.05         (~ (v1_relat_1 @ X6)
% 0.84/1.05          | ((k1_relat_1 @ (k5_relat_1 @ X7 @ X6))
% 0.84/1.05              = (k10_relat_1 @ X7 @ (k1_relat_1 @ X6)))
% 0.84/1.05          | ~ (v1_relat_1 @ X7))),
% 0.84/1.05      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.84/1.05  thf('118', plain,
% 0.84/1.05      (![X9 : $i, X14 : $i]:
% 0.84/1.05         (~ (v1_relat_1 @ X9)
% 0.84/1.05          | ~ (v1_funct_1 @ X9)
% 0.84/1.05          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X9))
% 0.84/1.05          | (r2_hidden @ (k1_funct_1 @ X9 @ X14) @ (k2_relat_1 @ X9)))),
% 0.84/1.05      inference('simplify', [status(thm)], ['61'])).
% 0.84/1.05  thf('119', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.05         (~ (r2_hidden @ X2 @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.84/1.05          | ~ (v1_relat_1 @ X1)
% 0.84/1.05          | ~ (v1_relat_1 @ X0)
% 0.84/1.05          | (r2_hidden @ (k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 0.84/1.05             (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.84/1.05          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.84/1.05          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['117', '118'])).
% 0.84/1.05  thf('120', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         (~ (r2_hidden @ X1 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ sk_B_1)))
% 0.84/1.05          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ sk_A))
% 0.84/1.05          | ~ (v1_funct_1 @ (k5_relat_1 @ X0 @ sk_A))
% 0.84/1.05          | (r2_hidden @ (k1_funct_1 @ (k5_relat_1 @ X0 @ sk_A) @ X1) @ 
% 0.84/1.05             (k2_relat_1 @ (k5_relat_1 @ X0 @ sk_A)))
% 0.84/1.05          | ~ (v1_relat_1 @ sk_A)
% 0.84/1.05          | ~ (v1_relat_1 @ X0))),
% 0.84/1.05      inference('sup-', [status(thm)], ['116', '119'])).
% 0.84/1.05  thf('121', plain, ((v1_relat_1 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('122', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         (~ (r2_hidden @ X1 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ sk_B_1)))
% 0.84/1.05          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ sk_A))
% 0.84/1.05          | ~ (v1_funct_1 @ (k5_relat_1 @ X0 @ sk_A))
% 0.84/1.05          | (r2_hidden @ (k1_funct_1 @ (k5_relat_1 @ X0 @ sk_A) @ X1) @ 
% 0.84/1.05             (k2_relat_1 @ (k5_relat_1 @ X0 @ sk_A)))
% 0.84/1.05          | ~ (v1_relat_1 @ X0))),
% 0.84/1.05      inference('demod', [status(thm)], ['120', '121'])).
% 0.84/1.05  thf('123', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.84/1.05          | ~ (v1_relat_1 @ sk_B_1)
% 0.84/1.05          | ~ (v1_relat_1 @ sk_B_1)
% 0.84/1.05          | (r2_hidden @ (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0) @ 
% 0.84/1.05             (k2_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.84/1.05          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.84/1.05          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['115', '122'])).
% 0.84/1.05  thf('124', plain, ((v1_relat_1 @ sk_B_1)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('125', plain, ((v1_relat_1 @ sk_B_1)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('126', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.84/1.05          | (r2_hidden @ (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0) @ 
% 0.84/1.05             (k2_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.84/1.05          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.84/1.05          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.84/1.05      inference('demod', [status(thm)], ['123', '124', '125'])).
% 0.84/1.05  thf('127', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         (~ (v1_funct_1 @ sk_A)
% 0.84/1.05          | ~ (v1_relat_1 @ sk_A)
% 0.84/1.05          | ~ (v1_relat_1 @ sk_B_1)
% 0.84/1.05          | ~ (v1_funct_1 @ sk_B_1)
% 0.84/1.05          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.84/1.05          | (r2_hidden @ (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0) @ 
% 0.84/1.05             (k2_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.84/1.05          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['114', '126'])).
% 0.84/1.05  thf('128', plain, ((v1_funct_1 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('129', plain, ((v1_relat_1 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('130', plain, ((v1_relat_1 @ sk_B_1)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('131', plain, ((v1_funct_1 @ sk_B_1)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('132', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         (~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.84/1.05          | (r2_hidden @ (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0) @ 
% 0.84/1.05             (k2_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.84/1.05          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1)))),
% 0.84/1.05      inference('demod', [status(thm)], ['127', '128', '129', '130', '131'])).
% 0.84/1.05  thf('133', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         (~ (v1_relat_1 @ sk_A)
% 0.84/1.05          | ~ (v1_relat_1 @ sk_B_1)
% 0.84/1.05          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.84/1.05          | (r2_hidden @ (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0) @ 
% 0.84/1.05             (k2_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))))),
% 0.84/1.05      inference('sup-', [status(thm)], ['113', '132'])).
% 0.84/1.05  thf('134', plain, ((v1_relat_1 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('135', plain, ((v1_relat_1 @ sk_B_1)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('136', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.84/1.05          | (r2_hidden @ (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0) @ 
% 0.84/1.05             (k2_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))))),
% 0.84/1.05      inference('demod', [status(thm)], ['133', '134', '135'])).
% 0.84/1.05  thf('137', plain,
% 0.84/1.05      ((r2_hidden @ 
% 0.84/1.05        (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.84/1.05         (sk_D_1 @ (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A) @ 
% 0.84/1.05          sk_B_1)) @ 
% 0.84/1.05        (k2_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['112', '136'])).
% 0.84/1.05  thf('138', plain,
% 0.84/1.05      ((r2_hidden @ 
% 0.84/1.05        (sk_D_1 @ (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A) @ 
% 0.84/1.05         sk_B_1) @ 
% 0.84/1.05        (k1_relat_1 @ sk_B_1))),
% 0.84/1.05      inference('demod', [status(thm)], ['109', '110', '111'])).
% 0.84/1.05  thf('139', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.84/1.05          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.84/1.05              = (k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B_1 @ X0))))),
% 0.84/1.05      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 0.84/1.05  thf('140', plain,
% 0.84/1.05      (((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.84/1.05         (sk_D_1 @ (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A) @ 
% 0.84/1.05          sk_B_1))
% 0.84/1.05         = (k1_funct_1 @ sk_A @ 
% 0.84/1.05            (k1_funct_1 @ sk_B_1 @ 
% 0.84/1.05             (sk_D_1 @ (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A) @ 
% 0.84/1.05              sk_B_1))))),
% 0.84/1.05      inference('sup-', [status(thm)], ['138', '139'])).
% 0.84/1.05  thf('141', plain,
% 0.84/1.05      ((r2_hidden @ (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A) @ 
% 0.84/1.05        (k2_relat_1 @ sk_B_1))),
% 0.84/1.05      inference('demod', [status(thm)], ['103', '104', '105', '106'])).
% 0.84/1.05  thf('142', plain,
% 0.84/1.05      (![X9 : $i, X12 : $i]:
% 0.84/1.05         (~ (v1_relat_1 @ X9)
% 0.84/1.05          | ~ (v1_funct_1 @ X9)
% 0.84/1.05          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 0.84/1.05          | ((X12) = (k1_funct_1 @ X9 @ (sk_D_1 @ X12 @ X9))))),
% 0.84/1.05      inference('simplify', [status(thm)], ['28'])).
% 0.84/1.05  thf('143', plain,
% 0.84/1.05      ((((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A)
% 0.84/1.05          = (k1_funct_1 @ sk_B_1 @ 
% 0.84/1.05             (sk_D_1 @ (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A) @ 
% 0.84/1.05              sk_B_1)))
% 0.84/1.05        | ~ (v1_funct_1 @ sk_B_1)
% 0.84/1.05        | ~ (v1_relat_1 @ sk_B_1))),
% 0.84/1.05      inference('sup-', [status(thm)], ['141', '142'])).
% 0.84/1.05  thf('144', plain, ((v1_funct_1 @ sk_B_1)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('145', plain, ((v1_relat_1 @ sk_B_1)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('146', plain,
% 0.84/1.05      (((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A)
% 0.84/1.05         = (k1_funct_1 @ sk_B_1 @ 
% 0.84/1.05            (sk_D_1 @ (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A) @ 
% 0.84/1.05             sk_B_1)))),
% 0.84/1.05      inference('demod', [status(thm)], ['143', '144', '145'])).
% 0.84/1.05  thf('147', plain,
% 0.84/1.05      (((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.84/1.05         = (k1_funct_1 @ sk_A @ 
% 0.84/1.05            (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A)))),
% 0.84/1.05      inference('demod', [status(thm)], ['85', '86', '87'])).
% 0.84/1.05  thf('148', plain,
% 0.84/1.05      (((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.84/1.05         (sk_D_1 @ (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A) @ 
% 0.84/1.05          sk_B_1))
% 0.84/1.05         = (k1_funct_1 @ sk_A @ (sk_B @ sk_A)))),
% 0.84/1.05      inference('demod', [status(thm)], ['140', '146', '147'])).
% 0.84/1.05  thf('149', plain,
% 0.84/1.05      ((r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05        (k2_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.84/1.05      inference('demod', [status(thm)], ['137', '148'])).
% 0.84/1.05  thf('150', plain,
% 0.84/1.05      (![X9 : $i, X12 : $i]:
% 0.84/1.05         (~ (v1_relat_1 @ X9)
% 0.84/1.05          | ~ (v1_funct_1 @ X9)
% 0.84/1.05          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 0.84/1.05          | (r2_hidden @ (sk_D_1 @ X12 @ X9) @ (k1_relat_1 @ X9)))),
% 0.84/1.05      inference('simplify', [status(thm)], ['35'])).
% 0.84/1.05  thf('151', plain,
% 0.84/1.05      (((r2_hidden @ 
% 0.84/1.05         (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05          (k5_relat_1 @ sk_B_1 @ sk_A)) @ 
% 0.84/1.05         (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.84/1.05        | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.84/1.05        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['149', '150'])).
% 0.84/1.05  thf('152', plain,
% 0.84/1.05      ((~ (v1_funct_1 @ sk_A)
% 0.84/1.05        | ~ (v1_relat_1 @ sk_A)
% 0.84/1.05        | ~ (v1_relat_1 @ sk_B_1)
% 0.84/1.05        | ~ (v1_funct_1 @ sk_B_1)
% 0.84/1.05        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.84/1.05        | (r2_hidden @ 
% 0.84/1.05           (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05            (k5_relat_1 @ sk_B_1 @ sk_A)) @ 
% 0.84/1.05           (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))))),
% 0.84/1.05      inference('sup-', [status(thm)], ['100', '151'])).
% 0.84/1.05  thf('153', plain, ((v1_funct_1 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('154', plain, ((v1_relat_1 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('155', plain, ((v1_relat_1 @ sk_B_1)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('156', plain, ((v1_funct_1 @ sk_B_1)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('157', plain,
% 0.84/1.05      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.84/1.05        | (r2_hidden @ 
% 0.84/1.05           (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05            (k5_relat_1 @ sk_B_1 @ sk_A)) @ 
% 0.84/1.05           (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))))),
% 0.84/1.05      inference('demod', [status(thm)], ['152', '153', '154', '155', '156'])).
% 0.84/1.05  thf('158', plain,
% 0.84/1.05      ((~ (v1_relat_1 @ sk_A)
% 0.84/1.05        | ~ (v1_relat_1 @ sk_B_1)
% 0.84/1.05        | (r2_hidden @ 
% 0.84/1.05           (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05            (k5_relat_1 @ sk_B_1 @ sk_A)) @ 
% 0.84/1.05           (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))))),
% 0.84/1.05      inference('sup-', [status(thm)], ['99', '157'])).
% 0.84/1.05  thf('159', plain, ((v1_relat_1 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('160', plain, ((v1_relat_1 @ sk_B_1)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('161', plain,
% 0.84/1.05      ((r2_hidden @ 
% 0.84/1.05        (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05         (k5_relat_1 @ sk_B_1 @ sk_A)) @ 
% 0.84/1.05        (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.84/1.05      inference('demod', [status(thm)], ['158', '159', '160'])).
% 0.84/1.05  thf('162', plain,
% 0.84/1.05      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.84/1.05         (~ (v1_relat_1 @ X20)
% 0.84/1.05          | ~ (v1_funct_1 @ X20)
% 0.84/1.05          | ((k1_funct_1 @ (k5_relat_1 @ X20 @ X21) @ X22)
% 0.84/1.05              = (k1_funct_1 @ X21 @ (k1_funct_1 @ X20 @ X22)))
% 0.84/1.05          | ~ (r2_hidden @ X22 @ (k1_relat_1 @ (k5_relat_1 @ X20 @ X21)))
% 0.84/1.05          | ~ (v1_funct_1 @ X21)
% 0.84/1.05          | ~ (v1_relat_1 @ X21))),
% 0.84/1.05      inference('cnf', [status(esa)], [t22_funct_1])).
% 0.84/1.05  thf('163', plain,
% 0.84/1.05      ((~ (v1_relat_1 @ sk_A)
% 0.84/1.05        | ~ (v1_funct_1 @ sk_A)
% 0.84/1.05        | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.84/1.05            (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05             (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.84/1.05            = (k1_funct_1 @ sk_A @ 
% 0.84/1.05               (k1_funct_1 @ sk_B_1 @ 
% 0.84/1.05                (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05                 (k5_relat_1 @ sk_B_1 @ sk_A)))))
% 0.84/1.05        | ~ (v1_funct_1 @ sk_B_1)
% 0.84/1.05        | ~ (v1_relat_1 @ sk_B_1))),
% 0.84/1.05      inference('sup-', [status(thm)], ['161', '162'])).
% 0.84/1.05  thf('164', plain, ((v1_relat_1 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('165', plain, ((v1_funct_1 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('166', plain, ((v1_funct_1 @ sk_B_1)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('167', plain, ((v1_relat_1 @ sk_B_1)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('168', plain,
% 0.84/1.05      (((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.84/1.05         (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05          (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.84/1.05         = (k1_funct_1 @ sk_A @ 
% 0.84/1.05            (k1_funct_1 @ sk_B_1 @ 
% 0.84/1.05             (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05              (k5_relat_1 @ sk_B_1 @ sk_A)))))),
% 0.84/1.05      inference('demod', [status(thm)], ['163', '164', '165', '166', '167'])).
% 0.84/1.05  thf('169', plain,
% 0.84/1.05      (![X3 : $i, X4 : $i]:
% 0.84/1.05         (~ (v1_relat_1 @ X3)
% 0.84/1.05          | ~ (v1_relat_1 @ X4)
% 0.84/1.05          | (v1_relat_1 @ (k5_relat_1 @ X3 @ X4)))),
% 0.84/1.05      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.84/1.05  thf('170', plain,
% 0.84/1.05      (![X18 : $i, X19 : $i]:
% 0.84/1.05         (~ (v1_funct_1 @ X18)
% 0.84/1.05          | ~ (v1_relat_1 @ X18)
% 0.84/1.05          | ~ (v1_relat_1 @ X19)
% 0.84/1.05          | ~ (v1_funct_1 @ X19)
% 0.84/1.05          | (v1_funct_1 @ (k5_relat_1 @ X18 @ X19)))),
% 0.84/1.05      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.84/1.05  thf('171', plain,
% 0.84/1.05      ((r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05        (k2_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.84/1.05      inference('demod', [status(thm)], ['137', '148'])).
% 0.84/1.05  thf('172', plain,
% 0.84/1.05      (![X9 : $i, X12 : $i]:
% 0.84/1.05         (~ (v1_relat_1 @ X9)
% 0.84/1.05          | ~ (v1_funct_1 @ X9)
% 0.84/1.05          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 0.84/1.05          | ((X12) = (k1_funct_1 @ X9 @ (sk_D_1 @ X12 @ X9))))),
% 0.84/1.05      inference('simplify', [status(thm)], ['28'])).
% 0.84/1.05  thf('173', plain,
% 0.84/1.05      ((((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.84/1.05          = (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.84/1.05             (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05              (k5_relat_1 @ sk_B_1 @ sk_A))))
% 0.84/1.05        | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.84/1.05        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['171', '172'])).
% 0.84/1.05  thf('174', plain,
% 0.84/1.05      (((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.84/1.05         (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05          (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.84/1.05         = (k1_funct_1 @ sk_A @ 
% 0.84/1.05            (k1_funct_1 @ sk_B_1 @ 
% 0.84/1.05             (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05              (k5_relat_1 @ sk_B_1 @ sk_A)))))),
% 0.84/1.05      inference('demod', [status(thm)], ['163', '164', '165', '166', '167'])).
% 0.84/1.05  thf('175', plain,
% 0.84/1.05      ((((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.84/1.05          = (k1_funct_1 @ sk_A @ 
% 0.84/1.05             (k1_funct_1 @ sk_B_1 @ 
% 0.84/1.05              (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05               (k5_relat_1 @ sk_B_1 @ sk_A)))))
% 0.84/1.05        | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.84/1.05        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.84/1.05      inference('demod', [status(thm)], ['173', '174'])).
% 0.84/1.05  thf('176', plain,
% 0.84/1.05      ((~ (v1_funct_1 @ sk_A)
% 0.84/1.05        | ~ (v1_relat_1 @ sk_A)
% 0.84/1.05        | ~ (v1_relat_1 @ sk_B_1)
% 0.84/1.05        | ~ (v1_funct_1 @ sk_B_1)
% 0.84/1.05        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.84/1.05        | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.84/1.05            = (k1_funct_1 @ sk_A @ 
% 0.84/1.05               (k1_funct_1 @ sk_B_1 @ 
% 0.84/1.05                (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05                 (k5_relat_1 @ sk_B_1 @ sk_A))))))),
% 0.84/1.05      inference('sup-', [status(thm)], ['170', '175'])).
% 0.84/1.05  thf('177', plain, ((v1_funct_1 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('178', plain, ((v1_relat_1 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('179', plain, ((v1_relat_1 @ sk_B_1)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('180', plain, ((v1_funct_1 @ sk_B_1)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('181', plain,
% 0.84/1.05      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.84/1.05        | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.84/1.05            = (k1_funct_1 @ sk_A @ 
% 0.84/1.05               (k1_funct_1 @ sk_B_1 @ 
% 0.84/1.05                (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05                 (k5_relat_1 @ sk_B_1 @ sk_A))))))),
% 0.84/1.05      inference('demod', [status(thm)], ['176', '177', '178', '179', '180'])).
% 0.84/1.05  thf('182', plain,
% 0.84/1.05      ((~ (v1_relat_1 @ sk_A)
% 0.84/1.05        | ~ (v1_relat_1 @ sk_B_1)
% 0.84/1.05        | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.84/1.05            = (k1_funct_1 @ sk_A @ 
% 0.84/1.05               (k1_funct_1 @ sk_B_1 @ 
% 0.84/1.05                (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05                 (k5_relat_1 @ sk_B_1 @ sk_A))))))),
% 0.84/1.05      inference('sup-', [status(thm)], ['169', '181'])).
% 0.84/1.05  thf('183', plain, ((v1_relat_1 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('184', plain, ((v1_relat_1 @ sk_B_1)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('185', plain,
% 0.84/1.05      (((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.84/1.05         = (k1_funct_1 @ sk_A @ 
% 0.84/1.05            (k1_funct_1 @ sk_B_1 @ 
% 0.84/1.05             (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05              (k5_relat_1 @ sk_B_1 @ sk_A)))))),
% 0.84/1.05      inference('demod', [status(thm)], ['182', '183', '184'])).
% 0.84/1.05  thf('186', plain,
% 0.84/1.05      (((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.84/1.05         (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05          (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.84/1.05         = (k1_funct_1 @ sk_A @ (sk_B @ sk_A)))),
% 0.84/1.05      inference('demod', [status(thm)], ['168', '185'])).
% 0.84/1.05  thf('187', plain,
% 0.84/1.05      (![X6 : $i, X7 : $i]:
% 0.84/1.05         (~ (v1_relat_1 @ X6)
% 0.84/1.05          | ((k1_relat_1 @ (k5_relat_1 @ X7 @ X6))
% 0.84/1.05              = (k10_relat_1 @ X7 @ (k1_relat_1 @ X6)))
% 0.84/1.05          | ~ (v1_relat_1 @ X7))),
% 0.84/1.05      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.84/1.05  thf('188', plain,
% 0.84/1.05      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.84/1.05         (~ (v2_funct_1 @ X15)
% 0.84/1.05          | ~ (r2_hidden @ X16 @ (k1_relat_1 @ X15))
% 0.84/1.05          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ X15))
% 0.84/1.05          | ((k1_funct_1 @ X15 @ X16) != (k1_funct_1 @ X15 @ X17))
% 0.84/1.05          | ((X16) = (X17))
% 0.84/1.05          | ~ (v1_funct_1 @ X15)
% 0.84/1.05          | ~ (v1_relat_1 @ X15))),
% 0.84/1.05      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.84/1.05  thf('189', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.84/1.05         (~ (r2_hidden @ X2 @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.84/1.05          | ~ (v1_relat_1 @ X1)
% 0.84/1.05          | ~ (v1_relat_1 @ X0)
% 0.84/1.05          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.84/1.05          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.84/1.05          | ((X2) = (X3))
% 0.84/1.05          | ((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.84/1.05              != (k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X3))
% 0.84/1.05          | ~ (r2_hidden @ X3 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.84/1.05          | ~ (v2_funct_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['187', '188'])).
% 0.84/1.05  thf('190', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         (((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.84/1.05            != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.84/1.05          | ~ (v2_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.84/1.05          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.84/1.05          | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05              (k5_relat_1 @ sk_B_1 @ sk_A)) = (X0))
% 0.84/1.05          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.84/1.05          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.84/1.05          | ~ (v1_relat_1 @ sk_A)
% 0.84/1.05          | ~ (v1_relat_1 @ sk_B_1)
% 0.84/1.05          | ~ (r2_hidden @ 
% 0.84/1.05               (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05                (k5_relat_1 @ sk_B_1 @ sk_A)) @ 
% 0.84/1.05               (k10_relat_1 @ sk_B_1 @ (k1_relat_1 @ sk_A))))),
% 0.84/1.05      inference('sup-', [status(thm)], ['186', '189'])).
% 0.84/1.05  thf('191', plain, ((v2_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('192', plain, ((v1_relat_1 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('193', plain, ((v1_relat_1 @ sk_B_1)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('194', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('195', plain,
% 0.84/1.05      (![X6 : $i, X7 : $i]:
% 0.84/1.05         (~ (v1_relat_1 @ X6)
% 0.84/1.05          | ((k1_relat_1 @ (k5_relat_1 @ X7 @ X6))
% 0.84/1.05              = (k10_relat_1 @ X7 @ (k1_relat_1 @ X6)))
% 0.84/1.05          | ~ (v1_relat_1 @ X7))),
% 0.84/1.05      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.84/1.05  thf('196', plain,
% 0.84/1.05      ((r2_hidden @ 
% 0.84/1.05        (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05         (k5_relat_1 @ sk_B_1 @ sk_A)) @ 
% 0.84/1.05        (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.84/1.05      inference('demod', [status(thm)], ['158', '159', '160'])).
% 0.84/1.05  thf('197', plain,
% 0.84/1.05      (((r2_hidden @ 
% 0.84/1.05         (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05          (k5_relat_1 @ sk_B_1 @ sk_A)) @ 
% 0.84/1.05         (k10_relat_1 @ sk_B_1 @ (k1_relat_1 @ sk_A)))
% 0.84/1.05        | ~ (v1_relat_1 @ sk_B_1)
% 0.84/1.05        | ~ (v1_relat_1 @ sk_A))),
% 0.84/1.05      inference('sup+', [status(thm)], ['195', '196'])).
% 0.84/1.05  thf('198', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('199', plain, ((v1_relat_1 @ sk_B_1)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('200', plain, ((v1_relat_1 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('201', plain,
% 0.84/1.05      ((r2_hidden @ 
% 0.84/1.05        (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05         (k5_relat_1 @ sk_B_1 @ sk_A)) @ 
% 0.84/1.05        (k10_relat_1 @ sk_B_1 @ (k2_relat_1 @ sk_B_1)))),
% 0.84/1.05      inference('demod', [status(thm)], ['197', '198', '199', '200'])).
% 0.84/1.05  thf('202', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         (((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.84/1.05            != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.84/1.05          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.84/1.05          | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05              (k5_relat_1 @ sk_B_1 @ sk_A)) = (X0))
% 0.84/1.05          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.84/1.05          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.84/1.05      inference('demod', [status(thm)],
% 0.84/1.05                ['190', '191', '192', '193', '194', '201'])).
% 0.84/1.05  thf('203', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         (~ (v1_funct_1 @ sk_A)
% 0.84/1.05          | ~ (v1_relat_1 @ sk_A)
% 0.84/1.05          | ~ (v1_relat_1 @ sk_B_1)
% 0.84/1.05          | ~ (v1_funct_1 @ sk_B_1)
% 0.84/1.05          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.84/1.05          | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05              (k5_relat_1 @ sk_B_1 @ sk_A)) = (X0))
% 0.84/1.05          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.84/1.05          | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.84/1.05              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['98', '202'])).
% 0.84/1.05  thf('204', plain, ((v1_funct_1 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('205', plain, ((v1_relat_1 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('206', plain, ((v1_relat_1 @ sk_B_1)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('207', plain, ((v1_funct_1 @ sk_B_1)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('208', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         (~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.84/1.05          | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05              (k5_relat_1 @ sk_B_1 @ sk_A)) = (X0))
% 0.84/1.05          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.84/1.05          | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.84/1.05              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)))),
% 0.84/1.05      inference('demod', [status(thm)], ['203', '204', '205', '206', '207'])).
% 0.84/1.05  thf('209', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         (~ (v1_relat_1 @ sk_A)
% 0.84/1.05          | ~ (v1_relat_1 @ sk_B_1)
% 0.84/1.05          | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.84/1.05              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.84/1.05          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.84/1.05          | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05              (k5_relat_1 @ sk_B_1 @ sk_A)) = (X0)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['97', '208'])).
% 0.84/1.05  thf('210', plain, ((v1_relat_1 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('211', plain, ((v1_relat_1 @ sk_B_1)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('212', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         (((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.84/1.05            != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.84/1.05          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.84/1.05          | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05              (k5_relat_1 @ sk_B_1 @ sk_A)) = (X0)))),
% 0.84/1.05      inference('demod', [status(thm)], ['209', '210', '211'])).
% 0.84/1.05  thf('213', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         (~ (r2_hidden @ X0 @ (k10_relat_1 @ sk_B_1 @ (k1_relat_1 @ sk_A)))
% 0.84/1.05          | ~ (v1_relat_1 @ sk_B_1)
% 0.84/1.05          | ~ (v1_relat_1 @ sk_A)
% 0.84/1.05          | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05              (k5_relat_1 @ sk_B_1 @ sk_A)) = (X0))
% 0.84/1.05          | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.84/1.05              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['96', '212'])).
% 0.84/1.05  thf('214', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('215', plain, ((v1_relat_1 @ sk_B_1)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('216', plain, ((v1_relat_1 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('217', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         (~ (r2_hidden @ X0 @ (k10_relat_1 @ sk_B_1 @ (k2_relat_1 @ sk_B_1)))
% 0.84/1.05          | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05              (k5_relat_1 @ sk_B_1 @ sk_A)) = (X0))
% 0.84/1.05          | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.84/1.05              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)))),
% 0.84/1.05      inference('demod', [status(thm)], ['213', '214', '215', '216'])).
% 0.84/1.05  thf('218', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.84/1.05          | ~ (v1_relat_1 @ sk_B_1)
% 0.84/1.05          | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.84/1.05              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.84/1.05          | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05              (k5_relat_1 @ sk_B_1 @ sk_A)) = (X0)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['95', '217'])).
% 0.84/1.05  thf('219', plain, ((v1_relat_1 @ sk_B_1)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('220', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.84/1.05          | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.84/1.05              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.84/1.05          | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05              (k5_relat_1 @ sk_B_1 @ sk_A)) = (X0)))),
% 0.84/1.05      inference('demod', [status(thm)], ['218', '219'])).
% 0.84/1.05  thf('221', plain,
% 0.84/1.05      ((((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.84/1.05          != (k1_funct_1 @ sk_A @ (sk_B @ sk_A)))
% 0.84/1.05        | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05            (k5_relat_1 @ sk_B_1 @ sk_A)) = (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1))
% 0.84/1.05        | ~ (r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1) @ 
% 0.84/1.05             (k1_relat_1 @ sk_B_1)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['94', '220'])).
% 0.84/1.05  thf('222', plain,
% 0.84/1.05      ((r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1) @ (k1_relat_1 @ sk_B_1))),
% 0.84/1.05      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.84/1.05  thf('223', plain,
% 0.84/1.05      ((((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.84/1.05          != (k1_funct_1 @ sk_A @ (sk_B @ sk_A)))
% 0.84/1.05        | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05            (k5_relat_1 @ sk_B_1 @ sk_A)) = (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1)))),
% 0.84/1.05      inference('demod', [status(thm)], ['221', '222'])).
% 0.84/1.05  thf('224', plain,
% 0.84/1.05      (((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05         (k5_relat_1 @ sk_B_1 @ sk_A)) = (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1))),
% 0.84/1.05      inference('simplify', [status(thm)], ['223'])).
% 0.84/1.05  thf('225', plain, ((r2_hidden @ (sk_B @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 0.84/1.05      inference('clc', [status(thm)], ['79', '80'])).
% 0.84/1.05  thf('226', plain,
% 0.84/1.05      (![X9 : $i, X12 : $i]:
% 0.84/1.05         (~ (v1_relat_1 @ X9)
% 0.84/1.05          | ~ (v1_funct_1 @ X9)
% 0.84/1.05          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 0.84/1.05          | (r2_hidden @ (sk_D_1 @ X12 @ X9) @ (k1_relat_1 @ X9)))),
% 0.84/1.05      inference('simplify', [status(thm)], ['35'])).
% 0.84/1.05  thf('227', plain,
% 0.84/1.05      (((r2_hidden @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) @ (k1_relat_1 @ sk_B_1))
% 0.84/1.05        | ~ (v1_funct_1 @ sk_B_1)
% 0.84/1.05        | ~ (v1_relat_1 @ sk_B_1))),
% 0.84/1.05      inference('sup-', [status(thm)], ['225', '226'])).
% 0.84/1.05  thf('228', plain, ((v1_funct_1 @ sk_B_1)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('229', plain, ((v1_relat_1 @ sk_B_1)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('230', plain,
% 0.84/1.05      ((r2_hidden @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) @ (k1_relat_1 @ sk_B_1))),
% 0.84/1.05      inference('demod', [status(thm)], ['227', '228', '229'])).
% 0.84/1.05  thf('231', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.84/1.05          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.84/1.05              = (k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B_1 @ X0))))),
% 0.84/1.05      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 0.84/1.05  thf('232', plain,
% 0.84/1.05      (((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.84/1.05         (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1))
% 0.84/1.05         = (k1_funct_1 @ sk_A @ 
% 0.84/1.05            (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1))))),
% 0.84/1.05      inference('sup-', [status(thm)], ['230', '231'])).
% 0.84/1.05  thf('233', plain, ((r2_hidden @ (sk_B @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 0.84/1.05      inference('clc', [status(thm)], ['79', '80'])).
% 0.84/1.05  thf('234', plain,
% 0.84/1.05      (![X9 : $i, X12 : $i]:
% 0.84/1.05         (~ (v1_relat_1 @ X9)
% 0.84/1.05          | ~ (v1_funct_1 @ X9)
% 0.84/1.05          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 0.84/1.05          | ((X12) = (k1_funct_1 @ X9 @ (sk_D_1 @ X12 @ X9))))),
% 0.84/1.05      inference('simplify', [status(thm)], ['28'])).
% 0.84/1.05  thf('235', plain,
% 0.84/1.05      ((((sk_B @ sk_A)
% 0.84/1.05          = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)))
% 0.84/1.05        | ~ (v1_funct_1 @ sk_B_1)
% 0.84/1.05        | ~ (v1_relat_1 @ sk_B_1))),
% 0.84/1.05      inference('sup-', [status(thm)], ['233', '234'])).
% 0.84/1.05  thf('236', plain, ((v1_funct_1 @ sk_B_1)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('237', plain, ((v1_relat_1 @ sk_B_1)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('238', plain,
% 0.84/1.05      (((sk_B @ sk_A)
% 0.84/1.05         = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)))),
% 0.84/1.05      inference('demod', [status(thm)], ['235', '236', '237'])).
% 0.84/1.05  thf('239', plain,
% 0.84/1.05      (((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.84/1.05         (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1))
% 0.84/1.05         = (k1_funct_1 @ sk_A @ (sk_B @ sk_A)))),
% 0.84/1.05      inference('demod', [status(thm)], ['232', '238'])).
% 0.84/1.05  thf('240', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.84/1.05          | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.84/1.05              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.84/1.05          | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05              (k5_relat_1 @ sk_B_1 @ sk_A)) = (X0)))),
% 0.84/1.05      inference('demod', [status(thm)], ['218', '219'])).
% 0.84/1.05  thf('241', plain,
% 0.84/1.05      ((((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.84/1.05          != (k1_funct_1 @ sk_A @ (sk_B @ sk_A)))
% 0.84/1.05        | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05            (k5_relat_1 @ sk_B_1 @ sk_A)) = (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1))
% 0.84/1.05        | ~ (r2_hidden @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) @ 
% 0.84/1.05             (k1_relat_1 @ sk_B_1)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['239', '240'])).
% 0.84/1.05  thf('242', plain,
% 0.84/1.05      ((r2_hidden @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) @ (k1_relat_1 @ sk_B_1))),
% 0.84/1.05      inference('demod', [status(thm)], ['227', '228', '229'])).
% 0.84/1.05  thf('243', plain,
% 0.84/1.05      ((((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.84/1.05          != (k1_funct_1 @ sk_A @ (sk_B @ sk_A)))
% 0.84/1.05        | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05            (k5_relat_1 @ sk_B_1 @ sk_A)) = (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)))),
% 0.84/1.05      inference('demod', [status(thm)], ['241', '242'])).
% 0.84/1.05  thf('244', plain,
% 0.84/1.05      (((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.84/1.05         (k5_relat_1 @ sk_B_1 @ sk_A)) = (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1))),
% 0.84/1.05      inference('simplify', [status(thm)], ['243'])).
% 0.84/1.05  thf('245', plain,
% 0.84/1.05      (((sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1) = (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1))),
% 0.84/1.05      inference('sup+', [status(thm)], ['224', '244'])).
% 0.84/1.05  thf('246', plain,
% 0.84/1.05      (((sk_C_1 @ sk_A)
% 0.84/1.05         = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)))),
% 0.84/1.05      inference('demod', [status(thm)], ['33', '245'])).
% 0.84/1.05  thf('247', plain,
% 0.84/1.05      (((sk_B @ sk_A)
% 0.84/1.05         = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)))),
% 0.84/1.05      inference('demod', [status(thm)], ['235', '236', '237'])).
% 0.84/1.05  thf('248', plain, (((sk_B @ sk_A) = (sk_C_1 @ sk_A))),
% 0.84/1.05      inference('sup+', [status(thm)], ['246', '247'])).
% 0.84/1.05  thf('249', plain,
% 0.84/1.05      (![X15 : $i]:
% 0.84/1.05         (((sk_B @ X15) != (sk_C_1 @ X15))
% 0.84/1.05          | (v2_funct_1 @ X15)
% 0.84/1.05          | ~ (v1_funct_1 @ X15)
% 0.84/1.05          | ~ (v1_relat_1 @ X15))),
% 0.84/1.05      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.84/1.05  thf('250', plain,
% 0.84/1.05      ((((sk_B @ sk_A) != (sk_B @ sk_A))
% 0.84/1.05        | ~ (v1_relat_1 @ sk_A)
% 0.84/1.05        | ~ (v1_funct_1 @ sk_A)
% 0.84/1.05        | (v2_funct_1 @ sk_A))),
% 0.84/1.05      inference('sup-', [status(thm)], ['248', '249'])).
% 0.84/1.05  thf('251', plain, ((v1_relat_1 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('252', plain, ((v1_funct_1 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('253', plain, ((((sk_B @ sk_A) != (sk_B @ sk_A)) | (v2_funct_1 @ sk_A))),
% 0.84/1.05      inference('demod', [status(thm)], ['250', '251', '252'])).
% 0.84/1.05  thf('254', plain, ((v2_funct_1 @ sk_A)),
% 0.84/1.05      inference('simplify', [status(thm)], ['253'])).
% 0.84/1.05  thf('255', plain, ($false), inference('demod', [status(thm)], ['19', '254'])).
% 0.84/1.05  
% 0.84/1.05  % SZS output end Refutation
% 0.84/1.05  
% 0.84/1.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
