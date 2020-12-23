%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.STlKsyJ3Fm

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:13 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  278 (3203 expanded)
%              Number of leaves         :   25 ( 903 expanded)
%              Depth                    :   44
%              Number of atoms          : 2740 (46079 expanded)
%              Number of equality atoms :  117 (2152 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

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

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X2: $i] :
      ( ( ( k10_relat_1 @ X2 @ ( k2_relat_1 @ X2 ) )
        = ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('3',plain,
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

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X4 @ X3 ) )
        = ( k10_relat_1 @ X4 @ ( k1_relat_1 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf(t27_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k1_relat_1 @ B ) )
           => ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( r1_tarski @ ( k2_relat_1 @ X20 ) @ ( k1_relat_1 @ X21 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X20 @ X21 ) )
       != ( k1_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t27_funct_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) )
       != ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) )
       != ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ sk_B_1 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ sk_B_1 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9','10','11'])).

thf('13',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
     != ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ ( k2_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['2','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
     != ( k1_relat_1 @ sk_B_1 ) )
    | ( r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('18',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
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

thf('20',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ( v2_funct_1 @ X22 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X22 ) @ ( k1_relat_1 @ X23 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X22 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t47_funct_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ sk_A ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ sk_B_1 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ sk_A ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_funct_1 @ sk_B_1 )
    | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,
    ( ~ ( v2_funct_1 @ sk_B_1 )
   <= ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( v2_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','33'])).

thf('35',plain,
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

thf('36',plain,(
    ! [X12: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X12 ) @ ( k1_relat_1 @ X12 ) )
      | ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('37',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['37','38','39'])).

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

thf('41',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ( X8
       != ( k2_relat_1 @ X6 ) )
      | ( X9
        = ( k1_funct_1 @ X6 @ ( sk_D_1 @ X9 @ X6 ) ) )
      | ~ ( r2_hidden @ X9 @ X8 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('42',plain,(
    ! [X6: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( r2_hidden @ X9 @ ( k2_relat_1 @ X6 ) )
      | ( X9
        = ( k1_funct_1 @ X6 @ ( sk_D_1 @ X9 @ X6 ) ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( v2_funct_1 @ sk_A )
    | ( ( sk_C_1 @ sk_A )
      = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v2_funct_1 @ sk_A )
    | ( ( sk_C_1 @ sk_A )
      = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','33'])).

thf('48',plain,
    ( ( sk_C_1 @ sk_A )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('50',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ( X8
       != ( k2_relat_1 @ X6 ) )
      | ( r2_hidden @ ( sk_D_1 @ X9 @ X6 ) @ ( k1_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ X9 @ X8 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('51',plain,(
    ! [X6: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( r2_hidden @ X9 @ ( k2_relat_1 @ X6 ) )
      | ( r2_hidden @ ( sk_D_1 @ X9 @ X6 ) @ ( k1_relat_1 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( v2_funct_1 @ sk_A )
    | ( r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v2_funct_1 @ sk_A )
    | ( r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','33'])).

thf('57',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['55','56'])).

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

thf('58',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X18 @ X17 ) @ X19 )
        = ( k1_funct_1 @ X17 @ ( k1_funct_1 @ X18 @ X19 ) ) )
      | ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ X0 ) @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( sk_C_1 @ sk_A )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ X0 ) @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) )
        = ( k1_funct_1 @ X0 @ ( sk_C_1 @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('64',plain,(
    ! [X2: $i] :
      ( ( ( k10_relat_1 @ X2 @ ( k2_relat_1 @ X2 ) )
        = ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('65',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X4 @ X3 ) )
        = ( k10_relat_1 @ X4 @ ( k1_relat_1 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(fc2_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) )).

thf('67',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('69',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('70',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X12: $i] :
      ( ( r2_hidden @ ( sk_B @ X12 ) @ ( k1_relat_1 @ X12 ) )
      | ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('72',plain,
    ( ( r2_hidden @ ( sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( r2_hidden @ ( sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ! [X6: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( r2_hidden @ X9 @ ( k2_relat_1 @ X6 ) )
      | ( r2_hidden @ ( sk_D_1 @ X9 @ X6 ) @ ( k1_relat_1 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('77',plain,
    ( ( v2_funct_1 @ sk_A )
    | ( r2_hidden @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v2_funct_1 @ sk_A )
    | ( r2_hidden @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','33'])).

thf('82',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X18 @ X17 ) @ X19 )
        = ( k1_funct_1 @ X17 @ ( k1_funct_1 @ X18 @ X19 ) ) )
      | ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ X0 ) @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( r2_hidden @ ( sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('88',plain,(
    ! [X6: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( r2_hidden @ X9 @ ( k2_relat_1 @ X6 ) )
      | ( X9
        = ( k1_funct_1 @ X6 @ ( sk_D_1 @ X9 @ X6 ) ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('89',plain,
    ( ( v2_funct_1 @ sk_A )
    | ( ( sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( v2_funct_1 @ sk_A )
    | ( ( sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','33'])).

thf('94',plain,
    ( ( sk_B @ sk_A )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ X0 ) @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) )
        = ( k1_funct_1 @ X0 @ ( sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85','86','94'])).

thf('96',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('98',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('99',plain,(
    ! [X2: $i] :
      ( ( ( k10_relat_1 @ X2 @ ( k2_relat_1 @ X2 ) )
        = ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('100',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X4 @ X3 ) )
        = ( k10_relat_1 @ X4 @ ( k1_relat_1 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('102',plain,(
    ! [X6: $i,X8: $i,X10: $i,X11: $i] :
      ( ( X8
       != ( k2_relat_1 @ X6 ) )
      | ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ X6 ) )
      | ( X10
       != ( k1_funct_1 @ X6 @ X11 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('103',plain,(
    ! [X6: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ X6 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X6 @ X11 ) @ ( k2_relat_1 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['101','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ sk_B_1 ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k5_relat_1 @ X0 @ sk_A ) @ X1 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['100','104'])).

thf('106',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ sk_B_1 ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k5_relat_1 @ X0 @ sk_A ) @ X1 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ( r2_hidden @ ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['99','107'])).

thf('109',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['98','111'])).

thf('113',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['112','113','114','115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['97','117'])).

thf('119',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['118','119','120'])).

thf('122',plain,(
    r2_hidden @ ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['96','121'])).

thf('123',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['95','122'])).

thf('124',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,(
    ! [X6: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( r2_hidden @ X9 @ ( k2_relat_1 @ X6 ) )
      | ( X9
        = ( k1_funct_1 @ X6 @ ( sk_D_1 @ X9 @ X6 ) ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('128',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
      = ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
    | ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
      = ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['69','128'])).

thf('130',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
    | ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
      = ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['129','130','131','132','133'])).

thf('135',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
      = ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['68','134'])).

thf('136',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
    = ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['135','136','137'])).

thf('139',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X4 @ X3 ) )
        = ( k10_relat_1 @ X4 @ ( k1_relat_1 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('140',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X12 ) )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X12 ) )
      | ( ( k1_funct_1 @ X12 @ X13 )
       != ( k1_funct_1 @ X12 @ X14 ) )
      | ( X13 = X14 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('141',plain,(
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
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
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
    inference('sup-',[status(thm)],['138','141'])).

thf('143',plain,(
    v2_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X4 @ X3 ) )
        = ( k10_relat_1 @ X4 @ ( k1_relat_1 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('149',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('150',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('151',plain,(
    ! [X6: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( r2_hidden @ X9 @ ( k2_relat_1 @ X6 ) )
      | ( r2_hidden @ ( sk_D_1 @ X9 @ X6 ) @ ( k1_relat_1 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('152',plain,
    ( ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['149','152'])).

thf('154',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['153','154','155','156','157'])).

thf('159',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['148','158'])).

thf('160',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['159','160','161'])).

thf('163',plain,
    ( ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) @ ( k10_relat_1 @ sk_B_1 @ ( k1_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['147','162'])).

thf('164',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) @ ( k10_relat_1 @ sk_B_1 @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['163','164','165','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
        = X0 )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['142','143','144','145','146','167'])).

thf('169',plain,(
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
    inference('sup-',[status(thm)],['67','168'])).

thf('170',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
        = X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['169','170','171','172','173'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['66','174'])).

thf('176',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['175','176','177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k10_relat_1 @ sk_B_1 @ ( k1_relat_1 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_A )
      | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
        = X0 )
      | ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','178'])).

thf('180',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k10_relat_1 @ sk_B_1 @ ( k2_relat_1 @ sk_B_1 ) ) )
      | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
        = X0 )
      | ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['179','180','181','182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['64','183'])).

thf('185',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['184','185'])).

thf('187',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
     != ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      = ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) )
    | ~ ( r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['63','186'])).

thf('188',plain,(
    ! [X12: $i] :
      ( ( ( k1_funct_1 @ X12 @ ( sk_B @ X12 ) )
        = ( k1_funct_1 @ X12 @ ( sk_C_1 @ X12 ) ) )
      | ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('189',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('190',plain,(
    ! [X6: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ X6 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X6 @ X11 ) @ ( k2_relat_1 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('191',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) ) @ ( k2_relat_1 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,
    ( ( sk_C_1 @ sk_A )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('193',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['191','192','193','194'])).

thf('196',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    ! [X6: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ X6 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X6 @ X11 ) @ ( k2_relat_1 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['198','199','200'])).

thf('202',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) ) @ ( k2_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['195','201'])).

thf('203',plain,(
    ! [X6: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( r2_hidden @ X9 @ ( k2_relat_1 @ X6 ) )
      | ( X9
        = ( k1_funct_1 @ X6 @ ( sk_D_1 @ X9 @ X6 ) ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('204',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) )
      = ( k1_funct_1 @ sk_A @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) )
    = ( k1_funct_1 @ sk_A @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['204','205','206'])).

thf('208',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) )
      = ( k1_funct_1 @ sk_A @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['188','207'])).

thf('209',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('210',plain,(
    ! [X6: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ X6 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X6 @ X11 ) @ ( k2_relat_1 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('211',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) @ ( k2_relat_1 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['209','210'])).

thf('212',plain,
    ( ( sk_B @ sk_A )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('213',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['211','212','213','214'])).

thf('216',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['198','199','200'])).

thf('217',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k2_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,(
    ! [X6: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( r2_hidden @ X9 @ ( k2_relat_1 @ X6 ) )
      | ( X9
        = ( k1_funct_1 @ X6 @ ( sk_D_1 @ X9 @ X6 ) ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('219',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
      = ( k1_funct_1 @ sk_A @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,
    ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
    = ( k1_funct_1 @ sk_A @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['219','220','221'])).

thf('223',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) )
      = ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['208','222','223','224'])).

thf('226',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','33'])).

thf('227',plain,
    ( ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) )
    = ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['225','226'])).

thf('228',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('231',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
     != ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      = ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['187','227','228','229','230'])).

thf('232',plain,
    ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
    = ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['231'])).

thf('233',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ X0 ) @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) )
        = ( k1_funct_1 @ X0 @ ( sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85','86','94'])).

thf('234',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['184','185'])).

thf('235',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
     != ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      = ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) )
    | ~ ( r2_hidden @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['233','234'])).

thf('236',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('239',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
     != ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      = ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['235','236','237','238'])).

thf('240',plain,
    ( ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
    = ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['239'])).

thf('241',plain,
    ( ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 )
    = ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['232','240'])).

thf('242',plain,
    ( ( sk_C_1 @ sk_A )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['48','241'])).

thf('243',plain,
    ( ( sk_B @ sk_A )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('244',plain,
    ( ( sk_B @ sk_A )
    = ( sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['242','243'])).

thf('245',plain,(
    ! [X12: $i] :
      ( ( ( sk_B @ X12 )
       != ( sk_C_1 @ X12 ) )
      | ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('246',plain,
    ( ( ( sk_B @ sk_A )
     != ( sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['244','245'])).

thf('247',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,
    ( ( ( sk_B @ sk_A )
     != ( sk_B @ sk_A ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['246','247','248'])).

thf('250',plain,(
    v2_funct_1 @ sk_A ),
    inference(simplify,[status(thm)],['249'])).

thf('251',plain,(
    $false ),
    inference(demod,[status(thm)],['34','250'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.STlKsyJ3Fm
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:55:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.91/1.16  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.91/1.16  % Solved by: fo/fo7.sh
% 0.91/1.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.16  % done 601 iterations in 0.703s
% 0.91/1.16  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.91/1.16  % SZS output start Refutation
% 0.91/1.16  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.91/1.16  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.91/1.16  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.91/1.16  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.91/1.16  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.91/1.16  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.16  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.91/1.16  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.16  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.91/1.16  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.91/1.16  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.91/1.16  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.91/1.16  thf(sk_B_type, type, sk_B: $i > $i).
% 0.91/1.16  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.91/1.16  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.91/1.16  thf(t48_funct_1, conjecture,
% 0.91/1.16    (![A:$i]:
% 0.91/1.16     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.91/1.16       ( ![B:$i]:
% 0.91/1.16         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.91/1.16           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.91/1.16               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.91/1.16             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.91/1.16  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.16    (~( ![A:$i]:
% 0.91/1.16        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.91/1.16          ( ![B:$i]:
% 0.91/1.16            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.91/1.16              ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.91/1.16                  ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.91/1.16                ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ) )),
% 0.91/1.16    inference('cnf.neg', [status(esa)], [t48_funct_1])).
% 0.91/1.16  thf('0', plain, ((~ (v2_funct_1 @ sk_B_1) | ~ (v2_funct_1 @ sk_A))),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('1', plain, ((~ (v2_funct_1 @ sk_A)) <= (~ ((v2_funct_1 @ sk_A)))),
% 0.91/1.16      inference('split', [status(esa)], ['0'])).
% 0.91/1.16  thf(t169_relat_1, axiom,
% 0.91/1.16    (![A:$i]:
% 0.91/1.16     ( ( v1_relat_1 @ A ) =>
% 0.91/1.16       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.91/1.16  thf('2', plain,
% 0.91/1.16      (![X2 : $i]:
% 0.91/1.16         (((k10_relat_1 @ X2 @ (k2_relat_1 @ X2)) = (k1_relat_1 @ X2))
% 0.91/1.16          | ~ (v1_relat_1 @ X2))),
% 0.91/1.16      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.91/1.16  thf('3', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf(t182_relat_1, axiom,
% 0.91/1.16    (![A:$i]:
% 0.91/1.16     ( ( v1_relat_1 @ A ) =>
% 0.91/1.16       ( ![B:$i]:
% 0.91/1.16         ( ( v1_relat_1 @ B ) =>
% 0.91/1.16           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.91/1.16             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.91/1.16  thf('4', plain,
% 0.91/1.16      (![X3 : $i, X4 : $i]:
% 0.91/1.16         (~ (v1_relat_1 @ X3)
% 0.91/1.16          | ((k1_relat_1 @ (k5_relat_1 @ X4 @ X3))
% 0.91/1.16              = (k10_relat_1 @ X4 @ (k1_relat_1 @ X3)))
% 0.91/1.16          | ~ (v1_relat_1 @ X4))),
% 0.91/1.16      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.91/1.16  thf(t27_funct_1, axiom,
% 0.91/1.16    (![A:$i]:
% 0.91/1.16     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.91/1.16       ( ![B:$i]:
% 0.91/1.16         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.91/1.16           ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k1_relat_1 @ B ) ) =>
% 0.91/1.16             ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.91/1.16  thf('5', plain,
% 0.91/1.16      (![X20 : $i, X21 : $i]:
% 0.91/1.16         (~ (v1_relat_1 @ X20)
% 0.91/1.16          | ~ (v1_funct_1 @ X20)
% 0.91/1.16          | (r1_tarski @ (k2_relat_1 @ X20) @ (k1_relat_1 @ X21))
% 0.91/1.16          | ((k1_relat_1 @ (k5_relat_1 @ X20 @ X21)) != (k1_relat_1 @ X20))
% 0.91/1.16          | ~ (v1_funct_1 @ X21)
% 0.91/1.16          | ~ (v1_relat_1 @ X21))),
% 0.91/1.16      inference('cnf', [status(esa)], [t27_funct_1])).
% 0.91/1.16  thf('6', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         (((k10_relat_1 @ X1 @ (k1_relat_1 @ X0)) != (k1_relat_1 @ X1))
% 0.91/1.16          | ~ (v1_relat_1 @ X1)
% 0.91/1.16          | ~ (v1_relat_1 @ X0)
% 0.91/1.16          | ~ (v1_relat_1 @ X0)
% 0.91/1.16          | ~ (v1_funct_1 @ X0)
% 0.91/1.16          | (r1_tarski @ (k2_relat_1 @ X1) @ (k1_relat_1 @ X0))
% 0.91/1.16          | ~ (v1_funct_1 @ X1)
% 0.91/1.16          | ~ (v1_relat_1 @ X1))),
% 0.91/1.16      inference('sup-', [status(thm)], ['4', '5'])).
% 0.91/1.16  thf('7', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         (~ (v1_funct_1 @ X1)
% 0.91/1.16          | (r1_tarski @ (k2_relat_1 @ X1) @ (k1_relat_1 @ X0))
% 0.91/1.16          | ~ (v1_funct_1 @ X0)
% 0.91/1.16          | ~ (v1_relat_1 @ X0)
% 0.91/1.16          | ~ (v1_relat_1 @ X1)
% 0.91/1.16          | ((k10_relat_1 @ X1 @ (k1_relat_1 @ X0)) != (k1_relat_1 @ X1)))),
% 0.91/1.16      inference('simplify', [status(thm)], ['6'])).
% 0.91/1.16  thf('8', plain,
% 0.91/1.16      (![X0 : $i]:
% 0.91/1.16         (((k10_relat_1 @ X0 @ (k2_relat_1 @ sk_B_1)) != (k1_relat_1 @ X0))
% 0.91/1.16          | ~ (v1_relat_1 @ X0)
% 0.91/1.16          | ~ (v1_relat_1 @ sk_A)
% 0.91/1.16          | ~ (v1_funct_1 @ sk_A)
% 0.91/1.16          | (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ sk_A))
% 0.91/1.16          | ~ (v1_funct_1 @ X0))),
% 0.91/1.16      inference('sup-', [status(thm)], ['3', '7'])).
% 0.91/1.16  thf('9', plain, ((v1_relat_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('10', plain, ((v1_funct_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('11', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('12', plain,
% 0.91/1.16      (![X0 : $i]:
% 0.91/1.16         (((k10_relat_1 @ X0 @ (k2_relat_1 @ sk_B_1)) != (k1_relat_1 @ X0))
% 0.91/1.16          | ~ (v1_relat_1 @ X0)
% 0.91/1.16          | (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ sk_B_1))
% 0.91/1.16          | ~ (v1_funct_1 @ X0))),
% 0.91/1.16      inference('demod', [status(thm)], ['8', '9', '10', '11'])).
% 0.91/1.16  thf('13', plain,
% 0.91/1.16      ((((k1_relat_1 @ sk_B_1) != (k1_relat_1 @ sk_B_1))
% 0.91/1.16        | ~ (v1_relat_1 @ sk_B_1)
% 0.91/1.16        | ~ (v1_funct_1 @ sk_B_1)
% 0.91/1.16        | (r1_tarski @ (k2_relat_1 @ sk_B_1) @ (k2_relat_1 @ sk_B_1))
% 0.91/1.16        | ~ (v1_relat_1 @ sk_B_1))),
% 0.91/1.16      inference('sup-', [status(thm)], ['2', '12'])).
% 0.91/1.16  thf('14', plain, ((v1_relat_1 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('15', plain, ((v1_funct_1 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('16', plain, ((v1_relat_1 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('17', plain,
% 0.91/1.16      ((((k1_relat_1 @ sk_B_1) != (k1_relat_1 @ sk_B_1))
% 0.91/1.16        | (r1_tarski @ (k2_relat_1 @ sk_B_1) @ (k2_relat_1 @ sk_B_1)))),
% 0.91/1.16      inference('demod', [status(thm)], ['13', '14', '15', '16'])).
% 0.91/1.16  thf('18', plain,
% 0.91/1.16      ((r1_tarski @ (k2_relat_1 @ sk_B_1) @ (k2_relat_1 @ sk_B_1))),
% 0.91/1.16      inference('simplify', [status(thm)], ['17'])).
% 0.91/1.16  thf('19', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf(t47_funct_1, axiom,
% 0.91/1.16    (![A:$i]:
% 0.91/1.16     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.91/1.16       ( ![B:$i]:
% 0.91/1.16         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.91/1.16           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.91/1.16               ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) =>
% 0.91/1.16             ( v2_funct_1 @ B ) ) ) ) ))).
% 0.91/1.16  thf('20', plain,
% 0.91/1.16      (![X22 : $i, X23 : $i]:
% 0.91/1.16         (~ (v1_relat_1 @ X22)
% 0.91/1.16          | ~ (v1_funct_1 @ X22)
% 0.91/1.16          | (v2_funct_1 @ X22)
% 0.91/1.16          | ~ (r1_tarski @ (k2_relat_1 @ X22) @ (k1_relat_1 @ X23))
% 0.91/1.16          | ~ (v2_funct_1 @ (k5_relat_1 @ X22 @ X23))
% 0.91/1.16          | ~ (v1_funct_1 @ X23)
% 0.91/1.16          | ~ (v1_relat_1 @ X23))),
% 0.91/1.16      inference('cnf', [status(esa)], [t47_funct_1])).
% 0.91/1.16  thf('21', plain,
% 0.91/1.16      (![X0 : $i]:
% 0.91/1.16         (~ (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ sk_B_1))
% 0.91/1.16          | ~ (v1_relat_1 @ sk_A)
% 0.91/1.16          | ~ (v1_funct_1 @ sk_A)
% 0.91/1.16          | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_A))
% 0.91/1.16          | (v2_funct_1 @ X0)
% 0.91/1.16          | ~ (v1_funct_1 @ X0)
% 0.91/1.16          | ~ (v1_relat_1 @ X0))),
% 0.91/1.16      inference('sup-', [status(thm)], ['19', '20'])).
% 0.91/1.16  thf('22', plain, ((v1_relat_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('23', plain, ((v1_funct_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('24', plain,
% 0.91/1.16      (![X0 : $i]:
% 0.91/1.16         (~ (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ sk_B_1))
% 0.91/1.16          | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_A))
% 0.91/1.16          | (v2_funct_1 @ X0)
% 0.91/1.16          | ~ (v1_funct_1 @ X0)
% 0.91/1.16          | ~ (v1_relat_1 @ X0))),
% 0.91/1.16      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.91/1.16  thf('25', plain,
% 0.91/1.16      ((~ (v1_relat_1 @ sk_B_1)
% 0.91/1.16        | ~ (v1_funct_1 @ sk_B_1)
% 0.91/1.16        | (v2_funct_1 @ sk_B_1)
% 0.91/1.16        | ~ (v2_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.91/1.16      inference('sup-', [status(thm)], ['18', '24'])).
% 0.91/1.16  thf('26', plain, ((v1_relat_1 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('27', plain, ((v1_funct_1 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('28', plain, ((v2_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('29', plain, ((v2_funct_1 @ sk_B_1)),
% 0.91/1.16      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 0.91/1.16  thf('30', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.91/1.16      inference('split', [status(esa)], ['0'])).
% 0.91/1.16  thf('31', plain, (((v2_funct_1 @ sk_B_1))),
% 0.91/1.16      inference('sup-', [status(thm)], ['29', '30'])).
% 0.91/1.16  thf('32', plain, (~ ((v2_funct_1 @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.91/1.16      inference('split', [status(esa)], ['0'])).
% 0.91/1.16  thf('33', plain, (~ ((v2_funct_1 @ sk_A))),
% 0.91/1.16      inference('sat_resolution*', [status(thm)], ['31', '32'])).
% 0.91/1.16  thf('34', plain, (~ (v2_funct_1 @ sk_A)),
% 0.91/1.16      inference('simpl_trail', [status(thm)], ['1', '33'])).
% 0.91/1.16  thf('35', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf(d8_funct_1, axiom,
% 0.91/1.16    (![A:$i]:
% 0.91/1.16     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.91/1.16       ( ( v2_funct_1 @ A ) <=>
% 0.91/1.16         ( ![B:$i,C:$i]:
% 0.91/1.16           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.91/1.16               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.91/1.16               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.91/1.16             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.91/1.16  thf('36', plain,
% 0.91/1.16      (![X12 : $i]:
% 0.91/1.16         ((r2_hidden @ (sk_C_1 @ X12) @ (k1_relat_1 @ X12))
% 0.91/1.16          | (v2_funct_1 @ X12)
% 0.91/1.16          | ~ (v1_funct_1 @ X12)
% 0.91/1.16          | ~ (v1_relat_1 @ X12))),
% 0.91/1.16      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.91/1.16  thf('37', plain,
% 0.91/1.16      (((r2_hidden @ (sk_C_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))
% 0.91/1.16        | ~ (v1_relat_1 @ sk_A)
% 0.91/1.16        | ~ (v1_funct_1 @ sk_A)
% 0.91/1.16        | (v2_funct_1 @ sk_A))),
% 0.91/1.16      inference('sup+', [status(thm)], ['35', '36'])).
% 0.91/1.16  thf('38', plain, ((v1_relat_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('39', plain, ((v1_funct_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('40', plain,
% 0.91/1.16      (((r2_hidden @ (sk_C_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))
% 0.91/1.16        | (v2_funct_1 @ sk_A))),
% 0.91/1.16      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.91/1.16  thf(d5_funct_1, axiom,
% 0.91/1.16    (![A:$i]:
% 0.91/1.16     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.91/1.16       ( ![B:$i]:
% 0.91/1.16         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.91/1.16           ( ![C:$i]:
% 0.91/1.16             ( ( r2_hidden @ C @ B ) <=>
% 0.91/1.16               ( ?[D:$i]:
% 0.91/1.16                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.91/1.16                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.91/1.16  thf('41', plain,
% 0.91/1.16      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.91/1.16         (((X8) != (k2_relat_1 @ X6))
% 0.91/1.16          | ((X9) = (k1_funct_1 @ X6 @ (sk_D_1 @ X9 @ X6)))
% 0.91/1.16          | ~ (r2_hidden @ X9 @ X8)
% 0.91/1.16          | ~ (v1_funct_1 @ X6)
% 0.91/1.16          | ~ (v1_relat_1 @ X6))),
% 0.91/1.16      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.91/1.16  thf('42', plain,
% 0.91/1.16      (![X6 : $i, X9 : $i]:
% 0.91/1.16         (~ (v1_relat_1 @ X6)
% 0.91/1.16          | ~ (v1_funct_1 @ X6)
% 0.91/1.16          | ~ (r2_hidden @ X9 @ (k2_relat_1 @ X6))
% 0.91/1.16          | ((X9) = (k1_funct_1 @ X6 @ (sk_D_1 @ X9 @ X6))))),
% 0.91/1.16      inference('simplify', [status(thm)], ['41'])).
% 0.91/1.16  thf('43', plain,
% 0.91/1.16      (((v2_funct_1 @ sk_A)
% 0.91/1.16        | ((sk_C_1 @ sk_A)
% 0.91/1.16            = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1)))
% 0.91/1.16        | ~ (v1_funct_1 @ sk_B_1)
% 0.91/1.16        | ~ (v1_relat_1 @ sk_B_1))),
% 0.91/1.16      inference('sup-', [status(thm)], ['40', '42'])).
% 0.91/1.16  thf('44', plain, ((v1_funct_1 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('45', plain, ((v1_relat_1 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('46', plain,
% 0.91/1.16      (((v2_funct_1 @ sk_A)
% 0.91/1.16        | ((sk_C_1 @ sk_A)
% 0.91/1.16            = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1))))),
% 0.91/1.16      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.91/1.16  thf('47', plain, (~ (v2_funct_1 @ sk_A)),
% 0.91/1.16      inference('simpl_trail', [status(thm)], ['1', '33'])).
% 0.91/1.16  thf('48', plain,
% 0.91/1.16      (((sk_C_1 @ sk_A)
% 0.91/1.16         = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1)))),
% 0.91/1.16      inference('clc', [status(thm)], ['46', '47'])).
% 0.91/1.16  thf('49', plain,
% 0.91/1.16      (((r2_hidden @ (sk_C_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))
% 0.91/1.16        | (v2_funct_1 @ sk_A))),
% 0.91/1.16      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.91/1.16  thf('50', plain,
% 0.91/1.16      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.91/1.16         (((X8) != (k2_relat_1 @ X6))
% 0.91/1.16          | (r2_hidden @ (sk_D_1 @ X9 @ X6) @ (k1_relat_1 @ X6))
% 0.91/1.16          | ~ (r2_hidden @ X9 @ X8)
% 0.91/1.16          | ~ (v1_funct_1 @ X6)
% 0.91/1.16          | ~ (v1_relat_1 @ X6))),
% 0.91/1.16      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.91/1.16  thf('51', plain,
% 0.91/1.16      (![X6 : $i, X9 : $i]:
% 0.91/1.16         (~ (v1_relat_1 @ X6)
% 0.91/1.16          | ~ (v1_funct_1 @ X6)
% 0.91/1.16          | ~ (r2_hidden @ X9 @ (k2_relat_1 @ X6))
% 0.91/1.16          | (r2_hidden @ (sk_D_1 @ X9 @ X6) @ (k1_relat_1 @ X6)))),
% 0.91/1.16      inference('simplify', [status(thm)], ['50'])).
% 0.91/1.16  thf('52', plain,
% 0.91/1.16      (((v2_funct_1 @ sk_A)
% 0.91/1.16        | (r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1) @ 
% 0.91/1.16           (k1_relat_1 @ sk_B_1))
% 0.91/1.16        | ~ (v1_funct_1 @ sk_B_1)
% 0.91/1.16        | ~ (v1_relat_1 @ sk_B_1))),
% 0.91/1.16      inference('sup-', [status(thm)], ['49', '51'])).
% 0.91/1.16  thf('53', plain, ((v1_funct_1 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('54', plain, ((v1_relat_1 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('55', plain,
% 0.91/1.16      (((v2_funct_1 @ sk_A)
% 0.91/1.16        | (r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1) @ 
% 0.91/1.16           (k1_relat_1 @ sk_B_1)))),
% 0.91/1.16      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.91/1.16  thf('56', plain, (~ (v2_funct_1 @ sk_A)),
% 0.91/1.16      inference('simpl_trail', [status(thm)], ['1', '33'])).
% 0.91/1.16  thf('57', plain,
% 0.91/1.16      ((r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1) @ (k1_relat_1 @ sk_B_1))),
% 0.91/1.16      inference('clc', [status(thm)], ['55', '56'])).
% 0.91/1.16  thf(t23_funct_1, axiom,
% 0.91/1.16    (![A:$i,B:$i]:
% 0.91/1.16     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.91/1.16       ( ![C:$i]:
% 0.91/1.16         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.91/1.16           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.91/1.16             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.91/1.16               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 0.91/1.16  thf('58', plain,
% 0.91/1.16      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.91/1.16         (~ (v1_relat_1 @ X17)
% 0.91/1.16          | ~ (v1_funct_1 @ X17)
% 0.91/1.16          | ((k1_funct_1 @ (k5_relat_1 @ X18 @ X17) @ X19)
% 0.91/1.16              = (k1_funct_1 @ X17 @ (k1_funct_1 @ X18 @ X19)))
% 0.91/1.16          | ~ (r2_hidden @ X19 @ (k1_relat_1 @ X18))
% 0.91/1.16          | ~ (v1_funct_1 @ X18)
% 0.91/1.16          | ~ (v1_relat_1 @ X18))),
% 0.91/1.16      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.91/1.16  thf('59', plain,
% 0.91/1.16      (![X0 : $i]:
% 0.91/1.16         (~ (v1_relat_1 @ sk_B_1)
% 0.91/1.16          | ~ (v1_funct_1 @ sk_B_1)
% 0.91/1.16          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ X0) @ 
% 0.91/1.16              (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1))
% 0.91/1.16              = (k1_funct_1 @ X0 @ 
% 0.91/1.16                 (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1))))
% 0.91/1.16          | ~ (v1_funct_1 @ X0)
% 0.91/1.16          | ~ (v1_relat_1 @ X0))),
% 0.91/1.16      inference('sup-', [status(thm)], ['57', '58'])).
% 0.91/1.16  thf('60', plain, ((v1_relat_1 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('61', plain, ((v1_funct_1 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('62', plain,
% 0.91/1.16      (((sk_C_1 @ sk_A)
% 0.91/1.16         = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1)))),
% 0.91/1.16      inference('clc', [status(thm)], ['46', '47'])).
% 0.91/1.16  thf('63', plain,
% 0.91/1.16      (![X0 : $i]:
% 0.91/1.16         (((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ X0) @ 
% 0.91/1.16            (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1))
% 0.91/1.16            = (k1_funct_1 @ X0 @ (sk_C_1 @ sk_A)))
% 0.91/1.16          | ~ (v1_funct_1 @ X0)
% 0.91/1.16          | ~ (v1_relat_1 @ X0))),
% 0.91/1.16      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 0.91/1.16  thf('64', plain,
% 0.91/1.16      (![X2 : $i]:
% 0.91/1.16         (((k10_relat_1 @ X2 @ (k2_relat_1 @ X2)) = (k1_relat_1 @ X2))
% 0.91/1.16          | ~ (v1_relat_1 @ X2))),
% 0.91/1.16      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.91/1.16  thf('65', plain,
% 0.91/1.16      (![X3 : $i, X4 : $i]:
% 0.91/1.16         (~ (v1_relat_1 @ X3)
% 0.91/1.16          | ((k1_relat_1 @ (k5_relat_1 @ X4 @ X3))
% 0.91/1.16              = (k10_relat_1 @ X4 @ (k1_relat_1 @ X3)))
% 0.91/1.16          | ~ (v1_relat_1 @ X4))),
% 0.91/1.16      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.91/1.16  thf(dt_k5_relat_1, axiom,
% 0.91/1.16    (![A:$i,B:$i]:
% 0.91/1.16     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.91/1.16       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.91/1.16  thf('66', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         (~ (v1_relat_1 @ X0)
% 0.91/1.16          | ~ (v1_relat_1 @ X1)
% 0.91/1.16          | (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 0.91/1.16      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.91/1.16  thf(fc2_funct_1, axiom,
% 0.91/1.16    (![A:$i,B:$i]:
% 0.91/1.16     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v1_relat_1 @ B ) & 
% 0.91/1.16         ( v1_funct_1 @ B ) ) =>
% 0.91/1.16       ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) & 
% 0.91/1.16         ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ))).
% 0.91/1.16  thf('67', plain,
% 0.91/1.16      (![X15 : $i, X16 : $i]:
% 0.91/1.16         (~ (v1_funct_1 @ X15)
% 0.91/1.16          | ~ (v1_relat_1 @ X15)
% 0.91/1.16          | ~ (v1_relat_1 @ X16)
% 0.91/1.16          | ~ (v1_funct_1 @ X16)
% 0.91/1.16          | (v1_funct_1 @ (k5_relat_1 @ X15 @ X16)))),
% 0.91/1.16      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.91/1.16  thf('68', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         (~ (v1_relat_1 @ X0)
% 0.91/1.16          | ~ (v1_relat_1 @ X1)
% 0.91/1.16          | (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 0.91/1.16      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.91/1.16  thf('69', plain,
% 0.91/1.16      (![X15 : $i, X16 : $i]:
% 0.91/1.16         (~ (v1_funct_1 @ X15)
% 0.91/1.16          | ~ (v1_relat_1 @ X15)
% 0.91/1.16          | ~ (v1_relat_1 @ X16)
% 0.91/1.16          | ~ (v1_funct_1 @ X16)
% 0.91/1.16          | (v1_funct_1 @ (k5_relat_1 @ X15 @ X16)))),
% 0.91/1.16      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.91/1.16  thf('70', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('71', plain,
% 0.91/1.16      (![X12 : $i]:
% 0.91/1.16         ((r2_hidden @ (sk_B @ X12) @ (k1_relat_1 @ X12))
% 0.91/1.16          | (v2_funct_1 @ X12)
% 0.91/1.16          | ~ (v1_funct_1 @ X12)
% 0.91/1.16          | ~ (v1_relat_1 @ X12))),
% 0.91/1.16      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.91/1.16  thf('72', plain,
% 0.91/1.16      (((r2_hidden @ (sk_B @ sk_A) @ (k2_relat_1 @ sk_B_1))
% 0.91/1.16        | ~ (v1_relat_1 @ sk_A)
% 0.91/1.16        | ~ (v1_funct_1 @ sk_A)
% 0.91/1.16        | (v2_funct_1 @ sk_A))),
% 0.91/1.16      inference('sup+', [status(thm)], ['70', '71'])).
% 0.91/1.16  thf('73', plain, ((v1_relat_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('74', plain, ((v1_funct_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('75', plain,
% 0.91/1.16      (((r2_hidden @ (sk_B @ sk_A) @ (k2_relat_1 @ sk_B_1))
% 0.91/1.16        | (v2_funct_1 @ sk_A))),
% 0.91/1.16      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.91/1.16  thf('76', plain,
% 0.91/1.16      (![X6 : $i, X9 : $i]:
% 0.91/1.16         (~ (v1_relat_1 @ X6)
% 0.91/1.16          | ~ (v1_funct_1 @ X6)
% 0.91/1.16          | ~ (r2_hidden @ X9 @ (k2_relat_1 @ X6))
% 0.91/1.16          | (r2_hidden @ (sk_D_1 @ X9 @ X6) @ (k1_relat_1 @ X6)))),
% 0.91/1.16      inference('simplify', [status(thm)], ['50'])).
% 0.91/1.16  thf('77', plain,
% 0.91/1.16      (((v2_funct_1 @ sk_A)
% 0.91/1.16        | (r2_hidden @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) @ 
% 0.91/1.16           (k1_relat_1 @ sk_B_1))
% 0.91/1.16        | ~ (v1_funct_1 @ sk_B_1)
% 0.91/1.16        | ~ (v1_relat_1 @ sk_B_1))),
% 0.91/1.16      inference('sup-', [status(thm)], ['75', '76'])).
% 0.91/1.16  thf('78', plain, ((v1_funct_1 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('79', plain, ((v1_relat_1 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('80', plain,
% 0.91/1.16      (((v2_funct_1 @ sk_A)
% 0.91/1.16        | (r2_hidden @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) @ 
% 0.91/1.16           (k1_relat_1 @ sk_B_1)))),
% 0.91/1.16      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.91/1.16  thf('81', plain, (~ (v2_funct_1 @ sk_A)),
% 0.91/1.16      inference('simpl_trail', [status(thm)], ['1', '33'])).
% 0.91/1.16  thf('82', plain,
% 0.91/1.16      ((r2_hidden @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) @ (k1_relat_1 @ sk_B_1))),
% 0.91/1.16      inference('clc', [status(thm)], ['80', '81'])).
% 0.91/1.16  thf('83', plain,
% 0.91/1.16      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.91/1.16         (~ (v1_relat_1 @ X17)
% 0.91/1.16          | ~ (v1_funct_1 @ X17)
% 0.91/1.16          | ((k1_funct_1 @ (k5_relat_1 @ X18 @ X17) @ X19)
% 0.91/1.16              = (k1_funct_1 @ X17 @ (k1_funct_1 @ X18 @ X19)))
% 0.91/1.16          | ~ (r2_hidden @ X19 @ (k1_relat_1 @ X18))
% 0.91/1.16          | ~ (v1_funct_1 @ X18)
% 0.91/1.16          | ~ (v1_relat_1 @ X18))),
% 0.91/1.16      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.91/1.16  thf('84', plain,
% 0.91/1.16      (![X0 : $i]:
% 0.91/1.16         (~ (v1_relat_1 @ sk_B_1)
% 0.91/1.16          | ~ (v1_funct_1 @ sk_B_1)
% 0.91/1.16          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ X0) @ 
% 0.91/1.16              (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1))
% 0.91/1.16              = (k1_funct_1 @ X0 @ 
% 0.91/1.16                 (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1))))
% 0.91/1.16          | ~ (v1_funct_1 @ X0)
% 0.91/1.16          | ~ (v1_relat_1 @ X0))),
% 0.91/1.16      inference('sup-', [status(thm)], ['82', '83'])).
% 0.91/1.16  thf('85', plain, ((v1_relat_1 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('86', plain, ((v1_funct_1 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('87', plain,
% 0.91/1.16      (((r2_hidden @ (sk_B @ sk_A) @ (k2_relat_1 @ sk_B_1))
% 0.91/1.16        | (v2_funct_1 @ sk_A))),
% 0.91/1.16      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.91/1.16  thf('88', plain,
% 0.91/1.16      (![X6 : $i, X9 : $i]:
% 0.91/1.16         (~ (v1_relat_1 @ X6)
% 0.91/1.16          | ~ (v1_funct_1 @ X6)
% 0.91/1.16          | ~ (r2_hidden @ X9 @ (k2_relat_1 @ X6))
% 0.91/1.16          | ((X9) = (k1_funct_1 @ X6 @ (sk_D_1 @ X9 @ X6))))),
% 0.91/1.16      inference('simplify', [status(thm)], ['41'])).
% 0.91/1.16  thf('89', plain,
% 0.91/1.16      (((v2_funct_1 @ sk_A)
% 0.91/1.16        | ((sk_B @ sk_A)
% 0.91/1.16            = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)))
% 0.91/1.16        | ~ (v1_funct_1 @ sk_B_1)
% 0.91/1.16        | ~ (v1_relat_1 @ sk_B_1))),
% 0.91/1.16      inference('sup-', [status(thm)], ['87', '88'])).
% 0.91/1.16  thf('90', plain, ((v1_funct_1 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('91', plain, ((v1_relat_1 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('92', plain,
% 0.91/1.16      (((v2_funct_1 @ sk_A)
% 0.91/1.16        | ((sk_B @ sk_A)
% 0.91/1.16            = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1))))),
% 0.91/1.16      inference('demod', [status(thm)], ['89', '90', '91'])).
% 0.91/1.16  thf('93', plain, (~ (v2_funct_1 @ sk_A)),
% 0.91/1.16      inference('simpl_trail', [status(thm)], ['1', '33'])).
% 0.91/1.16  thf('94', plain,
% 0.91/1.16      (((sk_B @ sk_A)
% 0.91/1.16         = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)))),
% 0.91/1.16      inference('clc', [status(thm)], ['92', '93'])).
% 0.91/1.16  thf('95', plain,
% 0.91/1.16      (![X0 : $i]:
% 0.91/1.16         (((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ X0) @ 
% 0.91/1.16            (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1))
% 0.91/1.16            = (k1_funct_1 @ X0 @ (sk_B @ sk_A)))
% 0.91/1.16          | ~ (v1_funct_1 @ X0)
% 0.91/1.16          | ~ (v1_relat_1 @ X0))),
% 0.91/1.16      inference('demod', [status(thm)], ['84', '85', '86', '94'])).
% 0.91/1.16  thf('96', plain,
% 0.91/1.16      ((r2_hidden @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) @ (k1_relat_1 @ sk_B_1))),
% 0.91/1.16      inference('clc', [status(thm)], ['80', '81'])).
% 0.91/1.16  thf('97', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         (~ (v1_relat_1 @ X0)
% 0.91/1.16          | ~ (v1_relat_1 @ X1)
% 0.91/1.16          | (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 0.91/1.16      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.91/1.16  thf('98', plain,
% 0.91/1.16      (![X15 : $i, X16 : $i]:
% 0.91/1.16         (~ (v1_funct_1 @ X15)
% 0.91/1.16          | ~ (v1_relat_1 @ X15)
% 0.91/1.16          | ~ (v1_relat_1 @ X16)
% 0.91/1.16          | ~ (v1_funct_1 @ X16)
% 0.91/1.16          | (v1_funct_1 @ (k5_relat_1 @ X15 @ X16)))),
% 0.91/1.16      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.91/1.16  thf('99', plain,
% 0.91/1.16      (![X2 : $i]:
% 0.91/1.16         (((k10_relat_1 @ X2 @ (k2_relat_1 @ X2)) = (k1_relat_1 @ X2))
% 0.91/1.16          | ~ (v1_relat_1 @ X2))),
% 0.91/1.16      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.91/1.16  thf('100', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('101', plain,
% 0.91/1.16      (![X3 : $i, X4 : $i]:
% 0.91/1.16         (~ (v1_relat_1 @ X3)
% 0.91/1.16          | ((k1_relat_1 @ (k5_relat_1 @ X4 @ X3))
% 0.91/1.16              = (k10_relat_1 @ X4 @ (k1_relat_1 @ X3)))
% 0.91/1.16          | ~ (v1_relat_1 @ X4))),
% 0.91/1.16      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.91/1.16  thf('102', plain,
% 0.91/1.16      (![X6 : $i, X8 : $i, X10 : $i, X11 : $i]:
% 0.91/1.16         (((X8) != (k2_relat_1 @ X6))
% 0.91/1.16          | (r2_hidden @ X10 @ X8)
% 0.91/1.16          | ~ (r2_hidden @ X11 @ (k1_relat_1 @ X6))
% 0.91/1.16          | ((X10) != (k1_funct_1 @ X6 @ X11))
% 0.91/1.16          | ~ (v1_funct_1 @ X6)
% 0.91/1.16          | ~ (v1_relat_1 @ X6))),
% 0.91/1.16      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.91/1.16  thf('103', plain,
% 0.91/1.16      (![X6 : $i, X11 : $i]:
% 0.91/1.16         (~ (v1_relat_1 @ X6)
% 0.91/1.16          | ~ (v1_funct_1 @ X6)
% 0.91/1.16          | ~ (r2_hidden @ X11 @ (k1_relat_1 @ X6))
% 0.91/1.16          | (r2_hidden @ (k1_funct_1 @ X6 @ X11) @ (k2_relat_1 @ X6)))),
% 0.91/1.16      inference('simplify', [status(thm)], ['102'])).
% 0.91/1.16  thf('104', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.16         (~ (r2_hidden @ X2 @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.91/1.16          | ~ (v1_relat_1 @ X1)
% 0.91/1.16          | ~ (v1_relat_1 @ X0)
% 0.91/1.16          | (r2_hidden @ (k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 0.91/1.16             (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.91/1.16          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.91/1.16          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.91/1.16      inference('sup-', [status(thm)], ['101', '103'])).
% 0.91/1.16  thf('105', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         (~ (r2_hidden @ X1 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ sk_B_1)))
% 0.91/1.16          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ sk_A))
% 0.91/1.16          | ~ (v1_funct_1 @ (k5_relat_1 @ X0 @ sk_A))
% 0.91/1.16          | (r2_hidden @ (k1_funct_1 @ (k5_relat_1 @ X0 @ sk_A) @ X1) @ 
% 0.91/1.16             (k2_relat_1 @ (k5_relat_1 @ X0 @ sk_A)))
% 0.91/1.16          | ~ (v1_relat_1 @ sk_A)
% 0.91/1.16          | ~ (v1_relat_1 @ X0))),
% 0.91/1.16      inference('sup-', [status(thm)], ['100', '104'])).
% 0.91/1.16  thf('106', plain, ((v1_relat_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('107', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         (~ (r2_hidden @ X1 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ sk_B_1)))
% 0.91/1.16          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ sk_A))
% 0.91/1.16          | ~ (v1_funct_1 @ (k5_relat_1 @ X0 @ sk_A))
% 0.91/1.16          | (r2_hidden @ (k1_funct_1 @ (k5_relat_1 @ X0 @ sk_A) @ X1) @ 
% 0.91/1.16             (k2_relat_1 @ (k5_relat_1 @ X0 @ sk_A)))
% 0.91/1.16          | ~ (v1_relat_1 @ X0))),
% 0.91/1.16      inference('demod', [status(thm)], ['105', '106'])).
% 0.91/1.16  thf('108', plain,
% 0.91/1.16      (![X0 : $i]:
% 0.91/1.16         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.91/1.16          | ~ (v1_relat_1 @ sk_B_1)
% 0.91/1.16          | ~ (v1_relat_1 @ sk_B_1)
% 0.91/1.16          | (r2_hidden @ (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0) @ 
% 0.91/1.16             (k2_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.91/1.16          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.91/1.16          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.91/1.16      inference('sup-', [status(thm)], ['99', '107'])).
% 0.91/1.16  thf('109', plain, ((v1_relat_1 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('110', plain, ((v1_relat_1 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('111', plain,
% 0.91/1.16      (![X0 : $i]:
% 0.91/1.16         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.91/1.16          | (r2_hidden @ (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0) @ 
% 0.91/1.16             (k2_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.91/1.16          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.91/1.16          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.91/1.16      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.91/1.16  thf('112', plain,
% 0.91/1.16      (![X0 : $i]:
% 0.91/1.16         (~ (v1_funct_1 @ sk_A)
% 0.91/1.16          | ~ (v1_relat_1 @ sk_A)
% 0.91/1.16          | ~ (v1_relat_1 @ sk_B_1)
% 0.91/1.16          | ~ (v1_funct_1 @ sk_B_1)
% 0.91/1.16          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.91/1.16          | (r2_hidden @ (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0) @ 
% 0.91/1.16             (k2_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.91/1.16          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1)))),
% 0.91/1.16      inference('sup-', [status(thm)], ['98', '111'])).
% 0.91/1.16  thf('113', plain, ((v1_funct_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('114', plain, ((v1_relat_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('115', plain, ((v1_relat_1 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('116', plain, ((v1_funct_1 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('117', plain,
% 0.91/1.16      (![X0 : $i]:
% 0.91/1.16         (~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.91/1.16          | (r2_hidden @ (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0) @ 
% 0.91/1.16             (k2_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.91/1.16          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1)))),
% 0.91/1.16      inference('demod', [status(thm)], ['112', '113', '114', '115', '116'])).
% 0.91/1.16  thf('118', plain,
% 0.91/1.16      (![X0 : $i]:
% 0.91/1.16         (~ (v1_relat_1 @ sk_A)
% 0.91/1.16          | ~ (v1_relat_1 @ sk_B_1)
% 0.91/1.16          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.91/1.16          | (r2_hidden @ (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0) @ 
% 0.91/1.16             (k2_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))))),
% 0.91/1.16      inference('sup-', [status(thm)], ['97', '117'])).
% 0.91/1.16  thf('119', plain, ((v1_relat_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('120', plain, ((v1_relat_1 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('121', plain,
% 0.91/1.16      (![X0 : $i]:
% 0.91/1.16         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.91/1.16          | (r2_hidden @ (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0) @ 
% 0.91/1.16             (k2_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))))),
% 0.91/1.16      inference('demod', [status(thm)], ['118', '119', '120'])).
% 0.91/1.16  thf('122', plain,
% 0.91/1.16      ((r2_hidden @ 
% 0.91/1.16        (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.91/1.16         (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)) @ 
% 0.91/1.16        (k2_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.91/1.16      inference('sup-', [status(thm)], ['96', '121'])).
% 0.91/1.16  thf('123', plain,
% 0.91/1.16      (((r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.91/1.16         (k2_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.91/1.16        | ~ (v1_relat_1 @ sk_A)
% 0.91/1.16        | ~ (v1_funct_1 @ sk_A))),
% 0.91/1.16      inference('sup+', [status(thm)], ['95', '122'])).
% 0.91/1.16  thf('124', plain, ((v1_relat_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('125', plain, ((v1_funct_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('126', plain,
% 0.91/1.16      ((r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.91/1.16        (k2_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.91/1.16      inference('demod', [status(thm)], ['123', '124', '125'])).
% 0.91/1.16  thf('127', plain,
% 0.91/1.16      (![X6 : $i, X9 : $i]:
% 0.91/1.16         (~ (v1_relat_1 @ X6)
% 0.91/1.16          | ~ (v1_funct_1 @ X6)
% 0.91/1.16          | ~ (r2_hidden @ X9 @ (k2_relat_1 @ X6))
% 0.91/1.16          | ((X9) = (k1_funct_1 @ X6 @ (sk_D_1 @ X9 @ X6))))),
% 0.91/1.16      inference('simplify', [status(thm)], ['41'])).
% 0.91/1.16  thf('128', plain,
% 0.91/1.16      ((((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.91/1.16          = (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.91/1.16             (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.91/1.16              (k5_relat_1 @ sk_B_1 @ sk_A))))
% 0.91/1.16        | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.91/1.16        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.91/1.16      inference('sup-', [status(thm)], ['126', '127'])).
% 0.91/1.16  thf('129', plain,
% 0.91/1.16      ((~ (v1_funct_1 @ sk_A)
% 0.91/1.16        | ~ (v1_relat_1 @ sk_A)
% 0.91/1.16        | ~ (v1_relat_1 @ sk_B_1)
% 0.91/1.16        | ~ (v1_funct_1 @ sk_B_1)
% 0.91/1.16        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.91/1.16        | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.91/1.16            = (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.91/1.16               (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.91/1.16                (k5_relat_1 @ sk_B_1 @ sk_A)))))),
% 0.91/1.16      inference('sup-', [status(thm)], ['69', '128'])).
% 0.91/1.16  thf('130', plain, ((v1_funct_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('131', plain, ((v1_relat_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('132', plain, ((v1_relat_1 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('133', plain, ((v1_funct_1 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('134', plain,
% 0.91/1.16      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.91/1.16        | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.91/1.16            = (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.91/1.16               (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.91/1.16                (k5_relat_1 @ sk_B_1 @ sk_A)))))),
% 0.91/1.16      inference('demod', [status(thm)], ['129', '130', '131', '132', '133'])).
% 0.91/1.16  thf('135', plain,
% 0.91/1.16      ((~ (v1_relat_1 @ sk_A)
% 0.91/1.16        | ~ (v1_relat_1 @ sk_B_1)
% 0.91/1.16        | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.91/1.16            = (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.91/1.16               (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.91/1.16                (k5_relat_1 @ sk_B_1 @ sk_A)))))),
% 0.91/1.16      inference('sup-', [status(thm)], ['68', '134'])).
% 0.91/1.16  thf('136', plain, ((v1_relat_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('137', plain, ((v1_relat_1 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('138', plain,
% 0.91/1.16      (((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.91/1.16         = (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.91/1.16            (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.91/1.16             (k5_relat_1 @ sk_B_1 @ sk_A))))),
% 0.91/1.16      inference('demod', [status(thm)], ['135', '136', '137'])).
% 0.91/1.16  thf('139', plain,
% 0.91/1.16      (![X3 : $i, X4 : $i]:
% 0.91/1.16         (~ (v1_relat_1 @ X3)
% 0.91/1.16          | ((k1_relat_1 @ (k5_relat_1 @ X4 @ X3))
% 0.91/1.16              = (k10_relat_1 @ X4 @ (k1_relat_1 @ X3)))
% 0.91/1.16          | ~ (v1_relat_1 @ X4))),
% 0.91/1.16      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.91/1.16  thf('140', plain,
% 0.91/1.16      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.91/1.16         (~ (v2_funct_1 @ X12)
% 0.91/1.16          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X12))
% 0.91/1.16          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X12))
% 0.91/1.16          | ((k1_funct_1 @ X12 @ X13) != (k1_funct_1 @ X12 @ X14))
% 0.91/1.16          | ((X13) = (X14))
% 0.91/1.16          | ~ (v1_funct_1 @ X12)
% 0.91/1.16          | ~ (v1_relat_1 @ X12))),
% 0.91/1.16      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.91/1.16  thf('141', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.91/1.16         (~ (r2_hidden @ X2 @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.91/1.16          | ~ (v1_relat_1 @ X1)
% 0.91/1.16          | ~ (v1_relat_1 @ X0)
% 0.91/1.16          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.91/1.16          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.91/1.16          | ((X2) = (X3))
% 0.91/1.16          | ((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.91/1.16              != (k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X3))
% 0.91/1.16          | ~ (r2_hidden @ X3 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.91/1.16          | ~ (v2_funct_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.91/1.16      inference('sup-', [status(thm)], ['139', '140'])).
% 0.91/1.16  thf('142', plain,
% 0.91/1.16      (![X0 : $i]:
% 0.91/1.16         (((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.91/1.16            != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.91/1.16          | ~ (v2_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.91/1.16          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.91/1.16          | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.91/1.16              (k5_relat_1 @ sk_B_1 @ sk_A)) = (X0))
% 0.91/1.16          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.91/1.16          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.91/1.16          | ~ (v1_relat_1 @ sk_A)
% 0.91/1.16          | ~ (v1_relat_1 @ sk_B_1)
% 0.91/1.16          | ~ (r2_hidden @ 
% 0.91/1.16               (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.91/1.16                (k5_relat_1 @ sk_B_1 @ sk_A)) @ 
% 0.91/1.16               (k10_relat_1 @ sk_B_1 @ (k1_relat_1 @ sk_A))))),
% 0.91/1.16      inference('sup-', [status(thm)], ['138', '141'])).
% 0.91/1.16  thf('143', plain, ((v2_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('144', plain, ((v1_relat_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('145', plain, ((v1_relat_1 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('146', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('147', plain,
% 0.91/1.16      (![X3 : $i, X4 : $i]:
% 0.91/1.16         (~ (v1_relat_1 @ X3)
% 0.91/1.16          | ((k1_relat_1 @ (k5_relat_1 @ X4 @ X3))
% 0.91/1.16              = (k10_relat_1 @ X4 @ (k1_relat_1 @ X3)))
% 0.91/1.16          | ~ (v1_relat_1 @ X4))),
% 0.91/1.16      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.91/1.16  thf('148', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         (~ (v1_relat_1 @ X0)
% 0.91/1.16          | ~ (v1_relat_1 @ X1)
% 0.91/1.16          | (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 0.91/1.16      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.91/1.16  thf('149', plain,
% 0.91/1.16      (![X15 : $i, X16 : $i]:
% 0.91/1.16         (~ (v1_funct_1 @ X15)
% 0.91/1.16          | ~ (v1_relat_1 @ X15)
% 0.91/1.16          | ~ (v1_relat_1 @ X16)
% 0.91/1.16          | ~ (v1_funct_1 @ X16)
% 0.91/1.16          | (v1_funct_1 @ (k5_relat_1 @ X15 @ X16)))),
% 0.91/1.16      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.91/1.16  thf('150', plain,
% 0.91/1.16      ((r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.91/1.16        (k2_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.91/1.16      inference('demod', [status(thm)], ['123', '124', '125'])).
% 0.91/1.16  thf('151', plain,
% 0.91/1.16      (![X6 : $i, X9 : $i]:
% 0.91/1.16         (~ (v1_relat_1 @ X6)
% 0.91/1.16          | ~ (v1_funct_1 @ X6)
% 0.91/1.16          | ~ (r2_hidden @ X9 @ (k2_relat_1 @ X6))
% 0.91/1.16          | (r2_hidden @ (sk_D_1 @ X9 @ X6) @ (k1_relat_1 @ X6)))),
% 0.91/1.16      inference('simplify', [status(thm)], ['50'])).
% 0.91/1.16  thf('152', plain,
% 0.91/1.16      (((r2_hidden @ 
% 0.91/1.16         (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.91/1.16          (k5_relat_1 @ sk_B_1 @ sk_A)) @ 
% 0.91/1.16         (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.91/1.16        | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.91/1.16        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.91/1.16      inference('sup-', [status(thm)], ['150', '151'])).
% 0.91/1.16  thf('153', plain,
% 0.91/1.16      ((~ (v1_funct_1 @ sk_A)
% 0.91/1.16        | ~ (v1_relat_1 @ sk_A)
% 0.91/1.16        | ~ (v1_relat_1 @ sk_B_1)
% 0.91/1.16        | ~ (v1_funct_1 @ sk_B_1)
% 0.91/1.16        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.91/1.16        | (r2_hidden @ 
% 0.91/1.16           (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.91/1.16            (k5_relat_1 @ sk_B_1 @ sk_A)) @ 
% 0.91/1.16           (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))))),
% 0.91/1.16      inference('sup-', [status(thm)], ['149', '152'])).
% 0.91/1.16  thf('154', plain, ((v1_funct_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('155', plain, ((v1_relat_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('156', plain, ((v1_relat_1 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('157', plain, ((v1_funct_1 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('158', plain,
% 0.91/1.16      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.91/1.16        | (r2_hidden @ 
% 0.91/1.16           (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.91/1.16            (k5_relat_1 @ sk_B_1 @ sk_A)) @ 
% 0.91/1.16           (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))))),
% 0.91/1.16      inference('demod', [status(thm)], ['153', '154', '155', '156', '157'])).
% 0.91/1.16  thf('159', plain,
% 0.91/1.16      ((~ (v1_relat_1 @ sk_A)
% 0.91/1.16        | ~ (v1_relat_1 @ sk_B_1)
% 0.91/1.16        | (r2_hidden @ 
% 0.91/1.16           (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.91/1.16            (k5_relat_1 @ sk_B_1 @ sk_A)) @ 
% 0.91/1.16           (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))))),
% 0.91/1.16      inference('sup-', [status(thm)], ['148', '158'])).
% 0.91/1.16  thf('160', plain, ((v1_relat_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('161', plain, ((v1_relat_1 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('162', plain,
% 0.91/1.16      ((r2_hidden @ 
% 0.91/1.16        (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.91/1.16         (k5_relat_1 @ sk_B_1 @ sk_A)) @ 
% 0.91/1.16        (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.91/1.16      inference('demod', [status(thm)], ['159', '160', '161'])).
% 0.91/1.16  thf('163', plain,
% 0.91/1.16      (((r2_hidden @ 
% 0.91/1.16         (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.91/1.16          (k5_relat_1 @ sk_B_1 @ sk_A)) @ 
% 0.91/1.16         (k10_relat_1 @ sk_B_1 @ (k1_relat_1 @ sk_A)))
% 0.91/1.16        | ~ (v1_relat_1 @ sk_B_1)
% 0.91/1.16        | ~ (v1_relat_1 @ sk_A))),
% 0.91/1.16      inference('sup+', [status(thm)], ['147', '162'])).
% 0.91/1.16  thf('164', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('165', plain, ((v1_relat_1 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('166', plain, ((v1_relat_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('167', plain,
% 0.91/1.16      ((r2_hidden @ 
% 0.91/1.16        (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.91/1.16         (k5_relat_1 @ sk_B_1 @ sk_A)) @ 
% 0.91/1.16        (k10_relat_1 @ sk_B_1 @ (k2_relat_1 @ sk_B_1)))),
% 0.91/1.16      inference('demod', [status(thm)], ['163', '164', '165', '166'])).
% 0.91/1.16  thf('168', plain,
% 0.91/1.16      (![X0 : $i]:
% 0.91/1.16         (((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.91/1.16            != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.91/1.16          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.91/1.16          | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.91/1.16              (k5_relat_1 @ sk_B_1 @ sk_A)) = (X0))
% 0.91/1.16          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.91/1.16          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.91/1.16      inference('demod', [status(thm)],
% 0.91/1.16                ['142', '143', '144', '145', '146', '167'])).
% 0.91/1.16  thf('169', plain,
% 0.91/1.16      (![X0 : $i]:
% 0.91/1.16         (~ (v1_funct_1 @ sk_A)
% 0.91/1.16          | ~ (v1_relat_1 @ sk_A)
% 0.91/1.16          | ~ (v1_relat_1 @ sk_B_1)
% 0.91/1.16          | ~ (v1_funct_1 @ sk_B_1)
% 0.91/1.16          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.91/1.16          | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.91/1.16              (k5_relat_1 @ sk_B_1 @ sk_A)) = (X0))
% 0.91/1.16          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.91/1.16          | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.91/1.16              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)))),
% 0.91/1.16      inference('sup-', [status(thm)], ['67', '168'])).
% 0.91/1.16  thf('170', plain, ((v1_funct_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('171', plain, ((v1_relat_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('172', plain, ((v1_relat_1 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('173', plain, ((v1_funct_1 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('174', plain,
% 0.91/1.16      (![X0 : $i]:
% 0.91/1.16         (~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.91/1.16          | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.91/1.16              (k5_relat_1 @ sk_B_1 @ sk_A)) = (X0))
% 0.91/1.16          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.91/1.16          | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.91/1.16              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)))),
% 0.91/1.16      inference('demod', [status(thm)], ['169', '170', '171', '172', '173'])).
% 0.91/1.16  thf('175', plain,
% 0.91/1.16      (![X0 : $i]:
% 0.91/1.16         (~ (v1_relat_1 @ sk_A)
% 0.91/1.16          | ~ (v1_relat_1 @ sk_B_1)
% 0.91/1.16          | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.91/1.16              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.91/1.16          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.91/1.16          | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.91/1.16              (k5_relat_1 @ sk_B_1 @ sk_A)) = (X0)))),
% 0.91/1.16      inference('sup-', [status(thm)], ['66', '174'])).
% 0.91/1.16  thf('176', plain, ((v1_relat_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('177', plain, ((v1_relat_1 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('178', plain,
% 0.91/1.16      (![X0 : $i]:
% 0.91/1.16         (((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.91/1.16            != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.91/1.16          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.91/1.16          | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.91/1.16              (k5_relat_1 @ sk_B_1 @ sk_A)) = (X0)))),
% 0.91/1.16      inference('demod', [status(thm)], ['175', '176', '177'])).
% 0.91/1.16  thf('179', plain,
% 0.91/1.16      (![X0 : $i]:
% 0.91/1.16         (~ (r2_hidden @ X0 @ (k10_relat_1 @ sk_B_1 @ (k1_relat_1 @ sk_A)))
% 0.91/1.16          | ~ (v1_relat_1 @ sk_B_1)
% 0.91/1.16          | ~ (v1_relat_1 @ sk_A)
% 0.91/1.16          | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.91/1.16              (k5_relat_1 @ sk_B_1 @ sk_A)) = (X0))
% 0.91/1.16          | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.91/1.16              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)))),
% 0.91/1.16      inference('sup-', [status(thm)], ['65', '178'])).
% 0.91/1.16  thf('180', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('181', plain, ((v1_relat_1 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('182', plain, ((v1_relat_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('183', plain,
% 0.91/1.16      (![X0 : $i]:
% 0.91/1.16         (~ (r2_hidden @ X0 @ (k10_relat_1 @ sk_B_1 @ (k2_relat_1 @ sk_B_1)))
% 0.91/1.16          | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.91/1.16              (k5_relat_1 @ sk_B_1 @ sk_A)) = (X0))
% 0.91/1.16          | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.91/1.16              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)))),
% 0.91/1.16      inference('demod', [status(thm)], ['179', '180', '181', '182'])).
% 0.91/1.16  thf('184', plain,
% 0.91/1.16      (![X0 : $i]:
% 0.91/1.16         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.91/1.16          | ~ (v1_relat_1 @ sk_B_1)
% 0.91/1.16          | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.91/1.16              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.91/1.16          | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.91/1.16              (k5_relat_1 @ sk_B_1 @ sk_A)) = (X0)))),
% 0.91/1.16      inference('sup-', [status(thm)], ['64', '183'])).
% 0.91/1.16  thf('185', plain, ((v1_relat_1 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('186', plain,
% 0.91/1.16      (![X0 : $i]:
% 0.91/1.16         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.91/1.16          | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.91/1.16              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.91/1.16          | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.91/1.16              (k5_relat_1 @ sk_B_1 @ sk_A)) = (X0)))),
% 0.91/1.16      inference('demod', [status(thm)], ['184', '185'])).
% 0.91/1.16  thf('187', plain,
% 0.91/1.16      ((((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.91/1.16          != (k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A)))
% 0.91/1.16        | ~ (v1_relat_1 @ sk_A)
% 0.91/1.16        | ~ (v1_funct_1 @ sk_A)
% 0.91/1.16        | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.91/1.16            (k5_relat_1 @ sk_B_1 @ sk_A)) = (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1))
% 0.91/1.16        | ~ (r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1) @ 
% 0.91/1.16             (k1_relat_1 @ sk_B_1)))),
% 0.91/1.16      inference('sup-', [status(thm)], ['63', '186'])).
% 0.91/1.16  thf('188', plain,
% 0.91/1.16      (![X12 : $i]:
% 0.91/1.16         (((k1_funct_1 @ X12 @ (sk_B @ X12))
% 0.91/1.16            = (k1_funct_1 @ X12 @ (sk_C_1 @ X12)))
% 0.91/1.16          | (v2_funct_1 @ X12)
% 0.91/1.16          | ~ (v1_funct_1 @ X12)
% 0.91/1.16          | ~ (v1_relat_1 @ X12))),
% 0.91/1.16      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.91/1.16  thf('189', plain,
% 0.91/1.16      ((r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1) @ (k1_relat_1 @ sk_B_1))),
% 0.91/1.16      inference('clc', [status(thm)], ['55', '56'])).
% 0.91/1.16  thf('190', plain,
% 0.91/1.16      (![X6 : $i, X11 : $i]:
% 0.91/1.16         (~ (v1_relat_1 @ X6)
% 0.91/1.16          | ~ (v1_funct_1 @ X6)
% 0.91/1.16          | ~ (r2_hidden @ X11 @ (k1_relat_1 @ X6))
% 0.91/1.16          | (r2_hidden @ (k1_funct_1 @ X6 @ X11) @ (k2_relat_1 @ X6)))),
% 0.91/1.16      inference('simplify', [status(thm)], ['102'])).
% 0.91/1.16  thf('191', plain,
% 0.91/1.16      (((r2_hidden @ 
% 0.91/1.16         (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1)) @ 
% 0.91/1.16         (k2_relat_1 @ sk_B_1))
% 0.91/1.16        | ~ (v1_funct_1 @ sk_B_1)
% 0.91/1.16        | ~ (v1_relat_1 @ sk_B_1))),
% 0.91/1.16      inference('sup-', [status(thm)], ['189', '190'])).
% 0.91/1.16  thf('192', plain,
% 0.91/1.16      (((sk_C_1 @ sk_A)
% 0.91/1.16         = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1)))),
% 0.91/1.16      inference('clc', [status(thm)], ['46', '47'])).
% 0.91/1.16  thf('193', plain, ((v1_funct_1 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('194', plain, ((v1_relat_1 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('195', plain, ((r2_hidden @ (sk_C_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 0.91/1.16      inference('demod', [status(thm)], ['191', '192', '193', '194'])).
% 0.91/1.16  thf('196', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('197', plain,
% 0.91/1.16      (![X6 : $i, X11 : $i]:
% 0.91/1.16         (~ (v1_relat_1 @ X6)
% 0.91/1.16          | ~ (v1_funct_1 @ X6)
% 0.91/1.16          | ~ (r2_hidden @ X11 @ (k1_relat_1 @ X6))
% 0.91/1.16          | (r2_hidden @ (k1_funct_1 @ X6 @ X11) @ (k2_relat_1 @ X6)))),
% 0.91/1.16      inference('simplify', [status(thm)], ['102'])).
% 0.91/1.16  thf('198', plain,
% 0.91/1.16      (![X0 : $i]:
% 0.91/1.16         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B_1))
% 0.91/1.16          | (r2_hidden @ (k1_funct_1 @ sk_A @ X0) @ (k2_relat_1 @ sk_A))
% 0.91/1.16          | ~ (v1_funct_1 @ sk_A)
% 0.91/1.16          | ~ (v1_relat_1 @ sk_A))),
% 0.91/1.16      inference('sup-', [status(thm)], ['196', '197'])).
% 0.91/1.16  thf('199', plain, ((v1_funct_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('200', plain, ((v1_relat_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('201', plain,
% 0.91/1.16      (![X0 : $i]:
% 0.91/1.16         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B_1))
% 0.91/1.16          | (r2_hidden @ (k1_funct_1 @ sk_A @ X0) @ (k2_relat_1 @ sk_A)))),
% 0.91/1.16      inference('demod', [status(thm)], ['198', '199', '200'])).
% 0.91/1.16  thf('202', plain,
% 0.91/1.16      ((r2_hidden @ (k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A)) @ (k2_relat_1 @ sk_A))),
% 0.91/1.16      inference('sup-', [status(thm)], ['195', '201'])).
% 0.91/1.16  thf('203', plain,
% 0.91/1.16      (![X6 : $i, X9 : $i]:
% 0.91/1.16         (~ (v1_relat_1 @ X6)
% 0.91/1.16          | ~ (v1_funct_1 @ X6)
% 0.91/1.16          | ~ (r2_hidden @ X9 @ (k2_relat_1 @ X6))
% 0.91/1.16          | ((X9) = (k1_funct_1 @ X6 @ (sk_D_1 @ X9 @ X6))))),
% 0.91/1.16      inference('simplify', [status(thm)], ['41'])).
% 0.91/1.16  thf('204', plain,
% 0.91/1.16      ((((k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A))
% 0.91/1.16          = (k1_funct_1 @ sk_A @ 
% 0.91/1.16             (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A)) @ sk_A)))
% 0.91/1.16        | ~ (v1_funct_1 @ sk_A)
% 0.91/1.16        | ~ (v1_relat_1 @ sk_A))),
% 0.91/1.16      inference('sup-', [status(thm)], ['202', '203'])).
% 0.91/1.16  thf('205', plain, ((v1_funct_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('206', plain, ((v1_relat_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('207', plain,
% 0.91/1.16      (((k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A))
% 0.91/1.16         = (k1_funct_1 @ sk_A @ 
% 0.91/1.16            (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A)) @ sk_A)))),
% 0.91/1.16      inference('demod', [status(thm)], ['204', '205', '206'])).
% 0.91/1.16  thf('208', plain,
% 0.91/1.16      ((((k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A))
% 0.91/1.16          = (k1_funct_1 @ sk_A @ 
% 0.91/1.16             (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A)))
% 0.91/1.16        | ~ (v1_relat_1 @ sk_A)
% 0.91/1.16        | ~ (v1_funct_1 @ sk_A)
% 0.91/1.16        | (v2_funct_1 @ sk_A))),
% 0.91/1.16      inference('sup+', [status(thm)], ['188', '207'])).
% 0.91/1.16  thf('209', plain,
% 0.91/1.16      ((r2_hidden @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) @ (k1_relat_1 @ sk_B_1))),
% 0.91/1.16      inference('clc', [status(thm)], ['80', '81'])).
% 0.91/1.16  thf('210', plain,
% 0.91/1.16      (![X6 : $i, X11 : $i]:
% 0.91/1.16         (~ (v1_relat_1 @ X6)
% 0.91/1.16          | ~ (v1_funct_1 @ X6)
% 0.91/1.16          | ~ (r2_hidden @ X11 @ (k1_relat_1 @ X6))
% 0.91/1.16          | (r2_hidden @ (k1_funct_1 @ X6 @ X11) @ (k2_relat_1 @ X6)))),
% 0.91/1.16      inference('simplify', [status(thm)], ['102'])).
% 0.91/1.16  thf('211', plain,
% 0.91/1.16      (((r2_hidden @ 
% 0.91/1.16         (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)) @ 
% 0.91/1.16         (k2_relat_1 @ sk_B_1))
% 0.91/1.16        | ~ (v1_funct_1 @ sk_B_1)
% 0.91/1.16        | ~ (v1_relat_1 @ sk_B_1))),
% 0.91/1.16      inference('sup-', [status(thm)], ['209', '210'])).
% 0.91/1.16  thf('212', plain,
% 0.91/1.16      (((sk_B @ sk_A)
% 0.91/1.16         = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)))),
% 0.91/1.16      inference('clc', [status(thm)], ['92', '93'])).
% 0.91/1.16  thf('213', plain, ((v1_funct_1 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('214', plain, ((v1_relat_1 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('215', plain, ((r2_hidden @ (sk_B @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 0.91/1.16      inference('demod', [status(thm)], ['211', '212', '213', '214'])).
% 0.91/1.16  thf('216', plain,
% 0.91/1.16      (![X0 : $i]:
% 0.91/1.16         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B_1))
% 0.91/1.16          | (r2_hidden @ (k1_funct_1 @ sk_A @ X0) @ (k2_relat_1 @ sk_A)))),
% 0.91/1.16      inference('demod', [status(thm)], ['198', '199', '200'])).
% 0.91/1.16  thf('217', plain,
% 0.91/1.16      ((r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ (k2_relat_1 @ sk_A))),
% 0.91/1.16      inference('sup-', [status(thm)], ['215', '216'])).
% 0.91/1.16  thf('218', plain,
% 0.91/1.16      (![X6 : $i, X9 : $i]:
% 0.91/1.16         (~ (v1_relat_1 @ X6)
% 0.91/1.16          | ~ (v1_funct_1 @ X6)
% 0.91/1.16          | ~ (r2_hidden @ X9 @ (k2_relat_1 @ X6))
% 0.91/1.16          | ((X9) = (k1_funct_1 @ X6 @ (sk_D_1 @ X9 @ X6))))),
% 0.91/1.16      inference('simplify', [status(thm)], ['41'])).
% 0.91/1.16  thf('219', plain,
% 0.91/1.16      ((((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.91/1.16          = (k1_funct_1 @ sk_A @ 
% 0.91/1.16             (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A)))
% 0.91/1.16        | ~ (v1_funct_1 @ sk_A)
% 0.91/1.16        | ~ (v1_relat_1 @ sk_A))),
% 0.91/1.16      inference('sup-', [status(thm)], ['217', '218'])).
% 0.91/1.16  thf('220', plain, ((v1_funct_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('221', plain, ((v1_relat_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('222', plain,
% 0.91/1.16      (((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.91/1.16         = (k1_funct_1 @ sk_A @ 
% 0.91/1.16            (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A)))),
% 0.91/1.16      inference('demod', [status(thm)], ['219', '220', '221'])).
% 0.91/1.16  thf('223', plain, ((v1_relat_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('224', plain, ((v1_funct_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('225', plain,
% 0.91/1.16      ((((k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A))
% 0.91/1.16          = (k1_funct_1 @ sk_A @ (sk_B @ sk_A)))
% 0.91/1.16        | (v2_funct_1 @ sk_A))),
% 0.91/1.16      inference('demod', [status(thm)], ['208', '222', '223', '224'])).
% 0.91/1.16  thf('226', plain, (~ (v2_funct_1 @ sk_A)),
% 0.91/1.16      inference('simpl_trail', [status(thm)], ['1', '33'])).
% 0.91/1.16  thf('227', plain,
% 0.91/1.16      (((k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A))
% 0.91/1.16         = (k1_funct_1 @ sk_A @ (sk_B @ sk_A)))),
% 0.91/1.16      inference('clc', [status(thm)], ['225', '226'])).
% 0.91/1.16  thf('228', plain, ((v1_relat_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('229', plain, ((v1_funct_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('230', plain,
% 0.91/1.16      ((r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1) @ (k1_relat_1 @ sk_B_1))),
% 0.91/1.16      inference('clc', [status(thm)], ['55', '56'])).
% 0.91/1.16  thf('231', plain,
% 0.91/1.16      ((((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.91/1.16          != (k1_funct_1 @ sk_A @ (sk_B @ sk_A)))
% 0.91/1.16        | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.91/1.16            (k5_relat_1 @ sk_B_1 @ sk_A)) = (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1)))),
% 0.91/1.16      inference('demod', [status(thm)], ['187', '227', '228', '229', '230'])).
% 0.91/1.16  thf('232', plain,
% 0.91/1.16      (((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.91/1.16         (k5_relat_1 @ sk_B_1 @ sk_A)) = (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1))),
% 0.91/1.16      inference('simplify', [status(thm)], ['231'])).
% 0.91/1.16  thf('233', plain,
% 0.91/1.16      (![X0 : $i]:
% 0.91/1.16         (((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ X0) @ 
% 0.91/1.16            (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1))
% 0.91/1.16            = (k1_funct_1 @ X0 @ (sk_B @ sk_A)))
% 0.91/1.16          | ~ (v1_funct_1 @ X0)
% 0.91/1.16          | ~ (v1_relat_1 @ X0))),
% 0.91/1.16      inference('demod', [status(thm)], ['84', '85', '86', '94'])).
% 0.91/1.16  thf('234', plain,
% 0.91/1.16      (![X0 : $i]:
% 0.91/1.16         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.91/1.16          | ((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.91/1.16              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.91/1.16          | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.91/1.16              (k5_relat_1 @ sk_B_1 @ sk_A)) = (X0)))),
% 0.91/1.16      inference('demod', [status(thm)], ['184', '185'])).
% 0.91/1.16  thf('235', plain,
% 0.91/1.16      ((((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.91/1.16          != (k1_funct_1 @ sk_A @ (sk_B @ sk_A)))
% 0.91/1.16        | ~ (v1_relat_1 @ sk_A)
% 0.91/1.16        | ~ (v1_funct_1 @ sk_A)
% 0.91/1.16        | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.91/1.16            (k5_relat_1 @ sk_B_1 @ sk_A)) = (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1))
% 0.91/1.16        | ~ (r2_hidden @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) @ 
% 0.91/1.16             (k1_relat_1 @ sk_B_1)))),
% 0.91/1.16      inference('sup-', [status(thm)], ['233', '234'])).
% 0.91/1.16  thf('236', plain, ((v1_relat_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('237', plain, ((v1_funct_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('238', plain,
% 0.91/1.16      ((r2_hidden @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) @ (k1_relat_1 @ sk_B_1))),
% 0.91/1.16      inference('clc', [status(thm)], ['80', '81'])).
% 0.91/1.16  thf('239', plain,
% 0.91/1.16      ((((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.91/1.16          != (k1_funct_1 @ sk_A @ (sk_B @ sk_A)))
% 0.91/1.16        | ((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.91/1.16            (k5_relat_1 @ sk_B_1 @ sk_A)) = (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)))),
% 0.91/1.16      inference('demod', [status(thm)], ['235', '236', '237', '238'])).
% 0.91/1.16  thf('240', plain,
% 0.91/1.16      (((sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.91/1.16         (k5_relat_1 @ sk_B_1 @ sk_A)) = (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1))),
% 0.91/1.16      inference('simplify', [status(thm)], ['239'])).
% 0.91/1.16  thf('241', plain,
% 0.91/1.16      (((sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1) = (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1))),
% 0.91/1.16      inference('sup+', [status(thm)], ['232', '240'])).
% 0.91/1.16  thf('242', plain,
% 0.91/1.16      (((sk_C_1 @ sk_A)
% 0.91/1.16         = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)))),
% 0.91/1.16      inference('demod', [status(thm)], ['48', '241'])).
% 0.91/1.16  thf('243', plain,
% 0.91/1.16      (((sk_B @ sk_A)
% 0.91/1.16         = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)))),
% 0.91/1.16      inference('clc', [status(thm)], ['92', '93'])).
% 0.91/1.16  thf('244', plain, (((sk_B @ sk_A) = (sk_C_1 @ sk_A))),
% 0.91/1.16      inference('sup+', [status(thm)], ['242', '243'])).
% 0.91/1.16  thf('245', plain,
% 0.91/1.16      (![X12 : $i]:
% 0.91/1.16         (((sk_B @ X12) != (sk_C_1 @ X12))
% 0.91/1.16          | (v2_funct_1 @ X12)
% 0.91/1.16          | ~ (v1_funct_1 @ X12)
% 0.91/1.16          | ~ (v1_relat_1 @ X12))),
% 0.91/1.16      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.91/1.16  thf('246', plain,
% 0.91/1.16      ((((sk_B @ sk_A) != (sk_B @ sk_A))
% 0.91/1.16        | ~ (v1_relat_1 @ sk_A)
% 0.91/1.16        | ~ (v1_funct_1 @ sk_A)
% 0.91/1.16        | (v2_funct_1 @ sk_A))),
% 0.91/1.16      inference('sup-', [status(thm)], ['244', '245'])).
% 0.91/1.16  thf('247', plain, ((v1_relat_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('248', plain, ((v1_funct_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('249', plain, ((((sk_B @ sk_A) != (sk_B @ sk_A)) | (v2_funct_1 @ sk_A))),
% 0.91/1.16      inference('demod', [status(thm)], ['246', '247', '248'])).
% 0.91/1.16  thf('250', plain, ((v2_funct_1 @ sk_A)),
% 0.91/1.16      inference('simplify', [status(thm)], ['249'])).
% 0.91/1.16  thf('251', plain, ($false), inference('demod', [status(thm)], ['34', '250'])).
% 0.91/1.16  
% 0.91/1.16  % SZS output end Refutation
% 0.91/1.16  
% 0.91/1.17  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
