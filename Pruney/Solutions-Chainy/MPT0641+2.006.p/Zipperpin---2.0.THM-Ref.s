%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4dX0NIovMt

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:13 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 929 expanded)
%              Number of leaves         :   23 ( 260 expanded)
%              Depth                    :   25
%              Number of atoms          : 1488 (12313 expanded)
%              Number of equality atoms :   78 ( 572 expanded)
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X20 @ X19 ) @ X21 )
        = ( k1_funct_1 @ X19 @ ( k1_funct_1 @ X20 @ X21 ) ) )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
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

thf('47',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X14: $i] :
      ( ( r2_hidden @ ( sk_B @ X14 ) @ ( k1_relat_1 @ X14 ) )
      | ( v2_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('49',plain,
    ( ( r2_hidden @ ( sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( r2_hidden @ ( sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','18'])).

thf('54',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X8: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( r2_hidden @ X11 @ ( k2_relat_1 @ X8 ) )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 ) @ ( k1_relat_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('56',plain,
    ( ( r2_hidden @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X20 @ X19 ) @ X21 )
        = ( k1_funct_1 @ X19 @ ( k1_funct_1 @ X20 @ X21 ) ) )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ X0 ) @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('65',plain,(
    ! [X8: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( r2_hidden @ X11 @ ( k2_relat_1 @ X8 ) )
      | ( X11
        = ( k1_funct_1 @ X8 @ ( sk_D_1 @ X11 @ X8 ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('66',plain,
    ( ( ( sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( sk_B @ sk_A )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ X0 ) @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) )
        = ( k1_funct_1 @ X0 @ ( sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['61','62','63','69'])).

thf(fc2_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) )).

thf('71',plain,(
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

thf('72',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('73',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('74',plain,
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

thf('75',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X6 ) @ ( k1_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ sk_A ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ sk_A ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      = ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['73','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
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

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('85',plain,(
    v2_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X1 )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ( X1 = X0 )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['72','86'])).

thf('88',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X1 )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ( X1 = X0 )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
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
    inference('sup-',[status(thm)],['71','90'])).

thf('92',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['91','92','93','94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 )
        = X0 )
      | ~ ( r2_hidden @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['70','96'])).

thf('98',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['97','98','99','100'])).

thf('102',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
     != ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 )
      = ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) )
    | ~ ( r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['46','101'])).

thf('103',plain,(
    ! [X14: $i] :
      ( ( ( k1_funct_1 @ X14 @ ( sk_B @ X14 ) )
        = ( k1_funct_1 @ X14 @ ( sk_C_1 @ X14 ) ) )
      | ( v2_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('104',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('105',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
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

thf('107',plain,(
    ! [X8: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X8 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X8 @ X13 ) @ ( k2_relat_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['105','107'])).

thf('109',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) ) @ ( k2_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['104','111'])).

thf('113',plain,(
    ! [X8: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( r2_hidden @ X11 @ ( k2_relat_1 @ X8 ) )
      | ( X11
        = ( k1_funct_1 @ X8 @ ( sk_D_1 @ X11 @ X8 ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('114',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) )
      = ( k1_funct_1 @ sk_A @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) )
    = ( k1_funct_1 @ sk_A @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) )
      = ( k1_funct_1 @ sk_A @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['103','117'])).

thf('119',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('121',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k2_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X8: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( r2_hidden @ X11 @ ( k2_relat_1 @ X8 ) )
      | ( X11
        = ( k1_funct_1 @ X8 @ ( sk_D_1 @ X11 @ X8 ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('123',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
      = ( k1_funct_1 @ sk_A @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
    = ( k1_funct_1 @ sk_A @ ( sk_D_1 @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) )
      = ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['118','126','127','128'])).

thf('130',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','18'])).

thf('131',plain,
    ( ( k1_funct_1 @ sk_A @ ( sk_C_1 @ sk_A ) )
    = ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['129','130'])).

thf('132',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('135',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) )
     != ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 )
      = ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['102','131','132','133','134'])).

thf('136',plain,
    ( ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 )
    = ( sk_D_1 @ ( sk_C_1 @ sk_A ) @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,
    ( ( sk_C_1 @ sk_A )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['33','136'])).

thf('138',plain,
    ( ( sk_B @ sk_A )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('139',plain,
    ( ( sk_B @ sk_A )
    = ( sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X14: $i] :
      ( ( ( sk_B @ X14 )
       != ( sk_C_1 @ X14 ) )
      | ( v2_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('141',plain,
    ( ( ( sk_B @ sk_A )
     != ( sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( ( sk_B @ sk_A )
     != ( sk_B @ sk_A ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('145',plain,(
    v2_funct_1 @ sk_A ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,(
    $false ),
    inference(demod,[status(thm)],['19','145'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4dX0NIovMt
% 0.14/0.37  % Computer   : n008.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.23/0.37  % DateTime   : Tue Dec  1 09:54:30 EST 2020
% 0.23/0.37  % CPUTime    : 
% 0.23/0.37  % Running portfolio for 600 s
% 0.23/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.23/0.38  % Number of cores: 8
% 0.23/0.38  % Python version: Python 3.6.8
% 0.23/0.38  % Running in FO mode
% 0.51/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.51/0.67  % Solved by: fo/fo7.sh
% 0.51/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.67  % done 235 iterations in 0.218s
% 0.51/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.51/0.67  % SZS output start Refutation
% 0.51/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.51/0.67  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.51/0.67  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.51/0.67  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.51/0.67  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.51/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.67  thf(sk_B_type, type, sk_B: $i > $i).
% 0.51/0.67  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.51/0.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.51/0.67  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.51/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.51/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.51/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.51/0.67  thf(t48_funct_1, conjecture,
% 0.51/0.67    (![A:$i]:
% 0.51/0.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.51/0.67       ( ![B:$i]:
% 0.51/0.67         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.51/0.67           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.51/0.67               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.51/0.67             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.51/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.67    (~( ![A:$i]:
% 0.51/0.67        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.51/0.67          ( ![B:$i]:
% 0.51/0.67            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.51/0.67              ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.51/0.67                  ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.51/0.67                ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ) )),
% 0.51/0.67    inference('cnf.neg', [status(esa)], [t48_funct_1])).
% 0.51/0.67  thf('0', plain, ((~ (v2_funct_1 @ sk_B_1) | ~ (v2_funct_1 @ sk_A))),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('1', plain, ((~ (v2_funct_1 @ sk_A)) <= (~ ((v2_funct_1 @ sk_A)))),
% 0.51/0.67      inference('split', [status(esa)], ['0'])).
% 0.51/0.67  thf(d10_xboole_0, axiom,
% 0.51/0.67    (![A:$i,B:$i]:
% 0.51/0.67     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.51/0.67  thf('2', plain,
% 0.51/0.67      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.51/0.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.51/0.67  thf('3', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.51/0.67      inference('simplify', [status(thm)], ['2'])).
% 0.51/0.67  thf('4', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf(t47_funct_1, axiom,
% 0.51/0.67    (![A:$i]:
% 0.51/0.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.51/0.67       ( ![B:$i]:
% 0.51/0.67         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.51/0.67           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.51/0.67               ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) =>
% 0.51/0.67             ( v2_funct_1 @ B ) ) ) ) ))).
% 0.51/0.67  thf('5', plain,
% 0.51/0.67      (![X22 : $i, X23 : $i]:
% 0.51/0.67         (~ (v1_relat_1 @ X22)
% 0.51/0.67          | ~ (v1_funct_1 @ X22)
% 0.51/0.67          | (v2_funct_1 @ X22)
% 0.51/0.67          | ~ (r1_tarski @ (k2_relat_1 @ X22) @ (k1_relat_1 @ X23))
% 0.51/0.67          | ~ (v2_funct_1 @ (k5_relat_1 @ X22 @ X23))
% 0.51/0.67          | ~ (v1_funct_1 @ X23)
% 0.51/0.67          | ~ (v1_relat_1 @ X23))),
% 0.51/0.67      inference('cnf', [status(esa)], [t47_funct_1])).
% 0.51/0.67  thf('6', plain,
% 0.51/0.67      (![X0 : $i]:
% 0.51/0.67         (~ (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ sk_B_1))
% 0.51/0.67          | ~ (v1_relat_1 @ sk_A)
% 0.51/0.67          | ~ (v1_funct_1 @ sk_A)
% 0.51/0.67          | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_A))
% 0.51/0.67          | (v2_funct_1 @ X0)
% 0.51/0.67          | ~ (v1_funct_1 @ X0)
% 0.51/0.67          | ~ (v1_relat_1 @ X0))),
% 0.51/0.67      inference('sup-', [status(thm)], ['4', '5'])).
% 0.51/0.67  thf('7', plain, ((v1_relat_1 @ sk_A)),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('8', plain, ((v1_funct_1 @ sk_A)),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('9', plain,
% 0.51/0.67      (![X0 : $i]:
% 0.51/0.67         (~ (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ sk_B_1))
% 0.51/0.67          | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_A))
% 0.51/0.67          | (v2_funct_1 @ X0)
% 0.51/0.67          | ~ (v1_funct_1 @ X0)
% 0.51/0.67          | ~ (v1_relat_1 @ X0))),
% 0.51/0.67      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.51/0.67  thf('10', plain,
% 0.51/0.67      ((~ (v1_relat_1 @ sk_B_1)
% 0.51/0.67        | ~ (v1_funct_1 @ sk_B_1)
% 0.51/0.67        | (v2_funct_1 @ sk_B_1)
% 0.51/0.68        | ~ (v2_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.51/0.68      inference('sup-', [status(thm)], ['3', '9'])).
% 0.51/0.68  thf('11', plain, ((v1_relat_1 @ sk_B_1)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('12', plain, ((v1_funct_1 @ sk_B_1)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('13', plain, ((v2_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('14', plain, ((v2_funct_1 @ sk_B_1)),
% 0.51/0.68      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.51/0.68  thf('15', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.51/0.68      inference('split', [status(esa)], ['0'])).
% 0.51/0.68  thf('16', plain, (((v2_funct_1 @ sk_B_1))),
% 0.51/0.68      inference('sup-', [status(thm)], ['14', '15'])).
% 0.51/0.68  thf('17', plain, (~ ((v2_funct_1 @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.51/0.68      inference('split', [status(esa)], ['0'])).
% 0.51/0.68  thf('18', plain, (~ ((v2_funct_1 @ sk_A))),
% 0.51/0.68      inference('sat_resolution*', [status(thm)], ['16', '17'])).
% 0.51/0.68  thf('19', plain, (~ (v2_funct_1 @ sk_A)),
% 0.51/0.68      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.51/0.68  thf('20', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf(d8_funct_1, axiom,
% 0.51/0.68    (![A:$i]:
% 0.51/0.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.51/0.68       ( ( v2_funct_1 @ A ) <=>
% 0.51/0.68         ( ![B:$i,C:$i]:
% 0.51/0.68           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.51/0.68               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.51/0.68               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.51/0.68             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.51/0.68  thf('21', plain,
% 0.51/0.68      (![X14 : $i]:
% 0.51/0.68         ((r2_hidden @ (sk_C_1 @ X14) @ (k1_relat_1 @ X14))
% 0.51/0.68          | (v2_funct_1 @ X14)
% 0.51/0.68          | ~ (v1_funct_1 @ X14)
% 0.51/0.68          | ~ (v1_relat_1 @ X14))),
% 0.51/0.68      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.51/0.68  thf('22', plain,
% 0.51/0.68      (((r2_hidden @ (sk_C_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))
% 0.51/0.68        | ~ (v1_relat_1 @ sk_A)
% 0.51/0.68        | ~ (v1_funct_1 @ sk_A)
% 0.51/0.68        | (v2_funct_1 @ sk_A))),
% 0.51/0.68      inference('sup+', [status(thm)], ['20', '21'])).
% 0.51/0.68  thf('23', plain, ((v1_relat_1 @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('24', plain, ((v1_funct_1 @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('25', plain,
% 0.51/0.68      (((r2_hidden @ (sk_C_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))
% 0.51/0.68        | (v2_funct_1 @ sk_A))),
% 0.51/0.68      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.51/0.68  thf('26', plain, (~ (v2_funct_1 @ sk_A)),
% 0.51/0.68      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.51/0.68  thf('27', plain, ((r2_hidden @ (sk_C_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 0.51/0.68      inference('clc', [status(thm)], ['25', '26'])).
% 0.51/0.68  thf(d5_funct_1, axiom,
% 0.51/0.68    (![A:$i]:
% 0.51/0.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.51/0.68       ( ![B:$i]:
% 0.51/0.68         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.51/0.68           ( ![C:$i]:
% 0.51/0.68             ( ( r2_hidden @ C @ B ) <=>
% 0.51/0.68               ( ?[D:$i]:
% 0.51/0.68                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.51/0.68                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.51/0.68  thf('28', plain,
% 0.51/0.68      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.51/0.68         (((X10) != (k2_relat_1 @ X8))
% 0.51/0.68          | ((X11) = (k1_funct_1 @ X8 @ (sk_D_1 @ X11 @ X8)))
% 0.51/0.68          | ~ (r2_hidden @ X11 @ X10)
% 0.51/0.68          | ~ (v1_funct_1 @ X8)
% 0.51/0.68          | ~ (v1_relat_1 @ X8))),
% 0.51/0.68      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.51/0.68  thf('29', plain,
% 0.51/0.68      (![X8 : $i, X11 : $i]:
% 0.51/0.68         (~ (v1_relat_1 @ X8)
% 0.51/0.68          | ~ (v1_funct_1 @ X8)
% 0.51/0.68          | ~ (r2_hidden @ X11 @ (k2_relat_1 @ X8))
% 0.51/0.68          | ((X11) = (k1_funct_1 @ X8 @ (sk_D_1 @ X11 @ X8))))),
% 0.51/0.68      inference('simplify', [status(thm)], ['28'])).
% 0.51/0.68  thf('30', plain,
% 0.51/0.68      ((((sk_C_1 @ sk_A)
% 0.51/0.68          = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1)))
% 0.51/0.68        | ~ (v1_funct_1 @ sk_B_1)
% 0.51/0.68        | ~ (v1_relat_1 @ sk_B_1))),
% 0.51/0.68      inference('sup-', [status(thm)], ['27', '29'])).
% 0.51/0.68  thf('31', plain, ((v1_funct_1 @ sk_B_1)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('32', plain, ((v1_relat_1 @ sk_B_1)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('33', plain,
% 0.51/0.68      (((sk_C_1 @ sk_A)
% 0.51/0.68         = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1)))),
% 0.51/0.68      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.51/0.68  thf('34', plain, ((r2_hidden @ (sk_C_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 0.51/0.68      inference('clc', [status(thm)], ['25', '26'])).
% 0.51/0.68  thf('35', plain,
% 0.51/0.68      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.51/0.68         (((X10) != (k2_relat_1 @ X8))
% 0.51/0.68          | (r2_hidden @ (sk_D_1 @ X11 @ X8) @ (k1_relat_1 @ X8))
% 0.51/0.68          | ~ (r2_hidden @ X11 @ X10)
% 0.51/0.68          | ~ (v1_funct_1 @ X8)
% 0.51/0.68          | ~ (v1_relat_1 @ X8))),
% 0.51/0.68      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.51/0.68  thf('36', plain,
% 0.51/0.68      (![X8 : $i, X11 : $i]:
% 0.51/0.68         (~ (v1_relat_1 @ X8)
% 0.51/0.68          | ~ (v1_funct_1 @ X8)
% 0.51/0.68          | ~ (r2_hidden @ X11 @ (k2_relat_1 @ X8))
% 0.51/0.68          | (r2_hidden @ (sk_D_1 @ X11 @ X8) @ (k1_relat_1 @ X8)))),
% 0.51/0.68      inference('simplify', [status(thm)], ['35'])).
% 0.51/0.68  thf('37', plain,
% 0.51/0.68      (((r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1) @ 
% 0.51/0.68         (k1_relat_1 @ sk_B_1))
% 0.51/0.68        | ~ (v1_funct_1 @ sk_B_1)
% 0.51/0.68        | ~ (v1_relat_1 @ sk_B_1))),
% 0.51/0.68      inference('sup-', [status(thm)], ['34', '36'])).
% 0.51/0.68  thf('38', plain, ((v1_funct_1 @ sk_B_1)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('39', plain, ((v1_relat_1 @ sk_B_1)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('40', plain,
% 0.51/0.68      ((r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1) @ (k1_relat_1 @ sk_B_1))),
% 0.51/0.68      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.51/0.68  thf(t23_funct_1, axiom,
% 0.51/0.68    (![A:$i,B:$i]:
% 0.51/0.68     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.51/0.68       ( ![C:$i]:
% 0.51/0.68         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.51/0.68           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.51/0.68             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.51/0.68               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 0.51/0.68  thf('41', plain,
% 0.51/0.68      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.51/0.68         (~ (v1_relat_1 @ X19)
% 0.51/0.68          | ~ (v1_funct_1 @ X19)
% 0.51/0.68          | ((k1_funct_1 @ (k5_relat_1 @ X20 @ X19) @ X21)
% 0.51/0.68              = (k1_funct_1 @ X19 @ (k1_funct_1 @ X20 @ X21)))
% 0.51/0.68          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X20))
% 0.51/0.68          | ~ (v1_funct_1 @ X20)
% 0.51/0.68          | ~ (v1_relat_1 @ X20))),
% 0.51/0.68      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.51/0.68  thf('42', plain,
% 0.51/0.68      (![X0 : $i]:
% 0.51/0.68         (~ (v1_relat_1 @ sk_B_1)
% 0.51/0.68          | ~ (v1_funct_1 @ sk_B_1)
% 0.51/0.68          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ X0) @ 
% 0.51/0.68              (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1))
% 0.51/0.68              = (k1_funct_1 @ X0 @ 
% 0.51/0.68                 (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1))))
% 0.51/0.68          | ~ (v1_funct_1 @ X0)
% 0.51/0.68          | ~ (v1_relat_1 @ X0))),
% 0.51/0.68      inference('sup-', [status(thm)], ['40', '41'])).
% 0.51/0.68  thf('43', plain, ((v1_relat_1 @ sk_B_1)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('44', plain, ((v1_funct_1 @ sk_B_1)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('45', plain,
% 0.51/0.68      (((sk_C_1 @ sk_A)
% 0.51/0.68         = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1)))),
% 0.51/0.68      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.51/0.68  thf('46', plain,
% 0.51/0.68      (![X0 : $i]:
% 0.51/0.68         (((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ X0) @ 
% 0.51/0.68            (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1))
% 0.51/0.68            = (k1_funct_1 @ X0 @ (sk_C_1 @ sk_A)))
% 0.51/0.68          | ~ (v1_funct_1 @ X0)
% 0.51/0.68          | ~ (v1_relat_1 @ X0))),
% 0.51/0.68      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 0.51/0.68  thf('47', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('48', plain,
% 0.51/0.68      (![X14 : $i]:
% 0.51/0.68         ((r2_hidden @ (sk_B @ X14) @ (k1_relat_1 @ X14))
% 0.51/0.68          | (v2_funct_1 @ X14)
% 0.51/0.68          | ~ (v1_funct_1 @ X14)
% 0.51/0.68          | ~ (v1_relat_1 @ X14))),
% 0.51/0.68      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.51/0.68  thf('49', plain,
% 0.51/0.68      (((r2_hidden @ (sk_B @ sk_A) @ (k2_relat_1 @ sk_B_1))
% 0.51/0.68        | ~ (v1_relat_1 @ sk_A)
% 0.51/0.68        | ~ (v1_funct_1 @ sk_A)
% 0.51/0.68        | (v2_funct_1 @ sk_A))),
% 0.51/0.68      inference('sup+', [status(thm)], ['47', '48'])).
% 0.51/0.68  thf('50', plain, ((v1_relat_1 @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('51', plain, ((v1_funct_1 @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('52', plain,
% 0.51/0.68      (((r2_hidden @ (sk_B @ sk_A) @ (k2_relat_1 @ sk_B_1))
% 0.51/0.68        | (v2_funct_1 @ sk_A))),
% 0.51/0.68      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.51/0.68  thf('53', plain, (~ (v2_funct_1 @ sk_A)),
% 0.51/0.68      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.51/0.68  thf('54', plain, ((r2_hidden @ (sk_B @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 0.51/0.68      inference('clc', [status(thm)], ['52', '53'])).
% 0.51/0.68  thf('55', plain,
% 0.51/0.68      (![X8 : $i, X11 : $i]:
% 0.51/0.68         (~ (v1_relat_1 @ X8)
% 0.51/0.68          | ~ (v1_funct_1 @ X8)
% 0.51/0.68          | ~ (r2_hidden @ X11 @ (k2_relat_1 @ X8))
% 0.51/0.68          | (r2_hidden @ (sk_D_1 @ X11 @ X8) @ (k1_relat_1 @ X8)))),
% 0.51/0.68      inference('simplify', [status(thm)], ['35'])).
% 0.51/0.68  thf('56', plain,
% 0.51/0.68      (((r2_hidden @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) @ (k1_relat_1 @ sk_B_1))
% 0.51/0.68        | ~ (v1_funct_1 @ sk_B_1)
% 0.51/0.68        | ~ (v1_relat_1 @ sk_B_1))),
% 0.51/0.68      inference('sup-', [status(thm)], ['54', '55'])).
% 0.51/0.68  thf('57', plain, ((v1_funct_1 @ sk_B_1)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('58', plain, ((v1_relat_1 @ sk_B_1)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('59', plain,
% 0.51/0.68      ((r2_hidden @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) @ (k1_relat_1 @ sk_B_1))),
% 0.51/0.68      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.51/0.68  thf('60', plain,
% 0.51/0.68      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.51/0.68         (~ (v1_relat_1 @ X19)
% 0.51/0.68          | ~ (v1_funct_1 @ X19)
% 0.51/0.68          | ((k1_funct_1 @ (k5_relat_1 @ X20 @ X19) @ X21)
% 0.51/0.68              = (k1_funct_1 @ X19 @ (k1_funct_1 @ X20 @ X21)))
% 0.51/0.68          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X20))
% 0.51/0.68          | ~ (v1_funct_1 @ X20)
% 0.51/0.68          | ~ (v1_relat_1 @ X20))),
% 0.51/0.68      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.51/0.68  thf('61', plain,
% 0.51/0.68      (![X0 : $i]:
% 0.51/0.68         (~ (v1_relat_1 @ sk_B_1)
% 0.51/0.68          | ~ (v1_funct_1 @ sk_B_1)
% 0.51/0.68          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ X0) @ 
% 0.51/0.68              (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1))
% 0.51/0.68              = (k1_funct_1 @ X0 @ 
% 0.51/0.68                 (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1))))
% 0.51/0.68          | ~ (v1_funct_1 @ X0)
% 0.51/0.68          | ~ (v1_relat_1 @ X0))),
% 0.51/0.68      inference('sup-', [status(thm)], ['59', '60'])).
% 0.51/0.68  thf('62', plain, ((v1_relat_1 @ sk_B_1)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('63', plain, ((v1_funct_1 @ sk_B_1)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('64', plain, ((r2_hidden @ (sk_B @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 0.51/0.68      inference('clc', [status(thm)], ['52', '53'])).
% 0.51/0.68  thf('65', plain,
% 0.51/0.68      (![X8 : $i, X11 : $i]:
% 0.51/0.68         (~ (v1_relat_1 @ X8)
% 0.51/0.68          | ~ (v1_funct_1 @ X8)
% 0.51/0.68          | ~ (r2_hidden @ X11 @ (k2_relat_1 @ X8))
% 0.51/0.68          | ((X11) = (k1_funct_1 @ X8 @ (sk_D_1 @ X11 @ X8))))),
% 0.51/0.68      inference('simplify', [status(thm)], ['28'])).
% 0.51/0.68  thf('66', plain,
% 0.51/0.68      ((((sk_B @ sk_A)
% 0.51/0.68          = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)))
% 0.51/0.68        | ~ (v1_funct_1 @ sk_B_1)
% 0.51/0.68        | ~ (v1_relat_1 @ sk_B_1))),
% 0.51/0.68      inference('sup-', [status(thm)], ['64', '65'])).
% 0.51/0.68  thf('67', plain, ((v1_funct_1 @ sk_B_1)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('68', plain, ((v1_relat_1 @ sk_B_1)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('69', plain,
% 0.51/0.68      (((sk_B @ sk_A)
% 0.51/0.68         = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)))),
% 0.51/0.68      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.51/0.68  thf('70', plain,
% 0.51/0.68      (![X0 : $i]:
% 0.51/0.68         (((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ X0) @ 
% 0.51/0.68            (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1))
% 0.51/0.68            = (k1_funct_1 @ X0 @ (sk_B @ sk_A)))
% 0.51/0.68          | ~ (v1_funct_1 @ X0)
% 0.51/0.68          | ~ (v1_relat_1 @ X0))),
% 0.51/0.68      inference('demod', [status(thm)], ['61', '62', '63', '69'])).
% 0.51/0.68  thf(fc2_funct_1, axiom,
% 0.51/0.68    (![A:$i,B:$i]:
% 0.51/0.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v1_relat_1 @ B ) & 
% 0.51/0.68         ( v1_funct_1 @ B ) ) =>
% 0.51/0.68       ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) & 
% 0.51/0.68         ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ))).
% 0.51/0.68  thf('71', plain,
% 0.51/0.68      (![X17 : $i, X18 : $i]:
% 0.51/0.68         (~ (v1_funct_1 @ X17)
% 0.51/0.68          | ~ (v1_relat_1 @ X17)
% 0.51/0.68          | ~ (v1_relat_1 @ X18)
% 0.51/0.68          | ~ (v1_funct_1 @ X18)
% 0.51/0.68          | (v1_funct_1 @ (k5_relat_1 @ X17 @ X18)))),
% 0.51/0.68      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.51/0.68  thf(dt_k5_relat_1, axiom,
% 0.51/0.68    (![A:$i,B:$i]:
% 0.51/0.68     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.51/0.68       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.51/0.68  thf('72', plain,
% 0.51/0.68      (![X3 : $i, X4 : $i]:
% 0.51/0.68         (~ (v1_relat_1 @ X3)
% 0.51/0.68          | ~ (v1_relat_1 @ X4)
% 0.51/0.68          | (v1_relat_1 @ (k5_relat_1 @ X3 @ X4)))),
% 0.51/0.68      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.51/0.68  thf('73', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.51/0.68      inference('simplify', [status(thm)], ['2'])).
% 0.51/0.68  thf('74', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf(t46_relat_1, axiom,
% 0.51/0.68    (![A:$i]:
% 0.51/0.68     ( ( v1_relat_1 @ A ) =>
% 0.51/0.68       ( ![B:$i]:
% 0.51/0.68         ( ( v1_relat_1 @ B ) =>
% 0.51/0.68           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.51/0.68             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.51/0.68  thf('75', plain,
% 0.51/0.68      (![X5 : $i, X6 : $i]:
% 0.51/0.68         (~ (v1_relat_1 @ X5)
% 0.51/0.68          | ((k1_relat_1 @ (k5_relat_1 @ X6 @ X5)) = (k1_relat_1 @ X6))
% 0.51/0.68          | ~ (r1_tarski @ (k2_relat_1 @ X6) @ (k1_relat_1 @ X5))
% 0.51/0.68          | ~ (v1_relat_1 @ X6))),
% 0.51/0.68      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.51/0.68  thf('76', plain,
% 0.51/0.68      (![X0 : $i]:
% 0.51/0.68         (~ (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ sk_B_1))
% 0.51/0.68          | ~ (v1_relat_1 @ X0)
% 0.51/0.68          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ sk_A)) = (k1_relat_1 @ X0))
% 0.51/0.68          | ~ (v1_relat_1 @ sk_A))),
% 0.51/0.68      inference('sup-', [status(thm)], ['74', '75'])).
% 0.51/0.68  thf('77', plain, ((v1_relat_1 @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('78', plain,
% 0.51/0.68      (![X0 : $i]:
% 0.51/0.68         (~ (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ sk_B_1))
% 0.51/0.68          | ~ (v1_relat_1 @ X0)
% 0.51/0.68          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ sk_A)) = (k1_relat_1 @ X0)))),
% 0.51/0.68      inference('demod', [status(thm)], ['76', '77'])).
% 0.51/0.68  thf('79', plain,
% 0.51/0.68      ((((k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)) = (k1_relat_1 @ sk_B_1))
% 0.51/0.68        | ~ (v1_relat_1 @ sk_B_1))),
% 0.51/0.68      inference('sup-', [status(thm)], ['73', '78'])).
% 0.51/0.68  thf('80', plain, ((v1_relat_1 @ sk_B_1)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('81', plain,
% 0.51/0.68      (((k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)) = (k1_relat_1 @ sk_B_1))),
% 0.51/0.68      inference('demod', [status(thm)], ['79', '80'])).
% 0.51/0.68  thf('82', plain,
% 0.51/0.68      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.51/0.68         (~ (v2_funct_1 @ X14)
% 0.51/0.68          | ~ (r2_hidden @ X15 @ (k1_relat_1 @ X14))
% 0.51/0.68          | ~ (r2_hidden @ X16 @ (k1_relat_1 @ X14))
% 0.51/0.68          | ((k1_funct_1 @ X14 @ X15) != (k1_funct_1 @ X14 @ X16))
% 0.51/0.68          | ((X15) = (X16))
% 0.51/0.68          | ~ (v1_funct_1 @ X14)
% 0.51/0.68          | ~ (v1_relat_1 @ X14))),
% 0.51/0.68      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.51/0.68  thf('83', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i]:
% 0.51/0.68         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.51/0.68          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.51/0.68          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.51/0.68          | ((X0) = (X1))
% 0.51/0.68          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.51/0.68              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X1))
% 0.51/0.68          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.51/0.68          | ~ (v2_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.51/0.68      inference('sup-', [status(thm)], ['81', '82'])).
% 0.51/0.68  thf('84', plain,
% 0.51/0.68      (((k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)) = (k1_relat_1 @ sk_B_1))),
% 0.51/0.68      inference('demod', [status(thm)], ['79', '80'])).
% 0.51/0.68  thf('85', plain, ((v2_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('86', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i]:
% 0.51/0.68         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.51/0.68          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.51/0.68          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.51/0.68          | ((X0) = (X1))
% 0.51/0.68          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.51/0.68              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X1))
% 0.51/0.68          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1)))),
% 0.51/0.68      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.51/0.68  thf('87', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i]:
% 0.51/0.68         (~ (v1_relat_1 @ sk_A)
% 0.51/0.68          | ~ (v1_relat_1 @ sk_B_1)
% 0.51/0.68          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.51/0.68          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X1)
% 0.51/0.68              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.51/0.68          | ((X1) = (X0))
% 0.51/0.68          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.51/0.68          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1)))),
% 0.51/0.68      inference('sup-', [status(thm)], ['72', '86'])).
% 0.51/0.68  thf('88', plain, ((v1_relat_1 @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('89', plain, ((v1_relat_1 @ sk_B_1)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('90', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i]:
% 0.51/0.68         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.51/0.68          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X1)
% 0.51/0.68              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.51/0.68          | ((X1) = (X0))
% 0.51/0.68          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.51/0.68          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1)))),
% 0.51/0.68      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.51/0.68  thf('91', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i]:
% 0.51/0.68         (~ (v1_funct_1 @ sk_A)
% 0.51/0.68          | ~ (v1_relat_1 @ sk_A)
% 0.51/0.68          | ~ (v1_relat_1 @ sk_B_1)
% 0.51/0.68          | ~ (v1_funct_1 @ sk_B_1)
% 0.51/0.68          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.51/0.68          | ((X0) = (X1))
% 0.51/0.68          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.51/0.68              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X1))
% 0.51/0.68          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1)))),
% 0.51/0.68      inference('sup-', [status(thm)], ['71', '90'])).
% 0.51/0.68  thf('92', plain, ((v1_funct_1 @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('93', plain, ((v1_relat_1 @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('94', plain, ((v1_relat_1 @ sk_B_1)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('95', plain, ((v1_funct_1 @ sk_B_1)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('96', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i]:
% 0.51/0.68         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.51/0.68          | ((X0) = (X1))
% 0.51/0.68          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.51/0.68              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X1))
% 0.51/0.68          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1)))),
% 0.51/0.68      inference('demod', [status(thm)], ['91', '92', '93', '94', '95'])).
% 0.51/0.68  thf('97', plain,
% 0.51/0.68      (![X0 : $i]:
% 0.51/0.68         (((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.51/0.68            != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.51/0.68          | ~ (v1_relat_1 @ sk_A)
% 0.51/0.68          | ~ (v1_funct_1 @ sk_A)
% 0.51/0.68          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.51/0.68          | ((sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) = (X0))
% 0.51/0.68          | ~ (r2_hidden @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) @ 
% 0.51/0.68               (k1_relat_1 @ sk_B_1)))),
% 0.51/0.68      inference('sup-', [status(thm)], ['70', '96'])).
% 0.51/0.68  thf('98', plain, ((v1_relat_1 @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('99', plain, ((v1_funct_1 @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('100', plain,
% 0.51/0.68      ((r2_hidden @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) @ (k1_relat_1 @ sk_B_1))),
% 0.51/0.68      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.51/0.68  thf('101', plain,
% 0.51/0.68      (![X0 : $i]:
% 0.51/0.68         (((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.51/0.68            != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.51/0.68          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.51/0.68          | ((sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) = (X0)))),
% 0.51/0.68      inference('demod', [status(thm)], ['97', '98', '99', '100'])).
% 0.51/0.68  thf('102', plain,
% 0.51/0.68      ((((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.51/0.68          != (k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A)))
% 0.51/0.68        | ~ (v1_relat_1 @ sk_A)
% 0.51/0.68        | ~ (v1_funct_1 @ sk_A)
% 0.51/0.68        | ((sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)
% 0.51/0.68            = (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1))
% 0.51/0.68        | ~ (r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1) @ 
% 0.51/0.68             (k1_relat_1 @ sk_B_1)))),
% 0.51/0.68      inference('sup-', [status(thm)], ['46', '101'])).
% 0.51/0.68  thf('103', plain,
% 0.51/0.68      (![X14 : $i]:
% 0.51/0.68         (((k1_funct_1 @ X14 @ (sk_B @ X14))
% 0.51/0.68            = (k1_funct_1 @ X14 @ (sk_C_1 @ X14)))
% 0.51/0.68          | (v2_funct_1 @ X14)
% 0.51/0.68          | ~ (v1_funct_1 @ X14)
% 0.51/0.68          | ~ (v1_relat_1 @ X14))),
% 0.51/0.68      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.51/0.68  thf('104', plain, ((r2_hidden @ (sk_C_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 0.51/0.68      inference('clc', [status(thm)], ['25', '26'])).
% 0.51/0.68  thf('105', plain, (((k2_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_A))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('106', plain,
% 0.51/0.68      (![X8 : $i, X10 : $i, X12 : $i, X13 : $i]:
% 0.51/0.68         (((X10) != (k2_relat_1 @ X8))
% 0.51/0.68          | (r2_hidden @ X12 @ X10)
% 0.51/0.68          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X8))
% 0.51/0.68          | ((X12) != (k1_funct_1 @ X8 @ X13))
% 0.51/0.68          | ~ (v1_funct_1 @ X8)
% 0.51/0.68          | ~ (v1_relat_1 @ X8))),
% 0.51/0.68      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.51/0.68  thf('107', plain,
% 0.51/0.68      (![X8 : $i, X13 : $i]:
% 0.51/0.68         (~ (v1_relat_1 @ X8)
% 0.51/0.68          | ~ (v1_funct_1 @ X8)
% 0.51/0.68          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X8))
% 0.51/0.68          | (r2_hidden @ (k1_funct_1 @ X8 @ X13) @ (k2_relat_1 @ X8)))),
% 0.51/0.68      inference('simplify', [status(thm)], ['106'])).
% 0.51/0.68  thf('108', plain,
% 0.51/0.68      (![X0 : $i]:
% 0.51/0.68         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B_1))
% 0.51/0.68          | (r2_hidden @ (k1_funct_1 @ sk_A @ X0) @ (k2_relat_1 @ sk_A))
% 0.51/0.68          | ~ (v1_funct_1 @ sk_A)
% 0.51/0.68          | ~ (v1_relat_1 @ sk_A))),
% 0.51/0.68      inference('sup-', [status(thm)], ['105', '107'])).
% 0.51/0.68  thf('109', plain, ((v1_funct_1 @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('110', plain, ((v1_relat_1 @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('111', plain,
% 0.51/0.68      (![X0 : $i]:
% 0.51/0.68         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B_1))
% 0.51/0.68          | (r2_hidden @ (k1_funct_1 @ sk_A @ X0) @ (k2_relat_1 @ sk_A)))),
% 0.51/0.68      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.51/0.68  thf('112', plain,
% 0.51/0.68      ((r2_hidden @ (k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A)) @ (k2_relat_1 @ sk_A))),
% 0.51/0.68      inference('sup-', [status(thm)], ['104', '111'])).
% 0.51/0.68  thf('113', plain,
% 0.51/0.68      (![X8 : $i, X11 : $i]:
% 0.51/0.68         (~ (v1_relat_1 @ X8)
% 0.51/0.68          | ~ (v1_funct_1 @ X8)
% 0.51/0.68          | ~ (r2_hidden @ X11 @ (k2_relat_1 @ X8))
% 0.51/0.68          | ((X11) = (k1_funct_1 @ X8 @ (sk_D_1 @ X11 @ X8))))),
% 0.51/0.68      inference('simplify', [status(thm)], ['28'])).
% 0.51/0.68  thf('114', plain,
% 0.51/0.68      ((((k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A))
% 0.51/0.68          = (k1_funct_1 @ sk_A @ 
% 0.51/0.68             (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A)) @ sk_A)))
% 0.51/0.68        | ~ (v1_funct_1 @ sk_A)
% 0.51/0.68        | ~ (v1_relat_1 @ sk_A))),
% 0.51/0.68      inference('sup-', [status(thm)], ['112', '113'])).
% 0.51/0.68  thf('115', plain, ((v1_funct_1 @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('116', plain, ((v1_relat_1 @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('117', plain,
% 0.51/0.68      (((k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A))
% 0.51/0.68         = (k1_funct_1 @ sk_A @ 
% 0.51/0.68            (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A)) @ sk_A)))),
% 0.51/0.68      inference('demod', [status(thm)], ['114', '115', '116'])).
% 0.51/0.68  thf('118', plain,
% 0.51/0.68      ((((k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A))
% 0.51/0.68          = (k1_funct_1 @ sk_A @ 
% 0.51/0.68             (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A)))
% 0.51/0.68        | ~ (v1_relat_1 @ sk_A)
% 0.51/0.68        | ~ (v1_funct_1 @ sk_A)
% 0.51/0.68        | (v2_funct_1 @ sk_A))),
% 0.51/0.68      inference('sup+', [status(thm)], ['103', '117'])).
% 0.51/0.68  thf('119', plain, ((r2_hidden @ (sk_B @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 0.51/0.68      inference('clc', [status(thm)], ['52', '53'])).
% 0.51/0.68  thf('120', plain,
% 0.51/0.68      (![X0 : $i]:
% 0.51/0.68         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B_1))
% 0.51/0.68          | (r2_hidden @ (k1_funct_1 @ sk_A @ X0) @ (k2_relat_1 @ sk_A)))),
% 0.51/0.68      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.51/0.68  thf('121', plain,
% 0.51/0.68      ((r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ (k2_relat_1 @ sk_A))),
% 0.51/0.68      inference('sup-', [status(thm)], ['119', '120'])).
% 0.51/0.68  thf('122', plain,
% 0.51/0.68      (![X8 : $i, X11 : $i]:
% 0.51/0.68         (~ (v1_relat_1 @ X8)
% 0.51/0.68          | ~ (v1_funct_1 @ X8)
% 0.51/0.68          | ~ (r2_hidden @ X11 @ (k2_relat_1 @ X8))
% 0.51/0.68          | ((X11) = (k1_funct_1 @ X8 @ (sk_D_1 @ X11 @ X8))))),
% 0.51/0.68      inference('simplify', [status(thm)], ['28'])).
% 0.51/0.68  thf('123', plain,
% 0.51/0.68      ((((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.51/0.68          = (k1_funct_1 @ sk_A @ 
% 0.51/0.68             (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A)))
% 0.51/0.68        | ~ (v1_funct_1 @ sk_A)
% 0.51/0.68        | ~ (v1_relat_1 @ sk_A))),
% 0.51/0.68      inference('sup-', [status(thm)], ['121', '122'])).
% 0.51/0.68  thf('124', plain, ((v1_funct_1 @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('125', plain, ((v1_relat_1 @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('126', plain,
% 0.51/0.68      (((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.51/0.68         = (k1_funct_1 @ sk_A @ 
% 0.51/0.68            (sk_D_1 @ (k1_funct_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A)))),
% 0.51/0.68      inference('demod', [status(thm)], ['123', '124', '125'])).
% 0.51/0.68  thf('127', plain, ((v1_relat_1 @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('128', plain, ((v1_funct_1 @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('129', plain,
% 0.51/0.68      ((((k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A))
% 0.51/0.68          = (k1_funct_1 @ sk_A @ (sk_B @ sk_A)))
% 0.51/0.68        | (v2_funct_1 @ sk_A))),
% 0.51/0.68      inference('demod', [status(thm)], ['118', '126', '127', '128'])).
% 0.51/0.68  thf('130', plain, (~ (v2_funct_1 @ sk_A)),
% 0.51/0.68      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.51/0.68  thf('131', plain,
% 0.51/0.68      (((k1_funct_1 @ sk_A @ (sk_C_1 @ sk_A))
% 0.51/0.68         = (k1_funct_1 @ sk_A @ (sk_B @ sk_A)))),
% 0.51/0.68      inference('clc', [status(thm)], ['129', '130'])).
% 0.51/0.68  thf('132', plain, ((v1_relat_1 @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('133', plain, ((v1_funct_1 @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('134', plain,
% 0.51/0.68      ((r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1) @ (k1_relat_1 @ sk_B_1))),
% 0.51/0.68      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.51/0.68  thf('135', plain,
% 0.51/0.68      ((((k1_funct_1 @ sk_A @ (sk_B @ sk_A))
% 0.51/0.68          != (k1_funct_1 @ sk_A @ (sk_B @ sk_A)))
% 0.51/0.68        | ((sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)
% 0.51/0.68            = (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1)))),
% 0.51/0.68      inference('demod', [status(thm)], ['102', '131', '132', '133', '134'])).
% 0.51/0.68  thf('136', plain,
% 0.51/0.68      (((sk_D_1 @ (sk_B @ sk_A) @ sk_B_1) = (sk_D_1 @ (sk_C_1 @ sk_A) @ sk_B_1))),
% 0.51/0.68      inference('simplify', [status(thm)], ['135'])).
% 0.51/0.68  thf('137', plain,
% 0.51/0.68      (((sk_C_1 @ sk_A)
% 0.51/0.68         = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)))),
% 0.51/0.68      inference('demod', [status(thm)], ['33', '136'])).
% 0.51/0.68  thf('138', plain,
% 0.51/0.68      (((sk_B @ sk_A)
% 0.51/0.68         = (k1_funct_1 @ sk_B_1 @ (sk_D_1 @ (sk_B @ sk_A) @ sk_B_1)))),
% 0.51/0.68      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.51/0.68  thf('139', plain, (((sk_B @ sk_A) = (sk_C_1 @ sk_A))),
% 0.51/0.68      inference('sup+', [status(thm)], ['137', '138'])).
% 0.51/0.68  thf('140', plain,
% 0.51/0.68      (![X14 : $i]:
% 0.51/0.68         (((sk_B @ X14) != (sk_C_1 @ X14))
% 0.51/0.68          | (v2_funct_1 @ X14)
% 0.51/0.68          | ~ (v1_funct_1 @ X14)
% 0.51/0.68          | ~ (v1_relat_1 @ X14))),
% 0.51/0.68      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.51/0.68  thf('141', plain,
% 0.51/0.68      ((((sk_B @ sk_A) != (sk_B @ sk_A))
% 0.51/0.68        | ~ (v1_relat_1 @ sk_A)
% 0.51/0.68        | ~ (v1_funct_1 @ sk_A)
% 0.51/0.68        | (v2_funct_1 @ sk_A))),
% 0.51/0.68      inference('sup-', [status(thm)], ['139', '140'])).
% 0.51/0.68  thf('142', plain, ((v1_relat_1 @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('143', plain, ((v1_funct_1 @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('144', plain, ((((sk_B @ sk_A) != (sk_B @ sk_A)) | (v2_funct_1 @ sk_A))),
% 0.51/0.68      inference('demod', [status(thm)], ['141', '142', '143'])).
% 0.51/0.68  thf('145', plain, ((v2_funct_1 @ sk_A)),
% 0.51/0.68      inference('simplify', [status(thm)], ['144'])).
% 0.51/0.68  thf('146', plain, ($false), inference('demod', [status(thm)], ['19', '145'])).
% 0.51/0.68  
% 0.51/0.68  % SZS output end Refutation
% 0.51/0.68  
% 0.51/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
