%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zKXqKlWUbc

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:12 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 174 expanded)
%              Number of leaves         :   18 (  60 expanded)
%              Depth                    :   29
%              Number of atoms          : 1005 (2494 expanded)
%              Number of equality atoms :   57 (  73 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t47_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) )
           => ( v2_funct_1 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
                & ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) )
             => ( v2_funct_1 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t47_funct_1])).

thf('0',plain,(
    ~ ( v2_funct_1 @ sk_B_1 ) ),
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

thf('1',plain,(
    ! [X2: $i] :
      ( ( r2_hidden @ ( sk_B @ X2 ) @ ( k1_relat_1 @ X2 ) )
      | ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('2',plain,(
    ! [X2: $i] :
      ( ( r2_hidden @ ( sk_B @ X2 ) @ ( k1_relat_1 @ X2 ) )
      | ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

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

thf('3',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k1_funct_1 @ X7 @ ( k1_funct_1 @ X8 @ X9 ) ) )
      | ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_B @ X0 ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_B @ X0 ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) ) ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X2: $i] :
      ( ( ( k1_funct_1 @ X2 @ ( sk_B @ X2 ) )
        = ( k1_funct_1 @ X2 @ ( sk_C @ X2 ) ) )
      | ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('7',plain,(
    ! [X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 ) @ ( k1_relat_1 @ X2 ) )
      | ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('8',plain,(
    ! [X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 ) @ ( k1_relat_1 @ X2 ) )
      | ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k1_funct_1 @ X7 @ ( k1_funct_1 @ X8 @ X9 ) ) )
      | ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_C @ X0 ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ X0 @ ( sk_C @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_C @ X0 ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ X0 @ ( sk_C @ X0 ) ) ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(fc2_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('14',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ X1 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ( ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      = ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ~ ( r2_hidden @ X3 @ ( k1_relat_1 @ X2 ) )
      | ~ ( r2_hidden @ X4 @ ( k1_relat_1 @ X2 ) )
      | ( ( k1_funct_1 @ X2 @ X3 )
       != ( k1_funct_1 @ X2 @ X4 ) )
      | ( X3 = X4 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('23',plain,(
    v2_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X1 )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ( X1 = X0 )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['13','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X1 )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ( X1 = X0 )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['25','26','27','28','29'])).

thf('31',plain,(
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
    inference('sup-',[status(thm)],['12','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['31','32','33','34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
       != ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_C @ sk_B_1 ) ) ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( v2_funct_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( r2_hidden @ ( sk_C @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) )
      | ( X0
        = ( sk_C @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['11','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
       != ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_C @ sk_B_1 ) ) ) )
      | ( v2_funct_1 @ sk_B_1 )
      | ~ ( r2_hidden @ ( sk_C @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) )
      | ( X0
        = ( sk_C @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['37','38','39','40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( v2_funct_1 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( X0
        = ( sk_C @ sk_B_1 ) )
      | ( v2_funct_1 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
       != ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_C @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['7','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( X0
        = ( sk_C @ sk_B_1 ) )
      | ( v2_funct_1 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
       != ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_C @ sk_B_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
       != ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_C @ sk_B_1 ) ) ) )
      | ( X0
        = ( sk_C @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( v2_funct_1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
       != ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( v2_funct_1 @ sk_B_1 )
      | ( v2_funct_1 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( X0
        = ( sk_C @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['6','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
       != ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) )
      | ( v2_funct_1 @ sk_B_1 )
      | ( v2_funct_1 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( X0
        = ( sk_C @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( sk_C @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( v2_funct_1 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
       != ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
     != ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A )
    | ( v2_funct_1 @ sk_B_1 )
    | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) )
    | ( ( sk_B @ sk_B_1 )
      = ( sk_C @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
     != ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) )
    | ( v2_funct_1 @ sk_B_1 )
    | ( v2_funct_1 @ sk_B_1 )
    | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) )
    | ( ( sk_B @ sk_B_1 )
      = ( sk_C @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['53','54','55','56','57'])).

thf('59',plain,
    ( ( ( sk_B @ sk_B_1 )
      = ( sk_C @ sk_B_1 ) )
    | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) )
    | ( ( sk_B @ sk_B_1 )
      = ( sk_C @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_funct_1 @ sk_B_1 )
    | ( ( sk_B @ sk_B_1 )
      = ( sk_C @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ( ( sk_B @ sk_B_1 )
      = ( sk_C @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( sk_B @ sk_B_1 )
    = ( sk_C @ sk_B_1 ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X2: $i] :
      ( ( ( sk_B @ X2 )
       != ( sk_C @ X2 ) )
      | ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('69',plain,
    ( ( ( sk_B @ sk_B_1 )
     != ( sk_B @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( ( sk_B @ sk_B_1 )
     != ( sk_B @ sk_B_1 ) )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['0','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zKXqKlWUbc
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:58:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 37 iterations in 0.032s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.49  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i > $i).
% 0.20/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.49  thf(t47_funct_1, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.49           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.20/0.49               ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) =>
% 0.20/0.49             ( v2_funct_1 @ B ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.49          ( ![B:$i]:
% 0.20/0.49            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.49              ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.20/0.49                  ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) =>
% 0.20/0.49                ( v2_funct_1 @ B ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t47_funct_1])).
% 0.20/0.49  thf('0', plain, (~ (v2_funct_1 @ sk_B_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(d8_funct_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.49       ( ( v2_funct_1 @ A ) <=>
% 0.20/0.49         ( ![B:$i,C:$i]:
% 0.20/0.49           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.49               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.49               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.20/0.49             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X2 : $i]:
% 0.20/0.49         ((r2_hidden @ (sk_B @ X2) @ (k1_relat_1 @ X2))
% 0.20/0.49          | (v2_funct_1 @ X2)
% 0.20/0.49          | ~ (v1_funct_1 @ X2)
% 0.20/0.49          | ~ (v1_relat_1 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X2 : $i]:
% 0.20/0.49         ((r2_hidden @ (sk_B @ X2) @ (k1_relat_1 @ X2))
% 0.20/0.49          | (v2_funct_1 @ X2)
% 0.20/0.49          | ~ (v1_funct_1 @ X2)
% 0.20/0.49          | ~ (v1_relat_1 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.20/0.49  thf(t23_funct_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.49       ( ![C:$i]:
% 0.20/0.49         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.49           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.49             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.20/0.49               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X7)
% 0.20/0.49          | ~ (v1_funct_1 @ X7)
% 0.20/0.49          | ((k1_funct_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 0.20/0.49              = (k1_funct_1 @ X7 @ (k1_funct_1 @ X8 @ X9)))
% 0.20/0.49          | ~ (r2_hidden @ X9 @ (k1_relat_1 @ X8))
% 0.20/0.49          | ~ (v1_funct_1 @ X8)
% 0.20/0.49          | ~ (v1_relat_1 @ X8))),
% 0.20/0.49      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X0)
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | (v2_funct_1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ X0)
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ((k1_funct_1 @ (k5_relat_1 @ X0 @ X1) @ (sk_B @ X0))
% 0.20/0.49              = (k1_funct_1 @ X1 @ (k1_funct_1 @ X0 @ (sk_B @ X0))))
% 0.20/0.49          | ~ (v1_funct_1 @ X1)
% 0.20/0.49          | ~ (v1_relat_1 @ X1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X1)
% 0.20/0.49          | ~ (v1_funct_1 @ X1)
% 0.20/0.49          | ((k1_funct_1 @ (k5_relat_1 @ X0 @ X1) @ (sk_B @ X0))
% 0.20/0.49              = (k1_funct_1 @ X1 @ (k1_funct_1 @ X0 @ (sk_B @ X0))))
% 0.20/0.49          | (v2_funct_1 @ X0)
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X2 : $i]:
% 0.20/0.49         (((k1_funct_1 @ X2 @ (sk_B @ X2)) = (k1_funct_1 @ X2 @ (sk_C @ X2)))
% 0.20/0.49          | (v2_funct_1 @ X2)
% 0.20/0.49          | ~ (v1_funct_1 @ X2)
% 0.20/0.49          | ~ (v1_relat_1 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X2 : $i]:
% 0.20/0.49         ((r2_hidden @ (sk_C @ X2) @ (k1_relat_1 @ X2))
% 0.20/0.49          | (v2_funct_1 @ X2)
% 0.20/0.49          | ~ (v1_funct_1 @ X2)
% 0.20/0.49          | ~ (v1_relat_1 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X2 : $i]:
% 0.20/0.49         ((r2_hidden @ (sk_C @ X2) @ (k1_relat_1 @ X2))
% 0.20/0.49          | (v2_funct_1 @ X2)
% 0.20/0.49          | ~ (v1_funct_1 @ X2)
% 0.20/0.49          | ~ (v1_relat_1 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X7)
% 0.20/0.49          | ~ (v1_funct_1 @ X7)
% 0.20/0.49          | ((k1_funct_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 0.20/0.49              = (k1_funct_1 @ X7 @ (k1_funct_1 @ X8 @ X9)))
% 0.20/0.49          | ~ (r2_hidden @ X9 @ (k1_relat_1 @ X8))
% 0.20/0.49          | ~ (v1_funct_1 @ X8)
% 0.20/0.49          | ~ (v1_relat_1 @ X8))),
% 0.20/0.49      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X0)
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | (v2_funct_1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ X0)
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ((k1_funct_1 @ (k5_relat_1 @ X0 @ X1) @ (sk_C @ X0))
% 0.20/0.49              = (k1_funct_1 @ X1 @ (k1_funct_1 @ X0 @ (sk_C @ X0))))
% 0.20/0.49          | ~ (v1_funct_1 @ X1)
% 0.20/0.49          | ~ (v1_relat_1 @ X1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X1)
% 0.20/0.49          | ~ (v1_funct_1 @ X1)
% 0.20/0.49          | ((k1_funct_1 @ (k5_relat_1 @ X0 @ X1) @ (sk_C @ X0))
% 0.20/0.49              = (k1_funct_1 @ X1 @ (k1_funct_1 @ X0 @ (sk_C @ X0))))
% 0.20/0.49          | (v2_funct_1 @ X0)
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.49  thf(fc2_funct_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v1_relat_1 @ B ) & 
% 0.20/0.49         ( v1_funct_1 @ B ) ) =>
% 0.20/0.49       ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) & 
% 0.20/0.49         ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ))).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i]:
% 0.20/0.49         (~ (v1_funct_1 @ X5)
% 0.20/0.49          | ~ (v1_relat_1 @ X5)
% 0.20/0.49          | ~ (v1_relat_1 @ X6)
% 0.20/0.49          | ~ (v1_funct_1 @ X6)
% 0.20/0.49          | (v1_funct_1 @ (k5_relat_1 @ X5 @ X6)))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i]:
% 0.20/0.49         (~ (v1_funct_1 @ X5)
% 0.20/0.49          | ~ (v1_relat_1 @ X5)
% 0.20/0.49          | ~ (v1_relat_1 @ X6)
% 0.20/0.49          | ~ (v1_funct_1 @ X6)
% 0.20/0.49          | (v1_relat_1 @ (k5_relat_1 @ X5 @ X6)))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.20/0.49  thf('14', plain, ((r1_tarski @ (k2_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t46_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( v1_relat_1 @ B ) =>
% 0.20/0.49           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.49             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X0)
% 0.20/0.49          | ((k1_relat_1 @ (k5_relat_1 @ X1 @ X0)) = (k1_relat_1 @ X1))
% 0.20/0.49          | ~ (r1_tarski @ (k2_relat_1 @ X1) @ (k1_relat_1 @ X0))
% 0.20/0.49          | ~ (v1_relat_1 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ sk_B_1)
% 0.20/0.49        | ((k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)) = (k1_relat_1 @ sk_B_1))
% 0.20/0.49        | ~ (v1_relat_1 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.49  thf('17', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('18', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (((k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)) = (k1_relat_1 @ sk_B_1))),
% 0.20/0.49      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.49         (~ (v2_funct_1 @ X2)
% 0.20/0.49          | ~ (r2_hidden @ X3 @ (k1_relat_1 @ X2))
% 0.20/0.49          | ~ (r2_hidden @ X4 @ (k1_relat_1 @ X2))
% 0.20/0.49          | ((k1_funct_1 @ X2 @ X3) != (k1_funct_1 @ X2 @ X4))
% 0.20/0.49          | ((X3) = (X4))
% 0.20/0.49          | ~ (v1_funct_1 @ X2)
% 0.20/0.49          | ~ (v1_relat_1 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.20/0.49          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.20/0.49          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.20/0.49          | ((X0) = (X1))
% 0.20/0.49          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.20/0.49              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X1))
% 0.20/0.49          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.20/0.49          | ~ (v2_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (((k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)) = (k1_relat_1 @ sk_B_1))),
% 0.20/0.49      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.20/0.49  thf('23', plain, ((v2_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.20/0.49          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.20/0.49          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.20/0.49          | ((X0) = (X1))
% 0.20/0.49          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.20/0.49              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X1))
% 0.20/0.49          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1)))),
% 0.20/0.49      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (v1_funct_1 @ sk_A)
% 0.20/0.49          | ~ (v1_relat_1 @ sk_A)
% 0.20/0.49          | ~ (v1_relat_1 @ sk_B_1)
% 0.20/0.49          | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.20/0.49          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X1)
% 0.20/0.49              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.20/0.49          | ((X1) = (X0))
% 0.20/0.49          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.20/0.49          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['13', '24'])).
% 0.20/0.49  thf('26', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('27', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('28', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('29', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.20/0.49          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X1)
% 0.20/0.49              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.20/0.49          | ((X1) = (X0))
% 0.20/0.49          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.20/0.49          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1)))),
% 0.20/0.49      inference('demod', [status(thm)], ['25', '26', '27', '28', '29'])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (v1_funct_1 @ sk_A)
% 0.20/0.49          | ~ (v1_relat_1 @ sk_A)
% 0.20/0.49          | ~ (v1_relat_1 @ sk_B_1)
% 0.20/0.49          | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.20/0.49          | ((X0) = (X1))
% 0.20/0.49          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.20/0.49              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X1))
% 0.20/0.49          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['12', '30'])).
% 0.20/0.49  thf('32', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('33', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('34', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('35', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.20/0.49          | ((X0) = (X1))
% 0.20/0.49          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.20/0.49              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X1))
% 0.20/0.49          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1)))),
% 0.20/0.49      inference('demod', [status(thm)], ['31', '32', '33', '34', '35'])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.20/0.49            != (k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B_1 @ (sk_C @ sk_B_1))))
% 0.20/0.49          | ~ (v1_relat_1 @ sk_B_1)
% 0.20/0.49          | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.49          | (v2_funct_1 @ sk_B_1)
% 0.20/0.49          | ~ (v1_funct_1 @ sk_A)
% 0.20/0.49          | ~ (v1_relat_1 @ sk_A)
% 0.20/0.49          | ~ (r2_hidden @ (sk_C @ sk_B_1) @ (k1_relat_1 @ sk_B_1))
% 0.20/0.49          | ((X0) = (sk_C @ sk_B_1))
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '36'])).
% 0.20/0.49  thf('38', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('39', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('40', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('41', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.20/0.49            != (k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B_1 @ (sk_C @ sk_B_1))))
% 0.20/0.49          | (v2_funct_1 @ sk_B_1)
% 0.20/0.49          | ~ (r2_hidden @ (sk_C @ sk_B_1) @ (k1_relat_1 @ sk_B_1))
% 0.20/0.49          | ((X0) = (sk_C @ sk_B_1))
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1)))),
% 0.20/0.49      inference('demod', [status(thm)], ['37', '38', '39', '40', '41'])).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ sk_B_1)
% 0.20/0.49          | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.49          | (v2_funct_1 @ sk_B_1)
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.20/0.49          | ((X0) = (sk_C @ sk_B_1))
% 0.20/0.49          | (v2_funct_1 @ sk_B_1)
% 0.20/0.49          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.20/0.49              != (k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B_1 @ (sk_C @ sk_B_1)))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['7', '42'])).
% 0.20/0.49  thf('44', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('45', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('46', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_funct_1 @ sk_B_1)
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.20/0.49          | ((X0) = (sk_C @ sk_B_1))
% 0.20/0.49          | (v2_funct_1 @ sk_B_1)
% 0.20/0.49          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.20/0.49              != (k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B_1 @ (sk_C @ sk_B_1)))))),
% 0.20/0.49      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.20/0.49  thf('47', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.20/0.49            != (k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B_1 @ (sk_C @ sk_B_1))))
% 0.20/0.49          | ((X0) = (sk_C @ sk_B_1))
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.20/0.49          | (v2_funct_1 @ sk_B_1))),
% 0.20/0.49      inference('simplify', [status(thm)], ['46'])).
% 0.20/0.49  thf('48', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.20/0.49            != (k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1))))
% 0.20/0.49          | ~ (v1_relat_1 @ sk_B_1)
% 0.20/0.49          | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.49          | (v2_funct_1 @ sk_B_1)
% 0.20/0.49          | (v2_funct_1 @ sk_B_1)
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.20/0.49          | ((X0) = (sk_C @ sk_B_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['6', '47'])).
% 0.20/0.49  thf('49', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('50', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('51', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.20/0.49            != (k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1))))
% 0.20/0.49          | (v2_funct_1 @ sk_B_1)
% 0.20/0.49          | (v2_funct_1 @ sk_B_1)
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.20/0.49          | ((X0) = (sk_C @ sk_B_1)))),
% 0.20/0.49      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.20/0.49  thf('52', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((X0) = (sk_C @ sk_B_1))
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.20/0.49          | (v2_funct_1 @ sk_B_1)
% 0.20/0.49          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.20/0.49              != (k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))))),
% 0.20/0.49      inference('simplify', [status(thm)], ['51'])).
% 0.20/0.49  thf('53', plain,
% 0.20/0.49      ((((k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.20/0.49          != (k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1))))
% 0.20/0.49        | ~ (v1_relat_1 @ sk_B_1)
% 0.20/0.49        | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.49        | (v2_funct_1 @ sk_B_1)
% 0.20/0.49        | ~ (v1_funct_1 @ sk_A)
% 0.20/0.49        | ~ (v1_relat_1 @ sk_A)
% 0.20/0.49        | (v2_funct_1 @ sk_B_1)
% 0.20/0.49        | ~ (r2_hidden @ (sk_B @ sk_B_1) @ (k1_relat_1 @ sk_B_1))
% 0.20/0.49        | ((sk_B @ sk_B_1) = (sk_C @ sk_B_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '52'])).
% 0.20/0.49  thf('54', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('55', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('56', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('57', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('58', plain,
% 0.20/0.49      ((((k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.20/0.49          != (k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1))))
% 0.20/0.49        | (v2_funct_1 @ sk_B_1)
% 0.20/0.49        | (v2_funct_1 @ sk_B_1)
% 0.20/0.49        | ~ (r2_hidden @ (sk_B @ sk_B_1) @ (k1_relat_1 @ sk_B_1))
% 0.20/0.49        | ((sk_B @ sk_B_1) = (sk_C @ sk_B_1)))),
% 0.20/0.49      inference('demod', [status(thm)], ['53', '54', '55', '56', '57'])).
% 0.20/0.49  thf('59', plain,
% 0.20/0.49      ((((sk_B @ sk_B_1) = (sk_C @ sk_B_1))
% 0.20/0.49        | ~ (r2_hidden @ (sk_B @ sk_B_1) @ (k1_relat_1 @ sk_B_1))
% 0.20/0.49        | (v2_funct_1 @ sk_B_1))),
% 0.20/0.49      inference('simplify', [status(thm)], ['58'])).
% 0.20/0.49  thf('60', plain, (~ (v2_funct_1 @ sk_B_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('61', plain,
% 0.20/0.49      ((~ (r2_hidden @ (sk_B @ sk_B_1) @ (k1_relat_1 @ sk_B_1))
% 0.20/0.49        | ((sk_B @ sk_B_1) = (sk_C @ sk_B_1)))),
% 0.20/0.49      inference('clc', [status(thm)], ['59', '60'])).
% 0.20/0.49  thf('62', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ sk_B_1)
% 0.20/0.49        | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.49        | (v2_funct_1 @ sk_B_1)
% 0.20/0.49        | ((sk_B @ sk_B_1) = (sk_C @ sk_B_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '61'])).
% 0.20/0.49  thf('63', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('64', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('65', plain,
% 0.20/0.49      (((v2_funct_1 @ sk_B_1) | ((sk_B @ sk_B_1) = (sk_C @ sk_B_1)))),
% 0.20/0.49      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.20/0.49  thf('66', plain, (~ (v2_funct_1 @ sk_B_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('67', plain, (((sk_B @ sk_B_1) = (sk_C @ sk_B_1))),
% 0.20/0.49      inference('clc', [status(thm)], ['65', '66'])).
% 0.20/0.49  thf('68', plain,
% 0.20/0.49      (![X2 : $i]:
% 0.20/0.49         (((sk_B @ X2) != (sk_C @ X2))
% 0.20/0.49          | (v2_funct_1 @ X2)
% 0.20/0.49          | ~ (v1_funct_1 @ X2)
% 0.20/0.49          | ~ (v1_relat_1 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.20/0.49  thf('69', plain,
% 0.20/0.49      ((((sk_B @ sk_B_1) != (sk_B @ sk_B_1))
% 0.20/0.49        | ~ (v1_relat_1 @ sk_B_1)
% 0.20/0.49        | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.49        | (v2_funct_1 @ sk_B_1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['67', '68'])).
% 0.20/0.49  thf('70', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('71', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('72', plain,
% 0.20/0.49      ((((sk_B @ sk_B_1) != (sk_B @ sk_B_1)) | (v2_funct_1 @ sk_B_1))),
% 0.20/0.49      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.20/0.49  thf('73', plain, ((v2_funct_1 @ sk_B_1)),
% 0.20/0.49      inference('simplify', [status(thm)], ['72'])).
% 0.20/0.49  thf('74', plain, ($false), inference('demod', [status(thm)], ['0', '73'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
