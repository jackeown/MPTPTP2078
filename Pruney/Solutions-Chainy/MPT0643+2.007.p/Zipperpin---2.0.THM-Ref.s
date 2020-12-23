%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.33DmvNjf6X

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 167 expanded)
%              Number of leaves         :   20 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :  725 (3049 expanded)
%              Number of equality atoms :   66 ( 366 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t50_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( ( ( k1_relat_1 @ B )
                = A )
              & ( ( k1_relat_1 @ C )
                = A )
              & ( r1_tarski @ ( k2_relat_1 @ C ) @ A )
              & ( v2_funct_1 @ B )
              & ( ( k5_relat_1 @ C @ B )
                = B ) )
           => ( C
              = ( k6_relat_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v1_funct_1 @ C ) )
           => ( ( ( ( k1_relat_1 @ B )
                  = A )
                & ( ( k1_relat_1 @ C )
                  = A )
                & ( r1_tarski @ ( k2_relat_1 @ C ) @ A )
                & ( v2_funct_1 @ B )
                & ( ( k5_relat_1 @ C @ B )
                  = B ) )
             => ( C
                = ( k6_relat_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_funct_1])).

thf('0',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t34_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( B
          = ( k6_relat_1 @ A ) )
      <=> ( ( ( k1_relat_1 @ B )
            = A )
          & ! [C: $i] :
              ( ( r2_hidden @ C @ A )
             => ( ( k1_funct_1 @ B @ C )
                = C ) ) ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k1_relat_1 @ X13 )
       != X12 )
      | ( r2_hidden @ ( sk_C_2 @ X13 @ X12 ) @ X12 )
      | ( X13
        = ( k6_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('2',plain,(
    ! [X13: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( X13
        = ( k6_relat_1 @ ( k1_relat_1 @ X13 ) ) )
      | ( r2_hidden @ ( sk_C_2 @ X13 @ ( k1_relat_1 @ X13 ) ) @ ( k1_relat_1 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,
    ( ( r2_hidden @ ( sk_C_2 @ sk_C_3 @ sk_A ) @ ( k1_relat_1 @ sk_C_3 ) )
    | ( sk_C_3
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_C_3 ) ) )
    | ~ ( v1_funct_1 @ sk_C_3 )
    | ~ ( v1_relat_1 @ sk_C_3 ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf('4',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ ( sk_C_2 @ sk_C_3 @ sk_A ) @ sk_A )
    | ( sk_C_3
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5','6','7'])).

thf('9',plain,(
    sk_C_3
 != ( k6_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    r2_hidden @ ( sk_C_2 @ sk_C_3 @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k5_relat_1 @ sk_C_3 @ sk_B_1 )
    = sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('12',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X9 @ X10 ) @ X11 )
        = ( k1_funct_1 @ X10 @ ( k1_funct_1 @ X9 @ X11 ) ) )
      | ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ ( k5_relat_1 @ X9 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_C_3 @ sk_B_1 ) @ X0 )
        = ( k1_funct_1 @ sk_B_1 @ ( k1_funct_1 @ sk_C_3 @ X0 ) ) )
      | ~ ( v1_funct_1 @ sk_C_3 )
      | ~ ( v1_relat_1 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k5_relat_1 @ sk_C_3 @ sk_B_1 )
    = sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( k1_funct_1 @ sk_B_1 @ X0 )
        = ( k1_funct_1 @ sk_B_1 @ ( k1_funct_1 @ sk_C_3 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17','18','19'])).

thf('21',plain,
    ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_2 @ sk_C_3 @ sk_A ) )
    = ( k1_funct_1 @ sk_B_1 @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','20'])).

thf('22',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
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

thf('23',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ~ ( r2_hidden @ X5 @ ( k1_relat_1 @ X4 ) )
      | ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ X4 ) )
      | ( ( k1_funct_1 @ X4 @ X5 )
       != ( k1_funct_1 @ X4 @ X6 ) )
      | ( X5 = X6 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','26','27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_2 @ sk_C_3 @ sk_A ) )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) )
        = X0 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','29'])).

thf('31',plain,(
    ! [X13: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( X13
        = ( k6_relat_1 @ ( k1_relat_1 @ X13 ) ) )
      | ( r2_hidden @ ( sk_C_2 @ X13 @ ( k1_relat_1 @ X13 ) ) @ ( k1_relat_1 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('32',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k1_relat_1 @ X8 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X8 @ X7 ) @ ( k2_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C_2 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C_2 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_3 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_C_3
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_C_3 ) ) )
    | ~ ( v1_funct_1 @ sk_C_3 )
    | ~ ( v1_relat_1 @ sk_C_3 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ ( k1_relat_1 @ sk_C_3 ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( sk_C_3
      = ( k6_relat_1 @ sk_A ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['38','39','40','41','42'])).

thf('44',plain,(
    sk_C_3
 != ( k6_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_2 @ sk_C_3 @ sk_A ) )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['30','45'])).

thf('47',plain,
    ( ( ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) )
      = ( sk_C_2 @ sk_C_3 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_C_2 @ sk_C_3 @ sk_A ) @ sk_A ) ),
    inference(eq_res,[status(thm)],['46'])).

thf('48',plain,(
    r2_hidden @ ( sk_C_2 @ sk_C_3 @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('49',plain,
    ( ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) )
    = ( sk_C_2 @ sk_C_3 @ sk_A ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k1_relat_1 @ X13 )
       != X12 )
      | ( ( k1_funct_1 @ X13 @ ( sk_C_2 @ X13 @ X12 ) )
       != ( sk_C_2 @ X13 @ X12 ) )
      | ( X13
        = ( k6_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('52',plain,(
    ! [X13: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( X13
        = ( k6_relat_1 @ ( k1_relat_1 @ X13 ) ) )
      | ( ( k1_funct_1 @ X13 @ ( sk_C_2 @ X13 @ ( k1_relat_1 @ X13 ) ) )
       != ( sk_C_2 @ X13 @ ( k1_relat_1 @ X13 ) ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) )
     != ( sk_C_2 @ sk_C_3 @ ( k1_relat_1 @ sk_C_3 ) ) )
    | ( sk_C_3
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_C_3 ) ) )
    | ~ ( v1_funct_1 @ sk_C_3 )
    | ~ ( v1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) )
     != ( sk_C_2 @ sk_C_3 @ sk_A ) )
    | ( sk_C_3
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54','55','56','57'])).

thf('59',plain,(
    sk_C_3
 != ( k6_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) )
 != ( sk_C_2 @ sk_C_3 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['58','59'])).

thf('61',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['49','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.33DmvNjf6X
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:11:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 186 iterations in 0.090s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.54  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.54  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.54  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.20/0.54  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.20/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.54  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.54  thf(t50_funct_1, conjecture,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.54       ( ![C:$i]:
% 0.20/0.54         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.54           ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.20/0.54               ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.20/0.54               ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) & ( v2_funct_1 @ B ) & 
% 0.20/0.54               ( ( k5_relat_1 @ C @ B ) = ( B ) ) ) =>
% 0.20/0.54             ( ( C ) = ( k6_relat_1 @ A ) ) ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i,B:$i]:
% 0.20/0.54        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.54          ( ![C:$i]:
% 0.20/0.54            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.54              ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.20/0.54                  ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.20/0.54                  ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) & 
% 0.20/0.54                  ( v2_funct_1 @ B ) & ( ( k5_relat_1 @ C @ B ) = ( B ) ) ) =>
% 0.20/0.54                ( ( C ) = ( k6_relat_1 @ A ) ) ) ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t50_funct_1])).
% 0.20/0.54  thf('0', plain, (((k1_relat_1 @ sk_C_3) = (sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t34_funct_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.54       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.20/0.54         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.20/0.54           ( ![C:$i]:
% 0.20/0.54             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      (![X12 : $i, X13 : $i]:
% 0.20/0.54         (((k1_relat_1 @ X13) != (X12))
% 0.20/0.54          | (r2_hidden @ (sk_C_2 @ X13 @ X12) @ X12)
% 0.20/0.54          | ((X13) = (k6_relat_1 @ X12))
% 0.20/0.54          | ~ (v1_funct_1 @ X13)
% 0.20/0.54          | ~ (v1_relat_1 @ X13))),
% 0.20/0.54      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      (![X13 : $i]:
% 0.20/0.54         (~ (v1_relat_1 @ X13)
% 0.20/0.54          | ~ (v1_funct_1 @ X13)
% 0.20/0.54          | ((X13) = (k6_relat_1 @ (k1_relat_1 @ X13)))
% 0.20/0.54          | (r2_hidden @ (sk_C_2 @ X13 @ (k1_relat_1 @ X13)) @ 
% 0.20/0.54             (k1_relat_1 @ X13)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['1'])).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      (((r2_hidden @ (sk_C_2 @ sk_C_3 @ sk_A) @ (k1_relat_1 @ sk_C_3))
% 0.20/0.54        | ((sk_C_3) = (k6_relat_1 @ (k1_relat_1 @ sk_C_3)))
% 0.20/0.54        | ~ (v1_funct_1 @ sk_C_3)
% 0.20/0.54        | ~ (v1_relat_1 @ sk_C_3))),
% 0.20/0.54      inference('sup+', [status(thm)], ['0', '2'])).
% 0.20/0.54  thf('4', plain, (((k1_relat_1 @ sk_C_3) = (sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('5', plain, (((k1_relat_1 @ sk_C_3) = (sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('6', plain, ((v1_funct_1 @ sk_C_3)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('7', plain, ((v1_relat_1 @ sk_C_3)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      (((r2_hidden @ (sk_C_2 @ sk_C_3 @ sk_A) @ sk_A)
% 0.20/0.54        | ((sk_C_3) = (k6_relat_1 @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['3', '4', '5', '6', '7'])).
% 0.20/0.54  thf('9', plain, (((sk_C_3) != (k6_relat_1 @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('10', plain, ((r2_hidden @ (sk_C_2 @ sk_C_3 @ sk_A) @ sk_A)),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.20/0.54  thf('11', plain, (((k5_relat_1 @ sk_C_3 @ sk_B_1) = (sk_B_1))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t22_funct_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.54       ( ![C:$i]:
% 0.20/0.54         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.54           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) =>
% 0.20/0.54             ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A ) =
% 0.20/0.54               ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) ))).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.54         (~ (v1_relat_1 @ X9)
% 0.20/0.54          | ~ (v1_funct_1 @ X9)
% 0.20/0.54          | ((k1_funct_1 @ (k5_relat_1 @ X9 @ X10) @ X11)
% 0.20/0.54              = (k1_funct_1 @ X10 @ (k1_funct_1 @ X9 @ X11)))
% 0.20/0.54          | ~ (r2_hidden @ X11 @ (k1_relat_1 @ (k5_relat_1 @ X9 @ X10)))
% 0.20/0.54          | ~ (v1_funct_1 @ X10)
% 0.20/0.54          | ~ (v1_relat_1 @ X10))),
% 0.20/0.54      inference('cnf', [status(esa)], [t22_funct_1])).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.20/0.54          | ~ (v1_relat_1 @ sk_B_1)
% 0.20/0.54          | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.54          | ((k1_funct_1 @ (k5_relat_1 @ sk_C_3 @ sk_B_1) @ X0)
% 0.20/0.54              = (k1_funct_1 @ sk_B_1 @ (k1_funct_1 @ sk_C_3 @ X0)))
% 0.20/0.54          | ~ (v1_funct_1 @ sk_C_3)
% 0.20/0.54          | ~ (v1_relat_1 @ sk_C_3))),
% 0.20/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.54  thf('14', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('15', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('16', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('17', plain, (((k5_relat_1 @ sk_C_3 @ sk_B_1) = (sk_B_1))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('18', plain, ((v1_funct_1 @ sk_C_3)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('19', plain, ((v1_relat_1 @ sk_C_3)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.54          | ((k1_funct_1 @ sk_B_1 @ X0)
% 0.20/0.54              = (k1_funct_1 @ sk_B_1 @ (k1_funct_1 @ sk_C_3 @ X0))))),
% 0.20/0.54      inference('demod', [status(thm)],
% 0.20/0.54                ['13', '14', '15', '16', '17', '18', '19'])).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      (((k1_funct_1 @ sk_B_1 @ (sk_C_2 @ sk_C_3 @ sk_A))
% 0.20/0.54         = (k1_funct_1 @ sk_B_1 @ 
% 0.20/0.54            (k1_funct_1 @ sk_C_3 @ (sk_C_2 @ sk_C_3 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['10', '20'])).
% 0.20/0.54  thf('22', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(d8_funct_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.54       ( ( v2_funct_1 @ A ) <=>
% 0.20/0.54         ( ![B:$i,C:$i]:
% 0.20/0.54           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.54               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.54               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.20/0.54             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.20/0.54  thf('23', plain,
% 0.20/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.54         (~ (v2_funct_1 @ X4)
% 0.20/0.54          | ~ (r2_hidden @ X5 @ (k1_relat_1 @ X4))
% 0.20/0.54          | ~ (r2_hidden @ X6 @ (k1_relat_1 @ X4))
% 0.20/0.54          | ((k1_funct_1 @ X4 @ X5) != (k1_funct_1 @ X4 @ X6))
% 0.20/0.54          | ((X5) = (X6))
% 0.20/0.54          | ~ (v1_funct_1 @ X4)
% 0.20/0.54          | ~ (v1_relat_1 @ X4))),
% 0.20/0.54      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.20/0.54  thf('24', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.54          | ~ (v1_relat_1 @ sk_B_1)
% 0.20/0.54          | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.54          | ((X0) = (X1))
% 0.20/0.54          | ((k1_funct_1 @ sk_B_1 @ X0) != (k1_funct_1 @ sk_B_1 @ X1))
% 0.20/0.54          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1))
% 0.20/0.54          | ~ (v2_funct_1 @ sk_B_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.54  thf('25', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('26', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('27', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('28', plain, ((v2_funct_1 @ sk_B_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('29', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.54          | ((X0) = (X1))
% 0.20/0.54          | ((k1_funct_1 @ sk_B_1 @ X0) != (k1_funct_1 @ sk_B_1 @ X1))
% 0.20/0.54          | ~ (r2_hidden @ X1 @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['24', '25', '26', '27', '28'])).
% 0.20/0.54  thf('30', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((k1_funct_1 @ sk_B_1 @ (sk_C_2 @ sk_C_3 @ sk_A))
% 0.20/0.54            != (k1_funct_1 @ sk_B_1 @ X0))
% 0.20/0.54          | ~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.54          | ((k1_funct_1 @ sk_C_3 @ (sk_C_2 @ sk_C_3 @ sk_A)) = (X0))
% 0.20/0.54          | ~ (r2_hidden @ (k1_funct_1 @ sk_C_3 @ (sk_C_2 @ sk_C_3 @ sk_A)) @ 
% 0.20/0.54               sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['21', '29'])).
% 0.20/0.54  thf('31', plain,
% 0.20/0.54      (![X13 : $i]:
% 0.20/0.54         (~ (v1_relat_1 @ X13)
% 0.20/0.54          | ~ (v1_funct_1 @ X13)
% 0.20/0.54          | ((X13) = (k6_relat_1 @ (k1_relat_1 @ X13)))
% 0.20/0.54          | (r2_hidden @ (sk_C_2 @ X13 @ (k1_relat_1 @ X13)) @ 
% 0.20/0.54             (k1_relat_1 @ X13)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['1'])).
% 0.20/0.54  thf(t12_funct_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.54       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.54         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.20/0.54  thf('32', plain,
% 0.20/0.54      (![X7 : $i, X8 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X7 @ (k1_relat_1 @ X8))
% 0.20/0.54          | (r2_hidden @ (k1_funct_1 @ X8 @ X7) @ (k2_relat_1 @ X8))
% 0.20/0.54          | ~ (v1_funct_1 @ X8)
% 0.20/0.54          | ~ (v1_relat_1 @ X8))),
% 0.20/0.54      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.20/0.54  thf('33', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((X0) = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.20/0.54          | ~ (v1_funct_1 @ X0)
% 0.20/0.54          | ~ (v1_relat_1 @ X0)
% 0.20/0.54          | ~ (v1_relat_1 @ X0)
% 0.20/0.54          | ~ (v1_funct_1 @ X0)
% 0.20/0.54          | (r2_hidden @ 
% 0.20/0.54             (k1_funct_1 @ X0 @ (sk_C_2 @ X0 @ (k1_relat_1 @ X0))) @ 
% 0.20/0.54             (k2_relat_1 @ X0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.54  thf('34', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r2_hidden @ (k1_funct_1 @ X0 @ (sk_C_2 @ X0 @ (k1_relat_1 @ X0))) @ 
% 0.20/0.54           (k2_relat_1 @ X0))
% 0.20/0.54          | ~ (v1_relat_1 @ X0)
% 0.20/0.54          | ~ (v1_funct_1 @ X0)
% 0.20/0.54          | ((X0) = (k6_relat_1 @ (k1_relat_1 @ X0))))),
% 0.20/0.54      inference('simplify', [status(thm)], ['33'])).
% 0.20/0.54  thf('35', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_3) @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(d3_tarski, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.54  thf('36', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.54          | (r2_hidden @ X0 @ X2)
% 0.20/0.54          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.54  thf('37', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_3)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.54  thf('38', plain,
% 0.20/0.54      ((((sk_C_3) = (k6_relat_1 @ (k1_relat_1 @ sk_C_3)))
% 0.20/0.54        | ~ (v1_funct_1 @ sk_C_3)
% 0.20/0.54        | ~ (v1_relat_1 @ sk_C_3)
% 0.20/0.54        | (r2_hidden @ 
% 0.20/0.54           (k1_funct_1 @ sk_C_3 @ (sk_C_2 @ sk_C_3 @ (k1_relat_1 @ sk_C_3))) @ 
% 0.20/0.54           sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['34', '37'])).
% 0.20/0.54  thf('39', plain, (((k1_relat_1 @ sk_C_3) = (sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('40', plain, ((v1_funct_1 @ sk_C_3)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('41', plain, ((v1_relat_1 @ sk_C_3)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('42', plain, (((k1_relat_1 @ sk_C_3) = (sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('43', plain,
% 0.20/0.54      ((((sk_C_3) = (k6_relat_1 @ sk_A))
% 0.20/0.54        | (r2_hidden @ (k1_funct_1 @ sk_C_3 @ (sk_C_2 @ sk_C_3 @ sk_A)) @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 0.20/0.54  thf('44', plain, (((sk_C_3) != (k6_relat_1 @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('45', plain,
% 0.20/0.54      ((r2_hidden @ (k1_funct_1 @ sk_C_3 @ (sk_C_2 @ sk_C_3 @ sk_A)) @ sk_A)),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['43', '44'])).
% 0.20/0.54  thf('46', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((k1_funct_1 @ sk_B_1 @ (sk_C_2 @ sk_C_3 @ sk_A))
% 0.20/0.54            != (k1_funct_1 @ sk_B_1 @ X0))
% 0.20/0.54          | ~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.54          | ((k1_funct_1 @ sk_C_3 @ (sk_C_2 @ sk_C_3 @ sk_A)) = (X0)))),
% 0.20/0.54      inference('demod', [status(thm)], ['30', '45'])).
% 0.20/0.54  thf('47', plain,
% 0.20/0.54      ((((k1_funct_1 @ sk_C_3 @ (sk_C_2 @ sk_C_3 @ sk_A))
% 0.20/0.54          = (sk_C_2 @ sk_C_3 @ sk_A))
% 0.20/0.54        | ~ (r2_hidden @ (sk_C_2 @ sk_C_3 @ sk_A) @ sk_A))),
% 0.20/0.54      inference('eq_res', [status(thm)], ['46'])).
% 0.20/0.54  thf('48', plain, ((r2_hidden @ (sk_C_2 @ sk_C_3 @ sk_A) @ sk_A)),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.20/0.54  thf('49', plain,
% 0.20/0.54      (((k1_funct_1 @ sk_C_3 @ (sk_C_2 @ sk_C_3 @ sk_A))
% 0.20/0.54         = (sk_C_2 @ sk_C_3 @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.54  thf('50', plain, (((k1_relat_1 @ sk_C_3) = (sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('51', plain,
% 0.20/0.54      (![X12 : $i, X13 : $i]:
% 0.20/0.54         (((k1_relat_1 @ X13) != (X12))
% 0.20/0.54          | ((k1_funct_1 @ X13 @ (sk_C_2 @ X13 @ X12)) != (sk_C_2 @ X13 @ X12))
% 0.20/0.54          | ((X13) = (k6_relat_1 @ X12))
% 0.20/0.54          | ~ (v1_funct_1 @ X13)
% 0.20/0.54          | ~ (v1_relat_1 @ X13))),
% 0.20/0.54      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.20/0.54  thf('52', plain,
% 0.20/0.54      (![X13 : $i]:
% 0.20/0.54         (~ (v1_relat_1 @ X13)
% 0.20/0.54          | ~ (v1_funct_1 @ X13)
% 0.20/0.54          | ((X13) = (k6_relat_1 @ (k1_relat_1 @ X13)))
% 0.20/0.54          | ((k1_funct_1 @ X13 @ (sk_C_2 @ X13 @ (k1_relat_1 @ X13)))
% 0.20/0.54              != (sk_C_2 @ X13 @ (k1_relat_1 @ X13))))),
% 0.20/0.54      inference('simplify', [status(thm)], ['51'])).
% 0.20/0.54  thf('53', plain,
% 0.20/0.54      ((((k1_funct_1 @ sk_C_3 @ (sk_C_2 @ sk_C_3 @ sk_A))
% 0.20/0.54          != (sk_C_2 @ sk_C_3 @ (k1_relat_1 @ sk_C_3)))
% 0.20/0.54        | ((sk_C_3) = (k6_relat_1 @ (k1_relat_1 @ sk_C_3)))
% 0.20/0.54        | ~ (v1_funct_1 @ sk_C_3)
% 0.20/0.54        | ~ (v1_relat_1 @ sk_C_3))),
% 0.20/0.54      inference('sup-', [status(thm)], ['50', '52'])).
% 0.20/0.54  thf('54', plain, (((k1_relat_1 @ sk_C_3) = (sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('55', plain, (((k1_relat_1 @ sk_C_3) = (sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('56', plain, ((v1_funct_1 @ sk_C_3)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('57', plain, ((v1_relat_1 @ sk_C_3)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('58', plain,
% 0.20/0.54      ((((k1_funct_1 @ sk_C_3 @ (sk_C_2 @ sk_C_3 @ sk_A))
% 0.20/0.54          != (sk_C_2 @ sk_C_3 @ sk_A))
% 0.20/0.54        | ((sk_C_3) = (k6_relat_1 @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['53', '54', '55', '56', '57'])).
% 0.20/0.54  thf('59', plain, (((sk_C_3) != (k6_relat_1 @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('60', plain,
% 0.20/0.54      (((k1_funct_1 @ sk_C_3 @ (sk_C_2 @ sk_C_3 @ sk_A))
% 0.20/0.54         != (sk_C_2 @ sk_C_3 @ sk_A))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['58', '59'])).
% 0.20/0.54  thf('61', plain, ($false),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['49', '60'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
