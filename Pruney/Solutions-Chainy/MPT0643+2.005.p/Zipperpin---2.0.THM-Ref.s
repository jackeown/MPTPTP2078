%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qNMf7LDH52

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:14 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 168 expanded)
%              Number of leaves         :   20 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :  751 (3075 expanded)
%              Number of equality atoms :   70 ( 370 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_4_type,type,(
    sk_C_4: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ( ( k1_relat_1 @ sk_C_4 )
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
    ! [X17: $i,X18: $i] :
      ( ( ( k1_relat_1 @ X18 )
       != X17 )
      | ( r2_hidden @ ( sk_C_3 @ X18 @ X17 ) @ X17 )
      | ( X18
        = ( k6_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('2',plain,(
    ! [X18: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( X18
        = ( k6_relat_1 @ ( k1_relat_1 @ X18 ) ) )
      | ( r2_hidden @ ( sk_C_3 @ X18 @ ( k1_relat_1 @ X18 ) ) @ ( k1_relat_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,
    ( ( r2_hidden @ ( sk_C_3 @ sk_C_4 @ sk_A ) @ ( k1_relat_1 @ sk_C_4 ) )
    | ( sk_C_4
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_C_4 ) ) )
    | ~ ( v1_funct_1 @ sk_C_4 )
    | ~ ( v1_relat_1 @ sk_C_4 ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf('4',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ ( sk_C_3 @ sk_C_4 @ sk_A ) @ sk_A )
    | ( sk_C_4
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5','6','7'])).

thf('9',plain,(
    sk_C_4
 != ( k6_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    r2_hidden @ ( sk_C_3 @ sk_C_4 @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k5_relat_1 @ sk_C_4 @ sk_B_1 )
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X14 @ X15 ) @ X16 )
        = ( k1_funct_1 @ X15 @ ( k1_funct_1 @ X14 @ X16 ) ) )
      | ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ ( k5_relat_1 @ X14 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_C_4 @ sk_B_1 ) @ X0 )
        = ( k1_funct_1 @ sk_B_1 @ ( k1_funct_1 @ sk_C_4 @ X0 ) ) )
      | ~ ( v1_funct_1 @ sk_C_4 )
      | ~ ( v1_relat_1 @ sk_C_4 ) ) ),
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
    ( ( k5_relat_1 @ sk_C_4 @ sk_B_1 )
    = sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( k1_funct_1 @ sk_B_1 @ X0 )
        = ( k1_funct_1 @ sk_B_1 @ ( k1_funct_1 @ sk_C_4 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17','18','19'])).

thf('21',plain,
    ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
    = ( k1_funct_1 @ sk_B_1 @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X11 ) )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X11 ) )
      | ( ( k1_funct_1 @ X11 @ X12 )
       != ( k1_funct_1 @ X11 @ X13 ) )
      | ( X12 = X13 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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
      ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
        = X0 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','29'])).

thf('31',plain,(
    ! [X18: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( X18
        = ( k6_relat_1 @ ( k1_relat_1 @ X18 ) ) )
      | ( r2_hidden @ ( sk_C_3 @ X18 @ ( k1_relat_1 @ X18 ) ) @ ( k1_relat_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

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

thf('32',plain,(
    ! [X5: $i,X7: $i,X9: $i,X10: $i] :
      ( ( X7
       != ( k2_relat_1 @ X5 ) )
      | ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X5 ) )
      | ( X9
       != ( k1_funct_1 @ X5 @ X10 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('33',plain,(
    ! [X5: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X5 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X5 @ X10 ) @ ( k2_relat_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C_3 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C_3 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_4 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_4 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_C_4
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_C_4 ) ) )
    | ~ ( v1_funct_1 @ sk_C_4 )
    | ~ ( v1_relat_1 @ sk_C_4 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ ( k1_relat_1 @ sk_C_4 ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( sk_C_4
      = ( k6_relat_1 @ sk_A ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','41','42','43'])).

thf('45',plain,(
    sk_C_4
 != ( k6_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['30','46'])).

thf('48',plain,
    ( ( ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
      = ( sk_C_3 @ sk_C_4 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_C_3 @ sk_C_4 @ sk_A ) @ sk_A ) ),
    inference(eq_res,[status(thm)],['47'])).

thf('49',plain,(
    r2_hidden @ ( sk_C_3 @ sk_C_4 @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('50',plain,
    ( ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
    = ( sk_C_3 @ sk_C_4 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k1_relat_1 @ X18 )
       != X17 )
      | ( ( k1_funct_1 @ X18 @ ( sk_C_3 @ X18 @ X17 ) )
       != ( sk_C_3 @ X18 @ X17 ) )
      | ( X18
        = ( k6_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('53',plain,(
    ! [X18: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( X18
        = ( k6_relat_1 @ ( k1_relat_1 @ X18 ) ) )
      | ( ( k1_funct_1 @ X18 @ ( sk_C_3 @ X18 @ ( k1_relat_1 @ X18 ) ) )
       != ( sk_C_3 @ X18 @ ( k1_relat_1 @ X18 ) ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
     != ( sk_C_3 @ sk_C_4 @ ( k1_relat_1 @ sk_C_4 ) ) )
    | ( sk_C_4
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_C_4 ) ) )
    | ~ ( v1_funct_1 @ sk_C_4 )
    | ~ ( v1_relat_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
     != ( sk_C_3 @ sk_C_4 @ sk_A ) )
    | ( sk_C_4
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55','56','57','58'])).

thf('60',plain,(
    sk_C_4
 != ( k6_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
 != ( sk_C_3 @ sk_C_4 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['59','60'])).

thf('62',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['50','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qNMf7LDH52
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:04:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.90/1.07  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.90/1.07  % Solved by: fo/fo7.sh
% 0.90/1.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.07  % done 858 iterations in 0.610s
% 0.90/1.07  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.90/1.07  % SZS output start Refutation
% 0.90/1.07  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.90/1.07  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.90/1.07  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.07  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.90/1.07  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.90/1.07  thf(sk_C_4_type, type, sk_C_4: $i).
% 0.90/1.07  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.90/1.07  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.90/1.07  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.07  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.07  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.90/1.07  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 0.90/1.07  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.90/1.07  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.90/1.07  thf(t50_funct_1, conjecture,
% 0.90/1.07    (![A:$i,B:$i]:
% 0.90/1.07     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.90/1.07       ( ![C:$i]:
% 0.90/1.07         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.90/1.07           ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.90/1.07               ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.90/1.07               ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) & ( v2_funct_1 @ B ) & 
% 0.90/1.07               ( ( k5_relat_1 @ C @ B ) = ( B ) ) ) =>
% 0.90/1.07             ( ( C ) = ( k6_relat_1 @ A ) ) ) ) ) ))).
% 0.90/1.07  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.07    (~( ![A:$i,B:$i]:
% 0.90/1.07        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.90/1.07          ( ![C:$i]:
% 0.90/1.07            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.90/1.07              ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.90/1.07                  ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.90/1.07                  ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) & 
% 0.90/1.07                  ( v2_funct_1 @ B ) & ( ( k5_relat_1 @ C @ B ) = ( B ) ) ) =>
% 0.90/1.07                ( ( C ) = ( k6_relat_1 @ A ) ) ) ) ) ) )),
% 0.90/1.07    inference('cnf.neg', [status(esa)], [t50_funct_1])).
% 0.90/1.07  thf('0', plain, (((k1_relat_1 @ sk_C_4) = (sk_A))),
% 0.90/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.07  thf(t34_funct_1, axiom,
% 0.90/1.07    (![A:$i,B:$i]:
% 0.90/1.07     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.90/1.07       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.90/1.07         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.90/1.07           ( ![C:$i]:
% 0.90/1.07             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 0.90/1.07  thf('1', plain,
% 0.90/1.07      (![X17 : $i, X18 : $i]:
% 0.90/1.07         (((k1_relat_1 @ X18) != (X17))
% 0.90/1.07          | (r2_hidden @ (sk_C_3 @ X18 @ X17) @ X17)
% 0.90/1.07          | ((X18) = (k6_relat_1 @ X17))
% 0.90/1.07          | ~ (v1_funct_1 @ X18)
% 0.90/1.07          | ~ (v1_relat_1 @ X18))),
% 0.90/1.07      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.90/1.07  thf('2', plain,
% 0.90/1.07      (![X18 : $i]:
% 0.90/1.07         (~ (v1_relat_1 @ X18)
% 0.90/1.07          | ~ (v1_funct_1 @ X18)
% 0.90/1.07          | ((X18) = (k6_relat_1 @ (k1_relat_1 @ X18)))
% 0.90/1.07          | (r2_hidden @ (sk_C_3 @ X18 @ (k1_relat_1 @ X18)) @ 
% 0.90/1.07             (k1_relat_1 @ X18)))),
% 0.90/1.07      inference('simplify', [status(thm)], ['1'])).
% 0.90/1.07  thf('3', plain,
% 0.90/1.07      (((r2_hidden @ (sk_C_3 @ sk_C_4 @ sk_A) @ (k1_relat_1 @ sk_C_4))
% 0.90/1.07        | ((sk_C_4) = (k6_relat_1 @ (k1_relat_1 @ sk_C_4)))
% 0.90/1.07        | ~ (v1_funct_1 @ sk_C_4)
% 0.90/1.07        | ~ (v1_relat_1 @ sk_C_4))),
% 0.90/1.07      inference('sup+', [status(thm)], ['0', '2'])).
% 0.90/1.07  thf('4', plain, (((k1_relat_1 @ sk_C_4) = (sk_A))),
% 0.90/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.07  thf('5', plain, (((k1_relat_1 @ sk_C_4) = (sk_A))),
% 0.90/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.07  thf('6', plain, ((v1_funct_1 @ sk_C_4)),
% 0.90/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.07  thf('7', plain, ((v1_relat_1 @ sk_C_4)),
% 0.90/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.07  thf('8', plain,
% 0.90/1.07      (((r2_hidden @ (sk_C_3 @ sk_C_4 @ sk_A) @ sk_A)
% 0.90/1.07        | ((sk_C_4) = (k6_relat_1 @ sk_A)))),
% 0.90/1.07      inference('demod', [status(thm)], ['3', '4', '5', '6', '7'])).
% 0.90/1.07  thf('9', plain, (((sk_C_4) != (k6_relat_1 @ sk_A))),
% 0.90/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.07  thf('10', plain, ((r2_hidden @ (sk_C_3 @ sk_C_4 @ sk_A) @ sk_A)),
% 0.90/1.07      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.90/1.07  thf('11', plain, (((k5_relat_1 @ sk_C_4 @ sk_B_1) = (sk_B_1))),
% 0.90/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.07  thf(t22_funct_1, axiom,
% 0.90/1.07    (![A:$i,B:$i]:
% 0.90/1.07     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.90/1.07       ( ![C:$i]:
% 0.90/1.07         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.90/1.07           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) =>
% 0.90/1.07             ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A ) =
% 0.90/1.07               ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) ))).
% 0.90/1.07  thf('12', plain,
% 0.90/1.07      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.90/1.07         (~ (v1_relat_1 @ X14)
% 0.90/1.07          | ~ (v1_funct_1 @ X14)
% 0.90/1.07          | ((k1_funct_1 @ (k5_relat_1 @ X14 @ X15) @ X16)
% 0.90/1.07              = (k1_funct_1 @ X15 @ (k1_funct_1 @ X14 @ X16)))
% 0.90/1.07          | ~ (r2_hidden @ X16 @ (k1_relat_1 @ (k5_relat_1 @ X14 @ X15)))
% 0.90/1.07          | ~ (v1_funct_1 @ X15)
% 0.90/1.07          | ~ (v1_relat_1 @ X15))),
% 0.90/1.07      inference('cnf', [status(esa)], [t22_funct_1])).
% 0.90/1.07  thf('13', plain,
% 0.90/1.07      (![X0 : $i]:
% 0.90/1.07         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.90/1.07          | ~ (v1_relat_1 @ sk_B_1)
% 0.90/1.07          | ~ (v1_funct_1 @ sk_B_1)
% 0.90/1.07          | ((k1_funct_1 @ (k5_relat_1 @ sk_C_4 @ sk_B_1) @ X0)
% 0.90/1.07              = (k1_funct_1 @ sk_B_1 @ (k1_funct_1 @ sk_C_4 @ X0)))
% 0.90/1.07          | ~ (v1_funct_1 @ sk_C_4)
% 0.90/1.07          | ~ (v1_relat_1 @ sk_C_4))),
% 0.90/1.07      inference('sup-', [status(thm)], ['11', '12'])).
% 0.90/1.07  thf('14', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.90/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.07  thf('15', plain, ((v1_relat_1 @ sk_B_1)),
% 0.90/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.07  thf('16', plain, ((v1_funct_1 @ sk_B_1)),
% 0.90/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.07  thf('17', plain, (((k5_relat_1 @ sk_C_4 @ sk_B_1) = (sk_B_1))),
% 0.90/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.07  thf('18', plain, ((v1_funct_1 @ sk_C_4)),
% 0.90/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.07  thf('19', plain, ((v1_relat_1 @ sk_C_4)),
% 0.90/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.07  thf('20', plain,
% 0.90/1.07      (![X0 : $i]:
% 0.90/1.07         (~ (r2_hidden @ X0 @ sk_A)
% 0.90/1.07          | ((k1_funct_1 @ sk_B_1 @ X0)
% 0.90/1.07              = (k1_funct_1 @ sk_B_1 @ (k1_funct_1 @ sk_C_4 @ X0))))),
% 0.90/1.07      inference('demod', [status(thm)],
% 0.90/1.07                ['13', '14', '15', '16', '17', '18', '19'])).
% 0.90/1.07  thf('21', plain,
% 0.90/1.07      (((k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 0.90/1.07         = (k1_funct_1 @ sk_B_1 @ 
% 0.90/1.07            (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A))))),
% 0.90/1.07      inference('sup-', [status(thm)], ['10', '20'])).
% 0.90/1.07  thf('22', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.90/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.07  thf(d8_funct_1, axiom,
% 0.90/1.07    (![A:$i]:
% 0.90/1.07     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.90/1.07       ( ( v2_funct_1 @ A ) <=>
% 0.90/1.07         ( ![B:$i,C:$i]:
% 0.90/1.07           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.90/1.07               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.90/1.07               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.90/1.07             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.90/1.07  thf('23', plain,
% 0.90/1.07      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.90/1.07         (~ (v2_funct_1 @ X11)
% 0.90/1.07          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ X11))
% 0.90/1.07          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X11))
% 0.90/1.07          | ((k1_funct_1 @ X11 @ X12) != (k1_funct_1 @ X11 @ X13))
% 0.90/1.07          | ((X12) = (X13))
% 0.90/1.07          | ~ (v1_funct_1 @ X11)
% 0.90/1.07          | ~ (v1_relat_1 @ X11))),
% 0.90/1.07      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.90/1.07  thf('24', plain,
% 0.90/1.07      (![X0 : $i, X1 : $i]:
% 0.90/1.07         (~ (r2_hidden @ X0 @ sk_A)
% 0.90/1.07          | ~ (v1_relat_1 @ sk_B_1)
% 0.90/1.07          | ~ (v1_funct_1 @ sk_B_1)
% 0.90/1.07          | ((X0) = (X1))
% 0.90/1.07          | ((k1_funct_1 @ sk_B_1 @ X0) != (k1_funct_1 @ sk_B_1 @ X1))
% 0.90/1.07          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1))
% 0.90/1.07          | ~ (v2_funct_1 @ sk_B_1))),
% 0.90/1.07      inference('sup-', [status(thm)], ['22', '23'])).
% 0.90/1.07  thf('25', plain, ((v1_relat_1 @ sk_B_1)),
% 0.90/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.07  thf('26', plain, ((v1_funct_1 @ sk_B_1)),
% 0.90/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.07  thf('27', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.90/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.07  thf('28', plain, ((v2_funct_1 @ sk_B_1)),
% 0.90/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.07  thf('29', plain,
% 0.90/1.07      (![X0 : $i, X1 : $i]:
% 0.90/1.07         (~ (r2_hidden @ X0 @ sk_A)
% 0.90/1.07          | ((X0) = (X1))
% 0.90/1.07          | ((k1_funct_1 @ sk_B_1 @ X0) != (k1_funct_1 @ sk_B_1 @ X1))
% 0.90/1.07          | ~ (r2_hidden @ X1 @ sk_A))),
% 0.90/1.07      inference('demod', [status(thm)], ['24', '25', '26', '27', '28'])).
% 0.90/1.07  thf('30', plain,
% 0.90/1.07      (![X0 : $i]:
% 0.90/1.07         (((k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 0.90/1.07            != (k1_funct_1 @ sk_B_1 @ X0))
% 0.90/1.07          | ~ (r2_hidden @ X0 @ sk_A)
% 0.90/1.07          | ((k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A)) = (X0))
% 0.90/1.07          | ~ (r2_hidden @ (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ 
% 0.90/1.07               sk_A))),
% 0.90/1.07      inference('sup-', [status(thm)], ['21', '29'])).
% 0.90/1.07  thf('31', plain,
% 0.90/1.07      (![X18 : $i]:
% 0.90/1.07         (~ (v1_relat_1 @ X18)
% 0.90/1.07          | ~ (v1_funct_1 @ X18)
% 0.90/1.07          | ((X18) = (k6_relat_1 @ (k1_relat_1 @ X18)))
% 0.90/1.07          | (r2_hidden @ (sk_C_3 @ X18 @ (k1_relat_1 @ X18)) @ 
% 0.90/1.07             (k1_relat_1 @ X18)))),
% 0.90/1.07      inference('simplify', [status(thm)], ['1'])).
% 0.90/1.07  thf(d5_funct_1, axiom,
% 0.90/1.07    (![A:$i]:
% 0.90/1.07     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.90/1.07       ( ![B:$i]:
% 0.90/1.07         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.90/1.07           ( ![C:$i]:
% 0.90/1.07             ( ( r2_hidden @ C @ B ) <=>
% 0.90/1.07               ( ?[D:$i]:
% 0.90/1.07                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.90/1.07                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.90/1.07  thf('32', plain,
% 0.90/1.07      (![X5 : $i, X7 : $i, X9 : $i, X10 : $i]:
% 0.90/1.07         (((X7) != (k2_relat_1 @ X5))
% 0.90/1.07          | (r2_hidden @ X9 @ X7)
% 0.90/1.07          | ~ (r2_hidden @ X10 @ (k1_relat_1 @ X5))
% 0.90/1.07          | ((X9) != (k1_funct_1 @ X5 @ X10))
% 0.90/1.07          | ~ (v1_funct_1 @ X5)
% 0.90/1.07          | ~ (v1_relat_1 @ X5))),
% 0.90/1.07      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.90/1.07  thf('33', plain,
% 0.90/1.07      (![X5 : $i, X10 : $i]:
% 0.90/1.07         (~ (v1_relat_1 @ X5)
% 0.90/1.07          | ~ (v1_funct_1 @ X5)
% 0.90/1.07          | ~ (r2_hidden @ X10 @ (k1_relat_1 @ X5))
% 0.90/1.07          | (r2_hidden @ (k1_funct_1 @ X5 @ X10) @ (k2_relat_1 @ X5)))),
% 0.90/1.07      inference('simplify', [status(thm)], ['32'])).
% 0.90/1.07  thf('34', plain,
% 0.90/1.07      (![X0 : $i]:
% 0.90/1.07         (((X0) = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.90/1.07          | ~ (v1_funct_1 @ X0)
% 0.90/1.07          | ~ (v1_relat_1 @ X0)
% 0.90/1.07          | (r2_hidden @ 
% 0.90/1.07             (k1_funct_1 @ X0 @ (sk_C_3 @ X0 @ (k1_relat_1 @ X0))) @ 
% 0.90/1.07             (k2_relat_1 @ X0))
% 0.90/1.07          | ~ (v1_funct_1 @ X0)
% 0.90/1.07          | ~ (v1_relat_1 @ X0))),
% 0.90/1.07      inference('sup-', [status(thm)], ['31', '33'])).
% 0.90/1.07  thf('35', plain,
% 0.90/1.07      (![X0 : $i]:
% 0.90/1.07         ((r2_hidden @ (k1_funct_1 @ X0 @ (sk_C_3 @ X0 @ (k1_relat_1 @ X0))) @ 
% 0.90/1.07           (k2_relat_1 @ X0))
% 0.90/1.07          | ~ (v1_relat_1 @ X0)
% 0.90/1.07          | ~ (v1_funct_1 @ X0)
% 0.90/1.07          | ((X0) = (k6_relat_1 @ (k1_relat_1 @ X0))))),
% 0.90/1.07      inference('simplify', [status(thm)], ['34'])).
% 0.90/1.07  thf('36', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_4) @ sk_A)),
% 0.90/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.07  thf(d3_tarski, axiom,
% 0.90/1.07    (![A:$i,B:$i]:
% 0.90/1.07     ( ( r1_tarski @ A @ B ) <=>
% 0.90/1.07       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.90/1.07  thf('37', plain,
% 0.90/1.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.07         (~ (r2_hidden @ X0 @ X1)
% 0.90/1.07          | (r2_hidden @ X0 @ X2)
% 0.90/1.07          | ~ (r1_tarski @ X1 @ X2))),
% 0.90/1.07      inference('cnf', [status(esa)], [d3_tarski])).
% 0.90/1.07  thf('38', plain,
% 0.90/1.07      (![X0 : $i]:
% 0.90/1.07         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_4)))),
% 0.90/1.07      inference('sup-', [status(thm)], ['36', '37'])).
% 0.90/1.07  thf('39', plain,
% 0.90/1.07      ((((sk_C_4) = (k6_relat_1 @ (k1_relat_1 @ sk_C_4)))
% 0.90/1.07        | ~ (v1_funct_1 @ sk_C_4)
% 0.90/1.07        | ~ (v1_relat_1 @ sk_C_4)
% 0.90/1.07        | (r2_hidden @ 
% 0.90/1.07           (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ (k1_relat_1 @ sk_C_4))) @ 
% 0.90/1.07           sk_A))),
% 0.90/1.07      inference('sup-', [status(thm)], ['35', '38'])).
% 0.90/1.07  thf('40', plain, (((k1_relat_1 @ sk_C_4) = (sk_A))),
% 0.90/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.07  thf('41', plain, ((v1_funct_1 @ sk_C_4)),
% 0.90/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.07  thf('42', plain, ((v1_relat_1 @ sk_C_4)),
% 0.90/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.07  thf('43', plain, (((k1_relat_1 @ sk_C_4) = (sk_A))),
% 0.90/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.07  thf('44', plain,
% 0.90/1.07      ((((sk_C_4) = (k6_relat_1 @ sk_A))
% 0.90/1.07        | (r2_hidden @ (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ sk_A))),
% 0.90/1.07      inference('demod', [status(thm)], ['39', '40', '41', '42', '43'])).
% 0.90/1.07  thf('45', plain, (((sk_C_4) != (k6_relat_1 @ sk_A))),
% 0.90/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.07  thf('46', plain,
% 0.90/1.07      ((r2_hidden @ (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ sk_A)),
% 0.90/1.07      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.90/1.07  thf('47', plain,
% 0.90/1.07      (![X0 : $i]:
% 0.90/1.07         (((k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 0.90/1.07            != (k1_funct_1 @ sk_B_1 @ X0))
% 0.90/1.07          | ~ (r2_hidden @ X0 @ sk_A)
% 0.90/1.07          | ((k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A)) = (X0)))),
% 0.90/1.07      inference('demod', [status(thm)], ['30', '46'])).
% 0.90/1.07  thf('48', plain,
% 0.90/1.07      ((((k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 0.90/1.07          = (sk_C_3 @ sk_C_4 @ sk_A))
% 0.90/1.07        | ~ (r2_hidden @ (sk_C_3 @ sk_C_4 @ sk_A) @ sk_A))),
% 0.90/1.07      inference('eq_res', [status(thm)], ['47'])).
% 0.90/1.07  thf('49', plain, ((r2_hidden @ (sk_C_3 @ sk_C_4 @ sk_A) @ sk_A)),
% 0.90/1.07      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.90/1.07  thf('50', plain,
% 0.90/1.07      (((k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 0.90/1.07         = (sk_C_3 @ sk_C_4 @ sk_A))),
% 0.90/1.07      inference('demod', [status(thm)], ['48', '49'])).
% 0.90/1.07  thf('51', plain, (((k1_relat_1 @ sk_C_4) = (sk_A))),
% 0.90/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.07  thf('52', plain,
% 0.90/1.07      (![X17 : $i, X18 : $i]:
% 0.90/1.07         (((k1_relat_1 @ X18) != (X17))
% 0.90/1.07          | ((k1_funct_1 @ X18 @ (sk_C_3 @ X18 @ X17)) != (sk_C_3 @ X18 @ X17))
% 0.90/1.07          | ((X18) = (k6_relat_1 @ X17))
% 0.90/1.07          | ~ (v1_funct_1 @ X18)
% 0.90/1.07          | ~ (v1_relat_1 @ X18))),
% 0.90/1.07      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.90/1.07  thf('53', plain,
% 0.90/1.07      (![X18 : $i]:
% 0.90/1.07         (~ (v1_relat_1 @ X18)
% 0.90/1.07          | ~ (v1_funct_1 @ X18)
% 0.90/1.07          | ((X18) = (k6_relat_1 @ (k1_relat_1 @ X18)))
% 0.90/1.07          | ((k1_funct_1 @ X18 @ (sk_C_3 @ X18 @ (k1_relat_1 @ X18)))
% 0.90/1.07              != (sk_C_3 @ X18 @ (k1_relat_1 @ X18))))),
% 0.90/1.07      inference('simplify', [status(thm)], ['52'])).
% 0.90/1.07  thf('54', plain,
% 0.90/1.07      ((((k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 0.90/1.07          != (sk_C_3 @ sk_C_4 @ (k1_relat_1 @ sk_C_4)))
% 0.90/1.07        | ((sk_C_4) = (k6_relat_1 @ (k1_relat_1 @ sk_C_4)))
% 0.90/1.07        | ~ (v1_funct_1 @ sk_C_4)
% 0.90/1.07        | ~ (v1_relat_1 @ sk_C_4))),
% 0.90/1.07      inference('sup-', [status(thm)], ['51', '53'])).
% 0.90/1.07  thf('55', plain, (((k1_relat_1 @ sk_C_4) = (sk_A))),
% 0.90/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.07  thf('56', plain, (((k1_relat_1 @ sk_C_4) = (sk_A))),
% 0.90/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.07  thf('57', plain, ((v1_funct_1 @ sk_C_4)),
% 0.90/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.07  thf('58', plain, ((v1_relat_1 @ sk_C_4)),
% 0.90/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.07  thf('59', plain,
% 0.90/1.07      ((((k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 0.90/1.07          != (sk_C_3 @ sk_C_4 @ sk_A))
% 0.90/1.07        | ((sk_C_4) = (k6_relat_1 @ sk_A)))),
% 0.90/1.07      inference('demod', [status(thm)], ['54', '55', '56', '57', '58'])).
% 0.90/1.07  thf('60', plain, (((sk_C_4) != (k6_relat_1 @ sk_A))),
% 0.90/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.07  thf('61', plain,
% 0.90/1.07      (((k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 0.90/1.07         != (sk_C_3 @ sk_C_4 @ sk_A))),
% 0.90/1.07      inference('simplify_reflect-', [status(thm)], ['59', '60'])).
% 0.90/1.07  thf('62', plain, ($false),
% 0.90/1.07      inference('simplify_reflect-', [status(thm)], ['50', '61'])).
% 0.90/1.07  
% 0.90/1.07  % SZS output end Refutation
% 0.90/1.07  
% 0.90/1.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
