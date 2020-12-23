%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3bSMgqtQzR

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:14 EST 2020

% Result     : Theorem 2.13s
% Output     : Refutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :  224 (1184 expanded)
%              Number of leaves         :   23 ( 339 expanded)
%              Depth                    :   29
%              Number of atoms          : 2595 (23345 expanded)
%              Number of equality atoms :  192 (2636 expanded)
%              Maximal formula depth    :   17 (   7 average)

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

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_4_type,type,(
    sk_C_4: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

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
    ( ( k5_relat_1 @ sk_C_4 @ sk_B_1 )
    = sk_B_1 ),
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

thf('3',plain,(
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

thf('4',plain,(
    ! [X5: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X5 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X5 @ X10 ) @ ( k2_relat_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C_3 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C_3 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ( X7
       != ( k2_relat_1 @ X5 ) )
      | ( X8
        = ( k1_funct_1 @ X5 @ ( sk_D_1 @ X8 @ X5 ) ) )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('8',plain,(
    ! [X5: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k2_relat_1 @ X5 ) )
      | ( X8
        = ( k1_funct_1 @ X5 @ ( sk_D_1 @ X8 @ X5 ) ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ ( sk_C_3 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( k1_funct_1 @ X0 @ ( sk_C_3 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ X0 @ ( sk_C_3 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( k1_funct_1 @ X0 @ ( sk_C_3 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C_3 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('12',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ( X7
       != ( k2_relat_1 @ X5 ) )
      | ( r2_hidden @ ( sk_D_1 @ X8 @ X5 ) @ ( k1_relat_1 @ X5 ) )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('13',plain,(
    ! [X5: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k2_relat_1 @ X5 ) )
      | ( r2_hidden @ ( sk_D_1 @ X8 @ X5 ) @ ( k1_relat_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ X0 @ ( sk_C_3 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ X0 @ ( sk_C_3 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

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

thf('16',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X15 @ X14 ) @ X16 )
        = ( k1_funct_1 @ X14 @ ( k1_funct_1 @ X15 @ X16 ) ) )
      | ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_D_1 @ ( k1_funct_1 @ X0 @ ( sk_C_3 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ X0 ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( k1_funct_1 @ X0 @ ( sk_C_3 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_D_1 @ ( k1_funct_1 @ X0 @ ( sk_C_3 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ X0 ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( k1_funct_1 @ X0 @ ( sk_C_3 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_D_1 @ ( k1_funct_1 @ X0 @ ( sk_C_3 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ X0 ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ X0 @ ( sk_C_3 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_D_1 @ ( k1_funct_1 @ X0 @ ( sk_C_3 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ X0 ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ X0 @ ( sk_C_3 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ ( k1_relat_1 @ sk_C_4 ) ) ) @ sk_C_4 ) )
      = ( k1_funct_1 @ sk_B_1 @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ ( k1_relat_1 @ sk_C_4 ) ) ) ) )
    | ( sk_C_4
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_C_4 ) ) )
    | ~ ( v1_funct_1 @ sk_C_4 )
    | ~ ( v1_relat_1 @ sk_C_4 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['0','20'])).

thf('22',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ sk_C_4 ) )
      = ( k1_funct_1 @ sk_B_1 @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) ) )
    | ( sk_C_4
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','25','26','27','28'])).

thf('30',plain,(
    sk_C_4
 != ( k6_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ sk_C_4 ) )
    = ( k1_funct_1 @ sk_B_1 @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X18: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( X18
        = ( k6_relat_1 @ ( k1_relat_1 @ X18 ) ) )
      | ( r2_hidden @ ( sk_C_3 @ X18 @ ( k1_relat_1 @ X18 ) ) @ ( k1_relat_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('34',plain,
    ( ( r2_hidden @ ( sk_C_3 @ sk_C_4 @ sk_A ) @ ( k1_relat_1 @ sk_C_4 ) )
    | ( sk_C_4
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_C_4 ) ) )
    | ~ ( v1_funct_1 @ sk_C_4 )
    | ~ ( v1_relat_1 @ sk_C_4 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( r2_hidden @ ( sk_C_3 @ sk_C_4 @ sk_A ) @ sk_A )
    | ( sk_C_4
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35','36','37','38'])).

thf('40',plain,(
    sk_C_4
 != ( k6_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r2_hidden @ ( sk_C_3 @ sk_C_4 @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X5: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X5 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X5 @ X10 ) @ ( k2_relat_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_4 @ X0 ) @ ( k2_relat_1 @ sk_C_4 ) )
      | ~ ( v1_funct_1 @ sk_C_4 )
      | ~ ( v1_relat_1 @ sk_C_4 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_funct_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_4 @ X0 ) @ ( k2_relat_1 @ sk_C_4 ) ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ ( k2_relat_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['41','47'])).

thf('49',plain,(
    ! [X5: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k2_relat_1 @ X5 ) )
      | ( X8
        = ( k1_funct_1 @ X5 @ ( sk_D_1 @ X8 @ X5 ) ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('50',plain,
    ( ( ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
      = ( k1_funct_1 @ sk_C_4 @ ( sk_D_1 @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ sk_C_4 ) ) )
    | ~ ( v1_funct_1 @ sk_C_4 )
    | ~ ( v1_relat_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
    = ( k1_funct_1 @ sk_C_4 @ ( sk_D_1 @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ sk_C_4 ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ! [X18: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( X18
        = ( k6_relat_1 @ ( k1_relat_1 @ X18 ) ) )
      | ( r2_hidden @ ( sk_C_3 @ X18 @ ( k1_relat_1 @ X18 ) ) @ ( k1_relat_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

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

thf('55',plain,(
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

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_C_3 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X1 )
      | ( ( k1_funct_1 @ X0 @ ( sk_C_3 @ X0 @ ( k1_relat_1 @ X0 ) ) )
       != ( k1_funct_1 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ X0 @ ( sk_C_3 @ X0 @ ( k1_relat_1 @ X0 ) ) )
       != ( k1_funct_1 @ X0 @ X1 ) )
      | ( ( sk_C_3 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ ( k1_relat_1 @ sk_C_4 ) ) )
     != ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) )
    | ( sk_C_4
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_C_4 ) ) )
    | ~ ( v1_funct_1 @ sk_C_4 )
    | ~ ( v1_relat_1 @ sk_C_4 )
    | ( ( sk_C_3 @ sk_C_4 @ ( k1_relat_1 @ sk_C_4 ) )
      = ( sk_D_1 @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ sk_C_4 ) )
    | ~ ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ sk_C_4 ) @ ( k1_relat_1 @ sk_C_4 ) )
    | ~ ( v2_funct_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['53','57'])).

thf('59',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ ( k2_relat_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['41','47'])).

thf('66',plain,(
    ! [X5: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k2_relat_1 @ X5 ) )
      | ( r2_hidden @ ( sk_D_1 @ X8 @ X5 ) @ ( k1_relat_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('67',plain,
    ( ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ sk_C_4 ) @ ( k1_relat_1 @ sk_C_4 ) )
    | ~ ( v1_funct_1 @ sk_C_4 )
    | ~ ( v1_relat_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ sk_C_4 ) @ sk_A ),
    inference(demod,[status(thm)],['67','68','69','70'])).

thf('72',plain,
    ( ( ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
     != ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) )
    | ( sk_C_4
      = ( k6_relat_1 @ sk_A ) )
    | ( ( sk_C_3 @ sk_C_4 @ sk_A )
      = ( sk_D_1 @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ sk_C_4 ) )
    | ~ ( v2_funct_1 @ sk_C_4 ) ),
    inference(demod,[status(thm)],['58','59','60','61','62','63','64','71'])).

thf('73',plain,
    ( ~ ( v2_funct_1 @ sk_C_4 )
    | ( ( sk_C_3 @ sk_C_4 @ sk_A )
      = ( sk_D_1 @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ sk_C_4 ) )
    | ( sk_C_4
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    sk_C_4
 != ( k6_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ~ ( v2_funct_1 @ sk_C_4 )
    | ( ( sk_C_3 @ sk_C_4 @ sk_A )
      = ( sk_D_1 @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ sk_C_4 ) ) ),
    inference('simplify_reflect-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X11: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X11 ) @ ( k1_relat_1 @ X11 ) )
      | ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('78',plain,
    ( ( r2_hidden @ ( sk_C_2 @ sk_C_4 ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C_4 )
    | ~ ( v1_funct_1 @ sk_C_4 )
    | ( v2_funct_1 @ sk_C_4 ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( r2_hidden @ ( sk_C_2 @ sk_C_4 ) @ sk_A )
    | ( v2_funct_1 @ sk_C_4 ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,
    ( ( k5_relat_1 @ sk_C_4 @ sk_B_1 )
    = sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X11: $i] :
      ( ( r2_hidden @ ( sk_B @ X11 ) @ ( k1_relat_1 @ X11 ) )
      | ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('84',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X15 @ X14 ) @ X16 )
        = ( k1_funct_1 @ X14 @ ( k1_funct_1 @ X15 @ X16 ) ) )
      | ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('85',plain,(
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
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_B @ X0 ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) ) ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X11: $i] :
      ( ( ( k1_funct_1 @ X11 @ ( sk_B @ X11 ) )
        = ( k1_funct_1 @ X11 @ ( sk_C_2 @ X11 ) ) )
      | ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('88',plain,(
    ! [X11: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X11 ) @ ( k1_relat_1 @ X11 ) )
      | ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('89',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X15 @ X14 ) @ X16 )
        = ( k1_funct_1 @ X14 @ ( k1_funct_1 @ X15 @ X16 ) ) )
      | ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_C_2 @ X0 ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ X0 @ ( sk_C_2 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_C_2 @ X0 ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ X0 @ ( sk_C_2 @ X0 ) ) ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_C_2 @ X0 ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['87','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_C_2 @ X0 ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_C_2 @ X0 ) )
        = ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_B @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['86','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_C_2 @ X0 ) )
        = ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_2 @ sk_C_4 ) )
      = ( k1_funct_1 @ ( k5_relat_1 @ sk_C_4 @ sk_B_1 ) @ ( sk_B @ sk_C_4 ) ) )
    | ~ ( v1_relat_1 @ sk_C_4 )
    | ~ ( v1_funct_1 @ sk_C_4 )
    | ( v2_funct_1 @ sk_C_4 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['82','95'])).

thf('97',plain,
    ( ( k5_relat_1 @ sk_C_4 @ sk_B_1 )
    = sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_funct_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_2 @ sk_C_4 ) )
      = ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_C_4 ) ) )
    | ( v2_funct_1 @ sk_C_4 ) ),
    inference(demod,[status(thm)],['96','97','98','99','100','101'])).

thf('103',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
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

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['105','106','107','108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_C_4 ) )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ( v2_funct_1 @ sk_C_4 )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( sk_C_2 @ sk_C_4 )
        = X0 )
      | ~ ( r2_hidden @ ( sk_C_2 @ sk_C_4 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['102','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ sk_C_4 )
      | ( ( sk_C_2 @ sk_C_4 )
        = X0 )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( v2_funct_1 @ sk_C_4 )
      | ( ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_C_4 ) )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['81','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_C_4 ) )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( sk_C_2 @ sk_C_4 )
        = X0 )
      | ( v2_funct_1 @ sk_C_4 ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,
    ( ( v2_funct_1 @ sk_C_4 )
    | ( ( sk_C_2 @ sk_C_4 )
      = ( sk_B @ sk_C_4 ) )
    | ~ ( r2_hidden @ ( sk_B @ sk_C_4 ) @ sk_A ) ),
    inference(eq_res,[status(thm)],['113'])).

thf('115',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X11: $i] :
      ( ( r2_hidden @ ( sk_B @ X11 ) @ ( k1_relat_1 @ X11 ) )
      | ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('117',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_4 ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C_4 )
    | ~ ( v1_funct_1 @ sk_C_4 )
    | ( v2_funct_1 @ sk_C_4 ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v1_funct_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_4 ) @ sk_A )
    | ( v2_funct_1 @ sk_C_4 ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,
    ( ( ( sk_C_2 @ sk_C_4 )
      = ( sk_B @ sk_C_4 ) )
    | ( v2_funct_1 @ sk_C_4 ) ),
    inference(clc,[status(thm)],['114','120'])).

thf('122',plain,
    ( ~ ( v2_funct_1 @ sk_C_4 )
    | ( ( sk_C_3 @ sk_C_4 @ sk_A )
      = ( sk_D_1 @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ sk_C_4 ) ) ),
    inference('simplify_reflect-',[status(thm)],['73','74'])).

thf('123',plain,
    ( ( ( sk_C_2 @ sk_C_4 )
      = ( sk_B @ sk_C_4 ) )
    | ( ( sk_C_3 @ sk_C_4 @ sk_A )
      = ( sk_D_1 @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ sk_C_4 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ sk_C_4 ) )
    = ( k1_funct_1 @ sk_B_1 @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf('125',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
      = ( k1_funct_1 @ sk_B_1 @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) ) )
    | ( ( sk_C_2 @ sk_C_4 )
      = ( sk_B @ sk_C_4 ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    r2_hidden @ ( sk_C_3 @ sk_C_4 @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['39','40'])).

thf('127',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X5: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X5 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X5 @ X10 ) @ ( k2_relat_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B_1 @ X0 ) @ ( k2_relat_1 @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B_1 @ X0 ) @ ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['126','132'])).

thf('134',plain,(
    ! [X5: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k2_relat_1 @ X5 ) )
      | ( X8
        = ( k1_funct_1 @ X5 @ ( sk_D_1 @ X8 @ X5 ) ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('135',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
      = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['135','136','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['105','106','107','108','109'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ sk_B_1 ) @ sk_A )
      | ( X0
        = ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['126','132'])).

thf('142',plain,(
    ! [X5: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k2_relat_1 @ X5 ) )
      | ( r2_hidden @ ( sk_D_1 @ X8 @ X5 ) @ ( k1_relat_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('143',plain,
    ( ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['143','144','145','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) )
      | ( X0
        = ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['140','147'])).

thf('149',plain,
    ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['135','136','137'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['105','106','107','108','109'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ sk_B_1 )
        = X0 )
      | ~ ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['143','144','145','146'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ sk_B_1 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,
    ( ( ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ sk_B_1 )
      = ( sk_C_3 @ sk_C_4 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_C_3 @ sk_C_4 @ sk_A ) @ sk_A ) ),
    inference(eq_res,[status(thm)],['153'])).

thf('155',plain,(
    r2_hidden @ ( sk_C_3 @ sk_C_4 @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['39','40'])).

thf('156',plain,
    ( ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ sk_B_1 )
    = ( sk_C_3 @ sk_C_4 @ sk_A ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) )
      | ( X0
        = ( sk_C_3 @ sk_C_4 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['148','156'])).

thf('158',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
     != ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) )
    | ( ( sk_C_2 @ sk_C_4 )
      = ( sk_B @ sk_C_4 ) )
    | ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ sk_A )
    | ( ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
      = ( sk_C_3 @ sk_C_4 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['125','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C_3 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('160',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_4 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('161',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_4 ) ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,
    ( ( sk_C_4
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_C_4 ) ) )
    | ~ ( v1_funct_1 @ sk_C_4 )
    | ~ ( v1_relat_1 @ sk_C_4 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ ( k1_relat_1 @ sk_C_4 ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['159','162'])).

thf('164',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v1_funct_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( sk_C_4
      = ( k6_relat_1 @ sk_A ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['163','164','165','166','167'])).

thf('169',plain,(
    sk_C_4
 != ( k6_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['168','169'])).

thf('171',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
     != ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) )
    | ( ( sk_C_2 @ sk_C_4 )
      = ( sk_B @ sk_C_4 ) )
    | ( ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
      = ( sk_C_3 @ sk_C_4 @ sk_A ) ) ),
    inference(demod,[status(thm)],['158','170'])).

thf('172',plain,
    ( ( ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
      = ( sk_C_3 @ sk_C_4 @ sk_A ) )
    | ( ( sk_C_2 @ sk_C_4 )
      = ( sk_B @ sk_C_4 ) ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
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

thf('175',plain,(
    ! [X18: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( X18
        = ( k6_relat_1 @ ( k1_relat_1 @ X18 ) ) )
      | ( ( k1_funct_1 @ X18 @ ( sk_C_3 @ X18 @ ( k1_relat_1 @ X18 ) ) )
       != ( sk_C_3 @ X18 @ ( k1_relat_1 @ X18 ) ) ) ) ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,
    ( ( ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
     != ( sk_C_3 @ sk_C_4 @ ( k1_relat_1 @ sk_C_4 ) ) )
    | ( sk_C_4
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_C_4 ) ) )
    | ~ ( v1_funct_1 @ sk_C_4 )
    | ~ ( v1_relat_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['173','175'])).

thf('177',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    v1_funct_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ( ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
     != ( sk_C_3 @ sk_C_4 @ sk_A ) )
    | ( sk_C_4
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['176','177','178','179','180'])).

thf('182',plain,(
    sk_C_4
 != ( k6_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
 != ( sk_C_3 @ sk_C_4 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['181','182'])).

thf('184',plain,
    ( ( sk_C_2 @ sk_C_4 )
    = ( sk_B @ sk_C_4 ) ),
    inference('simplify_reflect-',[status(thm)],['172','183'])).

thf('185',plain,(
    ! [X11: $i] :
      ( ( ( sk_B @ X11 )
       != ( sk_C_2 @ X11 ) )
      | ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('186',plain,
    ( ( ( sk_B @ sk_C_4 )
     != ( sk_B @ sk_C_4 ) )
    | ~ ( v1_relat_1 @ sk_C_4 )
    | ~ ( v1_funct_1 @ sk_C_4 )
    | ( v2_funct_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    v1_funct_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,
    ( ( ( sk_B @ sk_C_4 )
     != ( sk_B @ sk_C_4 ) )
    | ( v2_funct_1 @ sk_C_4 ) ),
    inference(demod,[status(thm)],['186','187','188'])).

thf('190',plain,(
    v2_funct_1 @ sk_C_4 ),
    inference(simplify,[status(thm)],['189'])).

thf('191',plain,
    ( ( sk_C_3 @ sk_C_4 @ sk_A )
    = ( sk_D_1 @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ sk_C_4 ) ),
    inference(demod,[status(thm)],['75','190'])).

thf('192',plain,
    ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
    = ( k1_funct_1 @ sk_B_1 @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['31','191'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) )
      | ( X0
        = ( sk_C_3 @ sk_C_4 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['148','156'])).

thf('194',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
     != ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) )
    | ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ sk_A )
    | ( ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
      = ( sk_C_3 @ sk_C_4 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['168','169'])).

thf('196',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
     != ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) )
    | ( ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
      = ( sk_C_3 @ sk_C_4 @ sk_A ) ) ),
    inference(demod,[status(thm)],['194','195'])).

thf('197',plain,
    ( ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
    = ( sk_C_3 @ sk_C_4 @ sk_A ) ),
    inference(simplify,[status(thm)],['196'])).

thf('198',plain,(
    ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
 != ( sk_C_3 @ sk_C_4 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['181','182'])).

thf('199',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['197','198'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3bSMgqtQzR
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:46:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 2.13/2.32  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.13/2.32  % Solved by: fo/fo7.sh
% 2.13/2.32  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.13/2.32  % done 2403 iterations in 1.864s
% 2.13/2.32  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.13/2.32  % SZS output start Refutation
% 2.13/2.32  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.13/2.32  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.13/2.32  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.13/2.32  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.13/2.32  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.13/2.32  thf(sk_B_type, type, sk_B: $i > $i).
% 2.13/2.32  thf(sk_C_4_type, type, sk_C_4: $i).
% 2.13/2.32  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.13/2.32  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.13/2.32  thf(sk_C_2_type, type, sk_C_2: $i > $i).
% 2.13/2.32  thf(sk_A_type, type, sk_A: $i).
% 2.13/2.32  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.13/2.32  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.13/2.32  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 2.13/2.32  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 2.13/2.32  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 2.13/2.32  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.13/2.32  thf(t50_funct_1, conjecture,
% 2.13/2.32    (![A:$i,B:$i]:
% 2.13/2.32     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.13/2.32       ( ![C:$i]:
% 2.13/2.32         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 2.13/2.32           ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 2.13/2.32               ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 2.13/2.32               ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) & ( v2_funct_1 @ B ) & 
% 2.13/2.32               ( ( k5_relat_1 @ C @ B ) = ( B ) ) ) =>
% 2.13/2.32             ( ( C ) = ( k6_relat_1 @ A ) ) ) ) ) ))).
% 2.13/2.32  thf(zf_stmt_0, negated_conjecture,
% 2.13/2.32    (~( ![A:$i,B:$i]:
% 2.13/2.32        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.13/2.32          ( ![C:$i]:
% 2.13/2.32            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 2.13/2.32              ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 2.13/2.32                  ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 2.13/2.32                  ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) & 
% 2.13/2.32                  ( v2_funct_1 @ B ) & ( ( k5_relat_1 @ C @ B ) = ( B ) ) ) =>
% 2.13/2.32                ( ( C ) = ( k6_relat_1 @ A ) ) ) ) ) ) )),
% 2.13/2.32    inference('cnf.neg', [status(esa)], [t50_funct_1])).
% 2.13/2.32  thf('0', plain, (((k5_relat_1 @ sk_C_4 @ sk_B_1) = (sk_B_1))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf(t34_funct_1, axiom,
% 2.13/2.32    (![A:$i,B:$i]:
% 2.13/2.32     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.13/2.32       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 2.13/2.32         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 2.13/2.32           ( ![C:$i]:
% 2.13/2.32             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 2.13/2.32  thf('1', plain,
% 2.13/2.32      (![X17 : $i, X18 : $i]:
% 2.13/2.32         (((k1_relat_1 @ X18) != (X17))
% 2.13/2.32          | (r2_hidden @ (sk_C_3 @ X18 @ X17) @ X17)
% 2.13/2.32          | ((X18) = (k6_relat_1 @ X17))
% 2.13/2.32          | ~ (v1_funct_1 @ X18)
% 2.13/2.32          | ~ (v1_relat_1 @ X18))),
% 2.13/2.32      inference('cnf', [status(esa)], [t34_funct_1])).
% 2.13/2.32  thf('2', plain,
% 2.13/2.32      (![X18 : $i]:
% 2.13/2.32         (~ (v1_relat_1 @ X18)
% 2.13/2.32          | ~ (v1_funct_1 @ X18)
% 2.13/2.32          | ((X18) = (k6_relat_1 @ (k1_relat_1 @ X18)))
% 2.13/2.32          | (r2_hidden @ (sk_C_3 @ X18 @ (k1_relat_1 @ X18)) @ 
% 2.13/2.32             (k1_relat_1 @ X18)))),
% 2.13/2.32      inference('simplify', [status(thm)], ['1'])).
% 2.13/2.32  thf(d5_funct_1, axiom,
% 2.13/2.32    (![A:$i]:
% 2.13/2.32     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.13/2.32       ( ![B:$i]:
% 2.13/2.32         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 2.13/2.32           ( ![C:$i]:
% 2.13/2.32             ( ( r2_hidden @ C @ B ) <=>
% 2.13/2.32               ( ?[D:$i]:
% 2.13/2.32                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 2.13/2.32                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 2.13/2.32  thf('3', plain,
% 2.13/2.32      (![X5 : $i, X7 : $i, X9 : $i, X10 : $i]:
% 2.13/2.32         (((X7) != (k2_relat_1 @ X5))
% 2.13/2.32          | (r2_hidden @ X9 @ X7)
% 2.13/2.32          | ~ (r2_hidden @ X10 @ (k1_relat_1 @ X5))
% 2.13/2.32          | ((X9) != (k1_funct_1 @ X5 @ X10))
% 2.13/2.32          | ~ (v1_funct_1 @ X5)
% 2.13/2.32          | ~ (v1_relat_1 @ X5))),
% 2.13/2.32      inference('cnf', [status(esa)], [d5_funct_1])).
% 2.13/2.32  thf('4', plain,
% 2.13/2.32      (![X5 : $i, X10 : $i]:
% 2.13/2.32         (~ (v1_relat_1 @ X5)
% 2.13/2.32          | ~ (v1_funct_1 @ X5)
% 2.13/2.32          | ~ (r2_hidden @ X10 @ (k1_relat_1 @ X5))
% 2.13/2.32          | (r2_hidden @ (k1_funct_1 @ X5 @ X10) @ (k2_relat_1 @ X5)))),
% 2.13/2.32      inference('simplify', [status(thm)], ['3'])).
% 2.13/2.32  thf('5', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         (((X0) = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 2.13/2.32          | ~ (v1_funct_1 @ X0)
% 2.13/2.32          | ~ (v1_relat_1 @ X0)
% 2.13/2.32          | (r2_hidden @ 
% 2.13/2.32             (k1_funct_1 @ X0 @ (sk_C_3 @ X0 @ (k1_relat_1 @ X0))) @ 
% 2.13/2.32             (k2_relat_1 @ X0))
% 2.13/2.32          | ~ (v1_funct_1 @ X0)
% 2.13/2.32          | ~ (v1_relat_1 @ X0))),
% 2.13/2.32      inference('sup-', [status(thm)], ['2', '4'])).
% 2.13/2.32  thf('6', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         ((r2_hidden @ (k1_funct_1 @ X0 @ (sk_C_3 @ X0 @ (k1_relat_1 @ X0))) @ 
% 2.13/2.32           (k2_relat_1 @ X0))
% 2.13/2.32          | ~ (v1_relat_1 @ X0)
% 2.13/2.32          | ~ (v1_funct_1 @ X0)
% 2.13/2.32          | ((X0) = (k6_relat_1 @ (k1_relat_1 @ X0))))),
% 2.13/2.32      inference('simplify', [status(thm)], ['5'])).
% 2.13/2.32  thf('7', plain,
% 2.13/2.32      (![X5 : $i, X7 : $i, X8 : $i]:
% 2.13/2.32         (((X7) != (k2_relat_1 @ X5))
% 2.13/2.32          | ((X8) = (k1_funct_1 @ X5 @ (sk_D_1 @ X8 @ X5)))
% 2.13/2.32          | ~ (r2_hidden @ X8 @ X7)
% 2.13/2.32          | ~ (v1_funct_1 @ X5)
% 2.13/2.32          | ~ (v1_relat_1 @ X5))),
% 2.13/2.32      inference('cnf', [status(esa)], [d5_funct_1])).
% 2.13/2.32  thf('8', plain,
% 2.13/2.32      (![X5 : $i, X8 : $i]:
% 2.13/2.32         (~ (v1_relat_1 @ X5)
% 2.13/2.32          | ~ (v1_funct_1 @ X5)
% 2.13/2.32          | ~ (r2_hidden @ X8 @ (k2_relat_1 @ X5))
% 2.13/2.32          | ((X8) = (k1_funct_1 @ X5 @ (sk_D_1 @ X8 @ X5))))),
% 2.13/2.32      inference('simplify', [status(thm)], ['7'])).
% 2.13/2.32  thf('9', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         (((X0) = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 2.13/2.32          | ~ (v1_funct_1 @ X0)
% 2.13/2.32          | ~ (v1_relat_1 @ X0)
% 2.13/2.32          | ((k1_funct_1 @ X0 @ (sk_C_3 @ X0 @ (k1_relat_1 @ X0)))
% 2.13/2.32              = (k1_funct_1 @ X0 @ 
% 2.13/2.32                 (sk_D_1 @ 
% 2.13/2.32                  (k1_funct_1 @ X0 @ (sk_C_3 @ X0 @ (k1_relat_1 @ X0))) @ X0)))
% 2.13/2.32          | ~ (v1_funct_1 @ X0)
% 2.13/2.32          | ~ (v1_relat_1 @ X0))),
% 2.13/2.32      inference('sup-', [status(thm)], ['6', '8'])).
% 2.13/2.32  thf('10', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         (((k1_funct_1 @ X0 @ (sk_C_3 @ X0 @ (k1_relat_1 @ X0)))
% 2.13/2.32            = (k1_funct_1 @ X0 @ 
% 2.13/2.32               (sk_D_1 @ 
% 2.13/2.32                (k1_funct_1 @ X0 @ (sk_C_3 @ X0 @ (k1_relat_1 @ X0))) @ X0)))
% 2.13/2.32          | ~ (v1_relat_1 @ X0)
% 2.13/2.32          | ~ (v1_funct_1 @ X0)
% 2.13/2.32          | ((X0) = (k6_relat_1 @ (k1_relat_1 @ X0))))),
% 2.13/2.32      inference('simplify', [status(thm)], ['9'])).
% 2.13/2.32  thf('11', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         ((r2_hidden @ (k1_funct_1 @ X0 @ (sk_C_3 @ X0 @ (k1_relat_1 @ X0))) @ 
% 2.13/2.32           (k2_relat_1 @ X0))
% 2.13/2.32          | ~ (v1_relat_1 @ X0)
% 2.13/2.32          | ~ (v1_funct_1 @ X0)
% 2.13/2.32          | ((X0) = (k6_relat_1 @ (k1_relat_1 @ X0))))),
% 2.13/2.32      inference('simplify', [status(thm)], ['5'])).
% 2.13/2.32  thf('12', plain,
% 2.13/2.32      (![X5 : $i, X7 : $i, X8 : $i]:
% 2.13/2.32         (((X7) != (k2_relat_1 @ X5))
% 2.13/2.32          | (r2_hidden @ (sk_D_1 @ X8 @ X5) @ (k1_relat_1 @ X5))
% 2.13/2.32          | ~ (r2_hidden @ X8 @ X7)
% 2.13/2.32          | ~ (v1_funct_1 @ X5)
% 2.13/2.32          | ~ (v1_relat_1 @ X5))),
% 2.13/2.32      inference('cnf', [status(esa)], [d5_funct_1])).
% 2.13/2.32  thf('13', plain,
% 2.13/2.32      (![X5 : $i, X8 : $i]:
% 2.13/2.32         (~ (v1_relat_1 @ X5)
% 2.13/2.32          | ~ (v1_funct_1 @ X5)
% 2.13/2.32          | ~ (r2_hidden @ X8 @ (k2_relat_1 @ X5))
% 2.13/2.32          | (r2_hidden @ (sk_D_1 @ X8 @ X5) @ (k1_relat_1 @ X5)))),
% 2.13/2.32      inference('simplify', [status(thm)], ['12'])).
% 2.13/2.32  thf('14', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         (((X0) = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 2.13/2.32          | ~ (v1_funct_1 @ X0)
% 2.13/2.32          | ~ (v1_relat_1 @ X0)
% 2.13/2.32          | (r2_hidden @ 
% 2.13/2.32             (sk_D_1 @ (k1_funct_1 @ X0 @ (sk_C_3 @ X0 @ (k1_relat_1 @ X0))) @ 
% 2.13/2.32              X0) @ 
% 2.13/2.32             (k1_relat_1 @ X0))
% 2.13/2.32          | ~ (v1_funct_1 @ X0)
% 2.13/2.32          | ~ (v1_relat_1 @ X0))),
% 2.13/2.32      inference('sup-', [status(thm)], ['11', '13'])).
% 2.13/2.32  thf('15', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         ((r2_hidden @ 
% 2.13/2.32           (sk_D_1 @ (k1_funct_1 @ X0 @ (sk_C_3 @ X0 @ (k1_relat_1 @ X0))) @ X0) @ 
% 2.13/2.32           (k1_relat_1 @ X0))
% 2.13/2.32          | ~ (v1_relat_1 @ X0)
% 2.13/2.32          | ~ (v1_funct_1 @ X0)
% 2.13/2.32          | ((X0) = (k6_relat_1 @ (k1_relat_1 @ X0))))),
% 2.13/2.32      inference('simplify', [status(thm)], ['14'])).
% 2.13/2.32  thf(t23_funct_1, axiom,
% 2.13/2.32    (![A:$i,B:$i]:
% 2.13/2.32     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.13/2.32       ( ![C:$i]:
% 2.13/2.32         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 2.13/2.32           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 2.13/2.32             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 2.13/2.32               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 2.13/2.32  thf('16', plain,
% 2.13/2.32      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.13/2.32         (~ (v1_relat_1 @ X14)
% 2.13/2.32          | ~ (v1_funct_1 @ X14)
% 2.13/2.32          | ((k1_funct_1 @ (k5_relat_1 @ X15 @ X14) @ X16)
% 2.13/2.32              = (k1_funct_1 @ X14 @ (k1_funct_1 @ X15 @ X16)))
% 2.13/2.32          | ~ (r2_hidden @ X16 @ (k1_relat_1 @ X15))
% 2.13/2.32          | ~ (v1_funct_1 @ X15)
% 2.13/2.32          | ~ (v1_relat_1 @ X15))),
% 2.13/2.32      inference('cnf', [status(esa)], [t23_funct_1])).
% 2.13/2.32  thf('17', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i]:
% 2.13/2.32         (((X0) = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 2.13/2.32          | ~ (v1_funct_1 @ X0)
% 2.13/2.32          | ~ (v1_relat_1 @ X0)
% 2.13/2.32          | ~ (v1_relat_1 @ X0)
% 2.13/2.32          | ~ (v1_funct_1 @ X0)
% 2.13/2.32          | ((k1_funct_1 @ (k5_relat_1 @ X0 @ X1) @ 
% 2.13/2.32              (sk_D_1 @ 
% 2.13/2.32               (k1_funct_1 @ X0 @ (sk_C_3 @ X0 @ (k1_relat_1 @ X0))) @ X0))
% 2.13/2.32              = (k1_funct_1 @ X1 @ 
% 2.13/2.32                 (k1_funct_1 @ X0 @ 
% 2.13/2.32                  (sk_D_1 @ 
% 2.13/2.32                   (k1_funct_1 @ X0 @ (sk_C_3 @ X0 @ (k1_relat_1 @ X0))) @ X0))))
% 2.13/2.32          | ~ (v1_funct_1 @ X1)
% 2.13/2.32          | ~ (v1_relat_1 @ X1))),
% 2.13/2.32      inference('sup-', [status(thm)], ['15', '16'])).
% 2.13/2.32  thf('18', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i]:
% 2.13/2.32         (~ (v1_relat_1 @ X1)
% 2.13/2.32          | ~ (v1_funct_1 @ X1)
% 2.13/2.32          | ((k1_funct_1 @ (k5_relat_1 @ X0 @ X1) @ 
% 2.13/2.32              (sk_D_1 @ 
% 2.13/2.32               (k1_funct_1 @ X0 @ (sk_C_3 @ X0 @ (k1_relat_1 @ X0))) @ X0))
% 2.13/2.32              = (k1_funct_1 @ X1 @ 
% 2.13/2.32                 (k1_funct_1 @ X0 @ 
% 2.13/2.32                  (sk_D_1 @ 
% 2.13/2.32                   (k1_funct_1 @ X0 @ (sk_C_3 @ X0 @ (k1_relat_1 @ X0))) @ X0))))
% 2.13/2.32          | ~ (v1_relat_1 @ X0)
% 2.13/2.32          | ~ (v1_funct_1 @ X0)
% 2.13/2.32          | ((X0) = (k6_relat_1 @ (k1_relat_1 @ X0))))),
% 2.13/2.32      inference('simplify', [status(thm)], ['17'])).
% 2.13/2.32  thf('19', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i]:
% 2.13/2.32         (((k1_funct_1 @ (k5_relat_1 @ X0 @ X1) @ 
% 2.13/2.32            (sk_D_1 @ (k1_funct_1 @ X0 @ (sk_C_3 @ X0 @ (k1_relat_1 @ X0))) @ 
% 2.13/2.32             X0))
% 2.13/2.32            = (k1_funct_1 @ X1 @ 
% 2.13/2.32               (k1_funct_1 @ X0 @ (sk_C_3 @ X0 @ (k1_relat_1 @ X0)))))
% 2.13/2.32          | ((X0) = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 2.13/2.32          | ~ (v1_funct_1 @ X0)
% 2.13/2.32          | ~ (v1_relat_1 @ X0)
% 2.13/2.32          | ((X0) = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 2.13/2.32          | ~ (v1_funct_1 @ X0)
% 2.13/2.32          | ~ (v1_relat_1 @ X0)
% 2.13/2.32          | ~ (v1_funct_1 @ X1)
% 2.13/2.32          | ~ (v1_relat_1 @ X1))),
% 2.13/2.32      inference('sup+', [status(thm)], ['10', '18'])).
% 2.13/2.32  thf('20', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i]:
% 2.13/2.32         (~ (v1_relat_1 @ X1)
% 2.13/2.32          | ~ (v1_funct_1 @ X1)
% 2.13/2.32          | ~ (v1_relat_1 @ X0)
% 2.13/2.32          | ~ (v1_funct_1 @ X0)
% 2.13/2.32          | ((X0) = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 2.13/2.32          | ((k1_funct_1 @ (k5_relat_1 @ X0 @ X1) @ 
% 2.13/2.32              (sk_D_1 @ 
% 2.13/2.32               (k1_funct_1 @ X0 @ (sk_C_3 @ X0 @ (k1_relat_1 @ X0))) @ X0))
% 2.13/2.32              = (k1_funct_1 @ X1 @ 
% 2.13/2.32                 (k1_funct_1 @ X0 @ (sk_C_3 @ X0 @ (k1_relat_1 @ X0))))))),
% 2.13/2.32      inference('simplify', [status(thm)], ['19'])).
% 2.13/2.32  thf('21', plain,
% 2.13/2.32      ((((k1_funct_1 @ sk_B_1 @ 
% 2.13/2.32          (sk_D_1 @ 
% 2.13/2.32           (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ (k1_relat_1 @ sk_C_4))) @ 
% 2.13/2.32           sk_C_4))
% 2.13/2.32          = (k1_funct_1 @ sk_B_1 @ 
% 2.13/2.32             (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ (k1_relat_1 @ sk_C_4)))))
% 2.13/2.32        | ((sk_C_4) = (k6_relat_1 @ (k1_relat_1 @ sk_C_4)))
% 2.13/2.32        | ~ (v1_funct_1 @ sk_C_4)
% 2.13/2.32        | ~ (v1_relat_1 @ sk_C_4)
% 2.13/2.32        | ~ (v1_funct_1 @ sk_B_1)
% 2.13/2.32        | ~ (v1_relat_1 @ sk_B_1))),
% 2.13/2.32      inference('sup+', [status(thm)], ['0', '20'])).
% 2.13/2.32  thf('22', plain, (((k1_relat_1 @ sk_C_4) = (sk_A))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('23', plain, (((k1_relat_1 @ sk_C_4) = (sk_A))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('24', plain, (((k1_relat_1 @ sk_C_4) = (sk_A))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('25', plain, ((v1_funct_1 @ sk_C_4)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('26', plain, ((v1_relat_1 @ sk_C_4)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('27', plain, ((v1_funct_1 @ sk_B_1)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('28', plain, ((v1_relat_1 @ sk_B_1)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('29', plain,
% 2.13/2.32      ((((k1_funct_1 @ sk_B_1 @ 
% 2.13/2.32          (sk_D_1 @ (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ sk_C_4))
% 2.13/2.32          = (k1_funct_1 @ sk_B_1 @ 
% 2.13/2.32             (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A))))
% 2.13/2.32        | ((sk_C_4) = (k6_relat_1 @ sk_A)))),
% 2.13/2.32      inference('demod', [status(thm)],
% 2.13/2.32                ['21', '22', '23', '24', '25', '26', '27', '28'])).
% 2.13/2.32  thf('30', plain, (((sk_C_4) != (k6_relat_1 @ sk_A))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('31', plain,
% 2.13/2.32      (((k1_funct_1 @ sk_B_1 @ 
% 2.13/2.32         (sk_D_1 @ (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ sk_C_4))
% 2.13/2.32         = (k1_funct_1 @ sk_B_1 @ 
% 2.13/2.32            (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A))))),
% 2.13/2.32      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 2.13/2.32  thf('32', plain, (((k1_relat_1 @ sk_C_4) = (sk_A))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('33', plain,
% 2.13/2.32      (![X18 : $i]:
% 2.13/2.32         (~ (v1_relat_1 @ X18)
% 2.13/2.32          | ~ (v1_funct_1 @ X18)
% 2.13/2.32          | ((X18) = (k6_relat_1 @ (k1_relat_1 @ X18)))
% 2.13/2.32          | (r2_hidden @ (sk_C_3 @ X18 @ (k1_relat_1 @ X18)) @ 
% 2.13/2.32             (k1_relat_1 @ X18)))),
% 2.13/2.32      inference('simplify', [status(thm)], ['1'])).
% 2.13/2.32  thf('34', plain,
% 2.13/2.32      (((r2_hidden @ (sk_C_3 @ sk_C_4 @ sk_A) @ (k1_relat_1 @ sk_C_4))
% 2.13/2.32        | ((sk_C_4) = (k6_relat_1 @ (k1_relat_1 @ sk_C_4)))
% 2.13/2.32        | ~ (v1_funct_1 @ sk_C_4)
% 2.13/2.32        | ~ (v1_relat_1 @ sk_C_4))),
% 2.13/2.32      inference('sup+', [status(thm)], ['32', '33'])).
% 2.13/2.32  thf('35', plain, (((k1_relat_1 @ sk_C_4) = (sk_A))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('36', plain, (((k1_relat_1 @ sk_C_4) = (sk_A))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('37', plain, ((v1_funct_1 @ sk_C_4)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('38', plain, ((v1_relat_1 @ sk_C_4)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('39', plain,
% 2.13/2.32      (((r2_hidden @ (sk_C_3 @ sk_C_4 @ sk_A) @ sk_A)
% 2.13/2.32        | ((sk_C_4) = (k6_relat_1 @ sk_A)))),
% 2.13/2.32      inference('demod', [status(thm)], ['34', '35', '36', '37', '38'])).
% 2.13/2.32  thf('40', plain, (((sk_C_4) != (k6_relat_1 @ sk_A))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('41', plain, ((r2_hidden @ (sk_C_3 @ sk_C_4 @ sk_A) @ sk_A)),
% 2.13/2.32      inference('simplify_reflect-', [status(thm)], ['39', '40'])).
% 2.13/2.32  thf('42', plain, (((k1_relat_1 @ sk_C_4) = (sk_A))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('43', plain,
% 2.13/2.32      (![X5 : $i, X10 : $i]:
% 2.13/2.32         (~ (v1_relat_1 @ X5)
% 2.13/2.32          | ~ (v1_funct_1 @ X5)
% 2.13/2.32          | ~ (r2_hidden @ X10 @ (k1_relat_1 @ X5))
% 2.13/2.32          | (r2_hidden @ (k1_funct_1 @ X5 @ X10) @ (k2_relat_1 @ X5)))),
% 2.13/2.32      inference('simplify', [status(thm)], ['3'])).
% 2.13/2.32  thf('44', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         (~ (r2_hidden @ X0 @ sk_A)
% 2.13/2.32          | (r2_hidden @ (k1_funct_1 @ sk_C_4 @ X0) @ (k2_relat_1 @ sk_C_4))
% 2.13/2.32          | ~ (v1_funct_1 @ sk_C_4)
% 2.13/2.32          | ~ (v1_relat_1 @ sk_C_4))),
% 2.13/2.32      inference('sup-', [status(thm)], ['42', '43'])).
% 2.13/2.32  thf('45', plain, ((v1_funct_1 @ sk_C_4)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('46', plain, ((v1_relat_1 @ sk_C_4)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('47', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         (~ (r2_hidden @ X0 @ sk_A)
% 2.13/2.32          | (r2_hidden @ (k1_funct_1 @ sk_C_4 @ X0) @ (k2_relat_1 @ sk_C_4)))),
% 2.13/2.32      inference('demod', [status(thm)], ['44', '45', '46'])).
% 2.13/2.32  thf('48', plain,
% 2.13/2.32      ((r2_hidden @ (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ 
% 2.13/2.32        (k2_relat_1 @ sk_C_4))),
% 2.13/2.32      inference('sup-', [status(thm)], ['41', '47'])).
% 2.13/2.32  thf('49', plain,
% 2.13/2.32      (![X5 : $i, X8 : $i]:
% 2.13/2.32         (~ (v1_relat_1 @ X5)
% 2.13/2.32          | ~ (v1_funct_1 @ X5)
% 2.13/2.32          | ~ (r2_hidden @ X8 @ (k2_relat_1 @ X5))
% 2.13/2.32          | ((X8) = (k1_funct_1 @ X5 @ (sk_D_1 @ X8 @ X5))))),
% 2.13/2.32      inference('simplify', [status(thm)], ['7'])).
% 2.13/2.32  thf('50', plain,
% 2.13/2.32      ((((k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 2.13/2.32          = (k1_funct_1 @ sk_C_4 @ 
% 2.13/2.32             (sk_D_1 @ (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ 
% 2.13/2.32              sk_C_4)))
% 2.13/2.32        | ~ (v1_funct_1 @ sk_C_4)
% 2.13/2.32        | ~ (v1_relat_1 @ sk_C_4))),
% 2.13/2.32      inference('sup-', [status(thm)], ['48', '49'])).
% 2.13/2.32  thf('51', plain, ((v1_funct_1 @ sk_C_4)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('52', plain, ((v1_relat_1 @ sk_C_4)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('53', plain,
% 2.13/2.32      (((k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 2.13/2.32         = (k1_funct_1 @ sk_C_4 @ 
% 2.13/2.32            (sk_D_1 @ (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ sk_C_4)))),
% 2.13/2.32      inference('demod', [status(thm)], ['50', '51', '52'])).
% 2.13/2.32  thf('54', plain,
% 2.13/2.32      (![X18 : $i]:
% 2.13/2.32         (~ (v1_relat_1 @ X18)
% 2.13/2.32          | ~ (v1_funct_1 @ X18)
% 2.13/2.32          | ((X18) = (k6_relat_1 @ (k1_relat_1 @ X18)))
% 2.13/2.32          | (r2_hidden @ (sk_C_3 @ X18 @ (k1_relat_1 @ X18)) @ 
% 2.13/2.32             (k1_relat_1 @ X18)))),
% 2.13/2.32      inference('simplify', [status(thm)], ['1'])).
% 2.13/2.32  thf(d8_funct_1, axiom,
% 2.13/2.32    (![A:$i]:
% 2.13/2.32     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.13/2.32       ( ( v2_funct_1 @ A ) <=>
% 2.13/2.32         ( ![B:$i,C:$i]:
% 2.13/2.32           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 2.13/2.32               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 2.13/2.32               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 2.13/2.32             ( ( B ) = ( C ) ) ) ) ) ))).
% 2.13/2.32  thf('55', plain,
% 2.13/2.32      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.13/2.32         (~ (v2_funct_1 @ X11)
% 2.13/2.32          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ X11))
% 2.13/2.32          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X11))
% 2.13/2.32          | ((k1_funct_1 @ X11 @ X12) != (k1_funct_1 @ X11 @ X13))
% 2.13/2.32          | ((X12) = (X13))
% 2.13/2.32          | ~ (v1_funct_1 @ X11)
% 2.13/2.32          | ~ (v1_relat_1 @ X11))),
% 2.13/2.32      inference('cnf', [status(esa)], [d8_funct_1])).
% 2.13/2.32  thf('56', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i]:
% 2.13/2.32         (((X0) = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 2.13/2.32          | ~ (v1_funct_1 @ X0)
% 2.13/2.32          | ~ (v1_relat_1 @ X0)
% 2.13/2.32          | ~ (v1_relat_1 @ X0)
% 2.13/2.32          | ~ (v1_funct_1 @ X0)
% 2.13/2.32          | ((sk_C_3 @ X0 @ (k1_relat_1 @ X0)) = (X1))
% 2.13/2.32          | ((k1_funct_1 @ X0 @ (sk_C_3 @ X0 @ (k1_relat_1 @ X0)))
% 2.13/2.32              != (k1_funct_1 @ X0 @ X1))
% 2.13/2.32          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 2.13/2.32          | ~ (v2_funct_1 @ X0))),
% 2.13/2.32      inference('sup-', [status(thm)], ['54', '55'])).
% 2.13/2.32  thf('57', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i]:
% 2.13/2.32         (~ (v2_funct_1 @ X0)
% 2.13/2.32          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 2.13/2.32          | ((k1_funct_1 @ X0 @ (sk_C_3 @ X0 @ (k1_relat_1 @ X0)))
% 2.13/2.32              != (k1_funct_1 @ X0 @ X1))
% 2.13/2.32          | ((sk_C_3 @ X0 @ (k1_relat_1 @ X0)) = (X1))
% 2.13/2.32          | ~ (v1_relat_1 @ X0)
% 2.13/2.32          | ~ (v1_funct_1 @ X0)
% 2.13/2.32          | ((X0) = (k6_relat_1 @ (k1_relat_1 @ X0))))),
% 2.13/2.32      inference('simplify', [status(thm)], ['56'])).
% 2.13/2.32  thf('58', plain,
% 2.13/2.32      ((((k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ (k1_relat_1 @ sk_C_4)))
% 2.13/2.32          != (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A)))
% 2.13/2.32        | ((sk_C_4) = (k6_relat_1 @ (k1_relat_1 @ sk_C_4)))
% 2.13/2.32        | ~ (v1_funct_1 @ sk_C_4)
% 2.13/2.32        | ~ (v1_relat_1 @ sk_C_4)
% 2.13/2.32        | ((sk_C_3 @ sk_C_4 @ (k1_relat_1 @ sk_C_4))
% 2.13/2.32            = (sk_D_1 @ (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ 
% 2.13/2.32               sk_C_4))
% 2.13/2.32        | ~ (r2_hidden @ 
% 2.13/2.32             (sk_D_1 @ (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ 
% 2.13/2.32              sk_C_4) @ 
% 2.13/2.32             (k1_relat_1 @ sk_C_4))
% 2.13/2.32        | ~ (v2_funct_1 @ sk_C_4))),
% 2.13/2.32      inference('sup-', [status(thm)], ['53', '57'])).
% 2.13/2.32  thf('59', plain, (((k1_relat_1 @ sk_C_4) = (sk_A))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('60', plain, (((k1_relat_1 @ sk_C_4) = (sk_A))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('61', plain, ((v1_funct_1 @ sk_C_4)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('62', plain, ((v1_relat_1 @ sk_C_4)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('63', plain, (((k1_relat_1 @ sk_C_4) = (sk_A))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('64', plain, (((k1_relat_1 @ sk_C_4) = (sk_A))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('65', plain,
% 2.13/2.32      ((r2_hidden @ (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ 
% 2.13/2.32        (k2_relat_1 @ sk_C_4))),
% 2.13/2.32      inference('sup-', [status(thm)], ['41', '47'])).
% 2.13/2.32  thf('66', plain,
% 2.13/2.32      (![X5 : $i, X8 : $i]:
% 2.13/2.32         (~ (v1_relat_1 @ X5)
% 2.13/2.32          | ~ (v1_funct_1 @ X5)
% 2.13/2.32          | ~ (r2_hidden @ X8 @ (k2_relat_1 @ X5))
% 2.13/2.32          | (r2_hidden @ (sk_D_1 @ X8 @ X5) @ (k1_relat_1 @ X5)))),
% 2.13/2.32      inference('simplify', [status(thm)], ['12'])).
% 2.13/2.32  thf('67', plain,
% 2.13/2.32      (((r2_hidden @ 
% 2.13/2.32         (sk_D_1 @ (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ sk_C_4) @ 
% 2.13/2.32         (k1_relat_1 @ sk_C_4))
% 2.13/2.32        | ~ (v1_funct_1 @ sk_C_4)
% 2.13/2.32        | ~ (v1_relat_1 @ sk_C_4))),
% 2.13/2.32      inference('sup-', [status(thm)], ['65', '66'])).
% 2.13/2.32  thf('68', plain, (((k1_relat_1 @ sk_C_4) = (sk_A))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('69', plain, ((v1_funct_1 @ sk_C_4)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('70', plain, ((v1_relat_1 @ sk_C_4)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('71', plain,
% 2.13/2.32      ((r2_hidden @ 
% 2.13/2.32        (sk_D_1 @ (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ sk_C_4) @ 
% 2.13/2.32        sk_A)),
% 2.13/2.32      inference('demod', [status(thm)], ['67', '68', '69', '70'])).
% 2.13/2.32  thf('72', plain,
% 2.13/2.32      ((((k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 2.13/2.32          != (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A)))
% 2.13/2.32        | ((sk_C_4) = (k6_relat_1 @ sk_A))
% 2.13/2.32        | ((sk_C_3 @ sk_C_4 @ sk_A)
% 2.13/2.32            = (sk_D_1 @ (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ 
% 2.13/2.32               sk_C_4))
% 2.13/2.32        | ~ (v2_funct_1 @ sk_C_4))),
% 2.13/2.32      inference('demod', [status(thm)],
% 2.13/2.32                ['58', '59', '60', '61', '62', '63', '64', '71'])).
% 2.13/2.32  thf('73', plain,
% 2.13/2.32      ((~ (v2_funct_1 @ sk_C_4)
% 2.13/2.32        | ((sk_C_3 @ sk_C_4 @ sk_A)
% 2.13/2.32            = (sk_D_1 @ (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ 
% 2.13/2.32               sk_C_4))
% 2.13/2.32        | ((sk_C_4) = (k6_relat_1 @ sk_A)))),
% 2.13/2.32      inference('simplify', [status(thm)], ['72'])).
% 2.13/2.32  thf('74', plain, (((sk_C_4) != (k6_relat_1 @ sk_A))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('75', plain,
% 2.13/2.32      ((~ (v2_funct_1 @ sk_C_4)
% 2.13/2.32        | ((sk_C_3 @ sk_C_4 @ sk_A)
% 2.13/2.32            = (sk_D_1 @ (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ 
% 2.13/2.32               sk_C_4)))),
% 2.13/2.32      inference('simplify_reflect-', [status(thm)], ['73', '74'])).
% 2.13/2.32  thf('76', plain, (((k1_relat_1 @ sk_C_4) = (sk_A))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('77', plain,
% 2.13/2.32      (![X11 : $i]:
% 2.13/2.32         ((r2_hidden @ (sk_C_2 @ X11) @ (k1_relat_1 @ X11))
% 2.13/2.32          | (v2_funct_1 @ X11)
% 2.13/2.32          | ~ (v1_funct_1 @ X11)
% 2.13/2.32          | ~ (v1_relat_1 @ X11))),
% 2.13/2.32      inference('cnf', [status(esa)], [d8_funct_1])).
% 2.13/2.32  thf('78', plain,
% 2.13/2.32      (((r2_hidden @ (sk_C_2 @ sk_C_4) @ sk_A)
% 2.13/2.32        | ~ (v1_relat_1 @ sk_C_4)
% 2.13/2.32        | ~ (v1_funct_1 @ sk_C_4)
% 2.13/2.32        | (v2_funct_1 @ sk_C_4))),
% 2.13/2.32      inference('sup+', [status(thm)], ['76', '77'])).
% 2.13/2.32  thf('79', plain, ((v1_relat_1 @ sk_C_4)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('80', plain, ((v1_funct_1 @ sk_C_4)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('81', plain,
% 2.13/2.32      (((r2_hidden @ (sk_C_2 @ sk_C_4) @ sk_A) | (v2_funct_1 @ sk_C_4))),
% 2.13/2.32      inference('demod', [status(thm)], ['78', '79', '80'])).
% 2.13/2.32  thf('82', plain, (((k5_relat_1 @ sk_C_4 @ sk_B_1) = (sk_B_1))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('83', plain,
% 2.13/2.32      (![X11 : $i]:
% 2.13/2.32         ((r2_hidden @ (sk_B @ X11) @ (k1_relat_1 @ X11))
% 2.13/2.32          | (v2_funct_1 @ X11)
% 2.13/2.32          | ~ (v1_funct_1 @ X11)
% 2.13/2.32          | ~ (v1_relat_1 @ X11))),
% 2.13/2.32      inference('cnf', [status(esa)], [d8_funct_1])).
% 2.13/2.32  thf('84', plain,
% 2.13/2.32      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.13/2.32         (~ (v1_relat_1 @ X14)
% 2.13/2.32          | ~ (v1_funct_1 @ X14)
% 2.13/2.32          | ((k1_funct_1 @ (k5_relat_1 @ X15 @ X14) @ X16)
% 2.13/2.32              = (k1_funct_1 @ X14 @ (k1_funct_1 @ X15 @ X16)))
% 2.13/2.32          | ~ (r2_hidden @ X16 @ (k1_relat_1 @ X15))
% 2.13/2.32          | ~ (v1_funct_1 @ X15)
% 2.13/2.32          | ~ (v1_relat_1 @ X15))),
% 2.13/2.32      inference('cnf', [status(esa)], [t23_funct_1])).
% 2.13/2.32  thf('85', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i]:
% 2.13/2.32         (~ (v1_relat_1 @ X0)
% 2.13/2.32          | ~ (v1_funct_1 @ X0)
% 2.13/2.32          | (v2_funct_1 @ X0)
% 2.13/2.32          | ~ (v1_relat_1 @ X0)
% 2.13/2.32          | ~ (v1_funct_1 @ X0)
% 2.13/2.32          | ((k1_funct_1 @ (k5_relat_1 @ X0 @ X1) @ (sk_B @ X0))
% 2.13/2.32              = (k1_funct_1 @ X1 @ (k1_funct_1 @ X0 @ (sk_B @ X0))))
% 2.13/2.32          | ~ (v1_funct_1 @ X1)
% 2.13/2.32          | ~ (v1_relat_1 @ X1))),
% 2.13/2.32      inference('sup-', [status(thm)], ['83', '84'])).
% 2.13/2.32  thf('86', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i]:
% 2.13/2.32         (~ (v1_relat_1 @ X1)
% 2.13/2.32          | ~ (v1_funct_1 @ X1)
% 2.13/2.32          | ((k1_funct_1 @ (k5_relat_1 @ X0 @ X1) @ (sk_B @ X0))
% 2.13/2.32              = (k1_funct_1 @ X1 @ (k1_funct_1 @ X0 @ (sk_B @ X0))))
% 2.13/2.32          | (v2_funct_1 @ X0)
% 2.13/2.32          | ~ (v1_funct_1 @ X0)
% 2.13/2.32          | ~ (v1_relat_1 @ X0))),
% 2.13/2.32      inference('simplify', [status(thm)], ['85'])).
% 2.13/2.32  thf('87', plain,
% 2.13/2.32      (![X11 : $i]:
% 2.13/2.32         (((k1_funct_1 @ X11 @ (sk_B @ X11))
% 2.13/2.32            = (k1_funct_1 @ X11 @ (sk_C_2 @ X11)))
% 2.13/2.32          | (v2_funct_1 @ X11)
% 2.13/2.32          | ~ (v1_funct_1 @ X11)
% 2.13/2.32          | ~ (v1_relat_1 @ X11))),
% 2.13/2.32      inference('cnf', [status(esa)], [d8_funct_1])).
% 2.13/2.32  thf('88', plain,
% 2.13/2.32      (![X11 : $i]:
% 2.13/2.32         ((r2_hidden @ (sk_C_2 @ X11) @ (k1_relat_1 @ X11))
% 2.13/2.32          | (v2_funct_1 @ X11)
% 2.13/2.32          | ~ (v1_funct_1 @ X11)
% 2.13/2.32          | ~ (v1_relat_1 @ X11))),
% 2.13/2.32      inference('cnf', [status(esa)], [d8_funct_1])).
% 2.13/2.32  thf('89', plain,
% 2.13/2.32      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.13/2.32         (~ (v1_relat_1 @ X14)
% 2.13/2.32          | ~ (v1_funct_1 @ X14)
% 2.13/2.32          | ((k1_funct_1 @ (k5_relat_1 @ X15 @ X14) @ X16)
% 2.13/2.32              = (k1_funct_1 @ X14 @ (k1_funct_1 @ X15 @ X16)))
% 2.13/2.32          | ~ (r2_hidden @ X16 @ (k1_relat_1 @ X15))
% 2.13/2.32          | ~ (v1_funct_1 @ X15)
% 2.13/2.32          | ~ (v1_relat_1 @ X15))),
% 2.13/2.32      inference('cnf', [status(esa)], [t23_funct_1])).
% 2.13/2.32  thf('90', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i]:
% 2.13/2.32         (~ (v1_relat_1 @ X0)
% 2.13/2.32          | ~ (v1_funct_1 @ X0)
% 2.13/2.32          | (v2_funct_1 @ X0)
% 2.13/2.32          | ~ (v1_relat_1 @ X0)
% 2.13/2.32          | ~ (v1_funct_1 @ X0)
% 2.13/2.32          | ((k1_funct_1 @ (k5_relat_1 @ X0 @ X1) @ (sk_C_2 @ X0))
% 2.13/2.32              = (k1_funct_1 @ X1 @ (k1_funct_1 @ X0 @ (sk_C_2 @ X0))))
% 2.13/2.32          | ~ (v1_funct_1 @ X1)
% 2.13/2.32          | ~ (v1_relat_1 @ X1))),
% 2.13/2.32      inference('sup-', [status(thm)], ['88', '89'])).
% 2.13/2.32  thf('91', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i]:
% 2.13/2.32         (~ (v1_relat_1 @ X1)
% 2.13/2.32          | ~ (v1_funct_1 @ X1)
% 2.13/2.32          | ((k1_funct_1 @ (k5_relat_1 @ X0 @ X1) @ (sk_C_2 @ X0))
% 2.13/2.32              = (k1_funct_1 @ X1 @ (k1_funct_1 @ X0 @ (sk_C_2 @ X0))))
% 2.13/2.32          | (v2_funct_1 @ X0)
% 2.13/2.32          | ~ (v1_funct_1 @ X0)
% 2.13/2.32          | ~ (v1_relat_1 @ X0))),
% 2.13/2.32      inference('simplify', [status(thm)], ['90'])).
% 2.13/2.32  thf('92', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i]:
% 2.13/2.32         (((k1_funct_1 @ (k5_relat_1 @ X0 @ X1) @ (sk_C_2 @ X0))
% 2.13/2.32            = (k1_funct_1 @ X1 @ (k1_funct_1 @ X0 @ (sk_B @ X0))))
% 2.13/2.32          | ~ (v1_relat_1 @ X0)
% 2.13/2.32          | ~ (v1_funct_1 @ X0)
% 2.13/2.32          | (v2_funct_1 @ X0)
% 2.13/2.32          | ~ (v1_relat_1 @ X0)
% 2.13/2.32          | ~ (v1_funct_1 @ X0)
% 2.13/2.32          | (v2_funct_1 @ X0)
% 2.13/2.32          | ~ (v1_funct_1 @ X1)
% 2.13/2.32          | ~ (v1_relat_1 @ X1))),
% 2.13/2.32      inference('sup+', [status(thm)], ['87', '91'])).
% 2.13/2.32  thf('93', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i]:
% 2.13/2.32         (~ (v1_relat_1 @ X1)
% 2.13/2.32          | ~ (v1_funct_1 @ X1)
% 2.13/2.32          | (v2_funct_1 @ X0)
% 2.13/2.32          | ~ (v1_funct_1 @ X0)
% 2.13/2.32          | ~ (v1_relat_1 @ X0)
% 2.13/2.32          | ((k1_funct_1 @ (k5_relat_1 @ X0 @ X1) @ (sk_C_2 @ X0))
% 2.13/2.32              = (k1_funct_1 @ X1 @ (k1_funct_1 @ X0 @ (sk_B @ X0)))))),
% 2.13/2.32      inference('simplify', [status(thm)], ['92'])).
% 2.13/2.32  thf('94', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i]:
% 2.13/2.32         (((k1_funct_1 @ (k5_relat_1 @ X0 @ X1) @ (sk_C_2 @ X0))
% 2.13/2.32            = (k1_funct_1 @ (k5_relat_1 @ X0 @ X1) @ (sk_B @ X0)))
% 2.13/2.32          | ~ (v1_relat_1 @ X0)
% 2.13/2.32          | ~ (v1_funct_1 @ X0)
% 2.13/2.32          | (v2_funct_1 @ X0)
% 2.13/2.32          | ~ (v1_funct_1 @ X1)
% 2.13/2.32          | ~ (v1_relat_1 @ X1)
% 2.13/2.32          | ~ (v1_relat_1 @ X0)
% 2.13/2.32          | ~ (v1_funct_1 @ X0)
% 2.13/2.32          | (v2_funct_1 @ X0)
% 2.13/2.32          | ~ (v1_funct_1 @ X1)
% 2.13/2.32          | ~ (v1_relat_1 @ X1))),
% 2.13/2.32      inference('sup+', [status(thm)], ['86', '93'])).
% 2.13/2.32  thf('95', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i]:
% 2.13/2.32         (~ (v1_relat_1 @ X1)
% 2.13/2.32          | ~ (v1_funct_1 @ X1)
% 2.13/2.32          | (v2_funct_1 @ X0)
% 2.13/2.32          | ~ (v1_funct_1 @ X0)
% 2.13/2.32          | ~ (v1_relat_1 @ X0)
% 2.13/2.32          | ((k1_funct_1 @ (k5_relat_1 @ X0 @ X1) @ (sk_C_2 @ X0))
% 2.13/2.32              = (k1_funct_1 @ (k5_relat_1 @ X0 @ X1) @ (sk_B @ X0))))),
% 2.13/2.32      inference('simplify', [status(thm)], ['94'])).
% 2.13/2.32  thf('96', plain,
% 2.13/2.32      ((((k1_funct_1 @ sk_B_1 @ (sk_C_2 @ sk_C_4))
% 2.13/2.32          = (k1_funct_1 @ (k5_relat_1 @ sk_C_4 @ sk_B_1) @ (sk_B @ sk_C_4)))
% 2.13/2.32        | ~ (v1_relat_1 @ sk_C_4)
% 2.13/2.32        | ~ (v1_funct_1 @ sk_C_4)
% 2.13/2.32        | (v2_funct_1 @ sk_C_4)
% 2.13/2.32        | ~ (v1_funct_1 @ sk_B_1)
% 2.13/2.32        | ~ (v1_relat_1 @ sk_B_1))),
% 2.13/2.32      inference('sup+', [status(thm)], ['82', '95'])).
% 2.13/2.32  thf('97', plain, (((k5_relat_1 @ sk_C_4 @ sk_B_1) = (sk_B_1))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('98', plain, ((v1_relat_1 @ sk_C_4)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('99', plain, ((v1_funct_1 @ sk_C_4)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('100', plain, ((v1_funct_1 @ sk_B_1)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('101', plain, ((v1_relat_1 @ sk_B_1)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('102', plain,
% 2.13/2.32      ((((k1_funct_1 @ sk_B_1 @ (sk_C_2 @ sk_C_4))
% 2.13/2.32          = (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_C_4)))
% 2.13/2.32        | (v2_funct_1 @ sk_C_4))),
% 2.13/2.32      inference('demod', [status(thm)], ['96', '97', '98', '99', '100', '101'])).
% 2.13/2.32  thf('103', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('104', plain,
% 2.13/2.32      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.13/2.32         (~ (v2_funct_1 @ X11)
% 2.13/2.32          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ X11))
% 2.13/2.32          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X11))
% 2.13/2.32          | ((k1_funct_1 @ X11 @ X12) != (k1_funct_1 @ X11 @ X13))
% 2.13/2.32          | ((X12) = (X13))
% 2.13/2.32          | ~ (v1_funct_1 @ X11)
% 2.13/2.32          | ~ (v1_relat_1 @ X11))),
% 2.13/2.32      inference('cnf', [status(esa)], [d8_funct_1])).
% 2.13/2.32  thf('105', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i]:
% 2.13/2.32         (~ (r2_hidden @ X0 @ sk_A)
% 2.13/2.32          | ~ (v1_relat_1 @ sk_B_1)
% 2.13/2.32          | ~ (v1_funct_1 @ sk_B_1)
% 2.13/2.32          | ((X0) = (X1))
% 2.13/2.32          | ((k1_funct_1 @ sk_B_1 @ X0) != (k1_funct_1 @ sk_B_1 @ X1))
% 2.13/2.32          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1))
% 2.13/2.32          | ~ (v2_funct_1 @ sk_B_1))),
% 2.13/2.32      inference('sup-', [status(thm)], ['103', '104'])).
% 2.13/2.32  thf('106', plain, ((v1_relat_1 @ sk_B_1)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('107', plain, ((v1_funct_1 @ sk_B_1)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('108', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('109', plain, ((v2_funct_1 @ sk_B_1)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('110', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i]:
% 2.13/2.32         (~ (r2_hidden @ X0 @ sk_A)
% 2.13/2.32          | ((X0) = (X1))
% 2.13/2.32          | ((k1_funct_1 @ sk_B_1 @ X0) != (k1_funct_1 @ sk_B_1 @ X1))
% 2.13/2.32          | ~ (r2_hidden @ X1 @ sk_A))),
% 2.13/2.32      inference('demod', [status(thm)], ['105', '106', '107', '108', '109'])).
% 2.13/2.32  thf('111', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         (((k1_funct_1 @ sk_B_1 @ (sk_B @ sk_C_4))
% 2.13/2.32            != (k1_funct_1 @ sk_B_1 @ X0))
% 2.13/2.32          | (v2_funct_1 @ sk_C_4)
% 2.13/2.32          | ~ (r2_hidden @ X0 @ sk_A)
% 2.13/2.32          | ((sk_C_2 @ sk_C_4) = (X0))
% 2.13/2.32          | ~ (r2_hidden @ (sk_C_2 @ sk_C_4) @ sk_A))),
% 2.13/2.32      inference('sup-', [status(thm)], ['102', '110'])).
% 2.13/2.32  thf('112', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         ((v2_funct_1 @ sk_C_4)
% 2.13/2.32          | ((sk_C_2 @ sk_C_4) = (X0))
% 2.13/2.32          | ~ (r2_hidden @ X0 @ sk_A)
% 2.13/2.32          | (v2_funct_1 @ sk_C_4)
% 2.13/2.32          | ((k1_funct_1 @ sk_B_1 @ (sk_B @ sk_C_4))
% 2.13/2.32              != (k1_funct_1 @ sk_B_1 @ X0)))),
% 2.13/2.32      inference('sup-', [status(thm)], ['81', '111'])).
% 2.13/2.32  thf('113', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         (((k1_funct_1 @ sk_B_1 @ (sk_B @ sk_C_4))
% 2.13/2.32            != (k1_funct_1 @ sk_B_1 @ X0))
% 2.13/2.32          | ~ (r2_hidden @ X0 @ sk_A)
% 2.13/2.32          | ((sk_C_2 @ sk_C_4) = (X0))
% 2.13/2.32          | (v2_funct_1 @ sk_C_4))),
% 2.13/2.32      inference('simplify', [status(thm)], ['112'])).
% 2.13/2.32  thf('114', plain,
% 2.13/2.32      (((v2_funct_1 @ sk_C_4)
% 2.13/2.32        | ((sk_C_2 @ sk_C_4) = (sk_B @ sk_C_4))
% 2.13/2.32        | ~ (r2_hidden @ (sk_B @ sk_C_4) @ sk_A))),
% 2.13/2.32      inference('eq_res', [status(thm)], ['113'])).
% 2.13/2.32  thf('115', plain, (((k1_relat_1 @ sk_C_4) = (sk_A))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('116', plain,
% 2.13/2.32      (![X11 : $i]:
% 2.13/2.32         ((r2_hidden @ (sk_B @ X11) @ (k1_relat_1 @ X11))
% 2.13/2.32          | (v2_funct_1 @ X11)
% 2.13/2.32          | ~ (v1_funct_1 @ X11)
% 2.13/2.32          | ~ (v1_relat_1 @ X11))),
% 2.13/2.32      inference('cnf', [status(esa)], [d8_funct_1])).
% 2.13/2.32  thf('117', plain,
% 2.13/2.32      (((r2_hidden @ (sk_B @ sk_C_4) @ sk_A)
% 2.13/2.32        | ~ (v1_relat_1 @ sk_C_4)
% 2.13/2.32        | ~ (v1_funct_1 @ sk_C_4)
% 2.13/2.32        | (v2_funct_1 @ sk_C_4))),
% 2.13/2.32      inference('sup+', [status(thm)], ['115', '116'])).
% 2.13/2.32  thf('118', plain, ((v1_relat_1 @ sk_C_4)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('119', plain, ((v1_funct_1 @ sk_C_4)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('120', plain,
% 2.13/2.32      (((r2_hidden @ (sk_B @ sk_C_4) @ sk_A) | (v2_funct_1 @ sk_C_4))),
% 2.13/2.32      inference('demod', [status(thm)], ['117', '118', '119'])).
% 2.13/2.32  thf('121', plain,
% 2.13/2.32      ((((sk_C_2 @ sk_C_4) = (sk_B @ sk_C_4)) | (v2_funct_1 @ sk_C_4))),
% 2.13/2.32      inference('clc', [status(thm)], ['114', '120'])).
% 2.13/2.32  thf('122', plain,
% 2.13/2.32      ((~ (v2_funct_1 @ sk_C_4)
% 2.13/2.32        | ((sk_C_3 @ sk_C_4 @ sk_A)
% 2.13/2.32            = (sk_D_1 @ (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ 
% 2.13/2.32               sk_C_4)))),
% 2.13/2.32      inference('simplify_reflect-', [status(thm)], ['73', '74'])).
% 2.13/2.32  thf('123', plain,
% 2.13/2.32      ((((sk_C_2 @ sk_C_4) = (sk_B @ sk_C_4))
% 2.13/2.32        | ((sk_C_3 @ sk_C_4 @ sk_A)
% 2.13/2.32            = (sk_D_1 @ (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ 
% 2.13/2.32               sk_C_4)))),
% 2.13/2.32      inference('sup-', [status(thm)], ['121', '122'])).
% 2.13/2.32  thf('124', plain,
% 2.13/2.32      (((k1_funct_1 @ sk_B_1 @ 
% 2.13/2.32         (sk_D_1 @ (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ sk_C_4))
% 2.13/2.32         = (k1_funct_1 @ sk_B_1 @ 
% 2.13/2.32            (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A))))),
% 2.13/2.32      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 2.13/2.32  thf('125', plain,
% 2.13/2.32      ((((k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 2.13/2.32          = (k1_funct_1 @ sk_B_1 @ 
% 2.13/2.32             (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A))))
% 2.13/2.32        | ((sk_C_2 @ sk_C_4) = (sk_B @ sk_C_4)))),
% 2.13/2.32      inference('sup+', [status(thm)], ['123', '124'])).
% 2.13/2.32  thf('126', plain, ((r2_hidden @ (sk_C_3 @ sk_C_4 @ sk_A) @ sk_A)),
% 2.13/2.32      inference('simplify_reflect-', [status(thm)], ['39', '40'])).
% 2.13/2.32  thf('127', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('128', plain,
% 2.13/2.32      (![X5 : $i, X10 : $i]:
% 2.13/2.32         (~ (v1_relat_1 @ X5)
% 2.13/2.32          | ~ (v1_funct_1 @ X5)
% 2.13/2.32          | ~ (r2_hidden @ X10 @ (k1_relat_1 @ X5))
% 2.13/2.32          | (r2_hidden @ (k1_funct_1 @ X5 @ X10) @ (k2_relat_1 @ X5)))),
% 2.13/2.32      inference('simplify', [status(thm)], ['3'])).
% 2.13/2.32  thf('129', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         (~ (r2_hidden @ X0 @ sk_A)
% 2.13/2.32          | (r2_hidden @ (k1_funct_1 @ sk_B_1 @ X0) @ (k2_relat_1 @ sk_B_1))
% 2.13/2.32          | ~ (v1_funct_1 @ sk_B_1)
% 2.13/2.32          | ~ (v1_relat_1 @ sk_B_1))),
% 2.13/2.32      inference('sup-', [status(thm)], ['127', '128'])).
% 2.13/2.32  thf('130', plain, ((v1_funct_1 @ sk_B_1)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('131', plain, ((v1_relat_1 @ sk_B_1)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('132', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         (~ (r2_hidden @ X0 @ sk_A)
% 2.13/2.32          | (r2_hidden @ (k1_funct_1 @ sk_B_1 @ X0) @ (k2_relat_1 @ sk_B_1)))),
% 2.13/2.32      inference('demod', [status(thm)], ['129', '130', '131'])).
% 2.13/2.32  thf('133', plain,
% 2.13/2.32      ((r2_hidden @ (k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ 
% 2.13/2.32        (k2_relat_1 @ sk_B_1))),
% 2.13/2.32      inference('sup-', [status(thm)], ['126', '132'])).
% 2.13/2.32  thf('134', plain,
% 2.13/2.32      (![X5 : $i, X8 : $i]:
% 2.13/2.32         (~ (v1_relat_1 @ X5)
% 2.13/2.32          | ~ (v1_funct_1 @ X5)
% 2.13/2.32          | ~ (r2_hidden @ X8 @ (k2_relat_1 @ X5))
% 2.13/2.32          | ((X8) = (k1_funct_1 @ X5 @ (sk_D_1 @ X8 @ X5))))),
% 2.13/2.32      inference('simplify', [status(thm)], ['7'])).
% 2.13/2.32  thf('135', plain,
% 2.13/2.32      ((((k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 2.13/2.32          = (k1_funct_1 @ sk_B_1 @ 
% 2.13/2.32             (sk_D_1 @ (k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ 
% 2.13/2.32              sk_B_1)))
% 2.13/2.32        | ~ (v1_funct_1 @ sk_B_1)
% 2.13/2.32        | ~ (v1_relat_1 @ sk_B_1))),
% 2.13/2.32      inference('sup-', [status(thm)], ['133', '134'])).
% 2.13/2.32  thf('136', plain, ((v1_funct_1 @ sk_B_1)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('137', plain, ((v1_relat_1 @ sk_B_1)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('138', plain,
% 2.13/2.32      (((k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 2.13/2.32         = (k1_funct_1 @ sk_B_1 @ 
% 2.13/2.32            (sk_D_1 @ (k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ sk_B_1)))),
% 2.13/2.32      inference('demod', [status(thm)], ['135', '136', '137'])).
% 2.13/2.32  thf('139', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i]:
% 2.13/2.32         (~ (r2_hidden @ X0 @ sk_A)
% 2.13/2.32          | ((X0) = (X1))
% 2.13/2.32          | ((k1_funct_1 @ sk_B_1 @ X0) != (k1_funct_1 @ sk_B_1 @ X1))
% 2.13/2.32          | ~ (r2_hidden @ X1 @ sk_A))),
% 2.13/2.32      inference('demod', [status(thm)], ['105', '106', '107', '108', '109'])).
% 2.13/2.32  thf('140', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         (((k1_funct_1 @ sk_B_1 @ X0)
% 2.13/2.32            != (k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A)))
% 2.13/2.32          | ~ (r2_hidden @ 
% 2.13/2.32               (sk_D_1 @ (k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ 
% 2.13/2.32                sk_B_1) @ 
% 2.13/2.32               sk_A)
% 2.13/2.32          | ((X0)
% 2.13/2.32              = (sk_D_1 @ (k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ 
% 2.13/2.32                 sk_B_1))
% 2.13/2.32          | ~ (r2_hidden @ X0 @ sk_A))),
% 2.13/2.32      inference('sup-', [status(thm)], ['138', '139'])).
% 2.13/2.32  thf('141', plain,
% 2.13/2.32      ((r2_hidden @ (k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ 
% 2.13/2.32        (k2_relat_1 @ sk_B_1))),
% 2.13/2.32      inference('sup-', [status(thm)], ['126', '132'])).
% 2.13/2.32  thf('142', plain,
% 2.13/2.32      (![X5 : $i, X8 : $i]:
% 2.13/2.32         (~ (v1_relat_1 @ X5)
% 2.13/2.32          | ~ (v1_funct_1 @ X5)
% 2.13/2.32          | ~ (r2_hidden @ X8 @ (k2_relat_1 @ X5))
% 2.13/2.32          | (r2_hidden @ (sk_D_1 @ X8 @ X5) @ (k1_relat_1 @ X5)))),
% 2.13/2.32      inference('simplify', [status(thm)], ['12'])).
% 2.13/2.32  thf('143', plain,
% 2.13/2.32      (((r2_hidden @ 
% 2.13/2.32         (sk_D_1 @ (k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ sk_B_1) @ 
% 2.13/2.32         (k1_relat_1 @ sk_B_1))
% 2.13/2.32        | ~ (v1_funct_1 @ sk_B_1)
% 2.13/2.32        | ~ (v1_relat_1 @ sk_B_1))),
% 2.13/2.32      inference('sup-', [status(thm)], ['141', '142'])).
% 2.13/2.32  thf('144', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('145', plain, ((v1_funct_1 @ sk_B_1)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('146', plain, ((v1_relat_1 @ sk_B_1)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('147', plain,
% 2.13/2.32      ((r2_hidden @ 
% 2.13/2.32        (sk_D_1 @ (k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ sk_B_1) @ 
% 2.13/2.32        sk_A)),
% 2.13/2.32      inference('demod', [status(thm)], ['143', '144', '145', '146'])).
% 2.13/2.32  thf('148', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         (((k1_funct_1 @ sk_B_1 @ X0)
% 2.13/2.32            != (k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A)))
% 2.13/2.32          | ((X0)
% 2.13/2.32              = (sk_D_1 @ (k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ 
% 2.13/2.32                 sk_B_1))
% 2.13/2.32          | ~ (r2_hidden @ X0 @ sk_A))),
% 2.13/2.32      inference('demod', [status(thm)], ['140', '147'])).
% 2.13/2.32  thf('149', plain,
% 2.13/2.32      (((k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 2.13/2.32         = (k1_funct_1 @ sk_B_1 @ 
% 2.13/2.32            (sk_D_1 @ (k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ sk_B_1)))),
% 2.13/2.32      inference('demod', [status(thm)], ['135', '136', '137'])).
% 2.13/2.32  thf('150', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i]:
% 2.13/2.32         (~ (r2_hidden @ X0 @ sk_A)
% 2.13/2.32          | ((X0) = (X1))
% 2.13/2.32          | ((k1_funct_1 @ sk_B_1 @ X0) != (k1_funct_1 @ sk_B_1 @ X1))
% 2.13/2.32          | ~ (r2_hidden @ X1 @ sk_A))),
% 2.13/2.32      inference('demod', [status(thm)], ['105', '106', '107', '108', '109'])).
% 2.13/2.32  thf('151', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         (((k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 2.13/2.32            != (k1_funct_1 @ sk_B_1 @ X0))
% 2.13/2.32          | ~ (r2_hidden @ X0 @ sk_A)
% 2.13/2.32          | ((sk_D_1 @ (k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ 
% 2.13/2.32              sk_B_1) = (X0))
% 2.13/2.32          | ~ (r2_hidden @ 
% 2.13/2.32               (sk_D_1 @ (k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ 
% 2.13/2.32                sk_B_1) @ 
% 2.13/2.32               sk_A))),
% 2.13/2.32      inference('sup-', [status(thm)], ['149', '150'])).
% 2.13/2.32  thf('152', plain,
% 2.13/2.32      ((r2_hidden @ 
% 2.13/2.32        (sk_D_1 @ (k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ sk_B_1) @ 
% 2.13/2.32        sk_A)),
% 2.13/2.32      inference('demod', [status(thm)], ['143', '144', '145', '146'])).
% 2.13/2.32  thf('153', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         (((k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 2.13/2.32            != (k1_funct_1 @ sk_B_1 @ X0))
% 2.13/2.32          | ~ (r2_hidden @ X0 @ sk_A)
% 2.13/2.32          | ((sk_D_1 @ (k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ 
% 2.13/2.32              sk_B_1) = (X0)))),
% 2.13/2.32      inference('demod', [status(thm)], ['151', '152'])).
% 2.13/2.32  thf('154', plain,
% 2.13/2.32      ((((sk_D_1 @ (k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ sk_B_1)
% 2.13/2.32          = (sk_C_3 @ sk_C_4 @ sk_A))
% 2.13/2.32        | ~ (r2_hidden @ (sk_C_3 @ sk_C_4 @ sk_A) @ sk_A))),
% 2.13/2.32      inference('eq_res', [status(thm)], ['153'])).
% 2.13/2.32  thf('155', plain, ((r2_hidden @ (sk_C_3 @ sk_C_4 @ sk_A) @ sk_A)),
% 2.13/2.32      inference('simplify_reflect-', [status(thm)], ['39', '40'])).
% 2.13/2.32  thf('156', plain,
% 2.13/2.32      (((sk_D_1 @ (k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ sk_B_1)
% 2.13/2.32         = (sk_C_3 @ sk_C_4 @ sk_A))),
% 2.13/2.32      inference('demod', [status(thm)], ['154', '155'])).
% 2.13/2.32  thf('157', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         (((k1_funct_1 @ sk_B_1 @ X0)
% 2.13/2.32            != (k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A)))
% 2.13/2.32          | ((X0) = (sk_C_3 @ sk_C_4 @ sk_A))
% 2.13/2.32          | ~ (r2_hidden @ X0 @ sk_A))),
% 2.13/2.32      inference('demod', [status(thm)], ['148', '156'])).
% 2.13/2.32  thf('158', plain,
% 2.13/2.32      ((((k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 2.13/2.32          != (k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A)))
% 2.13/2.32        | ((sk_C_2 @ sk_C_4) = (sk_B @ sk_C_4))
% 2.13/2.32        | ~ (r2_hidden @ (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ 
% 2.13/2.32             sk_A)
% 2.13/2.32        | ((k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 2.13/2.32            = (sk_C_3 @ sk_C_4 @ sk_A)))),
% 2.13/2.32      inference('sup-', [status(thm)], ['125', '157'])).
% 2.13/2.32  thf('159', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         ((r2_hidden @ (k1_funct_1 @ X0 @ (sk_C_3 @ X0 @ (k1_relat_1 @ X0))) @ 
% 2.13/2.32           (k2_relat_1 @ X0))
% 2.13/2.32          | ~ (v1_relat_1 @ X0)
% 2.13/2.32          | ~ (v1_funct_1 @ X0)
% 2.13/2.32          | ((X0) = (k6_relat_1 @ (k1_relat_1 @ X0))))),
% 2.13/2.32      inference('simplify', [status(thm)], ['5'])).
% 2.13/2.32  thf('160', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_4) @ sk_A)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf(d3_tarski, axiom,
% 2.13/2.32    (![A:$i,B:$i]:
% 2.13/2.32     ( ( r1_tarski @ A @ B ) <=>
% 2.13/2.32       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.13/2.32  thf('161', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.13/2.32         (~ (r2_hidden @ X0 @ X1)
% 2.13/2.32          | (r2_hidden @ X0 @ X2)
% 2.13/2.32          | ~ (r1_tarski @ X1 @ X2))),
% 2.13/2.32      inference('cnf', [status(esa)], [d3_tarski])).
% 2.13/2.32  thf('162', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_4)))),
% 2.13/2.32      inference('sup-', [status(thm)], ['160', '161'])).
% 2.13/2.32  thf('163', plain,
% 2.13/2.32      ((((sk_C_4) = (k6_relat_1 @ (k1_relat_1 @ sk_C_4)))
% 2.13/2.32        | ~ (v1_funct_1 @ sk_C_4)
% 2.13/2.32        | ~ (v1_relat_1 @ sk_C_4)
% 2.13/2.32        | (r2_hidden @ 
% 2.13/2.32           (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ (k1_relat_1 @ sk_C_4))) @ 
% 2.13/2.32           sk_A))),
% 2.13/2.32      inference('sup-', [status(thm)], ['159', '162'])).
% 2.13/2.32  thf('164', plain, (((k1_relat_1 @ sk_C_4) = (sk_A))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('165', plain, ((v1_funct_1 @ sk_C_4)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('166', plain, ((v1_relat_1 @ sk_C_4)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('167', plain, (((k1_relat_1 @ sk_C_4) = (sk_A))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('168', plain,
% 2.13/2.32      ((((sk_C_4) = (k6_relat_1 @ sk_A))
% 2.13/2.32        | (r2_hidden @ (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ sk_A))),
% 2.13/2.32      inference('demod', [status(thm)], ['163', '164', '165', '166', '167'])).
% 2.13/2.32  thf('169', plain, (((sk_C_4) != (k6_relat_1 @ sk_A))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('170', plain,
% 2.13/2.32      ((r2_hidden @ (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ sk_A)),
% 2.13/2.32      inference('simplify_reflect-', [status(thm)], ['168', '169'])).
% 2.13/2.32  thf('171', plain,
% 2.13/2.32      ((((k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 2.13/2.32          != (k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A)))
% 2.13/2.32        | ((sk_C_2 @ sk_C_4) = (sk_B @ sk_C_4))
% 2.13/2.32        | ((k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 2.13/2.32            = (sk_C_3 @ sk_C_4 @ sk_A)))),
% 2.13/2.32      inference('demod', [status(thm)], ['158', '170'])).
% 2.13/2.32  thf('172', plain,
% 2.13/2.32      ((((k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 2.13/2.32          = (sk_C_3 @ sk_C_4 @ sk_A))
% 2.13/2.32        | ((sk_C_2 @ sk_C_4) = (sk_B @ sk_C_4)))),
% 2.13/2.32      inference('simplify', [status(thm)], ['171'])).
% 2.13/2.32  thf('173', plain, (((k1_relat_1 @ sk_C_4) = (sk_A))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('174', plain,
% 2.13/2.32      (![X17 : $i, X18 : $i]:
% 2.13/2.32         (((k1_relat_1 @ X18) != (X17))
% 2.13/2.32          | ((k1_funct_1 @ X18 @ (sk_C_3 @ X18 @ X17)) != (sk_C_3 @ X18 @ X17))
% 2.13/2.32          | ((X18) = (k6_relat_1 @ X17))
% 2.13/2.32          | ~ (v1_funct_1 @ X18)
% 2.13/2.32          | ~ (v1_relat_1 @ X18))),
% 2.13/2.32      inference('cnf', [status(esa)], [t34_funct_1])).
% 2.13/2.32  thf('175', plain,
% 2.13/2.32      (![X18 : $i]:
% 2.13/2.32         (~ (v1_relat_1 @ X18)
% 2.13/2.32          | ~ (v1_funct_1 @ X18)
% 2.13/2.32          | ((X18) = (k6_relat_1 @ (k1_relat_1 @ X18)))
% 2.13/2.32          | ((k1_funct_1 @ X18 @ (sk_C_3 @ X18 @ (k1_relat_1 @ X18)))
% 2.13/2.32              != (sk_C_3 @ X18 @ (k1_relat_1 @ X18))))),
% 2.13/2.32      inference('simplify', [status(thm)], ['174'])).
% 2.13/2.32  thf('176', plain,
% 2.13/2.32      ((((k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 2.13/2.32          != (sk_C_3 @ sk_C_4 @ (k1_relat_1 @ sk_C_4)))
% 2.13/2.32        | ((sk_C_4) = (k6_relat_1 @ (k1_relat_1 @ sk_C_4)))
% 2.13/2.32        | ~ (v1_funct_1 @ sk_C_4)
% 2.13/2.32        | ~ (v1_relat_1 @ sk_C_4))),
% 2.13/2.32      inference('sup-', [status(thm)], ['173', '175'])).
% 2.13/2.32  thf('177', plain, (((k1_relat_1 @ sk_C_4) = (sk_A))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('178', plain, (((k1_relat_1 @ sk_C_4) = (sk_A))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('179', plain, ((v1_funct_1 @ sk_C_4)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('180', plain, ((v1_relat_1 @ sk_C_4)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('181', plain,
% 2.13/2.32      ((((k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 2.13/2.32          != (sk_C_3 @ sk_C_4 @ sk_A))
% 2.13/2.32        | ((sk_C_4) = (k6_relat_1 @ sk_A)))),
% 2.13/2.32      inference('demod', [status(thm)], ['176', '177', '178', '179', '180'])).
% 2.13/2.32  thf('182', plain, (((sk_C_4) != (k6_relat_1 @ sk_A))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('183', plain,
% 2.13/2.32      (((k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 2.13/2.32         != (sk_C_3 @ sk_C_4 @ sk_A))),
% 2.13/2.32      inference('simplify_reflect-', [status(thm)], ['181', '182'])).
% 2.13/2.32  thf('184', plain, (((sk_C_2 @ sk_C_4) = (sk_B @ sk_C_4))),
% 2.13/2.32      inference('simplify_reflect-', [status(thm)], ['172', '183'])).
% 2.13/2.32  thf('185', plain,
% 2.13/2.32      (![X11 : $i]:
% 2.13/2.32         (((sk_B @ X11) != (sk_C_2 @ X11))
% 2.13/2.32          | (v2_funct_1 @ X11)
% 2.13/2.32          | ~ (v1_funct_1 @ X11)
% 2.13/2.32          | ~ (v1_relat_1 @ X11))),
% 2.13/2.32      inference('cnf', [status(esa)], [d8_funct_1])).
% 2.13/2.32  thf('186', plain,
% 2.13/2.32      ((((sk_B @ sk_C_4) != (sk_B @ sk_C_4))
% 2.13/2.32        | ~ (v1_relat_1 @ sk_C_4)
% 2.13/2.32        | ~ (v1_funct_1 @ sk_C_4)
% 2.13/2.32        | (v2_funct_1 @ sk_C_4))),
% 2.13/2.32      inference('sup-', [status(thm)], ['184', '185'])).
% 2.13/2.32  thf('187', plain, ((v1_relat_1 @ sk_C_4)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('188', plain, ((v1_funct_1 @ sk_C_4)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.32  thf('189', plain,
% 2.13/2.32      ((((sk_B @ sk_C_4) != (sk_B @ sk_C_4)) | (v2_funct_1 @ sk_C_4))),
% 2.13/2.32      inference('demod', [status(thm)], ['186', '187', '188'])).
% 2.13/2.32  thf('190', plain, ((v2_funct_1 @ sk_C_4)),
% 2.13/2.32      inference('simplify', [status(thm)], ['189'])).
% 2.13/2.32  thf('191', plain,
% 2.13/2.32      (((sk_C_3 @ sk_C_4 @ sk_A)
% 2.13/2.32         = (sk_D_1 @ (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ sk_C_4))),
% 2.13/2.32      inference('demod', [status(thm)], ['75', '190'])).
% 2.13/2.32  thf('192', plain,
% 2.13/2.32      (((k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 2.13/2.32         = (k1_funct_1 @ sk_B_1 @ 
% 2.13/2.32            (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A))))),
% 2.13/2.32      inference('demod', [status(thm)], ['31', '191'])).
% 2.13/2.32  thf('193', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         (((k1_funct_1 @ sk_B_1 @ X0)
% 2.13/2.32            != (k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A)))
% 2.13/2.32          | ((X0) = (sk_C_3 @ sk_C_4 @ sk_A))
% 2.13/2.32          | ~ (r2_hidden @ X0 @ sk_A))),
% 2.13/2.32      inference('demod', [status(thm)], ['148', '156'])).
% 2.13/2.32  thf('194', plain,
% 2.13/2.32      ((((k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 2.13/2.32          != (k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A)))
% 2.13/2.32        | ~ (r2_hidden @ (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ 
% 2.13/2.32             sk_A)
% 2.13/2.32        | ((k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 2.13/2.32            = (sk_C_3 @ sk_C_4 @ sk_A)))),
% 2.13/2.32      inference('sup-', [status(thm)], ['192', '193'])).
% 2.13/2.32  thf('195', plain,
% 2.13/2.32      ((r2_hidden @ (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ sk_A)),
% 2.13/2.32      inference('simplify_reflect-', [status(thm)], ['168', '169'])).
% 2.13/2.32  thf('196', plain,
% 2.13/2.32      ((((k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 2.13/2.32          != (k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A)))
% 2.13/2.32        | ((k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 2.13/2.32            = (sk_C_3 @ sk_C_4 @ sk_A)))),
% 2.13/2.32      inference('demod', [status(thm)], ['194', '195'])).
% 2.13/2.32  thf('197', plain,
% 2.13/2.32      (((k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 2.13/2.32         = (sk_C_3 @ sk_C_4 @ sk_A))),
% 2.13/2.32      inference('simplify', [status(thm)], ['196'])).
% 2.13/2.32  thf('198', plain,
% 2.13/2.32      (((k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 2.13/2.32         != (sk_C_3 @ sk_C_4 @ sk_A))),
% 2.13/2.32      inference('simplify_reflect-', [status(thm)], ['181', '182'])).
% 2.13/2.32  thf('199', plain, ($false),
% 2.13/2.32      inference('simplify_reflect-', [status(thm)], ['197', '198'])).
% 2.13/2.32  
% 2.13/2.32  % SZS output end Refutation
% 2.13/2.32  
% 2.13/2.33  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
