%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5p0LHhXHcq

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:33 EST 2020

% Result     : Theorem 1.01s
% Output     : Refutation 1.01s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 228 expanded)
%              Number of leaves         :   18 (  74 expanded)
%              Depth                    :   28
%              Number of atoms          : 1160 (5196 expanded)
%              Number of equality atoms :   76 ( 532 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_relat_1 @ X6 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X3: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('2',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('3',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k1_relat_1 @ X6 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t60_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k1_relat_1 @ A )
                = ( k2_relat_1 @ B ) )
              & ( ( k2_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ! [C: $i,D: $i] :
                  ( ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                    & ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) )
                 => ( ( ( k1_funct_1 @ A @ C )
                      = D )
                  <=> ( ( k1_funct_1 @ B @ D )
                      = C ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ( ( ( v2_funct_1 @ A )
                & ( ( k1_relat_1 @ A )
                  = ( k2_relat_1 @ B ) )
                & ( ( k2_relat_1 @ A )
                  = ( k1_relat_1 @ B ) )
                & ! [C: $i,D: $i] :
                    ( ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                      & ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) )
                   => ( ( ( k1_funct_1 @ A @ C )
                        = D )
                    <=> ( ( k1_funct_1 @ B @ D )
                        = C ) ) ) )
             => ( B
                = ( k2_funct_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t60_funct_1])).

thf('4',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('6',plain,(
    ! [X3: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('7',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_relat_1 @ X6 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k1_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ! [C: $i] :
                  ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                 => ( ( k1_funct_1 @ A @ C )
                    = ( k1_funct_1 @ B @ C ) ) ) )
           => ( A = B ) ) ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( X10 = X9 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X10 ) @ ( k1_relat_1 @ X10 ) )
      | ( ( k1_relat_1 @ X10 )
       != ( k1_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ ( k2_funct_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ( X1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( X1
        = ( k2_funct_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ ( k2_funct_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X1 )
       != ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ ( k2_funct_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ( X1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X1
        = ( k2_funct_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ ( k2_funct_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X1 )
       != ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ ( k2_funct_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ( X1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_A )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( sk_B_1
        = ( k2_funct_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ ( k2_funct_1 @ X0 ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','13'])).

thf('15',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_A )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( sk_B_1
        = ( k2_funct_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ ( k2_funct_1 @ X0 ) @ sk_B_1 ) @ ( k2_relat_1 @ sk_A ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15','16','17'])).

thf('19',plain,
    ( ~ ( v2_funct_1 @ sk_A )
    | ( r2_hidden @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B_1 ) @ ( k2_relat_1 @ sk_A ) )
    | ( sk_B_1
      = ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('20',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( r2_hidden @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B_1 ) @ ( k2_relat_1 @ sk_A ) )
    | ( sk_B_1
      = ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20','21','22'])).

thf('24',plain,(
    sk_B_1
 != ( k2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    r2_hidden @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B_1 ) @ ( k2_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X3: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('27',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('28',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_relat_1 @ X6 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('29',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k1_relat_1 @ X5 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X5 @ X4 ) @ ( k2_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( r2_hidden @ ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B_1 ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r2_hidden @ ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B_1 ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('40',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B_1 ) ) @ ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['3','39'])).

thf('41',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k2_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    r2_hidden @ ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B_1 ) ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['40','41','42','43','44'])).

thf('46',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ sk_A ) )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( k1_funct_1 @ sk_B_1 @ X12 )
        = X11 )
      | ( ( k1_funct_1 @ sk_A @ X11 )
       != X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X11: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ ( k1_funct_1 @ sk_A @ X11 ) )
        = X11 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_A @ X11 ) @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k2_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X11: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ ( k1_funct_1 @ sk_A @ X11 ) )
        = X11 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_A @ X11 ) @ ( k2_relat_1 @ sk_A ) )
      | ~ ( r2_hidden @ X11 @ ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k2_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k1_relat_1 @ X5 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X5 @ X4 ) @ ( k2_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ! [X11: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k2_relat_1 @ sk_B_1 ) )
      | ( ( k1_funct_1 @ sk_B_1 @ ( k1_funct_1 @ sk_A @ X11 ) )
        = X11 ) ) ),
    inference(clc,[status(thm)],['50','56'])).

thf('58',plain,
    ( ( k1_funct_1 @ sk_B_1 @ ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B_1 ) ) ) )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['45','57'])).

thf('59',plain,(
    r2_hidden @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B_1 ) @ ( k2_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

thf(t57_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( v2_funct_1 @ B )
          & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) )
       => ( ( A
            = ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) )
          & ( A
            = ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) )).

thf('60',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ~ ( r2_hidden @ X8 @ ( k2_relat_1 @ X7 ) )
      | ( X8
        = ( k1_funct_1 @ X7 @ ( k1_funct_1 @ ( k2_funct_1 @ X7 ) @ X8 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t57_funct_1])).

thf('61',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B_1 )
      = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B_1 ) ) ) )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B_1 )
    = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['61','62','63','64'])).

thf('66',plain,
    ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B_1 ) )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['58','65'])).

thf('67',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( X10 = X9 )
      | ( ( k1_funct_1 @ X10 @ ( sk_C_1 @ X9 @ X10 ) )
       != ( k1_funct_1 @ X9 @ ( sk_C_1 @ X9 @ X10 ) ) )
      | ( ( k1_relat_1 @ X10 )
       != ( k1_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('68',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B_1 ) )
     != ( k1_funct_1 @ sk_B_1 @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( ( k1_relat_1 @ sk_B_1 )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
    | ( sk_B_1
      = ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B_1 ) )
     != ( k1_funct_1 @ sk_B_1 @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B_1 ) ) )
    | ( ( k2_relat_1 @ sk_A )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
    | ( sk_B_1
      = ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69','70','71'])).

thf('73',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ( sk_B_1
      = ( k2_funct_1 @ sk_A ) )
    | ( ( k2_relat_1 @ sk_A )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    sk_B_1
 != ( k2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ( ( k2_relat_1 @ sk_A )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( k2_relat_1 @ sk_A )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( k2_relat_1 @ sk_A )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','79'])).

thf('81',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ( k2_relat_1 @ sk_A )
 != ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','83'])).

thf('85',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ( k2_relat_1 @ sk_A )
 != ( k2_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['84','85','86','87'])).

thf('89',plain,(
    $false ),
    inference(simplify,[status(thm)],['88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5p0LHhXHcq
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:43:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.21/0.34  % Running in FO mode
% 1.01/1.19  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.01/1.19  % Solved by: fo/fo7.sh
% 1.01/1.19  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.01/1.19  % done 1103 iterations in 0.745s
% 1.01/1.19  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.01/1.19  % SZS output start Refutation
% 1.01/1.19  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.01/1.19  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.01/1.19  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.01/1.19  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.01/1.19  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.01/1.19  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.01/1.19  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.01/1.19  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.01/1.19  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.01/1.19  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.01/1.19  thf(sk_A_type, type, sk_A: $i).
% 1.01/1.19  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.01/1.19  thf(t55_funct_1, axiom,
% 1.01/1.19    (![A:$i]:
% 1.01/1.19     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.01/1.19       ( ( v2_funct_1 @ A ) =>
% 1.01/1.19         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.01/1.19           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.01/1.19  thf('0', plain,
% 1.01/1.19      (![X6 : $i]:
% 1.01/1.19         (~ (v2_funct_1 @ X6)
% 1.01/1.19          | ((k2_relat_1 @ X6) = (k1_relat_1 @ (k2_funct_1 @ X6)))
% 1.01/1.19          | ~ (v1_funct_1 @ X6)
% 1.01/1.19          | ~ (v1_relat_1 @ X6))),
% 1.01/1.19      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.01/1.19  thf(dt_k2_funct_1, axiom,
% 1.01/1.19    (![A:$i]:
% 1.01/1.19     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.01/1.19       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.01/1.19         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.01/1.19  thf('1', plain,
% 1.01/1.19      (![X3 : $i]:
% 1.01/1.19         ((v1_funct_1 @ (k2_funct_1 @ X3))
% 1.01/1.19          | ~ (v1_funct_1 @ X3)
% 1.01/1.19          | ~ (v1_relat_1 @ X3))),
% 1.01/1.19      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.01/1.19  thf('2', plain,
% 1.01/1.19      (![X3 : $i]:
% 1.01/1.19         ((v1_relat_1 @ (k2_funct_1 @ X3))
% 1.01/1.19          | ~ (v1_funct_1 @ X3)
% 1.01/1.19          | ~ (v1_relat_1 @ X3))),
% 1.01/1.19      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.01/1.19  thf('3', plain,
% 1.01/1.19      (![X6 : $i]:
% 1.01/1.19         (~ (v2_funct_1 @ X6)
% 1.01/1.19          | ((k1_relat_1 @ X6) = (k2_relat_1 @ (k2_funct_1 @ X6)))
% 1.01/1.19          | ~ (v1_funct_1 @ X6)
% 1.01/1.19          | ~ (v1_relat_1 @ X6))),
% 1.01/1.19      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.01/1.19  thf(t60_funct_1, conjecture,
% 1.01/1.19    (![A:$i]:
% 1.01/1.19     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.01/1.19       ( ![B:$i]:
% 1.01/1.19         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.01/1.19           ( ( ( v2_funct_1 @ A ) & 
% 1.01/1.19               ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ B ) ) & 
% 1.01/1.19               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 1.01/1.19               ( ![C:$i,D:$i]:
% 1.01/1.19                 ( ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 1.01/1.19                     ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) ) =>
% 1.01/1.19                   ( ( ( k1_funct_1 @ A @ C ) = ( D ) ) <=>
% 1.01/1.19                     ( ( k1_funct_1 @ B @ D ) = ( C ) ) ) ) ) ) =>
% 1.01/1.19             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.01/1.19  thf(zf_stmt_0, negated_conjecture,
% 1.01/1.19    (~( ![A:$i]:
% 1.01/1.19        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.01/1.19          ( ![B:$i]:
% 1.01/1.19            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.01/1.19              ( ( ( v2_funct_1 @ A ) & 
% 1.01/1.19                  ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ B ) ) & 
% 1.01/1.19                  ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 1.01/1.19                  ( ![C:$i,D:$i]:
% 1.01/1.19                    ( ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 1.01/1.19                        ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) ) =>
% 1.01/1.19                      ( ( ( k1_funct_1 @ A @ C ) = ( D ) ) <=>
% 1.01/1.19                        ( ( k1_funct_1 @ B @ D ) = ( C ) ) ) ) ) ) =>
% 1.01/1.19                ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ) )),
% 1.01/1.19    inference('cnf.neg', [status(esa)], [t60_funct_1])).
% 1.01/1.19  thf('4', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B_1))),
% 1.01/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.19  thf('5', plain,
% 1.01/1.19      (![X3 : $i]:
% 1.01/1.19         ((v1_relat_1 @ (k2_funct_1 @ X3))
% 1.01/1.19          | ~ (v1_funct_1 @ X3)
% 1.01/1.19          | ~ (v1_relat_1 @ X3))),
% 1.01/1.19      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.01/1.19  thf('6', plain,
% 1.01/1.19      (![X3 : $i]:
% 1.01/1.19         ((v1_funct_1 @ (k2_funct_1 @ X3))
% 1.01/1.19          | ~ (v1_funct_1 @ X3)
% 1.01/1.19          | ~ (v1_relat_1 @ X3))),
% 1.01/1.19      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.01/1.19  thf('7', plain,
% 1.01/1.19      (![X6 : $i]:
% 1.01/1.19         (~ (v2_funct_1 @ X6)
% 1.01/1.19          | ((k2_relat_1 @ X6) = (k1_relat_1 @ (k2_funct_1 @ X6)))
% 1.01/1.19          | ~ (v1_funct_1 @ X6)
% 1.01/1.19          | ~ (v1_relat_1 @ X6))),
% 1.01/1.19      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.01/1.19  thf(t9_funct_1, axiom,
% 1.01/1.19    (![A:$i]:
% 1.01/1.19     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.01/1.19       ( ![B:$i]:
% 1.01/1.19         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.01/1.19           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 1.01/1.19               ( ![C:$i]:
% 1.01/1.19                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 1.01/1.19                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 1.01/1.19             ( ( A ) = ( B ) ) ) ) ) ))).
% 1.01/1.19  thf('8', plain,
% 1.01/1.19      (![X9 : $i, X10 : $i]:
% 1.01/1.19         (~ (v1_relat_1 @ X9)
% 1.01/1.19          | ~ (v1_funct_1 @ X9)
% 1.01/1.19          | ((X10) = (X9))
% 1.01/1.19          | (r2_hidden @ (sk_C_1 @ X9 @ X10) @ (k1_relat_1 @ X10))
% 1.01/1.19          | ((k1_relat_1 @ X10) != (k1_relat_1 @ X9))
% 1.01/1.19          | ~ (v1_funct_1 @ X10)
% 1.01/1.19          | ~ (v1_relat_1 @ X10))),
% 1.01/1.19      inference('cnf', [status(esa)], [t9_funct_1])).
% 1.01/1.19  thf('9', plain,
% 1.01/1.19      (![X0 : $i, X1 : $i]:
% 1.01/1.19         (((k1_relat_1 @ X1) != (k2_relat_1 @ X0))
% 1.01/1.19          | ~ (v1_relat_1 @ X0)
% 1.01/1.19          | ~ (v1_funct_1 @ X0)
% 1.01/1.19          | ~ (v2_funct_1 @ X0)
% 1.01/1.19          | ~ (v1_relat_1 @ X1)
% 1.01/1.19          | ~ (v1_funct_1 @ X1)
% 1.01/1.19          | (r2_hidden @ (sk_C_1 @ (k2_funct_1 @ X0) @ X1) @ (k1_relat_1 @ X1))
% 1.01/1.19          | ((X1) = (k2_funct_1 @ X0))
% 1.01/1.19          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.01/1.19          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.01/1.19      inference('sup-', [status(thm)], ['7', '8'])).
% 1.01/1.19  thf('10', plain,
% 1.01/1.19      (![X0 : $i, X1 : $i]:
% 1.01/1.19         (~ (v1_relat_1 @ X0)
% 1.01/1.19          | ~ (v1_funct_1 @ X0)
% 1.01/1.19          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.01/1.19          | ((X1) = (k2_funct_1 @ X0))
% 1.01/1.19          | (r2_hidden @ (sk_C_1 @ (k2_funct_1 @ X0) @ X1) @ (k1_relat_1 @ X1))
% 1.01/1.19          | ~ (v1_funct_1 @ X1)
% 1.01/1.19          | ~ (v1_relat_1 @ X1)
% 1.01/1.19          | ~ (v2_funct_1 @ X0)
% 1.01/1.19          | ~ (v1_funct_1 @ X0)
% 1.01/1.19          | ~ (v1_relat_1 @ X0)
% 1.01/1.19          | ((k1_relat_1 @ X1) != (k2_relat_1 @ X0)))),
% 1.01/1.19      inference('sup-', [status(thm)], ['6', '9'])).
% 1.01/1.19  thf('11', plain,
% 1.01/1.19      (![X0 : $i, X1 : $i]:
% 1.01/1.19         (((k1_relat_1 @ X1) != (k2_relat_1 @ X0))
% 1.01/1.19          | ~ (v2_funct_1 @ X0)
% 1.01/1.19          | ~ (v1_relat_1 @ X1)
% 1.01/1.19          | ~ (v1_funct_1 @ X1)
% 1.01/1.19          | (r2_hidden @ (sk_C_1 @ (k2_funct_1 @ X0) @ X1) @ (k1_relat_1 @ X1))
% 1.01/1.19          | ((X1) = (k2_funct_1 @ X0))
% 1.01/1.19          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.01/1.19          | ~ (v1_funct_1 @ X0)
% 1.01/1.19          | ~ (v1_relat_1 @ X0))),
% 1.01/1.19      inference('simplify', [status(thm)], ['10'])).
% 1.01/1.19  thf('12', plain,
% 1.01/1.19      (![X0 : $i, X1 : $i]:
% 1.01/1.19         (~ (v1_relat_1 @ X0)
% 1.01/1.19          | ~ (v1_funct_1 @ X0)
% 1.01/1.19          | ~ (v1_relat_1 @ X0)
% 1.01/1.19          | ~ (v1_funct_1 @ X0)
% 1.01/1.19          | ((X1) = (k2_funct_1 @ X0))
% 1.01/1.19          | (r2_hidden @ (sk_C_1 @ (k2_funct_1 @ X0) @ X1) @ (k1_relat_1 @ X1))
% 1.01/1.19          | ~ (v1_funct_1 @ X1)
% 1.01/1.19          | ~ (v1_relat_1 @ X1)
% 1.01/1.19          | ~ (v2_funct_1 @ X0)
% 1.01/1.19          | ((k1_relat_1 @ X1) != (k2_relat_1 @ X0)))),
% 1.01/1.19      inference('sup-', [status(thm)], ['5', '11'])).
% 1.01/1.19  thf('13', plain,
% 1.01/1.19      (![X0 : $i, X1 : $i]:
% 1.01/1.19         (((k1_relat_1 @ X1) != (k2_relat_1 @ X0))
% 1.01/1.19          | ~ (v2_funct_1 @ X0)
% 1.01/1.19          | ~ (v1_relat_1 @ X1)
% 1.01/1.19          | ~ (v1_funct_1 @ X1)
% 1.01/1.19          | (r2_hidden @ (sk_C_1 @ (k2_funct_1 @ X0) @ X1) @ (k1_relat_1 @ X1))
% 1.01/1.19          | ((X1) = (k2_funct_1 @ X0))
% 1.01/1.19          | ~ (v1_funct_1 @ X0)
% 1.01/1.19          | ~ (v1_relat_1 @ X0))),
% 1.01/1.19      inference('simplify', [status(thm)], ['12'])).
% 1.01/1.19  thf('14', plain,
% 1.01/1.19      (![X0 : $i]:
% 1.01/1.19         (((k2_relat_1 @ sk_A) != (k2_relat_1 @ X0))
% 1.01/1.19          | ~ (v1_relat_1 @ X0)
% 1.01/1.19          | ~ (v1_funct_1 @ X0)
% 1.01/1.19          | ((sk_B_1) = (k2_funct_1 @ X0))
% 1.01/1.19          | (r2_hidden @ (sk_C_1 @ (k2_funct_1 @ X0) @ sk_B_1) @ 
% 1.01/1.19             (k1_relat_1 @ sk_B_1))
% 1.01/1.19          | ~ (v1_funct_1 @ sk_B_1)
% 1.01/1.19          | ~ (v1_relat_1 @ sk_B_1)
% 1.01/1.19          | ~ (v2_funct_1 @ X0))),
% 1.01/1.19      inference('sup-', [status(thm)], ['4', '13'])).
% 1.01/1.19  thf('15', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B_1))),
% 1.01/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.19  thf('16', plain, ((v1_funct_1 @ sk_B_1)),
% 1.01/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.19  thf('17', plain, ((v1_relat_1 @ sk_B_1)),
% 1.01/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.19  thf('18', plain,
% 1.01/1.19      (![X0 : $i]:
% 1.01/1.19         (((k2_relat_1 @ sk_A) != (k2_relat_1 @ X0))
% 1.01/1.19          | ~ (v1_relat_1 @ X0)
% 1.01/1.19          | ~ (v1_funct_1 @ X0)
% 1.01/1.19          | ((sk_B_1) = (k2_funct_1 @ X0))
% 1.01/1.19          | (r2_hidden @ (sk_C_1 @ (k2_funct_1 @ X0) @ sk_B_1) @ 
% 1.01/1.19             (k2_relat_1 @ sk_A))
% 1.01/1.19          | ~ (v2_funct_1 @ X0))),
% 1.01/1.19      inference('demod', [status(thm)], ['14', '15', '16', '17'])).
% 1.01/1.19  thf('19', plain,
% 1.01/1.19      ((~ (v2_funct_1 @ sk_A)
% 1.01/1.19        | (r2_hidden @ (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B_1) @ 
% 1.01/1.19           (k2_relat_1 @ sk_A))
% 1.01/1.19        | ((sk_B_1) = (k2_funct_1 @ sk_A))
% 1.01/1.19        | ~ (v1_funct_1 @ sk_A)
% 1.01/1.19        | ~ (v1_relat_1 @ sk_A))),
% 1.01/1.19      inference('eq_res', [status(thm)], ['18'])).
% 1.01/1.19  thf('20', plain, ((v2_funct_1 @ sk_A)),
% 1.01/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.19  thf('21', plain, ((v1_funct_1 @ sk_A)),
% 1.01/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.19  thf('22', plain, ((v1_relat_1 @ sk_A)),
% 1.01/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.19  thf('23', plain,
% 1.01/1.19      (((r2_hidden @ (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B_1) @ 
% 1.01/1.19         (k2_relat_1 @ sk_A))
% 1.01/1.19        | ((sk_B_1) = (k2_funct_1 @ sk_A)))),
% 1.01/1.19      inference('demod', [status(thm)], ['19', '20', '21', '22'])).
% 1.01/1.19  thf('24', plain, (((sk_B_1) != (k2_funct_1 @ sk_A))),
% 1.01/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.19  thf('25', plain,
% 1.01/1.19      ((r2_hidden @ (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B_1) @ 
% 1.01/1.19        (k2_relat_1 @ sk_A))),
% 1.01/1.19      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 1.01/1.19  thf('26', plain,
% 1.01/1.19      (![X3 : $i]:
% 1.01/1.19         ((v1_funct_1 @ (k2_funct_1 @ X3))
% 1.01/1.19          | ~ (v1_funct_1 @ X3)
% 1.01/1.19          | ~ (v1_relat_1 @ X3))),
% 1.01/1.19      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.01/1.19  thf('27', plain,
% 1.01/1.19      (![X3 : $i]:
% 1.01/1.19         ((v1_relat_1 @ (k2_funct_1 @ X3))
% 1.01/1.19          | ~ (v1_funct_1 @ X3)
% 1.01/1.19          | ~ (v1_relat_1 @ X3))),
% 1.01/1.19      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.01/1.19  thf('28', plain,
% 1.01/1.19      (![X6 : $i]:
% 1.01/1.19         (~ (v2_funct_1 @ X6)
% 1.01/1.19          | ((k2_relat_1 @ X6) = (k1_relat_1 @ (k2_funct_1 @ X6)))
% 1.01/1.19          | ~ (v1_funct_1 @ X6)
% 1.01/1.19          | ~ (v1_relat_1 @ X6))),
% 1.01/1.19      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.01/1.19  thf(t12_funct_1, axiom,
% 1.01/1.19    (![A:$i,B:$i]:
% 1.01/1.19     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.01/1.19       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 1.01/1.19         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 1.01/1.19  thf('29', plain,
% 1.01/1.19      (![X4 : $i, X5 : $i]:
% 1.01/1.19         (~ (r2_hidden @ X4 @ (k1_relat_1 @ X5))
% 1.01/1.19          | (r2_hidden @ (k1_funct_1 @ X5 @ X4) @ (k2_relat_1 @ X5))
% 1.01/1.19          | ~ (v1_funct_1 @ X5)
% 1.01/1.19          | ~ (v1_relat_1 @ X5))),
% 1.01/1.19      inference('cnf', [status(esa)], [t12_funct_1])).
% 1.01/1.19  thf('30', plain,
% 1.01/1.19      (![X0 : $i, X1 : $i]:
% 1.01/1.19         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 1.01/1.19          | ~ (v1_relat_1 @ X0)
% 1.01/1.19          | ~ (v1_funct_1 @ X0)
% 1.01/1.19          | ~ (v2_funct_1 @ X0)
% 1.01/1.19          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.01/1.19          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.01/1.19          | (r2_hidden @ (k1_funct_1 @ (k2_funct_1 @ X0) @ X1) @ 
% 1.01/1.19             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 1.01/1.19      inference('sup-', [status(thm)], ['28', '29'])).
% 1.01/1.19  thf('31', plain,
% 1.01/1.19      (![X0 : $i, X1 : $i]:
% 1.01/1.19         (~ (v1_relat_1 @ X0)
% 1.01/1.19          | ~ (v1_funct_1 @ X0)
% 1.01/1.19          | (r2_hidden @ (k1_funct_1 @ (k2_funct_1 @ X0) @ X1) @ 
% 1.01/1.19             (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.01/1.19          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.01/1.19          | ~ (v2_funct_1 @ X0)
% 1.01/1.19          | ~ (v1_funct_1 @ X0)
% 1.01/1.19          | ~ (v1_relat_1 @ X0)
% 1.01/1.19          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 1.01/1.19      inference('sup-', [status(thm)], ['27', '30'])).
% 1.01/1.19  thf('32', plain,
% 1.01/1.19      (![X0 : $i, X1 : $i]:
% 1.01/1.19         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 1.01/1.19          | ~ (v2_funct_1 @ X0)
% 1.01/1.19          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.01/1.19          | (r2_hidden @ (k1_funct_1 @ (k2_funct_1 @ X0) @ X1) @ 
% 1.01/1.19             (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.01/1.19          | ~ (v1_funct_1 @ X0)
% 1.01/1.19          | ~ (v1_relat_1 @ X0))),
% 1.01/1.19      inference('simplify', [status(thm)], ['31'])).
% 1.01/1.19  thf('33', plain,
% 1.01/1.19      (![X0 : $i, X1 : $i]:
% 1.01/1.19         (~ (v1_relat_1 @ X0)
% 1.01/1.19          | ~ (v1_funct_1 @ X0)
% 1.01/1.19          | ~ (v1_relat_1 @ X0)
% 1.01/1.19          | ~ (v1_funct_1 @ X0)
% 1.01/1.19          | (r2_hidden @ (k1_funct_1 @ (k2_funct_1 @ X0) @ X1) @ 
% 1.01/1.19             (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.01/1.19          | ~ (v2_funct_1 @ X0)
% 1.01/1.19          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 1.01/1.19      inference('sup-', [status(thm)], ['26', '32'])).
% 1.01/1.19  thf('34', plain,
% 1.01/1.19      (![X0 : $i, X1 : $i]:
% 1.01/1.19         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 1.01/1.19          | ~ (v2_funct_1 @ X0)
% 1.01/1.19          | (r2_hidden @ (k1_funct_1 @ (k2_funct_1 @ X0) @ X1) @ 
% 1.01/1.19             (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.01/1.19          | ~ (v1_funct_1 @ X0)
% 1.01/1.19          | ~ (v1_relat_1 @ X0))),
% 1.01/1.19      inference('simplify', [status(thm)], ['33'])).
% 1.01/1.19  thf('35', plain,
% 1.01/1.19      ((~ (v1_relat_1 @ sk_A)
% 1.01/1.19        | ~ (v1_funct_1 @ sk_A)
% 1.01/1.19        | (r2_hidden @ 
% 1.01/1.19           (k1_funct_1 @ (k2_funct_1 @ sk_A) @ 
% 1.01/1.19            (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B_1)) @ 
% 1.01/1.19           (k2_relat_1 @ (k2_funct_1 @ sk_A)))
% 1.01/1.19        | ~ (v2_funct_1 @ sk_A))),
% 1.01/1.19      inference('sup-', [status(thm)], ['25', '34'])).
% 1.01/1.19  thf('36', plain, ((v1_relat_1 @ sk_A)),
% 1.01/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.19  thf('37', plain, ((v1_funct_1 @ sk_A)),
% 1.01/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.19  thf('38', plain, ((v2_funct_1 @ sk_A)),
% 1.01/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.19  thf('39', plain,
% 1.01/1.19      ((r2_hidden @ 
% 1.01/1.19        (k1_funct_1 @ (k2_funct_1 @ sk_A) @ 
% 1.01/1.19         (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B_1)) @ 
% 1.01/1.19        (k2_relat_1 @ (k2_funct_1 @ sk_A)))),
% 1.01/1.19      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 1.01/1.19  thf('40', plain,
% 1.01/1.19      (((r2_hidden @ 
% 1.01/1.19         (k1_funct_1 @ (k2_funct_1 @ sk_A) @ 
% 1.01/1.19          (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B_1)) @ 
% 1.01/1.19         (k1_relat_1 @ sk_A))
% 1.01/1.19        | ~ (v1_relat_1 @ sk_A)
% 1.01/1.19        | ~ (v1_funct_1 @ sk_A)
% 1.01/1.19        | ~ (v2_funct_1 @ sk_A))),
% 1.01/1.19      inference('sup+', [status(thm)], ['3', '39'])).
% 1.01/1.19  thf('41', plain, (((k1_relat_1 @ sk_A) = (k2_relat_1 @ sk_B_1))),
% 1.01/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.19  thf('42', plain, ((v1_relat_1 @ sk_A)),
% 1.01/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.19  thf('43', plain, ((v1_funct_1 @ sk_A)),
% 1.01/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.19  thf('44', plain, ((v2_funct_1 @ sk_A)),
% 1.01/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.19  thf('45', plain,
% 1.01/1.19      ((r2_hidden @ 
% 1.01/1.19        (k1_funct_1 @ (k2_funct_1 @ sk_A) @ 
% 1.01/1.19         (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B_1)) @ 
% 1.01/1.19        (k2_relat_1 @ sk_B_1))),
% 1.01/1.19      inference('demod', [status(thm)], ['40', '41', '42', '43', '44'])).
% 1.01/1.19  thf('46', plain,
% 1.01/1.19      (![X11 : $i, X12 : $i]:
% 1.01/1.19         (~ (r2_hidden @ X11 @ (k1_relat_1 @ sk_A))
% 1.01/1.19          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ sk_B_1))
% 1.01/1.19          | ((k1_funct_1 @ sk_B_1 @ X12) = (X11))
% 1.01/1.19          | ((k1_funct_1 @ sk_A @ X11) != (X12)))),
% 1.01/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.19  thf('47', plain,
% 1.01/1.19      (![X11 : $i]:
% 1.01/1.19         (((k1_funct_1 @ sk_B_1 @ (k1_funct_1 @ sk_A @ X11)) = (X11))
% 1.01/1.19          | ~ (r2_hidden @ (k1_funct_1 @ sk_A @ X11) @ (k1_relat_1 @ sk_B_1))
% 1.01/1.19          | ~ (r2_hidden @ X11 @ (k1_relat_1 @ sk_A)))),
% 1.01/1.19      inference('simplify', [status(thm)], ['46'])).
% 1.01/1.19  thf('48', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B_1))),
% 1.01/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.19  thf('49', plain, (((k1_relat_1 @ sk_A) = (k2_relat_1 @ sk_B_1))),
% 1.01/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.19  thf('50', plain,
% 1.01/1.19      (![X11 : $i]:
% 1.01/1.19         (((k1_funct_1 @ sk_B_1 @ (k1_funct_1 @ sk_A @ X11)) = (X11))
% 1.01/1.19          | ~ (r2_hidden @ (k1_funct_1 @ sk_A @ X11) @ (k2_relat_1 @ sk_A))
% 1.01/1.19          | ~ (r2_hidden @ X11 @ (k2_relat_1 @ sk_B_1)))),
% 1.01/1.19      inference('demod', [status(thm)], ['47', '48', '49'])).
% 1.01/1.19  thf('51', plain, (((k1_relat_1 @ sk_A) = (k2_relat_1 @ sk_B_1))),
% 1.01/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.19  thf('52', plain,
% 1.01/1.19      (![X4 : $i, X5 : $i]:
% 1.01/1.19         (~ (r2_hidden @ X4 @ (k1_relat_1 @ X5))
% 1.01/1.19          | (r2_hidden @ (k1_funct_1 @ X5 @ X4) @ (k2_relat_1 @ X5))
% 1.01/1.19          | ~ (v1_funct_1 @ X5)
% 1.01/1.19          | ~ (v1_relat_1 @ X5))),
% 1.01/1.19      inference('cnf', [status(esa)], [t12_funct_1])).
% 1.01/1.19  thf('53', plain,
% 1.01/1.19      (![X0 : $i]:
% 1.01/1.19         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B_1))
% 1.01/1.19          | ~ (v1_relat_1 @ sk_A)
% 1.01/1.19          | ~ (v1_funct_1 @ sk_A)
% 1.01/1.19          | (r2_hidden @ (k1_funct_1 @ sk_A @ X0) @ (k2_relat_1 @ sk_A)))),
% 1.01/1.19      inference('sup-', [status(thm)], ['51', '52'])).
% 1.01/1.19  thf('54', plain, ((v1_relat_1 @ sk_A)),
% 1.01/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.19  thf('55', plain, ((v1_funct_1 @ sk_A)),
% 1.01/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.19  thf('56', plain,
% 1.01/1.19      (![X0 : $i]:
% 1.01/1.19         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B_1))
% 1.01/1.19          | (r2_hidden @ (k1_funct_1 @ sk_A @ X0) @ (k2_relat_1 @ sk_A)))),
% 1.01/1.19      inference('demod', [status(thm)], ['53', '54', '55'])).
% 1.01/1.19  thf('57', plain,
% 1.01/1.19      (![X11 : $i]:
% 1.01/1.19         (~ (r2_hidden @ X11 @ (k2_relat_1 @ sk_B_1))
% 1.01/1.19          | ((k1_funct_1 @ sk_B_1 @ (k1_funct_1 @ sk_A @ X11)) = (X11)))),
% 1.01/1.19      inference('clc', [status(thm)], ['50', '56'])).
% 1.01/1.19  thf('58', plain,
% 1.01/1.19      (((k1_funct_1 @ sk_B_1 @ 
% 1.01/1.19         (k1_funct_1 @ sk_A @ 
% 1.01/1.19          (k1_funct_1 @ (k2_funct_1 @ sk_A) @ 
% 1.01/1.19           (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B_1))))
% 1.01/1.19         = (k1_funct_1 @ (k2_funct_1 @ sk_A) @ 
% 1.01/1.19            (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B_1)))),
% 1.01/1.19      inference('sup-', [status(thm)], ['45', '57'])).
% 1.01/1.19  thf('59', plain,
% 1.01/1.19      ((r2_hidden @ (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B_1) @ 
% 1.01/1.19        (k2_relat_1 @ sk_A))),
% 1.01/1.19      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 1.01/1.19  thf(t57_funct_1, axiom,
% 1.01/1.19    (![A:$i,B:$i]:
% 1.01/1.19     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.01/1.19       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 1.01/1.19         ( ( ( A ) =
% 1.01/1.19             ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 1.01/1.19           ( ( A ) =
% 1.01/1.19             ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ))).
% 1.01/1.19  thf('60', plain,
% 1.01/1.19      (![X7 : $i, X8 : $i]:
% 1.01/1.19         (~ (v2_funct_1 @ X7)
% 1.01/1.19          | ~ (r2_hidden @ X8 @ (k2_relat_1 @ X7))
% 1.01/1.19          | ((X8) = (k1_funct_1 @ X7 @ (k1_funct_1 @ (k2_funct_1 @ X7) @ X8)))
% 1.01/1.19          | ~ (v1_funct_1 @ X7)
% 1.01/1.19          | ~ (v1_relat_1 @ X7))),
% 1.01/1.19      inference('cnf', [status(esa)], [t57_funct_1])).
% 1.01/1.19  thf('61', plain,
% 1.01/1.19      ((~ (v1_relat_1 @ sk_A)
% 1.01/1.19        | ~ (v1_funct_1 @ sk_A)
% 1.01/1.19        | ((sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B_1)
% 1.01/1.19            = (k1_funct_1 @ sk_A @ 
% 1.01/1.19               (k1_funct_1 @ (k2_funct_1 @ sk_A) @ 
% 1.01/1.19                (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B_1))))
% 1.01/1.19        | ~ (v2_funct_1 @ sk_A))),
% 1.01/1.19      inference('sup-', [status(thm)], ['59', '60'])).
% 1.01/1.19  thf('62', plain, ((v1_relat_1 @ sk_A)),
% 1.01/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.19  thf('63', plain, ((v1_funct_1 @ sk_A)),
% 1.01/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.19  thf('64', plain, ((v2_funct_1 @ sk_A)),
% 1.01/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.19  thf('65', plain,
% 1.01/1.19      (((sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B_1)
% 1.01/1.19         = (k1_funct_1 @ sk_A @ 
% 1.01/1.19            (k1_funct_1 @ (k2_funct_1 @ sk_A) @ 
% 1.01/1.19             (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B_1))))),
% 1.01/1.19      inference('demod', [status(thm)], ['61', '62', '63', '64'])).
% 1.01/1.19  thf('66', plain,
% 1.01/1.19      (((k1_funct_1 @ sk_B_1 @ (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B_1))
% 1.01/1.19         = (k1_funct_1 @ (k2_funct_1 @ sk_A) @ 
% 1.01/1.19            (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B_1)))),
% 1.01/1.19      inference('demod', [status(thm)], ['58', '65'])).
% 1.01/1.19  thf('67', plain,
% 1.01/1.19      (![X9 : $i, X10 : $i]:
% 1.01/1.19         (~ (v1_relat_1 @ X9)
% 1.01/1.19          | ~ (v1_funct_1 @ X9)
% 1.01/1.19          | ((X10) = (X9))
% 1.01/1.19          | ((k1_funct_1 @ X10 @ (sk_C_1 @ X9 @ X10))
% 1.01/1.19              != (k1_funct_1 @ X9 @ (sk_C_1 @ X9 @ X10)))
% 1.01/1.19          | ((k1_relat_1 @ X10) != (k1_relat_1 @ X9))
% 1.01/1.19          | ~ (v1_funct_1 @ X10)
% 1.01/1.19          | ~ (v1_relat_1 @ X10))),
% 1.01/1.19      inference('cnf', [status(esa)], [t9_funct_1])).
% 1.01/1.19  thf('68', plain,
% 1.01/1.19      ((((k1_funct_1 @ sk_B_1 @ (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B_1))
% 1.01/1.19          != (k1_funct_1 @ sk_B_1 @ (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B_1)))
% 1.01/1.19        | ~ (v1_relat_1 @ sk_B_1)
% 1.01/1.19        | ~ (v1_funct_1 @ sk_B_1)
% 1.01/1.19        | ((k1_relat_1 @ sk_B_1) != (k1_relat_1 @ (k2_funct_1 @ sk_A)))
% 1.01/1.19        | ((sk_B_1) = (k2_funct_1 @ sk_A))
% 1.01/1.19        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 1.01/1.19        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 1.01/1.19      inference('sup-', [status(thm)], ['66', '67'])).
% 1.01/1.19  thf('69', plain, ((v1_relat_1 @ sk_B_1)),
% 1.01/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.19  thf('70', plain, ((v1_funct_1 @ sk_B_1)),
% 1.01/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.19  thf('71', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B_1))),
% 1.01/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.19  thf('72', plain,
% 1.01/1.19      ((((k1_funct_1 @ sk_B_1 @ (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B_1))
% 1.01/1.19          != (k1_funct_1 @ sk_B_1 @ (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B_1)))
% 1.01/1.19        | ((k2_relat_1 @ sk_A) != (k1_relat_1 @ (k2_funct_1 @ sk_A)))
% 1.01/1.19        | ((sk_B_1) = (k2_funct_1 @ sk_A))
% 1.01/1.19        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 1.01/1.19        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 1.01/1.19      inference('demod', [status(thm)], ['68', '69', '70', '71'])).
% 1.01/1.19  thf('73', plain,
% 1.01/1.19      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 1.01/1.19        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 1.01/1.19        | ((sk_B_1) = (k2_funct_1 @ sk_A))
% 1.01/1.19        | ((k2_relat_1 @ sk_A) != (k1_relat_1 @ (k2_funct_1 @ sk_A))))),
% 1.01/1.19      inference('simplify', [status(thm)], ['72'])).
% 1.01/1.19  thf('74', plain, (((sk_B_1) != (k2_funct_1 @ sk_A))),
% 1.01/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.19  thf('75', plain,
% 1.01/1.19      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 1.01/1.19        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 1.01/1.19        | ((k2_relat_1 @ sk_A) != (k1_relat_1 @ (k2_funct_1 @ sk_A))))),
% 1.01/1.19      inference('simplify_reflect-', [status(thm)], ['73', '74'])).
% 1.01/1.19  thf('76', plain,
% 1.01/1.19      ((~ (v1_relat_1 @ sk_A)
% 1.01/1.19        | ~ (v1_funct_1 @ sk_A)
% 1.01/1.19        | ((k2_relat_1 @ sk_A) != (k1_relat_1 @ (k2_funct_1 @ sk_A)))
% 1.01/1.19        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A)))),
% 1.01/1.19      inference('sup-', [status(thm)], ['2', '75'])).
% 1.01/1.19  thf('77', plain, ((v1_relat_1 @ sk_A)),
% 1.01/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.19  thf('78', plain, ((v1_funct_1 @ sk_A)),
% 1.01/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.19  thf('79', plain,
% 1.01/1.19      ((((k2_relat_1 @ sk_A) != (k1_relat_1 @ (k2_funct_1 @ sk_A)))
% 1.01/1.19        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A)))),
% 1.01/1.19      inference('demod', [status(thm)], ['76', '77', '78'])).
% 1.01/1.19  thf('80', plain,
% 1.01/1.19      ((~ (v1_relat_1 @ sk_A)
% 1.01/1.19        | ~ (v1_funct_1 @ sk_A)
% 1.01/1.19        | ((k2_relat_1 @ sk_A) != (k1_relat_1 @ (k2_funct_1 @ sk_A))))),
% 1.01/1.19      inference('sup-', [status(thm)], ['1', '79'])).
% 1.01/1.19  thf('81', plain, ((v1_relat_1 @ sk_A)),
% 1.01/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.19  thf('82', plain, ((v1_funct_1 @ sk_A)),
% 1.01/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.19  thf('83', plain,
% 1.01/1.19      (((k2_relat_1 @ sk_A) != (k1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 1.01/1.19      inference('demod', [status(thm)], ['80', '81', '82'])).
% 1.01/1.19  thf('84', plain,
% 1.01/1.19      ((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))
% 1.01/1.19        | ~ (v1_relat_1 @ sk_A)
% 1.01/1.19        | ~ (v1_funct_1 @ sk_A)
% 1.01/1.19        | ~ (v2_funct_1 @ sk_A))),
% 1.01/1.19      inference('sup-', [status(thm)], ['0', '83'])).
% 1.01/1.19  thf('85', plain, ((v1_relat_1 @ sk_A)),
% 1.01/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.19  thf('86', plain, ((v1_funct_1 @ sk_A)),
% 1.01/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.19  thf('87', plain, ((v2_funct_1 @ sk_A)),
% 1.01/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.19  thf('88', plain, (((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))),
% 1.01/1.19      inference('demod', [status(thm)], ['84', '85', '86', '87'])).
% 1.01/1.19  thf('89', plain, ($false), inference('simplify', [status(thm)], ['88'])).
% 1.01/1.19  
% 1.01/1.19  % SZS output end Refutation
% 1.01/1.19  
% 1.05/1.20  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
