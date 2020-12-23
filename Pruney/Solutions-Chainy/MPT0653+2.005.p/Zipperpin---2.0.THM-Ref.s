%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LLIWy9SacP

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:33 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 206 expanded)
%              Number of leaves         :   18 (  67 expanded)
%              Depth                    :   25
%              Number of atoms          :  959 (4724 expanded)
%              Number of equality atoms :   75 ( 498 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

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
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k2_relat_1 @ X3 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X3 ) ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

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

thf('3',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('6',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k2_relat_1 @ X3 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X3 ) ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
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

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( X7 = X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X7 ) @ ( k1_relat_1 @ X7 ) )
      | ( ( k1_relat_1 @ X7 )
       != ( k1_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ ( k2_funct_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ( X1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( X1
        = ( k2_funct_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k2_funct_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X1 )
       != ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ ( k2_funct_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ( X1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X1
        = ( k2_funct_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k2_funct_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X1 )
       != ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ ( k2_funct_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ( X1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_A )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( sk_B
        = ( k2_funct_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k2_funct_1 @ X0 ) @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','12'])).

thf('14',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_A )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( sk_B
        = ( k2_funct_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k2_funct_1 @ X0 ) @ sk_B ) @ ( k2_relat_1 @ sk_A ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('18',plain,
    ( ~ ( v2_funct_1 @ sk_A )
    | ( r2_hidden @ ( sk_C @ ( k2_funct_1 @ sk_A ) @ sk_B ) @ ( k2_relat_1 @ sk_A ) )
    | ( sk_B
      = ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference(eq_res,[status(thm)],['17'])).

thf('19',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( r2_hidden @ ( sk_C @ ( k2_funct_1 @ sk_A ) @ sk_B ) @ ( k2_relat_1 @ sk_A ) )
    | ( sk_B
      = ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19','20','21'])).

thf('23',plain,(
    sk_B
 != ( k2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r2_hidden @ ( sk_C @ ( k2_funct_1 @ sk_A ) @ sk_B ) @ ( k2_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('26',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X2 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X2 @ X1 ) @ ( k2_relat_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_A ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_C @ ( k2_funct_1 @ sk_A ) @ sk_B ) ) @ ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t56_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( v2_funct_1 @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) )
       => ( ( A
            = ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) )
          & ( A
            = ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ) )).

thf('33',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ~ ( r2_hidden @ X5 @ ( k1_relat_1 @ X4 ) )
      | ( X5
        = ( k1_funct_1 @ ( k2_funct_1 @ X4 ) @ ( k1_funct_1 @ X4 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t56_funct_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( X0
        = ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( k1_funct_1 @ sk_A @ X0 ) ) )
      | ~ ( v2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ( X0
        = ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( k1_funct_1 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf('39',plain,
    ( ( k1_funct_1 @ sk_B @ ( sk_C @ ( k2_funct_1 @ sk_A ) @ sk_B ) )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B @ ( sk_C @ ( k2_funct_1 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['31','38'])).

thf('40',plain,(
    r2_hidden @ ( sk_C @ ( k2_funct_1 @ sk_A ) @ sk_B ) @ ( k2_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf('41',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ sk_A ) )
      | ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ sk_B ) )
      | ( ( k1_funct_1 @ sk_A @ X8 )
        = X9 )
      | ( ( k1_funct_1 @ sk_B @ X9 )
       != X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X9: $i] :
      ( ( ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B @ X9 ) )
        = X9 )
      | ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ X9 ) @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X9: $i] :
      ( ( ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B @ X9 ) )
        = X9 )
      | ~ ( r2_hidden @ X9 @ ( k2_relat_1 @ sk_A ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ X9 ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_A ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('47',plain,(
    ! [X9: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k2_relat_1 @ sk_A ) )
      | ( ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B @ X9 ) )
        = X9 ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B @ ( sk_C @ ( k2_funct_1 @ sk_A ) @ sk_B ) ) )
    = ( sk_C @ ( k2_funct_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['40','47'])).

thf('49',plain,
    ( ( k1_funct_1 @ sk_B @ ( sk_C @ ( k2_funct_1 @ sk_A ) @ sk_B ) )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( sk_C @ ( k2_funct_1 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','48'])).

thf('50',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( X7 = X6 )
      | ( ( k1_funct_1 @ X7 @ ( sk_C @ X6 @ X7 ) )
       != ( k1_funct_1 @ X6 @ ( sk_C @ X6 @ X7 ) ) )
      | ( ( k1_relat_1 @ X7 )
       != ( k1_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('51',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C @ ( k2_funct_1 @ sk_A ) @ sk_B ) )
     != ( k1_funct_1 @ sk_B @ ( sk_C @ ( k2_funct_1 @ sk_A ) @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_relat_1 @ sk_B )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
    | ( sk_B
      = ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C @ ( k2_funct_1 @ sk_A ) @ sk_B ) )
     != ( k1_funct_1 @ sk_B @ ( sk_C @ ( k2_funct_1 @ sk_A ) @ sk_B ) ) )
    | ( ( k2_relat_1 @ sk_A )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
    | ( sk_B
      = ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('56',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ( sk_B
      = ( k2_funct_1 @ sk_A ) )
    | ( ( k2_relat_1 @ sk_A )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    sk_B
 != ( k2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ( ( k2_relat_1 @ sk_A )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( k2_relat_1 @ sk_A )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( k2_relat_1 @ sk_A )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ( k2_relat_1 @ sk_A )
 != ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ( k2_relat_1 @ sk_A )
 != ( k2_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68','69','70'])).

thf('72',plain,(
    $false ),
    inference(simplify,[status(thm)],['71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LLIWy9SacP
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:53:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.53  % Solved by: fo/fo7.sh
% 0.35/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.53  % done 77 iterations in 0.064s
% 0.35/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.53  % SZS output start Refutation
% 0.35/0.53  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.35/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.35/0.53  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.35/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.35/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.35/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.53  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.35/0.53  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.35/0.53  thf(t55_funct_1, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.35/0.53       ( ( v2_funct_1 @ A ) =>
% 0.35/0.53         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.35/0.53           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.35/0.53  thf('0', plain,
% 0.35/0.53      (![X3 : $i]:
% 0.35/0.53         (~ (v2_funct_1 @ X3)
% 0.35/0.53          | ((k2_relat_1 @ X3) = (k1_relat_1 @ (k2_funct_1 @ X3)))
% 0.35/0.53          | ~ (v1_funct_1 @ X3)
% 0.35/0.53          | ~ (v1_relat_1 @ X3))),
% 0.35/0.53      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.35/0.53  thf(dt_k2_funct_1, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.35/0.53       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.35/0.53         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.35/0.53  thf('1', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.35/0.53          | ~ (v1_funct_1 @ X0)
% 0.35/0.53          | ~ (v1_relat_1 @ X0))),
% 0.35/0.53      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.35/0.53  thf('2', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.35/0.53          | ~ (v1_funct_1 @ X0)
% 0.35/0.53          | ~ (v1_relat_1 @ X0))),
% 0.35/0.53      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.35/0.53  thf(t60_funct_1, conjecture,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.35/0.53       ( ![B:$i]:
% 0.35/0.53         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.35/0.53           ( ( ( v2_funct_1 @ A ) & 
% 0.35/0.53               ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ B ) ) & 
% 0.35/0.53               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.35/0.53               ( ![C:$i,D:$i]:
% 0.35/0.53                 ( ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.35/0.53                     ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) ) =>
% 0.35/0.53                   ( ( ( k1_funct_1 @ A @ C ) = ( D ) ) <=>
% 0.35/0.53                     ( ( k1_funct_1 @ B @ D ) = ( C ) ) ) ) ) ) =>
% 0.35/0.53             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.35/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.53    (~( ![A:$i]:
% 0.35/0.53        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.35/0.53          ( ![B:$i]:
% 0.35/0.53            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.35/0.53              ( ( ( v2_funct_1 @ A ) & 
% 0.35/0.53                  ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ B ) ) & 
% 0.35/0.53                  ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.35/0.53                  ( ![C:$i,D:$i]:
% 0.35/0.53                    ( ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.35/0.53                        ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) ) =>
% 0.35/0.53                      ( ( ( k1_funct_1 @ A @ C ) = ( D ) ) <=>
% 0.35/0.53                        ( ( k1_funct_1 @ B @ D ) = ( C ) ) ) ) ) ) =>
% 0.35/0.53                ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ) )),
% 0.35/0.53    inference('cnf.neg', [status(esa)], [t60_funct_1])).
% 0.35/0.53  thf('3', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('4', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.35/0.53          | ~ (v1_funct_1 @ X0)
% 0.35/0.53          | ~ (v1_relat_1 @ X0))),
% 0.35/0.53      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.35/0.53  thf('5', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.35/0.53          | ~ (v1_funct_1 @ X0)
% 0.35/0.53          | ~ (v1_relat_1 @ X0))),
% 0.35/0.53      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.35/0.53  thf('6', plain,
% 0.35/0.53      (![X3 : $i]:
% 0.35/0.53         (~ (v2_funct_1 @ X3)
% 0.35/0.53          | ((k2_relat_1 @ X3) = (k1_relat_1 @ (k2_funct_1 @ X3)))
% 0.35/0.53          | ~ (v1_funct_1 @ X3)
% 0.35/0.53          | ~ (v1_relat_1 @ X3))),
% 0.35/0.53      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.35/0.53  thf(t9_funct_1, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.35/0.53       ( ![B:$i]:
% 0.35/0.53         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.35/0.53           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.35/0.53               ( ![C:$i]:
% 0.35/0.53                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 0.35/0.53                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 0.35/0.53             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.35/0.53  thf('7', plain,
% 0.35/0.53      (![X6 : $i, X7 : $i]:
% 0.35/0.53         (~ (v1_relat_1 @ X6)
% 0.35/0.53          | ~ (v1_funct_1 @ X6)
% 0.35/0.53          | ((X7) = (X6))
% 0.35/0.53          | (r2_hidden @ (sk_C @ X6 @ X7) @ (k1_relat_1 @ X7))
% 0.35/0.53          | ((k1_relat_1 @ X7) != (k1_relat_1 @ X6))
% 0.35/0.53          | ~ (v1_funct_1 @ X7)
% 0.35/0.53          | ~ (v1_relat_1 @ X7))),
% 0.35/0.53      inference('cnf', [status(esa)], [t9_funct_1])).
% 0.35/0.53  thf('8', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         (((k1_relat_1 @ X1) != (k2_relat_1 @ X0))
% 0.35/0.53          | ~ (v1_relat_1 @ X0)
% 0.35/0.53          | ~ (v1_funct_1 @ X0)
% 0.35/0.53          | ~ (v2_funct_1 @ X0)
% 0.35/0.53          | ~ (v1_relat_1 @ X1)
% 0.35/0.53          | ~ (v1_funct_1 @ X1)
% 0.35/0.53          | (r2_hidden @ (sk_C @ (k2_funct_1 @ X0) @ X1) @ (k1_relat_1 @ X1))
% 0.35/0.53          | ((X1) = (k2_funct_1 @ X0))
% 0.35/0.53          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.35/0.53          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.35/0.53  thf('9', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         (~ (v1_relat_1 @ X0)
% 0.35/0.53          | ~ (v1_funct_1 @ X0)
% 0.35/0.53          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.35/0.53          | ((X1) = (k2_funct_1 @ X0))
% 0.35/0.53          | (r2_hidden @ (sk_C @ (k2_funct_1 @ X0) @ X1) @ (k1_relat_1 @ X1))
% 0.35/0.53          | ~ (v1_funct_1 @ X1)
% 0.35/0.53          | ~ (v1_relat_1 @ X1)
% 0.35/0.53          | ~ (v2_funct_1 @ X0)
% 0.35/0.53          | ~ (v1_funct_1 @ X0)
% 0.35/0.53          | ~ (v1_relat_1 @ X0)
% 0.35/0.53          | ((k1_relat_1 @ X1) != (k2_relat_1 @ X0)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['5', '8'])).
% 0.35/0.53  thf('10', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         (((k1_relat_1 @ X1) != (k2_relat_1 @ X0))
% 0.35/0.53          | ~ (v2_funct_1 @ X0)
% 0.35/0.53          | ~ (v1_relat_1 @ X1)
% 0.35/0.53          | ~ (v1_funct_1 @ X1)
% 0.35/0.53          | (r2_hidden @ (sk_C @ (k2_funct_1 @ X0) @ X1) @ (k1_relat_1 @ X1))
% 0.35/0.53          | ((X1) = (k2_funct_1 @ X0))
% 0.35/0.53          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.35/0.53          | ~ (v1_funct_1 @ X0)
% 0.35/0.53          | ~ (v1_relat_1 @ X0))),
% 0.35/0.53      inference('simplify', [status(thm)], ['9'])).
% 0.35/0.53  thf('11', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         (~ (v1_relat_1 @ X0)
% 0.35/0.53          | ~ (v1_funct_1 @ X0)
% 0.35/0.53          | ~ (v1_relat_1 @ X0)
% 0.35/0.53          | ~ (v1_funct_1 @ X0)
% 0.35/0.53          | ((X1) = (k2_funct_1 @ X0))
% 0.35/0.53          | (r2_hidden @ (sk_C @ (k2_funct_1 @ X0) @ X1) @ (k1_relat_1 @ X1))
% 0.35/0.53          | ~ (v1_funct_1 @ X1)
% 0.35/0.53          | ~ (v1_relat_1 @ X1)
% 0.35/0.53          | ~ (v2_funct_1 @ X0)
% 0.35/0.53          | ((k1_relat_1 @ X1) != (k2_relat_1 @ X0)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['4', '10'])).
% 0.35/0.53  thf('12', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         (((k1_relat_1 @ X1) != (k2_relat_1 @ X0))
% 0.35/0.53          | ~ (v2_funct_1 @ X0)
% 0.35/0.53          | ~ (v1_relat_1 @ X1)
% 0.35/0.53          | ~ (v1_funct_1 @ X1)
% 0.35/0.53          | (r2_hidden @ (sk_C @ (k2_funct_1 @ X0) @ X1) @ (k1_relat_1 @ X1))
% 0.35/0.53          | ((X1) = (k2_funct_1 @ X0))
% 0.35/0.53          | ~ (v1_funct_1 @ X0)
% 0.35/0.53          | ~ (v1_relat_1 @ X0))),
% 0.35/0.53      inference('simplify', [status(thm)], ['11'])).
% 0.35/0.53  thf('13', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (((k2_relat_1 @ sk_A) != (k2_relat_1 @ X0))
% 0.35/0.53          | ~ (v1_relat_1 @ X0)
% 0.35/0.53          | ~ (v1_funct_1 @ X0)
% 0.35/0.53          | ((sk_B) = (k2_funct_1 @ X0))
% 0.35/0.53          | (r2_hidden @ (sk_C @ (k2_funct_1 @ X0) @ sk_B) @ 
% 0.35/0.53             (k1_relat_1 @ sk_B))
% 0.35/0.53          | ~ (v1_funct_1 @ sk_B)
% 0.35/0.53          | ~ (v1_relat_1 @ sk_B)
% 0.35/0.53          | ~ (v2_funct_1 @ X0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['3', '12'])).
% 0.35/0.53  thf('14', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('15', plain, ((v1_funct_1 @ sk_B)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('16', plain, ((v1_relat_1 @ sk_B)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('17', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (((k2_relat_1 @ sk_A) != (k2_relat_1 @ X0))
% 0.35/0.53          | ~ (v1_relat_1 @ X0)
% 0.35/0.53          | ~ (v1_funct_1 @ X0)
% 0.35/0.53          | ((sk_B) = (k2_funct_1 @ X0))
% 0.35/0.53          | (r2_hidden @ (sk_C @ (k2_funct_1 @ X0) @ sk_B) @ 
% 0.35/0.53             (k2_relat_1 @ sk_A))
% 0.35/0.53          | ~ (v2_funct_1 @ X0))),
% 0.35/0.53      inference('demod', [status(thm)], ['13', '14', '15', '16'])).
% 0.35/0.53  thf('18', plain,
% 0.35/0.53      ((~ (v2_funct_1 @ sk_A)
% 0.35/0.53        | (r2_hidden @ (sk_C @ (k2_funct_1 @ sk_A) @ sk_B) @ 
% 0.35/0.53           (k2_relat_1 @ sk_A))
% 0.35/0.53        | ((sk_B) = (k2_funct_1 @ sk_A))
% 0.35/0.53        | ~ (v1_funct_1 @ sk_A)
% 0.35/0.53        | ~ (v1_relat_1 @ sk_A))),
% 0.35/0.53      inference('eq_res', [status(thm)], ['17'])).
% 0.35/0.53  thf('19', plain, ((v2_funct_1 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('20', plain, ((v1_funct_1 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('21', plain, ((v1_relat_1 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('22', plain,
% 0.35/0.53      (((r2_hidden @ (sk_C @ (k2_funct_1 @ sk_A) @ sk_B) @ (k2_relat_1 @ sk_A))
% 0.35/0.53        | ((sk_B) = (k2_funct_1 @ sk_A)))),
% 0.35/0.53      inference('demod', [status(thm)], ['18', '19', '20', '21'])).
% 0.35/0.53  thf('23', plain, (((sk_B) != (k2_funct_1 @ sk_A))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('24', plain,
% 0.35/0.53      ((r2_hidden @ (sk_C @ (k2_funct_1 @ sk_A) @ sk_B) @ (k2_relat_1 @ sk_A))),
% 0.35/0.53      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.35/0.53  thf('25', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(t12_funct_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.35/0.53       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.35/0.53         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.35/0.53  thf('26', plain,
% 0.35/0.53      (![X1 : $i, X2 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X2))
% 0.35/0.53          | (r2_hidden @ (k1_funct_1 @ X2 @ X1) @ (k2_relat_1 @ X2))
% 0.35/0.53          | ~ (v1_funct_1 @ X2)
% 0.35/0.53          | ~ (v1_relat_1 @ X2))),
% 0.35/0.53      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.35/0.53  thf('27', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_A))
% 0.35/0.53          | ~ (v1_relat_1 @ sk_B)
% 0.35/0.53          | ~ (v1_funct_1 @ sk_B)
% 0.35/0.53          | (r2_hidden @ (k1_funct_1 @ sk_B @ X0) @ (k2_relat_1 @ sk_B)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['25', '26'])).
% 0.35/0.53  thf('28', plain, ((v1_relat_1 @ sk_B)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('29', plain, ((v1_funct_1 @ sk_B)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('30', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_A))
% 0.35/0.53          | (r2_hidden @ (k1_funct_1 @ sk_B @ X0) @ (k2_relat_1 @ sk_B)))),
% 0.35/0.53      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.35/0.53  thf('31', plain,
% 0.35/0.53      ((r2_hidden @ 
% 0.35/0.53        (k1_funct_1 @ sk_B @ (sk_C @ (k2_funct_1 @ sk_A) @ sk_B)) @ 
% 0.35/0.53        (k2_relat_1 @ sk_B))),
% 0.35/0.53      inference('sup-', [status(thm)], ['24', '30'])).
% 0.35/0.53  thf('32', plain, (((k1_relat_1 @ sk_A) = (k2_relat_1 @ sk_B))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(t56_funct_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.35/0.53       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) ) =>
% 0.35/0.53         ( ( ( A ) =
% 0.35/0.53             ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) ) & 
% 0.35/0.53           ( ( A ) =
% 0.35/0.53             ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ))).
% 0.35/0.53  thf('33', plain,
% 0.35/0.53      (![X4 : $i, X5 : $i]:
% 0.35/0.53         (~ (v2_funct_1 @ X4)
% 0.35/0.53          | ~ (r2_hidden @ X5 @ (k1_relat_1 @ X4))
% 0.35/0.53          | ((X5) = (k1_funct_1 @ (k2_funct_1 @ X4) @ (k1_funct_1 @ X4 @ X5)))
% 0.35/0.53          | ~ (v1_funct_1 @ X4)
% 0.35/0.53          | ~ (v1_relat_1 @ X4))),
% 0.35/0.53      inference('cnf', [status(esa)], [t56_funct_1])).
% 0.35/0.53  thf('34', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 0.35/0.53          | ~ (v1_relat_1 @ sk_A)
% 0.35/0.53          | ~ (v1_funct_1 @ sk_A)
% 0.35/0.53          | ((X0)
% 0.35/0.53              = (k1_funct_1 @ (k2_funct_1 @ sk_A) @ (k1_funct_1 @ sk_A @ X0)))
% 0.35/0.53          | ~ (v2_funct_1 @ sk_A))),
% 0.35/0.53      inference('sup-', [status(thm)], ['32', '33'])).
% 0.35/0.53  thf('35', plain, ((v1_relat_1 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('36', plain, ((v1_funct_1 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('37', plain, ((v2_funct_1 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('38', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 0.35/0.53          | ((X0)
% 0.35/0.53              = (k1_funct_1 @ (k2_funct_1 @ sk_A) @ (k1_funct_1 @ sk_A @ X0))))),
% 0.35/0.53      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 0.35/0.53  thf('39', plain,
% 0.35/0.53      (((k1_funct_1 @ sk_B @ (sk_C @ (k2_funct_1 @ sk_A) @ sk_B))
% 0.35/0.53         = (k1_funct_1 @ (k2_funct_1 @ sk_A) @ 
% 0.35/0.53            (k1_funct_1 @ sk_A @ 
% 0.35/0.53             (k1_funct_1 @ sk_B @ (sk_C @ (k2_funct_1 @ sk_A) @ sk_B)))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['31', '38'])).
% 0.35/0.53  thf('40', plain,
% 0.35/0.53      ((r2_hidden @ (sk_C @ (k2_funct_1 @ sk_A) @ sk_B) @ (k2_relat_1 @ sk_A))),
% 0.35/0.53      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.35/0.53  thf('41', plain,
% 0.35/0.53      (![X8 : $i, X9 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X8 @ (k1_relat_1 @ sk_A))
% 0.35/0.53          | ~ (r2_hidden @ X9 @ (k1_relat_1 @ sk_B))
% 0.35/0.53          | ((k1_funct_1 @ sk_A @ X8) = (X9))
% 0.35/0.53          | ((k1_funct_1 @ sk_B @ X9) != (X8)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('42', plain,
% 0.35/0.53      (![X9 : $i]:
% 0.35/0.53         (((k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B @ X9)) = (X9))
% 0.35/0.53          | ~ (r2_hidden @ X9 @ (k1_relat_1 @ sk_B))
% 0.35/0.53          | ~ (r2_hidden @ (k1_funct_1 @ sk_B @ X9) @ (k1_relat_1 @ sk_A)))),
% 0.35/0.53      inference('simplify', [status(thm)], ['41'])).
% 0.35/0.53  thf('43', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('44', plain, (((k1_relat_1 @ sk_A) = (k2_relat_1 @ sk_B))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('45', plain,
% 0.35/0.53      (![X9 : $i]:
% 0.35/0.53         (((k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B @ X9)) = (X9))
% 0.35/0.53          | ~ (r2_hidden @ X9 @ (k2_relat_1 @ sk_A))
% 0.35/0.53          | ~ (r2_hidden @ (k1_funct_1 @ sk_B @ X9) @ (k2_relat_1 @ sk_B)))),
% 0.35/0.53      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.35/0.53  thf('46', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_A))
% 0.35/0.53          | (r2_hidden @ (k1_funct_1 @ sk_B @ X0) @ (k2_relat_1 @ sk_B)))),
% 0.35/0.53      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.35/0.53  thf('47', plain,
% 0.35/0.53      (![X9 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X9 @ (k2_relat_1 @ sk_A))
% 0.35/0.53          | ((k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B @ X9)) = (X9)))),
% 0.35/0.53      inference('clc', [status(thm)], ['45', '46'])).
% 0.35/0.53  thf('48', plain,
% 0.35/0.53      (((k1_funct_1 @ sk_A @ 
% 0.35/0.53         (k1_funct_1 @ sk_B @ (sk_C @ (k2_funct_1 @ sk_A) @ sk_B)))
% 0.35/0.53         = (sk_C @ (k2_funct_1 @ sk_A) @ sk_B))),
% 0.35/0.53      inference('sup-', [status(thm)], ['40', '47'])).
% 0.35/0.53  thf('49', plain,
% 0.35/0.53      (((k1_funct_1 @ sk_B @ (sk_C @ (k2_funct_1 @ sk_A) @ sk_B))
% 0.35/0.53         = (k1_funct_1 @ (k2_funct_1 @ sk_A) @ 
% 0.35/0.53            (sk_C @ (k2_funct_1 @ sk_A) @ sk_B)))),
% 0.35/0.53      inference('demod', [status(thm)], ['39', '48'])).
% 0.35/0.53  thf('50', plain,
% 0.35/0.53      (![X6 : $i, X7 : $i]:
% 0.35/0.53         (~ (v1_relat_1 @ X6)
% 0.35/0.53          | ~ (v1_funct_1 @ X6)
% 0.35/0.53          | ((X7) = (X6))
% 0.35/0.53          | ((k1_funct_1 @ X7 @ (sk_C @ X6 @ X7))
% 0.35/0.53              != (k1_funct_1 @ X6 @ (sk_C @ X6 @ X7)))
% 0.35/0.53          | ((k1_relat_1 @ X7) != (k1_relat_1 @ X6))
% 0.35/0.53          | ~ (v1_funct_1 @ X7)
% 0.35/0.53          | ~ (v1_relat_1 @ X7))),
% 0.35/0.53      inference('cnf', [status(esa)], [t9_funct_1])).
% 0.35/0.53  thf('51', plain,
% 0.35/0.53      ((((k1_funct_1 @ sk_B @ (sk_C @ (k2_funct_1 @ sk_A) @ sk_B))
% 0.35/0.53          != (k1_funct_1 @ sk_B @ (sk_C @ (k2_funct_1 @ sk_A) @ sk_B)))
% 0.35/0.53        | ~ (v1_relat_1 @ sk_B)
% 0.35/0.53        | ~ (v1_funct_1 @ sk_B)
% 0.35/0.53        | ((k1_relat_1 @ sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.35/0.53        | ((sk_B) = (k2_funct_1 @ sk_A))
% 0.35/0.53        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 0.35/0.53        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['49', '50'])).
% 0.35/0.53  thf('52', plain, ((v1_relat_1 @ sk_B)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('53', plain, ((v1_funct_1 @ sk_B)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('54', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('55', plain,
% 0.35/0.53      ((((k1_funct_1 @ sk_B @ (sk_C @ (k2_funct_1 @ sk_A) @ sk_B))
% 0.35/0.53          != (k1_funct_1 @ sk_B @ (sk_C @ (k2_funct_1 @ sk_A) @ sk_B)))
% 0.35/0.53        | ((k2_relat_1 @ sk_A) != (k1_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.35/0.53        | ((sk_B) = (k2_funct_1 @ sk_A))
% 0.35/0.53        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 0.35/0.53        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 0.35/0.53      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 0.35/0.53  thf('56', plain,
% 0.35/0.53      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.35/0.53        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 0.35/0.53        | ((sk_B) = (k2_funct_1 @ sk_A))
% 0.35/0.53        | ((k2_relat_1 @ sk_A) != (k1_relat_1 @ (k2_funct_1 @ sk_A))))),
% 0.35/0.53      inference('simplify', [status(thm)], ['55'])).
% 0.35/0.53  thf('57', plain, (((sk_B) != (k2_funct_1 @ sk_A))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('58', plain,
% 0.35/0.53      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.35/0.53        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 0.35/0.53        | ((k2_relat_1 @ sk_A) != (k1_relat_1 @ (k2_funct_1 @ sk_A))))),
% 0.35/0.53      inference('simplify_reflect-', [status(thm)], ['56', '57'])).
% 0.35/0.53  thf('59', plain,
% 0.35/0.53      ((~ (v1_relat_1 @ sk_A)
% 0.35/0.53        | ~ (v1_funct_1 @ sk_A)
% 0.35/0.53        | ((k2_relat_1 @ sk_A) != (k1_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.35/0.53        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['2', '58'])).
% 0.35/0.53  thf('60', plain, ((v1_relat_1 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('61', plain, ((v1_funct_1 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('62', plain,
% 0.35/0.53      ((((k2_relat_1 @ sk_A) != (k1_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.35/0.53        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A)))),
% 0.35/0.53      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.35/0.53  thf('63', plain,
% 0.35/0.53      ((~ (v1_relat_1 @ sk_A)
% 0.35/0.53        | ~ (v1_funct_1 @ sk_A)
% 0.35/0.53        | ((k2_relat_1 @ sk_A) != (k1_relat_1 @ (k2_funct_1 @ sk_A))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['1', '62'])).
% 0.35/0.53  thf('64', plain, ((v1_relat_1 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('65', plain, ((v1_funct_1 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('66', plain,
% 0.35/0.53      (((k2_relat_1 @ sk_A) != (k1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 0.35/0.53      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.35/0.53  thf('67', plain,
% 0.35/0.53      ((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))
% 0.35/0.53        | ~ (v1_relat_1 @ sk_A)
% 0.35/0.53        | ~ (v1_funct_1 @ sk_A)
% 0.35/0.53        | ~ (v2_funct_1 @ sk_A))),
% 0.35/0.53      inference('sup-', [status(thm)], ['0', '66'])).
% 0.35/0.53  thf('68', plain, ((v1_relat_1 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('69', plain, ((v1_funct_1 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('70', plain, ((v2_funct_1 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('71', plain, (((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))),
% 0.35/0.53      inference('demod', [status(thm)], ['67', '68', '69', '70'])).
% 0.35/0.53  thf('72', plain, ($false), inference('simplify', [status(thm)], ['71'])).
% 0.35/0.53  
% 0.35/0.53  % SZS output end Refutation
% 0.35/0.53  
% 0.35/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
