%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6OBKH1ytbW

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:16 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 281 expanded)
%              Number of leaves         :   19 (  90 expanded)
%              Depth                    :   44
%              Number of atoms          : 1593 (4224 expanded)
%              Number of equality atoms :  101 ( 269 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(t53_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ? [B: $i] :
            ( ( ( k5_relat_1 @ A @ B )
              = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
            & ( v1_funct_1 @ B )
            & ( v1_relat_1 @ B ) )
       => ( v2_funct_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ? [B: $i] :
              ( ( ( k5_relat_1 @ A @ B )
                = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
              & ( v1_funct_1 @ B )
              & ( v1_relat_1 @ B ) )
         => ( v2_funct_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t53_funct_1])).

thf('0',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t49_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
      <=> ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ! [C: $i] :
                ( ( ( v1_relat_1 @ C )
                  & ( v1_funct_1 @ C ) )
               => ( ( ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) )
                    & ( r1_tarski @ ( k2_relat_1 @ C ) @ ( k1_relat_1 @ A ) )
                    & ( ( k1_relat_1 @ B )
                      = ( k1_relat_1 @ C ) )
                    & ( ( k5_relat_1 @ B @ A )
                      = ( k5_relat_1 @ C @ A ) ) )
                 => ( B = C ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( sk_B @ X9 ) )
      | ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t49_funct_1])).

thf('2',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( sk_B @ X9 ) )
      | ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t49_funct_1])).

thf('3',plain,(
    ! [X9: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_B @ X9 ) ) @ ( k1_relat_1 @ X9 ) )
      | ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t49_funct_1])).

thf('4',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( sk_C @ X9 ) )
      | ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t49_funct_1])).

thf('5',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( sk_C @ X9 ) )
      | ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t49_funct_1])).

thf('6',plain,(
    ! [X9: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C @ X9 ) ) @ ( k1_relat_1 @ X9 ) )
      | ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t49_funct_1])).

thf('7',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( sk_B @ X9 ) )
      | ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t49_funct_1])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('9',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B_1 )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( sk_C @ X9 ) )
      | ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t49_funct_1])).

thf('11',plain,(
    ! [X9: $i] :
      ( ( ( k5_relat_1 @ ( sk_B @ X9 ) @ X9 )
        = ( k5_relat_1 @ ( sk_C @ X9 ) @ X9 ) )
      | ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t49_funct_1])).

thf('12',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ ( sk_B @ X0 ) @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( sk_C @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( sk_C @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( sk_C @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ ( sk_B @ X0 ) @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( sk_C @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ ( sk_B @ X0 ) @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( sk_C @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ ( sk_B @ X0 ) @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( sk_C @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( ( k5_relat_1 @ ( k5_relat_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_B_1 )
      = ( k5_relat_1 @ ( sk_C @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['9','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( k5_relat_1 @ ( k5_relat_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_B_1 )
      = ( k5_relat_1 @ ( sk_C @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18','19','20'])).

thf('22',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k5_relat_1 @ ( k5_relat_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_B_1 )
    = ( k5_relat_1 @ ( sk_C @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k5_relat_1 @ ( sk_B @ sk_A ) @ ( k5_relat_1 @ sk_A @ sk_B_1 ) )
      = ( k5_relat_1 @ ( sk_C @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ ( sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['8','23'])).

thf('25',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B_1 )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( ( k5_relat_1 @ ( sk_B @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
      = ( k5_relat_1 @ ( sk_C @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ ( sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','26','27'])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A )
    | ( ( k5_relat_1 @ ( sk_B @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
      = ( k5_relat_1 @ ( sk_C @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['7','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v2_funct_1 @ sk_A )
    | ( ( k5_relat_1 @ ( sk_B @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
      = ( k5_relat_1 @ ( sk_C @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k5_relat_1 @ ( sk_B @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
    = ( k5_relat_1 @ ( sk_C @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('35',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('36',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( X11 = X10 )
      | ( ( k5_relat_1 @ X11 @ X9 )
       != ( k5_relat_1 @ X10 @ X9 ) )
      | ( ( k1_relat_1 @ X11 )
       != ( k1_relat_1 @ X10 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X10 ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X11 ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t49_funct_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X2 ) @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ( ( k1_relat_1 @ X2 )
       != ( k1_relat_1 @ X1 ) )
      | ( ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X0 ) )
       != ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ( X2 = X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('38',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('39',plain,(
    ! [X8: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('40',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('41',plain,(
    ! [X12: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X2 ) @ X0 )
      | ( ( k1_relat_1 @ X2 )
       != ( k1_relat_1 @ X1 ) )
      | ( ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X0 ) )
       != ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ( X2 = X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['37','38','39','40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
       != ( k5_relat_1 @ ( sk_B @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) )
      | ~ ( v1_relat_1 @ ( sk_C @ sk_A ) )
      | ~ ( v1_funct_1 @ ( sk_C @ sk_A ) )
      | ( X0
        = ( sk_C @ sk_A ) )
      | ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ ( sk_C @ sk_A ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( sk_C @ sk_A ) ) @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','42'])).

thf('44',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( sk_B @ X9 ) )
      | ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t49_funct_1])).

thf('45',plain,(
    ! [X9: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_B @ X9 ) ) @ ( k1_relat_1 @ X9 ) )
      | ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t49_funct_1])).

thf('46',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ X1 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( sk_B @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( sk_B @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( sk_B @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( sk_B @ X0 ) ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( sk_B @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( sk_B @ X0 ) ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( k5_relat_1 @ ( sk_B @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
    = ( k5_relat_1 @ ( sk_C @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('55',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( sk_C @ X9 ) )
      | ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t49_funct_1])).

thf('56',plain,(
    ! [X9: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C @ X9 ) ) @ ( k1_relat_1 @ X9 ) )
      | ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t49_funct_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( sk_C @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( sk_C @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( sk_C @ X0 ) ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( sk_C @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( sk_C @ X0 ) ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( sk_B @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) )
      = ( k1_relat_1 @ ( sk_C @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['54','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( sk_B @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) )
      = ( k1_relat_1 @ ( sk_C @ sk_A ) ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ ( sk_B @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) )
    = ( k1_relat_1 @ ( sk_C @ sk_A ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k1_relat_1 @ ( sk_B @ sk_A ) )
      = ( k1_relat_1 @ ( sk_C @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['53','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( ( k1_relat_1 @ ( sk_B @ sk_A ) )
      = ( k1_relat_1 @ ( sk_C @ sk_A ) ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( k1_relat_1 @ ( sk_B @ sk_A ) )
    = ( k1_relat_1 @ ( sk_C @ sk_A ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
       != ( k5_relat_1 @ ( sk_B @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) )
      | ~ ( v1_relat_1 @ ( sk_C @ sk_A ) )
      | ~ ( v1_funct_1 @ ( sk_C @ sk_A ) )
      | ( X0
        = ( sk_C @ sk_A ) )
      | ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( sk_C @ sk_A ) ) @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['43','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( v2_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ sk_A ) )
      | ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ ( sk_B @ sk_A ) ) )
      | ( X0
        = ( sk_C @ sk_A ) )
      | ~ ( v1_funct_1 @ ( sk_C @ sk_A ) )
      | ~ ( v1_relat_1 @ ( sk_C @ sk_A ) )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
       != ( k5_relat_1 @ ( sk_B @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['6','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ sk_A ) )
      | ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ ( sk_B @ sk_A ) ) )
      | ( X0
        = ( sk_C @ sk_A ) )
      | ~ ( v1_funct_1 @ ( sk_C @ sk_A ) )
      | ~ ( v1_relat_1 @ ( sk_C @ sk_A ) )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
       != ( k5_relat_1 @ ( sk_B @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( v2_funct_1 @ sk_A )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
       != ( k5_relat_1 @ ( sk_B @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) )
      | ~ ( v1_relat_1 @ ( sk_C @ sk_A ) )
      | ( X0
        = ( sk_C @ sk_A ) )
      | ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ sk_A )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
       != ( k5_relat_1 @ ( sk_B @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) )
      | ~ ( v1_relat_1 @ ( sk_C @ sk_A ) )
      | ( X0
        = ( sk_C @ sk_A ) )
      | ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ sk_A ) )
      | ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ ( sk_B @ sk_A ) ) )
      | ( X0
        = ( sk_C @ sk_A ) )
      | ~ ( v1_relat_1 @ ( sk_C @ sk_A ) )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
       != ( k5_relat_1 @ ( sk_B @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) )
      | ( v2_funct_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( v2_funct_1 @ sk_A )
      | ( v2_funct_1 @ sk_A )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
       != ( k5_relat_1 @ ( sk_B @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) )
      | ( X0
        = ( sk_C @ sk_A ) )
      | ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','82'])).

thf('84',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ sk_A )
      | ( v2_funct_1 @ sk_A )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
       != ( k5_relat_1 @ ( sk_B @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) )
      | ( X0
        = ( sk_C @ sk_A ) )
      | ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ sk_A ) )
      | ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ ( sk_B @ sk_A ) ) )
      | ( X0
        = ( sk_C @ sk_A ) )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
       != ( k5_relat_1 @ ( sk_B @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) )
      | ( v2_funct_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ( v2_funct_1 @ sk_A )
    | ( ( sk_B @ sk_A )
      = ( sk_C @ sk_A ) )
    | ( ( k1_relat_1 @ ( sk_B @ sk_A ) )
     != ( k1_relat_1 @ ( sk_B @ sk_A ) ) )
    | ~ ( r1_tarski @ ( k2_relat_1 @ ( sk_B @ sk_A ) ) @ ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ ( sk_B @ sk_A ) ) ),
    inference(eq_res,[status(thm)],['87'])).

thf('89',plain,
    ( ~ ( v1_relat_1 @ ( sk_B @ sk_A ) )
    | ~ ( v1_funct_1 @ ( sk_B @ sk_A ) )
    | ~ ( r1_tarski @ ( k2_relat_1 @ ( sk_B @ sk_A ) ) @ ( k1_relat_1 @ sk_A ) )
    | ( ( sk_B @ sk_A )
      = ( sk_C @ sk_A ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A )
    | ( ( sk_B @ sk_A )
      = ( sk_C @ sk_A ) )
    | ~ ( v1_funct_1 @ ( sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ ( sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','89'])).

thf('91',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( v2_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A )
    | ( ( sk_B @ sk_A )
      = ( sk_C @ sk_A ) )
    | ~ ( v1_funct_1 @ ( sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ ( sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,
    ( ~ ( v1_relat_1 @ ( sk_B @ sk_A ) )
    | ~ ( v1_funct_1 @ ( sk_B @ sk_A ) )
    | ( ( sk_B @ sk_A )
      = ( sk_C @ sk_A ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A )
    | ( ( sk_B @ sk_A )
      = ( sk_C @ sk_A ) )
    | ~ ( v1_funct_1 @ ( sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','94'])).

thf('96',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v2_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A )
    | ( ( sk_B @ sk_A )
      = ( sk_C @ sk_A ) )
    | ~ ( v1_funct_1 @ ( sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,
    ( ~ ( v1_funct_1 @ ( sk_B @ sk_A ) )
    | ( ( sk_B @ sk_A )
      = ( sk_C @ sk_A ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( ( sk_B @ sk_A )
      = ( sk_C @ sk_A ) )
    | ~ ( v1_funct_1 @ ( sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A )
    | ( ( sk_B @ sk_A )
      = ( sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','101'])).

thf('103',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( v2_funct_1 @ sk_A )
    | ( ( sk_B @ sk_A )
      = ( sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( sk_B @ sk_A )
    = ( sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X9: $i] :
      ( ( ( sk_B @ X9 )
       != ( sk_C @ X9 ) )
      | ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t49_funct_1])).

thf('109',plain,
    ( ( ( sk_B @ sk_A )
     != ( sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( ( sk_B @ sk_A )
     != ( sk_B @ sk_A ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,(
    v2_funct_1 @ sk_A ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    $false ),
    inference(demod,[status(thm)],['0','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6OBKH1ytbW
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:45:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.58/0.80  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.80  % Solved by: fo/fo7.sh
% 0.58/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.80  % done 255 iterations in 0.345s
% 0.58/0.80  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.80  % SZS output start Refutation
% 0.58/0.80  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.58/0.80  thf(sk_C_type, type, sk_C: $i > $i).
% 0.58/0.80  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.58/0.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.80  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.58/0.80  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.58/0.80  thf(sk_B_type, type, sk_B: $i > $i).
% 0.58/0.80  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.58/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.80  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.58/0.80  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.58/0.80  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.58/0.80  thf(t53_funct_1, conjecture,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.58/0.80       ( ( ?[B:$i]:
% 0.58/0.80           ( ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.58/0.80             ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) ) =>
% 0.58/0.80         ( v2_funct_1 @ A ) ) ))).
% 0.58/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.80    (~( ![A:$i]:
% 0.58/0.80        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.58/0.80          ( ( ?[B:$i]:
% 0.58/0.80              ( ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.58/0.80                ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) ) =>
% 0.58/0.80            ( v2_funct_1 @ A ) ) ) )),
% 0.58/0.80    inference('cnf.neg', [status(esa)], [t53_funct_1])).
% 0.58/0.80  thf('0', plain, (~ (v2_funct_1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf(t49_funct_1, axiom,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.58/0.80       ( ( v2_funct_1 @ A ) <=>
% 0.58/0.80         ( ![B:$i]:
% 0.58/0.80           ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.58/0.80             ( ![C:$i]:
% 0.58/0.80               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.58/0.80                 ( ( ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) & 
% 0.58/0.80                     ( r1_tarski @ ( k2_relat_1 @ C ) @ ( k1_relat_1 @ A ) ) & 
% 0.58/0.80                     ( ( k1_relat_1 @ B ) = ( k1_relat_1 @ C ) ) & 
% 0.58/0.80                     ( ( k5_relat_1 @ B @ A ) = ( k5_relat_1 @ C @ A ) ) ) =>
% 0.58/0.80                   ( ( B ) = ( C ) ) ) ) ) ) ) ) ))).
% 0.58/0.80  thf('1', plain,
% 0.58/0.80      (![X9 : $i]:
% 0.58/0.80         ((v1_funct_1 @ (sk_B @ X9))
% 0.58/0.80          | (v2_funct_1 @ X9)
% 0.58/0.80          | ~ (v1_funct_1 @ X9)
% 0.58/0.80          | ~ (v1_relat_1 @ X9))),
% 0.58/0.80      inference('cnf', [status(esa)], [t49_funct_1])).
% 0.58/0.80  thf('2', plain,
% 0.58/0.80      (![X9 : $i]:
% 0.58/0.80         ((v1_relat_1 @ (sk_B @ X9))
% 0.58/0.80          | (v2_funct_1 @ X9)
% 0.58/0.80          | ~ (v1_funct_1 @ X9)
% 0.58/0.80          | ~ (v1_relat_1 @ X9))),
% 0.58/0.80      inference('cnf', [status(esa)], [t49_funct_1])).
% 0.58/0.80  thf('3', plain,
% 0.58/0.80      (![X9 : $i]:
% 0.58/0.80         ((r1_tarski @ (k2_relat_1 @ (sk_B @ X9)) @ (k1_relat_1 @ X9))
% 0.58/0.80          | (v2_funct_1 @ X9)
% 0.58/0.80          | ~ (v1_funct_1 @ X9)
% 0.58/0.80          | ~ (v1_relat_1 @ X9))),
% 0.58/0.80      inference('cnf', [status(esa)], [t49_funct_1])).
% 0.58/0.80  thf('4', plain,
% 0.58/0.80      (![X9 : $i]:
% 0.58/0.80         ((v1_relat_1 @ (sk_C @ X9))
% 0.58/0.80          | (v2_funct_1 @ X9)
% 0.58/0.80          | ~ (v1_funct_1 @ X9)
% 0.58/0.80          | ~ (v1_relat_1 @ X9))),
% 0.58/0.80      inference('cnf', [status(esa)], [t49_funct_1])).
% 0.58/0.80  thf('5', plain,
% 0.58/0.80      (![X9 : $i]:
% 0.58/0.80         ((v1_funct_1 @ (sk_C @ X9))
% 0.58/0.80          | (v2_funct_1 @ X9)
% 0.58/0.80          | ~ (v1_funct_1 @ X9)
% 0.58/0.80          | ~ (v1_relat_1 @ X9))),
% 0.58/0.80      inference('cnf', [status(esa)], [t49_funct_1])).
% 0.58/0.80  thf('6', plain,
% 0.58/0.80      (![X9 : $i]:
% 0.58/0.80         ((r1_tarski @ (k2_relat_1 @ (sk_C @ X9)) @ (k1_relat_1 @ X9))
% 0.58/0.80          | (v2_funct_1 @ X9)
% 0.58/0.80          | ~ (v1_funct_1 @ X9)
% 0.58/0.80          | ~ (v1_relat_1 @ X9))),
% 0.58/0.80      inference('cnf', [status(esa)], [t49_funct_1])).
% 0.58/0.80  thf('7', plain,
% 0.58/0.80      (![X9 : $i]:
% 0.58/0.80         ((v1_relat_1 @ (sk_B @ X9))
% 0.58/0.80          | (v2_funct_1 @ X9)
% 0.58/0.80          | ~ (v1_funct_1 @ X9)
% 0.58/0.80          | ~ (v1_relat_1 @ X9))),
% 0.58/0.80      inference('cnf', [status(esa)], [t49_funct_1])).
% 0.58/0.80  thf(t55_relat_1, axiom,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( v1_relat_1 @ A ) =>
% 0.58/0.80       ( ![B:$i]:
% 0.58/0.80         ( ( v1_relat_1 @ B ) =>
% 0.58/0.80           ( ![C:$i]:
% 0.58/0.80             ( ( v1_relat_1 @ C ) =>
% 0.58/0.80               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.58/0.80                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.58/0.80  thf('8', plain,
% 0.58/0.80      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.58/0.80         (~ (v1_relat_1 @ X2)
% 0.58/0.80          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 0.58/0.80              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 0.58/0.80          | ~ (v1_relat_1 @ X4)
% 0.58/0.80          | ~ (v1_relat_1 @ X3))),
% 0.58/0.80      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.58/0.80  thf('9', plain,
% 0.58/0.80      (((k5_relat_1 @ sk_A @ sk_B_1) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('10', plain,
% 0.58/0.80      (![X9 : $i]:
% 0.58/0.80         ((v1_relat_1 @ (sk_C @ X9))
% 0.58/0.80          | (v2_funct_1 @ X9)
% 0.58/0.80          | ~ (v1_funct_1 @ X9)
% 0.58/0.80          | ~ (v1_relat_1 @ X9))),
% 0.58/0.80      inference('cnf', [status(esa)], [t49_funct_1])).
% 0.58/0.80  thf('11', plain,
% 0.58/0.80      (![X9 : $i]:
% 0.58/0.80         (((k5_relat_1 @ (sk_B @ X9) @ X9) = (k5_relat_1 @ (sk_C @ X9) @ X9))
% 0.58/0.80          | (v2_funct_1 @ X9)
% 0.58/0.80          | ~ (v1_funct_1 @ X9)
% 0.58/0.80          | ~ (v1_relat_1 @ X9))),
% 0.58/0.80      inference('cnf', [status(esa)], [t49_funct_1])).
% 0.58/0.80  thf('12', plain,
% 0.58/0.80      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.58/0.80         (~ (v1_relat_1 @ X2)
% 0.58/0.80          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 0.58/0.80              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 0.58/0.80          | ~ (v1_relat_1 @ X4)
% 0.58/0.80          | ~ (v1_relat_1 @ X3))),
% 0.58/0.80      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.58/0.80  thf('13', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         (((k5_relat_1 @ (k5_relat_1 @ (sk_B @ X0) @ X0) @ X1)
% 0.58/0.80            = (k5_relat_1 @ (sk_C @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 0.58/0.80          | ~ (v1_relat_1 @ X0)
% 0.58/0.80          | ~ (v1_funct_1 @ X0)
% 0.58/0.80          | (v2_funct_1 @ X0)
% 0.58/0.80          | ~ (v1_relat_1 @ (sk_C @ X0))
% 0.58/0.80          | ~ (v1_relat_1 @ X1)
% 0.58/0.80          | ~ (v1_relat_1 @ X0))),
% 0.58/0.80      inference('sup+', [status(thm)], ['11', '12'])).
% 0.58/0.80  thf('14', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         (~ (v1_relat_1 @ X1)
% 0.58/0.80          | ~ (v1_relat_1 @ (sk_C @ X0))
% 0.58/0.80          | (v2_funct_1 @ X0)
% 0.58/0.80          | ~ (v1_funct_1 @ X0)
% 0.58/0.80          | ~ (v1_relat_1 @ X0)
% 0.58/0.80          | ((k5_relat_1 @ (k5_relat_1 @ (sk_B @ X0) @ X0) @ X1)
% 0.58/0.80              = (k5_relat_1 @ (sk_C @ X0) @ (k5_relat_1 @ X0 @ X1))))),
% 0.58/0.80      inference('simplify', [status(thm)], ['13'])).
% 0.58/0.80  thf('15', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         (~ (v1_relat_1 @ X0)
% 0.58/0.80          | ~ (v1_funct_1 @ X0)
% 0.58/0.80          | (v2_funct_1 @ X0)
% 0.58/0.80          | ((k5_relat_1 @ (k5_relat_1 @ (sk_B @ X0) @ X0) @ X1)
% 0.58/0.80              = (k5_relat_1 @ (sk_C @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 0.58/0.80          | ~ (v1_relat_1 @ X0)
% 0.58/0.80          | ~ (v1_funct_1 @ X0)
% 0.58/0.80          | (v2_funct_1 @ X0)
% 0.58/0.80          | ~ (v1_relat_1 @ X1))),
% 0.58/0.80      inference('sup-', [status(thm)], ['10', '14'])).
% 0.58/0.80  thf('16', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         (~ (v1_relat_1 @ X1)
% 0.58/0.80          | ((k5_relat_1 @ (k5_relat_1 @ (sk_B @ X0) @ X0) @ X1)
% 0.58/0.80              = (k5_relat_1 @ (sk_C @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 0.58/0.80          | (v2_funct_1 @ X0)
% 0.58/0.80          | ~ (v1_funct_1 @ X0)
% 0.58/0.80          | ~ (v1_relat_1 @ X0))),
% 0.58/0.80      inference('simplify', [status(thm)], ['15'])).
% 0.58/0.80  thf('17', plain,
% 0.58/0.80      ((((k5_relat_1 @ (k5_relat_1 @ (sk_B @ sk_A) @ sk_A) @ sk_B_1)
% 0.58/0.80          = (k5_relat_1 @ (sk_C @ sk_A) @ (k6_relat_1 @ (k1_relat_1 @ sk_A))))
% 0.58/0.80        | ~ (v1_relat_1 @ sk_A)
% 0.58/0.80        | ~ (v1_funct_1 @ sk_A)
% 0.58/0.80        | (v2_funct_1 @ sk_A)
% 0.58/0.80        | ~ (v1_relat_1 @ sk_B_1))),
% 0.58/0.80      inference('sup+', [status(thm)], ['9', '16'])).
% 0.58/0.80  thf('18', plain, ((v1_relat_1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('19', plain, ((v1_funct_1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('20', plain, ((v1_relat_1 @ sk_B_1)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('21', plain,
% 0.58/0.80      ((((k5_relat_1 @ (k5_relat_1 @ (sk_B @ sk_A) @ sk_A) @ sk_B_1)
% 0.58/0.80          = (k5_relat_1 @ (sk_C @ sk_A) @ (k6_relat_1 @ (k1_relat_1 @ sk_A))))
% 0.58/0.80        | (v2_funct_1 @ sk_A))),
% 0.58/0.80      inference('demod', [status(thm)], ['17', '18', '19', '20'])).
% 0.58/0.80  thf('22', plain, (~ (v2_funct_1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('23', plain,
% 0.58/0.80      (((k5_relat_1 @ (k5_relat_1 @ (sk_B @ sk_A) @ sk_A) @ sk_B_1)
% 0.58/0.80         = (k5_relat_1 @ (sk_C @ sk_A) @ (k6_relat_1 @ (k1_relat_1 @ sk_A))))),
% 0.58/0.80      inference('clc', [status(thm)], ['21', '22'])).
% 0.58/0.80  thf('24', plain,
% 0.58/0.80      ((((k5_relat_1 @ (sk_B @ sk_A) @ (k5_relat_1 @ sk_A @ sk_B_1))
% 0.58/0.80          = (k5_relat_1 @ (sk_C @ sk_A) @ (k6_relat_1 @ (k1_relat_1 @ sk_A))))
% 0.58/0.80        | ~ (v1_relat_1 @ (sk_B @ sk_A))
% 0.58/0.80        | ~ (v1_relat_1 @ sk_B_1)
% 0.58/0.80        | ~ (v1_relat_1 @ sk_A))),
% 0.58/0.80      inference('sup+', [status(thm)], ['8', '23'])).
% 0.58/0.80  thf('25', plain,
% 0.58/0.80      (((k5_relat_1 @ sk_A @ sk_B_1) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('26', plain, ((v1_relat_1 @ sk_B_1)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('27', plain, ((v1_relat_1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('28', plain,
% 0.58/0.80      ((((k5_relat_1 @ (sk_B @ sk_A) @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 0.58/0.80          = (k5_relat_1 @ (sk_C @ sk_A) @ (k6_relat_1 @ (k1_relat_1 @ sk_A))))
% 0.58/0.80        | ~ (v1_relat_1 @ (sk_B @ sk_A)))),
% 0.58/0.80      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 0.58/0.80  thf('29', plain,
% 0.58/0.80      ((~ (v1_relat_1 @ sk_A)
% 0.58/0.80        | ~ (v1_funct_1 @ sk_A)
% 0.58/0.80        | (v2_funct_1 @ sk_A)
% 0.58/0.80        | ((k5_relat_1 @ (sk_B @ sk_A) @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 0.58/0.80            = (k5_relat_1 @ (sk_C @ sk_A) @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))))),
% 0.58/0.80      inference('sup-', [status(thm)], ['7', '28'])).
% 0.58/0.80  thf('30', plain, ((v1_relat_1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('31', plain, ((v1_funct_1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('32', plain,
% 0.58/0.80      (((v2_funct_1 @ sk_A)
% 0.58/0.80        | ((k5_relat_1 @ (sk_B @ sk_A) @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 0.58/0.80            = (k5_relat_1 @ (sk_C @ sk_A) @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))))),
% 0.58/0.80      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.58/0.80  thf('33', plain, (~ (v2_funct_1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('34', plain,
% 0.58/0.80      (((k5_relat_1 @ (sk_B @ sk_A) @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 0.58/0.80         = (k5_relat_1 @ (sk_C @ sk_A) @ (k6_relat_1 @ (k1_relat_1 @ sk_A))))),
% 0.58/0.80      inference('clc', [status(thm)], ['32', '33'])).
% 0.58/0.80  thf(t71_relat_1, axiom,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.58/0.80       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.58/0.80  thf('35', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 0.58/0.80      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.58/0.80  thf('36', plain,
% 0.58/0.80      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.58/0.80         (~ (v2_funct_1 @ X9)
% 0.58/0.80          | ~ (v1_relat_1 @ X10)
% 0.58/0.80          | ~ (v1_funct_1 @ X10)
% 0.58/0.80          | ((X11) = (X10))
% 0.58/0.80          | ((k5_relat_1 @ X11 @ X9) != (k5_relat_1 @ X10 @ X9))
% 0.58/0.80          | ((k1_relat_1 @ X11) != (k1_relat_1 @ X10))
% 0.58/0.80          | ~ (r1_tarski @ (k2_relat_1 @ X10) @ (k1_relat_1 @ X9))
% 0.58/0.80          | ~ (r1_tarski @ (k2_relat_1 @ X11) @ (k1_relat_1 @ X9))
% 0.58/0.80          | ~ (v1_funct_1 @ X11)
% 0.58/0.80          | ~ (v1_relat_1 @ X11)
% 0.58/0.80          | ~ (v1_funct_1 @ X9)
% 0.58/0.80          | ~ (v1_relat_1 @ X9))),
% 0.58/0.80      inference('cnf', [status(esa)], [t49_funct_1])).
% 0.58/0.80  thf('37', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.80         (~ (r1_tarski @ (k2_relat_1 @ X1) @ X0)
% 0.58/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.58/0.80          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.58/0.80          | ~ (v1_relat_1 @ X2)
% 0.58/0.80          | ~ (v1_funct_1 @ X2)
% 0.58/0.80          | ~ (r1_tarski @ (k2_relat_1 @ X2) @ (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.58/0.80          | ((k1_relat_1 @ X2) != (k1_relat_1 @ X1))
% 0.58/0.80          | ((k5_relat_1 @ X2 @ (k6_relat_1 @ X0))
% 0.58/0.80              != (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.58/0.80          | ((X2) = (X1))
% 0.58/0.80          | ~ (v1_funct_1 @ X1)
% 0.58/0.80          | ~ (v1_relat_1 @ X1)
% 0.58/0.80          | ~ (v2_funct_1 @ (k6_relat_1 @ X0)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['35', '36'])).
% 0.58/0.80  thf(fc3_funct_1, axiom,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.58/0.80       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.58/0.80  thf('38', plain, (![X7 : $i]: (v1_relat_1 @ (k6_relat_1 @ X7))),
% 0.58/0.80      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.58/0.80  thf('39', plain, (![X8 : $i]: (v1_funct_1 @ (k6_relat_1 @ X8))),
% 0.58/0.80      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.58/0.80  thf('40', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 0.58/0.80      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.58/0.80  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 0.58/0.80  thf('41', plain, (![X12 : $i]: (v2_funct_1 @ (k6_relat_1 @ X12))),
% 0.58/0.80      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.58/0.80  thf('42', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.80         (~ (r1_tarski @ (k2_relat_1 @ X1) @ X0)
% 0.58/0.80          | ~ (v1_relat_1 @ X2)
% 0.58/0.80          | ~ (v1_funct_1 @ X2)
% 0.58/0.80          | ~ (r1_tarski @ (k2_relat_1 @ X2) @ X0)
% 0.58/0.80          | ((k1_relat_1 @ X2) != (k1_relat_1 @ X1))
% 0.58/0.80          | ((k5_relat_1 @ X2 @ (k6_relat_1 @ X0))
% 0.58/0.80              != (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.58/0.80          | ((X2) = (X1))
% 0.58/0.80          | ~ (v1_funct_1 @ X1)
% 0.58/0.80          | ~ (v1_relat_1 @ X1))),
% 0.58/0.80      inference('demod', [status(thm)], ['37', '38', '39', '40', '41'])).
% 0.58/0.80  thf('43', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 0.58/0.80            != (k5_relat_1 @ (sk_B @ sk_A) @ (k6_relat_1 @ (k1_relat_1 @ sk_A))))
% 0.58/0.80          | ~ (v1_relat_1 @ (sk_C @ sk_A))
% 0.58/0.80          | ~ (v1_funct_1 @ (sk_C @ sk_A))
% 0.58/0.80          | ((X0) = (sk_C @ sk_A))
% 0.58/0.80          | ((k1_relat_1 @ X0) != (k1_relat_1 @ (sk_C @ sk_A)))
% 0.58/0.80          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ sk_A))
% 0.58/0.80          | ~ (v1_funct_1 @ X0)
% 0.58/0.80          | ~ (v1_relat_1 @ X0)
% 0.58/0.80          | ~ (r1_tarski @ (k2_relat_1 @ (sk_C @ sk_A)) @ (k1_relat_1 @ sk_A)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['34', '42'])).
% 0.58/0.80  thf('44', plain,
% 0.58/0.80      (![X9 : $i]:
% 0.58/0.80         ((v1_relat_1 @ (sk_B @ X9))
% 0.58/0.80          | (v2_funct_1 @ X9)
% 0.58/0.80          | ~ (v1_funct_1 @ X9)
% 0.58/0.80          | ~ (v1_relat_1 @ X9))),
% 0.58/0.80      inference('cnf', [status(esa)], [t49_funct_1])).
% 0.58/0.80  thf('45', plain,
% 0.58/0.80      (![X9 : $i]:
% 0.58/0.80         ((r1_tarski @ (k2_relat_1 @ (sk_B @ X9)) @ (k1_relat_1 @ X9))
% 0.58/0.80          | (v2_funct_1 @ X9)
% 0.58/0.80          | ~ (v1_funct_1 @ X9)
% 0.58/0.80          | ~ (v1_relat_1 @ X9))),
% 0.58/0.80      inference('cnf', [status(esa)], [t49_funct_1])).
% 0.58/0.80  thf('46', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 0.58/0.80      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.58/0.80  thf(t46_relat_1, axiom,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( v1_relat_1 @ A ) =>
% 0.58/0.80       ( ![B:$i]:
% 0.58/0.80         ( ( v1_relat_1 @ B ) =>
% 0.58/0.80           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.58/0.80             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.58/0.80  thf('47', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         (~ (v1_relat_1 @ X0)
% 0.58/0.80          | ((k1_relat_1 @ (k5_relat_1 @ X1 @ X0)) = (k1_relat_1 @ X1))
% 0.58/0.80          | ~ (r1_tarski @ (k2_relat_1 @ X1) @ (k1_relat_1 @ X0))
% 0.58/0.80          | ~ (v1_relat_1 @ X1))),
% 0.58/0.80      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.58/0.80  thf('48', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         (~ (r1_tarski @ (k2_relat_1 @ X1) @ X0)
% 0.58/0.80          | ~ (v1_relat_1 @ X1)
% 0.58/0.80          | ((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.58/0.80              = (k1_relat_1 @ X1))
% 0.58/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['46', '47'])).
% 0.58/0.80  thf('49', plain, (![X7 : $i]: (v1_relat_1 @ (k6_relat_1 @ X7))),
% 0.58/0.80      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.58/0.80  thf('50', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         (~ (r1_tarski @ (k2_relat_1 @ X1) @ X0)
% 0.58/0.80          | ~ (v1_relat_1 @ X1)
% 0.58/0.80          | ((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.58/0.80              = (k1_relat_1 @ X1)))),
% 0.58/0.80      inference('demod', [status(thm)], ['48', '49'])).
% 0.58/0.80  thf('51', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (~ (v1_relat_1 @ X0)
% 0.58/0.80          | ~ (v1_funct_1 @ X0)
% 0.58/0.80          | (v2_funct_1 @ X0)
% 0.58/0.80          | ((k1_relat_1 @ 
% 0.58/0.80              (k5_relat_1 @ (sk_B @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0))))
% 0.58/0.80              = (k1_relat_1 @ (sk_B @ X0)))
% 0.58/0.80          | ~ (v1_relat_1 @ (sk_B @ X0)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['45', '50'])).
% 0.58/0.80  thf('52', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (~ (v1_relat_1 @ X0)
% 0.58/0.80          | ~ (v1_funct_1 @ X0)
% 0.58/0.80          | (v2_funct_1 @ X0)
% 0.58/0.80          | ((k1_relat_1 @ 
% 0.58/0.80              (k5_relat_1 @ (sk_B @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0))))
% 0.58/0.80              = (k1_relat_1 @ (sk_B @ X0)))
% 0.58/0.80          | (v2_funct_1 @ X0)
% 0.58/0.80          | ~ (v1_funct_1 @ X0)
% 0.58/0.80          | ~ (v1_relat_1 @ X0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['44', '51'])).
% 0.58/0.80  thf('53', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (((k1_relat_1 @ 
% 0.58/0.80            (k5_relat_1 @ (sk_B @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0))))
% 0.58/0.80            = (k1_relat_1 @ (sk_B @ X0)))
% 0.58/0.80          | (v2_funct_1 @ X0)
% 0.58/0.80          | ~ (v1_funct_1 @ X0)
% 0.58/0.80          | ~ (v1_relat_1 @ X0))),
% 0.58/0.80      inference('simplify', [status(thm)], ['52'])).
% 0.58/0.80  thf('54', plain,
% 0.58/0.80      (((k5_relat_1 @ (sk_B @ sk_A) @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 0.58/0.80         = (k5_relat_1 @ (sk_C @ sk_A) @ (k6_relat_1 @ (k1_relat_1 @ sk_A))))),
% 0.58/0.80      inference('clc', [status(thm)], ['32', '33'])).
% 0.58/0.80  thf('55', plain,
% 0.58/0.80      (![X9 : $i]:
% 0.58/0.80         ((v1_relat_1 @ (sk_C @ X9))
% 0.58/0.80          | (v2_funct_1 @ X9)
% 0.58/0.80          | ~ (v1_funct_1 @ X9)
% 0.58/0.80          | ~ (v1_relat_1 @ X9))),
% 0.58/0.80      inference('cnf', [status(esa)], [t49_funct_1])).
% 0.58/0.80  thf('56', plain,
% 0.58/0.80      (![X9 : $i]:
% 0.58/0.80         ((r1_tarski @ (k2_relat_1 @ (sk_C @ X9)) @ (k1_relat_1 @ X9))
% 0.58/0.80          | (v2_funct_1 @ X9)
% 0.58/0.80          | ~ (v1_funct_1 @ X9)
% 0.58/0.80          | ~ (v1_relat_1 @ X9))),
% 0.58/0.80      inference('cnf', [status(esa)], [t49_funct_1])).
% 0.58/0.80  thf('57', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         (~ (r1_tarski @ (k2_relat_1 @ X1) @ X0)
% 0.58/0.80          | ~ (v1_relat_1 @ X1)
% 0.58/0.80          | ((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.58/0.80              = (k1_relat_1 @ X1)))),
% 0.58/0.80      inference('demod', [status(thm)], ['48', '49'])).
% 0.58/0.80  thf('58', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (~ (v1_relat_1 @ X0)
% 0.58/0.80          | ~ (v1_funct_1 @ X0)
% 0.58/0.80          | (v2_funct_1 @ X0)
% 0.58/0.80          | ((k1_relat_1 @ 
% 0.58/0.80              (k5_relat_1 @ (sk_C @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0))))
% 0.58/0.80              = (k1_relat_1 @ (sk_C @ X0)))
% 0.58/0.80          | ~ (v1_relat_1 @ (sk_C @ X0)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['56', '57'])).
% 0.58/0.80  thf('59', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (~ (v1_relat_1 @ X0)
% 0.58/0.80          | ~ (v1_funct_1 @ X0)
% 0.58/0.80          | (v2_funct_1 @ X0)
% 0.58/0.80          | ((k1_relat_1 @ 
% 0.58/0.80              (k5_relat_1 @ (sk_C @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0))))
% 0.58/0.80              = (k1_relat_1 @ (sk_C @ X0)))
% 0.58/0.80          | (v2_funct_1 @ X0)
% 0.58/0.80          | ~ (v1_funct_1 @ X0)
% 0.58/0.80          | ~ (v1_relat_1 @ X0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['55', '58'])).
% 0.58/0.80  thf('60', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (((k1_relat_1 @ 
% 0.58/0.80            (k5_relat_1 @ (sk_C @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0))))
% 0.58/0.80            = (k1_relat_1 @ (sk_C @ X0)))
% 0.58/0.80          | (v2_funct_1 @ X0)
% 0.58/0.80          | ~ (v1_funct_1 @ X0)
% 0.58/0.80          | ~ (v1_relat_1 @ X0))),
% 0.58/0.80      inference('simplify', [status(thm)], ['59'])).
% 0.58/0.80  thf('61', plain,
% 0.58/0.80      ((((k1_relat_1 @ 
% 0.58/0.80          (k5_relat_1 @ (sk_B @ sk_A) @ (k6_relat_1 @ (k1_relat_1 @ sk_A))))
% 0.58/0.80          = (k1_relat_1 @ (sk_C @ sk_A)))
% 0.58/0.80        | ~ (v1_relat_1 @ sk_A)
% 0.58/0.80        | ~ (v1_funct_1 @ sk_A)
% 0.58/0.80        | (v2_funct_1 @ sk_A))),
% 0.58/0.80      inference('sup+', [status(thm)], ['54', '60'])).
% 0.58/0.80  thf('62', plain, ((v1_relat_1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('63', plain, ((v1_funct_1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('64', plain,
% 0.58/0.80      ((((k1_relat_1 @ 
% 0.58/0.80          (k5_relat_1 @ (sk_B @ sk_A) @ (k6_relat_1 @ (k1_relat_1 @ sk_A))))
% 0.58/0.80          = (k1_relat_1 @ (sk_C @ sk_A)))
% 0.58/0.80        | (v2_funct_1 @ sk_A))),
% 0.58/0.80      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.58/0.80  thf('65', plain, (~ (v2_funct_1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('66', plain,
% 0.58/0.80      (((k1_relat_1 @ 
% 0.58/0.80         (k5_relat_1 @ (sk_B @ sk_A) @ (k6_relat_1 @ (k1_relat_1 @ sk_A))))
% 0.58/0.80         = (k1_relat_1 @ (sk_C @ sk_A)))),
% 0.58/0.80      inference('clc', [status(thm)], ['64', '65'])).
% 0.58/0.80  thf('67', plain,
% 0.58/0.80      ((((k1_relat_1 @ (sk_B @ sk_A)) = (k1_relat_1 @ (sk_C @ sk_A)))
% 0.58/0.80        | ~ (v1_relat_1 @ sk_A)
% 0.58/0.80        | ~ (v1_funct_1 @ sk_A)
% 0.58/0.80        | (v2_funct_1 @ sk_A))),
% 0.58/0.80      inference('sup+', [status(thm)], ['53', '66'])).
% 0.58/0.80  thf('68', plain, ((v1_relat_1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('69', plain, ((v1_funct_1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('70', plain,
% 0.58/0.80      ((((k1_relat_1 @ (sk_B @ sk_A)) = (k1_relat_1 @ (sk_C @ sk_A)))
% 0.58/0.80        | (v2_funct_1 @ sk_A))),
% 0.58/0.80      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.58/0.80  thf('71', plain, (~ (v2_funct_1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('72', plain,
% 0.58/0.80      (((k1_relat_1 @ (sk_B @ sk_A)) = (k1_relat_1 @ (sk_C @ sk_A)))),
% 0.58/0.80      inference('clc', [status(thm)], ['70', '71'])).
% 0.58/0.80  thf('73', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 0.58/0.80            != (k5_relat_1 @ (sk_B @ sk_A) @ (k6_relat_1 @ (k1_relat_1 @ sk_A))))
% 0.58/0.80          | ~ (v1_relat_1 @ (sk_C @ sk_A))
% 0.58/0.80          | ~ (v1_funct_1 @ (sk_C @ sk_A))
% 0.58/0.80          | ((X0) = (sk_C @ sk_A))
% 0.58/0.80          | ((k1_relat_1 @ X0) != (k1_relat_1 @ (sk_B @ sk_A)))
% 0.58/0.80          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ sk_A))
% 0.58/0.80          | ~ (v1_funct_1 @ X0)
% 0.58/0.80          | ~ (v1_relat_1 @ X0)
% 0.58/0.80          | ~ (r1_tarski @ (k2_relat_1 @ (sk_C @ sk_A)) @ (k1_relat_1 @ sk_A)))),
% 0.58/0.80      inference('demod', [status(thm)], ['43', '72'])).
% 0.58/0.80  thf('74', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (~ (v1_relat_1 @ sk_A)
% 0.58/0.80          | ~ (v1_funct_1 @ sk_A)
% 0.58/0.80          | (v2_funct_1 @ sk_A)
% 0.58/0.80          | ~ (v1_relat_1 @ X0)
% 0.58/0.80          | ~ (v1_funct_1 @ X0)
% 0.58/0.80          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ sk_A))
% 0.58/0.80          | ((k1_relat_1 @ X0) != (k1_relat_1 @ (sk_B @ sk_A)))
% 0.58/0.80          | ((X0) = (sk_C @ sk_A))
% 0.58/0.80          | ~ (v1_funct_1 @ (sk_C @ sk_A))
% 0.58/0.80          | ~ (v1_relat_1 @ (sk_C @ sk_A))
% 0.58/0.80          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 0.58/0.80              != (k5_relat_1 @ (sk_B @ sk_A) @ 
% 0.58/0.80                  (k6_relat_1 @ (k1_relat_1 @ sk_A)))))),
% 0.58/0.80      inference('sup-', [status(thm)], ['6', '73'])).
% 0.58/0.80  thf('75', plain, ((v1_relat_1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('76', plain, ((v1_funct_1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('77', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((v2_funct_1 @ sk_A)
% 0.58/0.80          | ~ (v1_relat_1 @ X0)
% 0.58/0.80          | ~ (v1_funct_1 @ X0)
% 0.58/0.80          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ sk_A))
% 0.58/0.80          | ((k1_relat_1 @ X0) != (k1_relat_1 @ (sk_B @ sk_A)))
% 0.58/0.80          | ((X0) = (sk_C @ sk_A))
% 0.58/0.80          | ~ (v1_funct_1 @ (sk_C @ sk_A))
% 0.58/0.80          | ~ (v1_relat_1 @ (sk_C @ sk_A))
% 0.58/0.80          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 0.58/0.80              != (k5_relat_1 @ (sk_B @ sk_A) @ 
% 0.58/0.80                  (k6_relat_1 @ (k1_relat_1 @ sk_A)))))),
% 0.58/0.80      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.58/0.80  thf('78', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (~ (v1_relat_1 @ sk_A)
% 0.58/0.80          | ~ (v1_funct_1 @ sk_A)
% 0.58/0.80          | (v2_funct_1 @ sk_A)
% 0.58/0.80          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 0.58/0.80              != (k5_relat_1 @ (sk_B @ sk_A) @ 
% 0.58/0.80                  (k6_relat_1 @ (k1_relat_1 @ sk_A))))
% 0.58/0.80          | ~ (v1_relat_1 @ (sk_C @ sk_A))
% 0.58/0.80          | ((X0) = (sk_C @ sk_A))
% 0.58/0.80          | ((k1_relat_1 @ X0) != (k1_relat_1 @ (sk_B @ sk_A)))
% 0.58/0.80          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ sk_A))
% 0.58/0.80          | ~ (v1_funct_1 @ X0)
% 0.58/0.80          | ~ (v1_relat_1 @ X0)
% 0.58/0.80          | (v2_funct_1 @ sk_A))),
% 0.58/0.80      inference('sup-', [status(thm)], ['5', '77'])).
% 0.58/0.80  thf('79', plain, ((v1_relat_1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('80', plain, ((v1_funct_1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('81', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((v2_funct_1 @ sk_A)
% 0.58/0.80          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 0.58/0.80              != (k5_relat_1 @ (sk_B @ sk_A) @ 
% 0.58/0.80                  (k6_relat_1 @ (k1_relat_1 @ sk_A))))
% 0.58/0.80          | ~ (v1_relat_1 @ (sk_C @ sk_A))
% 0.58/0.80          | ((X0) = (sk_C @ sk_A))
% 0.58/0.80          | ((k1_relat_1 @ X0) != (k1_relat_1 @ (sk_B @ sk_A)))
% 0.58/0.80          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ sk_A))
% 0.58/0.80          | ~ (v1_funct_1 @ X0)
% 0.58/0.80          | ~ (v1_relat_1 @ X0)
% 0.58/0.80          | (v2_funct_1 @ sk_A))),
% 0.58/0.80      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.58/0.80  thf('82', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (~ (v1_relat_1 @ X0)
% 0.58/0.80          | ~ (v1_funct_1 @ X0)
% 0.58/0.80          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ sk_A))
% 0.58/0.80          | ((k1_relat_1 @ X0) != (k1_relat_1 @ (sk_B @ sk_A)))
% 0.58/0.80          | ((X0) = (sk_C @ sk_A))
% 0.58/0.80          | ~ (v1_relat_1 @ (sk_C @ sk_A))
% 0.58/0.80          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 0.58/0.80              != (k5_relat_1 @ (sk_B @ sk_A) @ 
% 0.58/0.80                  (k6_relat_1 @ (k1_relat_1 @ sk_A))))
% 0.58/0.80          | (v2_funct_1 @ sk_A))),
% 0.58/0.80      inference('simplify', [status(thm)], ['81'])).
% 0.58/0.80  thf('83', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (~ (v1_relat_1 @ sk_A)
% 0.58/0.80          | ~ (v1_funct_1 @ sk_A)
% 0.58/0.80          | (v2_funct_1 @ sk_A)
% 0.58/0.80          | (v2_funct_1 @ sk_A)
% 0.58/0.80          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 0.58/0.80              != (k5_relat_1 @ (sk_B @ sk_A) @ 
% 0.58/0.80                  (k6_relat_1 @ (k1_relat_1 @ sk_A))))
% 0.58/0.80          | ((X0) = (sk_C @ sk_A))
% 0.58/0.80          | ((k1_relat_1 @ X0) != (k1_relat_1 @ (sk_B @ sk_A)))
% 0.58/0.80          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ sk_A))
% 0.58/0.80          | ~ (v1_funct_1 @ X0)
% 0.58/0.80          | ~ (v1_relat_1 @ X0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['4', '82'])).
% 0.58/0.80  thf('84', plain, ((v1_relat_1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('85', plain, ((v1_funct_1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('86', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((v2_funct_1 @ sk_A)
% 0.58/0.80          | (v2_funct_1 @ sk_A)
% 0.58/0.80          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 0.58/0.80              != (k5_relat_1 @ (sk_B @ sk_A) @ 
% 0.58/0.80                  (k6_relat_1 @ (k1_relat_1 @ sk_A))))
% 0.58/0.80          | ((X0) = (sk_C @ sk_A))
% 0.58/0.80          | ((k1_relat_1 @ X0) != (k1_relat_1 @ (sk_B @ sk_A)))
% 0.58/0.80          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ sk_A))
% 0.58/0.80          | ~ (v1_funct_1 @ X0)
% 0.58/0.80          | ~ (v1_relat_1 @ X0))),
% 0.58/0.80      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.58/0.80  thf('87', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (~ (v1_relat_1 @ X0)
% 0.58/0.80          | ~ (v1_funct_1 @ X0)
% 0.58/0.80          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ sk_A))
% 0.58/0.80          | ((k1_relat_1 @ X0) != (k1_relat_1 @ (sk_B @ sk_A)))
% 0.58/0.80          | ((X0) = (sk_C @ sk_A))
% 0.58/0.80          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 0.58/0.80              != (k5_relat_1 @ (sk_B @ sk_A) @ 
% 0.58/0.80                  (k6_relat_1 @ (k1_relat_1 @ sk_A))))
% 0.58/0.80          | (v2_funct_1 @ sk_A))),
% 0.58/0.80      inference('simplify', [status(thm)], ['86'])).
% 0.58/0.80  thf('88', plain,
% 0.58/0.80      (((v2_funct_1 @ sk_A)
% 0.58/0.80        | ((sk_B @ sk_A) = (sk_C @ sk_A))
% 0.58/0.80        | ((k1_relat_1 @ (sk_B @ sk_A)) != (k1_relat_1 @ (sk_B @ sk_A)))
% 0.58/0.80        | ~ (r1_tarski @ (k2_relat_1 @ (sk_B @ sk_A)) @ (k1_relat_1 @ sk_A))
% 0.58/0.80        | ~ (v1_funct_1 @ (sk_B @ sk_A))
% 0.58/0.80        | ~ (v1_relat_1 @ (sk_B @ sk_A)))),
% 0.58/0.80      inference('eq_res', [status(thm)], ['87'])).
% 0.58/0.80  thf('89', plain,
% 0.58/0.80      ((~ (v1_relat_1 @ (sk_B @ sk_A))
% 0.58/0.80        | ~ (v1_funct_1 @ (sk_B @ sk_A))
% 0.58/0.80        | ~ (r1_tarski @ (k2_relat_1 @ (sk_B @ sk_A)) @ (k1_relat_1 @ sk_A))
% 0.58/0.80        | ((sk_B @ sk_A) = (sk_C @ sk_A))
% 0.58/0.80        | (v2_funct_1 @ sk_A))),
% 0.58/0.80      inference('simplify', [status(thm)], ['88'])).
% 0.58/0.80  thf('90', plain,
% 0.58/0.80      ((~ (v1_relat_1 @ sk_A)
% 0.58/0.80        | ~ (v1_funct_1 @ sk_A)
% 0.58/0.80        | (v2_funct_1 @ sk_A)
% 0.58/0.80        | (v2_funct_1 @ sk_A)
% 0.58/0.80        | ((sk_B @ sk_A) = (sk_C @ sk_A))
% 0.58/0.80        | ~ (v1_funct_1 @ (sk_B @ sk_A))
% 0.58/0.80        | ~ (v1_relat_1 @ (sk_B @ sk_A)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['3', '89'])).
% 0.58/0.80  thf('91', plain, ((v1_relat_1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('92', plain, ((v1_funct_1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('93', plain,
% 0.58/0.80      (((v2_funct_1 @ sk_A)
% 0.58/0.80        | (v2_funct_1 @ sk_A)
% 0.58/0.80        | ((sk_B @ sk_A) = (sk_C @ sk_A))
% 0.58/0.80        | ~ (v1_funct_1 @ (sk_B @ sk_A))
% 0.58/0.80        | ~ (v1_relat_1 @ (sk_B @ sk_A)))),
% 0.58/0.80      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.58/0.80  thf('94', plain,
% 0.58/0.80      ((~ (v1_relat_1 @ (sk_B @ sk_A))
% 0.58/0.80        | ~ (v1_funct_1 @ (sk_B @ sk_A))
% 0.58/0.80        | ((sk_B @ sk_A) = (sk_C @ sk_A))
% 0.58/0.80        | (v2_funct_1 @ sk_A))),
% 0.58/0.80      inference('simplify', [status(thm)], ['93'])).
% 0.58/0.80  thf('95', plain,
% 0.58/0.80      ((~ (v1_relat_1 @ sk_A)
% 0.58/0.80        | ~ (v1_funct_1 @ sk_A)
% 0.58/0.80        | (v2_funct_1 @ sk_A)
% 0.58/0.80        | (v2_funct_1 @ sk_A)
% 0.58/0.80        | ((sk_B @ sk_A) = (sk_C @ sk_A))
% 0.58/0.80        | ~ (v1_funct_1 @ (sk_B @ sk_A)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['2', '94'])).
% 0.58/0.80  thf('96', plain, ((v1_relat_1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('97', plain, ((v1_funct_1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('98', plain,
% 0.58/0.80      (((v2_funct_1 @ sk_A)
% 0.58/0.80        | (v2_funct_1 @ sk_A)
% 0.58/0.80        | ((sk_B @ sk_A) = (sk_C @ sk_A))
% 0.58/0.80        | ~ (v1_funct_1 @ (sk_B @ sk_A)))),
% 0.58/0.80      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.58/0.80  thf('99', plain,
% 0.58/0.80      ((~ (v1_funct_1 @ (sk_B @ sk_A))
% 0.58/0.80        | ((sk_B @ sk_A) = (sk_C @ sk_A))
% 0.58/0.80        | (v2_funct_1 @ sk_A))),
% 0.58/0.80      inference('simplify', [status(thm)], ['98'])).
% 0.58/0.80  thf('100', plain, (~ (v2_funct_1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('101', plain,
% 0.58/0.80      ((((sk_B @ sk_A) = (sk_C @ sk_A)) | ~ (v1_funct_1 @ (sk_B @ sk_A)))),
% 0.58/0.80      inference('clc', [status(thm)], ['99', '100'])).
% 0.58/0.80  thf('102', plain,
% 0.58/0.80      ((~ (v1_relat_1 @ sk_A)
% 0.58/0.80        | ~ (v1_funct_1 @ sk_A)
% 0.58/0.80        | (v2_funct_1 @ sk_A)
% 0.58/0.80        | ((sk_B @ sk_A) = (sk_C @ sk_A)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['1', '101'])).
% 0.58/0.80  thf('103', plain, ((v1_relat_1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('104', plain, ((v1_funct_1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('105', plain, (((v2_funct_1 @ sk_A) | ((sk_B @ sk_A) = (sk_C @ sk_A)))),
% 0.58/0.80      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.58/0.80  thf('106', plain, (~ (v2_funct_1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('107', plain, (((sk_B @ sk_A) = (sk_C @ sk_A))),
% 0.58/0.80      inference('clc', [status(thm)], ['105', '106'])).
% 0.58/0.80  thf('108', plain,
% 0.58/0.80      (![X9 : $i]:
% 0.58/0.80         (((sk_B @ X9) != (sk_C @ X9))
% 0.58/0.80          | (v2_funct_1 @ X9)
% 0.58/0.80          | ~ (v1_funct_1 @ X9)
% 0.58/0.80          | ~ (v1_relat_1 @ X9))),
% 0.58/0.80      inference('cnf', [status(esa)], [t49_funct_1])).
% 0.58/0.80  thf('109', plain,
% 0.58/0.80      ((((sk_B @ sk_A) != (sk_B @ sk_A))
% 0.58/0.80        | ~ (v1_relat_1 @ sk_A)
% 0.58/0.80        | ~ (v1_funct_1 @ sk_A)
% 0.58/0.80        | (v2_funct_1 @ sk_A))),
% 0.58/0.80      inference('sup-', [status(thm)], ['107', '108'])).
% 0.58/0.80  thf('110', plain, ((v1_relat_1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('111', plain, ((v1_funct_1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('112', plain, ((((sk_B @ sk_A) != (sk_B @ sk_A)) | (v2_funct_1 @ sk_A))),
% 0.58/0.80      inference('demod', [status(thm)], ['109', '110', '111'])).
% 0.58/0.80  thf('113', plain, ((v2_funct_1 @ sk_A)),
% 0.58/0.80      inference('simplify', [status(thm)], ['112'])).
% 0.58/0.80  thf('114', plain, ($false), inference('demod', [status(thm)], ['0', '113'])).
% 0.58/0.80  
% 0.58/0.80  % SZS output end Refutation
% 0.58/0.80  
% 0.63/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
