%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lCehpM27T9

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:16 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 182 expanded)
%              Number of leaves         :   18 (  61 expanded)
%              Depth                    :   41
%              Number of atoms          : 1326 (2774 expanded)
%              Number of equality atoms :   95 ( 189 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
      ( ( ( k1_relat_1 @ ( sk_B @ X9 ) )
        = ( k1_relat_1 @ ( sk_C @ X9 ) ) )
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
      ( ( v1_funct_1 @ ( sk_B @ X9 ) )
      | ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t49_funct_1])).

thf('4',plain,(
    ! [X9: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_B @ X9 ) ) @ ( k1_relat_1 @ X9 ) )
      | ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t49_funct_1])).

thf('5',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( sk_C @ X9 ) )
      | ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t49_funct_1])).

thf('6',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( sk_C @ X9 ) )
      | ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t49_funct_1])).

thf('7',plain,(
    ! [X9: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C @ X9 ) ) @ ( k1_relat_1 @ X9 ) )
      | ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t49_funct_1])).

thf('8',plain,(
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

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('10',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B_1 )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( sk_C @ X9 ) )
      | ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t49_funct_1])).

thf('12',plain,(
    ! [X9: $i] :
      ( ( ( k5_relat_1 @ ( sk_B @ X9 ) @ X9 )
        = ( k5_relat_1 @ ( sk_C @ X9 ) @ X9 ) )
      | ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t49_funct_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ ( sk_B @ X0 ) @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( sk_C @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( sk_C @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( sk_C @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ ( sk_B @ X0 ) @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( sk_C @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
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
    inference('sup-',[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ ( sk_B @ X0 ) @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( sk_C @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ( ( k5_relat_1 @ ( k5_relat_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_B_1 )
      = ( k5_relat_1 @ ( sk_C @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['10','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( k5_relat_1 @ ( k5_relat_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_B_1 )
      = ( k5_relat_1 @ ( sk_C @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19','20','21'])).

thf('23',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k5_relat_1 @ ( k5_relat_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_B_1 )
    = ( k5_relat_1 @ ( sk_C @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k5_relat_1 @ ( sk_B @ sk_A ) @ ( k5_relat_1 @ sk_A @ sk_B_1 ) )
      = ( k5_relat_1 @ ( sk_C @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ ( sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['9','24'])).

thf('26',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B_1 )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( k5_relat_1 @ ( sk_B @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
      = ( k5_relat_1 @ ( sk_C @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ ( sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A )
    | ( ( k5_relat_1 @ ( sk_B @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
      = ( k5_relat_1 @ ( sk_C @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['8','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v2_funct_1 @ sk_A )
    | ( ( k5_relat_1 @ ( sk_B @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
      = ( k5_relat_1 @ ( sk_C @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k5_relat_1 @ ( sk_B @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
    = ( k5_relat_1 @ ( sk_C @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('36',plain,(
    ! [X3: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X3 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('37',plain,(
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

thf('38',plain,(
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
    inference('sup-',[status(thm)],['36','37'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('39',plain,(
    ! [X5: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('40',plain,(
    ! [X6: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('41',plain,(
    ! [X3: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X3 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('42',plain,(
    ! [X8: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('43',plain,(
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
    inference(demod,[status(thm)],['38','39','40','41','42'])).

thf('44',plain,(
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
    inference('sup-',[status(thm)],['35','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( v2_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ sk_A ) )
      | ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ ( sk_C @ sk_A ) ) )
      | ( X0
        = ( sk_C @ sk_A ) )
      | ~ ( v1_funct_1 @ ( sk_C @ sk_A ) )
      | ~ ( v1_relat_1 @ ( sk_C @ sk_A ) )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
       != ( k5_relat_1 @ ( sk_B @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['7','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ sk_A ) )
      | ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ ( sk_C @ sk_A ) ) )
      | ( X0
        = ( sk_C @ sk_A ) )
      | ~ ( v1_funct_1 @ ( sk_C @ sk_A ) )
      | ~ ( v1_relat_1 @ ( sk_C @ sk_A ) )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
       != ( k5_relat_1 @ ( sk_B @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
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
       != ( k1_relat_1 @ ( sk_C @ sk_A ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ sk_A )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
       != ( k5_relat_1 @ ( sk_B @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) )
      | ~ ( v1_relat_1 @ ( sk_C @ sk_A ) )
      | ( X0
        = ( sk_C @ sk_A ) )
      | ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ ( sk_C @ sk_A ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ sk_A ) )
      | ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ ( sk_C @ sk_A ) ) )
      | ( X0
        = ( sk_C @ sk_A ) )
      | ~ ( v1_relat_1 @ ( sk_C @ sk_A ) )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
       != ( k5_relat_1 @ ( sk_B @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) )
      | ( v2_funct_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
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
       != ( k1_relat_1 @ ( sk_C @ sk_A ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ sk_A )
      | ( v2_funct_1 @ sk_A )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
       != ( k5_relat_1 @ ( sk_B @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) )
      | ( X0
        = ( sk_C @ sk_A ) )
      | ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ ( sk_C @ sk_A ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ sk_A ) )
      | ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ ( sk_C @ sk_A ) ) )
      | ( X0
        = ( sk_C @ sk_A ) )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
       != ( k5_relat_1 @ ( sk_B @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) )
      | ( v2_funct_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( v2_funct_1 @ sk_A )
    | ( ( sk_B @ sk_A )
      = ( sk_C @ sk_A ) )
    | ( ( k1_relat_1 @ ( sk_B @ sk_A ) )
     != ( k1_relat_1 @ ( sk_C @ sk_A ) ) )
    | ~ ( r1_tarski @ ( k2_relat_1 @ ( sk_B @ sk_A ) ) @ ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ ( sk_B @ sk_A ) ) ),
    inference(eq_res,[status(thm)],['58'])).

thf('60',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( sk_B @ sk_A ) )
    | ~ ( v1_funct_1 @ ( sk_B @ sk_A ) )
    | ( ( k1_relat_1 @ ( sk_B @ sk_A ) )
     != ( k1_relat_1 @ ( sk_C @ sk_A ) ) )
    | ( ( sk_B @ sk_A )
      = ( sk_C @ sk_A ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v2_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( sk_B @ sk_A ) )
    | ~ ( v1_funct_1 @ ( sk_B @ sk_A ) )
    | ( ( k1_relat_1 @ ( sk_B @ sk_A ) )
     != ( k1_relat_1 @ ( sk_C @ sk_A ) ) )
    | ( ( sk_B @ sk_A )
      = ( sk_C @ sk_A ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ( ( sk_B @ sk_A )
      = ( sk_C @ sk_A ) )
    | ( ( k1_relat_1 @ ( sk_B @ sk_A ) )
     != ( k1_relat_1 @ ( sk_C @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ ( sk_B @ sk_A ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( sk_B @ sk_A ) )
    | ( ( k1_relat_1 @ ( sk_B @ sk_A ) )
     != ( k1_relat_1 @ ( sk_C @ sk_A ) ) )
    | ( ( sk_B @ sk_A )
      = ( sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v2_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( sk_B @ sk_A ) )
    | ( ( k1_relat_1 @ ( sk_B @ sk_A ) )
     != ( k1_relat_1 @ ( sk_C @ sk_A ) ) )
    | ( ( sk_B @ sk_A )
      = ( sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,
    ( ( ( sk_B @ sk_A )
      = ( sk_C @ sk_A ) )
    | ( ( k1_relat_1 @ ( sk_B @ sk_A ) )
     != ( k1_relat_1 @ ( sk_C @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( sk_B @ sk_A ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A )
    | ( ( k1_relat_1 @ ( sk_B @ sk_A ) )
     != ( k1_relat_1 @ ( sk_C @ sk_A ) ) )
    | ( ( sk_B @ sk_A )
      = ( sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( v2_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A )
    | ( ( k1_relat_1 @ ( sk_B @ sk_A ) )
     != ( k1_relat_1 @ ( sk_C @ sk_A ) ) )
    | ( ( sk_B @ sk_A )
      = ( sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ( ( sk_B @ sk_A )
      = ( sk_C @ sk_A ) )
    | ( ( k1_relat_1 @ ( sk_B @ sk_A ) )
     != ( k1_relat_1 @ ( sk_C @ sk_A ) ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( ( k1_relat_1 @ ( sk_B @ sk_A ) )
     != ( k1_relat_1 @ ( sk_C @ sk_A ) ) )
    | ( ( sk_B @ sk_A )
      = ( sk_C @ sk_A ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( k1_relat_1 @ ( sk_B @ sk_A ) )
     != ( k1_relat_1 @ ( sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A )
    | ( ( sk_B @ sk_A )
      = ( sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( ( k1_relat_1 @ ( sk_B @ sk_A ) )
     != ( k1_relat_1 @ ( sk_B @ sk_A ) ) )
    | ( v2_funct_1 @ sk_A )
    | ( ( sk_B @ sk_A )
      = ( sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,
    ( ( ( sk_B @ sk_A )
      = ( sk_C @ sk_A ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( sk_B @ sk_A )
    = ( sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X9: $i] :
      ( ( ( sk_B @ X9 )
       != ( sk_C @ X9 ) )
      | ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t49_funct_1])).

thf('85',plain,
    ( ( ( sk_B @ sk_A )
     != ( sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( ( sk_B @ sk_A )
     != ( sk_B @ sk_A ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,(
    v2_funct_1 @ sk_A ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    $false ),
    inference(demod,[status(thm)],['0','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lCehpM27T9
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:11:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.59  % Solved by: fo/fo7.sh
% 0.38/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.59  % done 67 iterations in 0.128s
% 0.38/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.59  % SZS output start Refutation
% 0.38/0.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.38/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.59  thf(sk_B_type, type, sk_B: $i > $i).
% 0.38/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.59  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.38/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.59  thf(sk_C_type, type, sk_C: $i > $i).
% 0.38/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.59  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.38/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.59  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.38/0.59  thf(t53_funct_1, conjecture,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.59       ( ( ?[B:$i]:
% 0.38/0.59           ( ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.38/0.59             ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) ) =>
% 0.38/0.59         ( v2_funct_1 @ A ) ) ))).
% 0.38/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.59    (~( ![A:$i]:
% 0.38/0.59        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.59          ( ( ?[B:$i]:
% 0.38/0.59              ( ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.38/0.59                ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) ) =>
% 0.38/0.59            ( v2_funct_1 @ A ) ) ) )),
% 0.38/0.59    inference('cnf.neg', [status(esa)], [t53_funct_1])).
% 0.38/0.59  thf('0', plain, (~ (v2_funct_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(t49_funct_1, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.59       ( ( v2_funct_1 @ A ) <=>
% 0.38/0.59         ( ![B:$i]:
% 0.38/0.59           ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.59             ( ![C:$i]:
% 0.38/0.59               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.38/0.59                 ( ( ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) & 
% 0.38/0.59                     ( r1_tarski @ ( k2_relat_1 @ C ) @ ( k1_relat_1 @ A ) ) & 
% 0.38/0.59                     ( ( k1_relat_1 @ B ) = ( k1_relat_1 @ C ) ) & 
% 0.38/0.59                     ( ( k5_relat_1 @ B @ A ) = ( k5_relat_1 @ C @ A ) ) ) =>
% 0.38/0.59                   ( ( B ) = ( C ) ) ) ) ) ) ) ) ))).
% 0.38/0.59  thf('1', plain,
% 0.38/0.59      (![X9 : $i]:
% 0.38/0.59         (((k1_relat_1 @ (sk_B @ X9)) = (k1_relat_1 @ (sk_C @ X9)))
% 0.38/0.59          | (v2_funct_1 @ X9)
% 0.38/0.59          | ~ (v1_funct_1 @ X9)
% 0.38/0.59          | ~ (v1_relat_1 @ X9))),
% 0.38/0.59      inference('cnf', [status(esa)], [t49_funct_1])).
% 0.38/0.59  thf('2', plain,
% 0.38/0.59      (![X9 : $i]:
% 0.38/0.59         ((v1_relat_1 @ (sk_B @ X9))
% 0.38/0.59          | (v2_funct_1 @ X9)
% 0.38/0.59          | ~ (v1_funct_1 @ X9)
% 0.38/0.59          | ~ (v1_relat_1 @ X9))),
% 0.38/0.59      inference('cnf', [status(esa)], [t49_funct_1])).
% 0.38/0.59  thf('3', plain,
% 0.38/0.59      (![X9 : $i]:
% 0.38/0.59         ((v1_funct_1 @ (sk_B @ X9))
% 0.38/0.59          | (v2_funct_1 @ X9)
% 0.38/0.59          | ~ (v1_funct_1 @ X9)
% 0.38/0.59          | ~ (v1_relat_1 @ X9))),
% 0.38/0.59      inference('cnf', [status(esa)], [t49_funct_1])).
% 0.38/0.59  thf('4', plain,
% 0.38/0.59      (![X9 : $i]:
% 0.38/0.59         ((r1_tarski @ (k2_relat_1 @ (sk_B @ X9)) @ (k1_relat_1 @ X9))
% 0.38/0.59          | (v2_funct_1 @ X9)
% 0.38/0.59          | ~ (v1_funct_1 @ X9)
% 0.38/0.59          | ~ (v1_relat_1 @ X9))),
% 0.38/0.59      inference('cnf', [status(esa)], [t49_funct_1])).
% 0.38/0.59  thf('5', plain,
% 0.38/0.59      (![X9 : $i]:
% 0.38/0.59         ((v1_relat_1 @ (sk_C @ X9))
% 0.38/0.59          | (v2_funct_1 @ X9)
% 0.38/0.59          | ~ (v1_funct_1 @ X9)
% 0.38/0.59          | ~ (v1_relat_1 @ X9))),
% 0.38/0.59      inference('cnf', [status(esa)], [t49_funct_1])).
% 0.38/0.59  thf('6', plain,
% 0.38/0.59      (![X9 : $i]:
% 0.38/0.59         ((v1_funct_1 @ (sk_C @ X9))
% 0.38/0.59          | (v2_funct_1 @ X9)
% 0.38/0.59          | ~ (v1_funct_1 @ X9)
% 0.38/0.59          | ~ (v1_relat_1 @ X9))),
% 0.38/0.59      inference('cnf', [status(esa)], [t49_funct_1])).
% 0.38/0.59  thf('7', plain,
% 0.38/0.59      (![X9 : $i]:
% 0.38/0.59         ((r1_tarski @ (k2_relat_1 @ (sk_C @ X9)) @ (k1_relat_1 @ X9))
% 0.38/0.59          | (v2_funct_1 @ X9)
% 0.38/0.59          | ~ (v1_funct_1 @ X9)
% 0.38/0.59          | ~ (v1_relat_1 @ X9))),
% 0.38/0.59      inference('cnf', [status(esa)], [t49_funct_1])).
% 0.38/0.59  thf('8', plain,
% 0.38/0.59      (![X9 : $i]:
% 0.38/0.59         ((v1_relat_1 @ (sk_B @ X9))
% 0.38/0.59          | (v2_funct_1 @ X9)
% 0.38/0.59          | ~ (v1_funct_1 @ X9)
% 0.38/0.59          | ~ (v1_relat_1 @ X9))),
% 0.38/0.59      inference('cnf', [status(esa)], [t49_funct_1])).
% 0.38/0.59  thf(t55_relat_1, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( v1_relat_1 @ A ) =>
% 0.38/0.59       ( ![B:$i]:
% 0.38/0.59         ( ( v1_relat_1 @ B ) =>
% 0.38/0.59           ( ![C:$i]:
% 0.38/0.59             ( ( v1_relat_1 @ C ) =>
% 0.38/0.59               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.38/0.59                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.38/0.59  thf('9', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X0)
% 0.38/0.59          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.38/0.59              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 0.38/0.59          | ~ (v1_relat_1 @ X2)
% 0.38/0.59          | ~ (v1_relat_1 @ X1))),
% 0.38/0.59      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.38/0.59  thf('10', plain,
% 0.38/0.59      (((k5_relat_1 @ sk_A @ sk_B_1) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('11', plain,
% 0.38/0.59      (![X9 : $i]:
% 0.38/0.59         ((v1_relat_1 @ (sk_C @ X9))
% 0.38/0.59          | (v2_funct_1 @ X9)
% 0.38/0.59          | ~ (v1_funct_1 @ X9)
% 0.38/0.59          | ~ (v1_relat_1 @ X9))),
% 0.38/0.59      inference('cnf', [status(esa)], [t49_funct_1])).
% 0.38/0.59  thf('12', plain,
% 0.38/0.59      (![X9 : $i]:
% 0.38/0.59         (((k5_relat_1 @ (sk_B @ X9) @ X9) = (k5_relat_1 @ (sk_C @ X9) @ X9))
% 0.38/0.59          | (v2_funct_1 @ X9)
% 0.38/0.59          | ~ (v1_funct_1 @ X9)
% 0.38/0.59          | ~ (v1_relat_1 @ X9))),
% 0.38/0.59      inference('cnf', [status(esa)], [t49_funct_1])).
% 0.38/0.59  thf('13', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X0)
% 0.38/0.59          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.38/0.59              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 0.38/0.59          | ~ (v1_relat_1 @ X2)
% 0.38/0.59          | ~ (v1_relat_1 @ X1))),
% 0.38/0.59      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.38/0.59  thf('14', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (((k5_relat_1 @ (k5_relat_1 @ (sk_B @ X0) @ X0) @ X1)
% 0.38/0.59            = (k5_relat_1 @ (sk_C @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 0.38/0.59          | ~ (v1_relat_1 @ X0)
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | (v2_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ (sk_C @ X0))
% 0.38/0.59          | ~ (v1_relat_1 @ X1)
% 0.38/0.59          | ~ (v1_relat_1 @ X0))),
% 0.38/0.59      inference('sup+', [status(thm)], ['12', '13'])).
% 0.38/0.59  thf('15', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X1)
% 0.38/0.59          | ~ (v1_relat_1 @ (sk_C @ X0))
% 0.38/0.59          | (v2_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X0)
% 0.38/0.59          | ((k5_relat_1 @ (k5_relat_1 @ (sk_B @ X0) @ X0) @ X1)
% 0.38/0.59              = (k5_relat_1 @ (sk_C @ X0) @ (k5_relat_1 @ X0 @ X1))))),
% 0.38/0.59      inference('simplify', [status(thm)], ['14'])).
% 0.38/0.59  thf('16', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X0)
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | (v2_funct_1 @ X0)
% 0.38/0.59          | ((k5_relat_1 @ (k5_relat_1 @ (sk_B @ X0) @ X0) @ X1)
% 0.38/0.59              = (k5_relat_1 @ (sk_C @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 0.38/0.59          | ~ (v1_relat_1 @ X0)
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | (v2_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X1))),
% 0.38/0.59      inference('sup-', [status(thm)], ['11', '15'])).
% 0.38/0.59  thf('17', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X1)
% 0.38/0.59          | ((k5_relat_1 @ (k5_relat_1 @ (sk_B @ X0) @ X0) @ X1)
% 0.38/0.59              = (k5_relat_1 @ (sk_C @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 0.38/0.59          | (v2_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X0))),
% 0.38/0.59      inference('simplify', [status(thm)], ['16'])).
% 0.38/0.59  thf('18', plain,
% 0.38/0.59      ((((k5_relat_1 @ (k5_relat_1 @ (sk_B @ sk_A) @ sk_A) @ sk_B_1)
% 0.38/0.59          = (k5_relat_1 @ (sk_C @ sk_A) @ (k6_relat_1 @ (k1_relat_1 @ sk_A))))
% 0.38/0.59        | ~ (v1_relat_1 @ sk_A)
% 0.38/0.59        | ~ (v1_funct_1 @ sk_A)
% 0.38/0.59        | (v2_funct_1 @ sk_A)
% 0.38/0.59        | ~ (v1_relat_1 @ sk_B_1))),
% 0.38/0.59      inference('sup+', [status(thm)], ['10', '17'])).
% 0.38/0.59  thf('19', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('20', plain, ((v1_funct_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('21', plain, ((v1_relat_1 @ sk_B_1)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('22', plain,
% 0.38/0.59      ((((k5_relat_1 @ (k5_relat_1 @ (sk_B @ sk_A) @ sk_A) @ sk_B_1)
% 0.38/0.59          = (k5_relat_1 @ (sk_C @ sk_A) @ (k6_relat_1 @ (k1_relat_1 @ sk_A))))
% 0.38/0.59        | (v2_funct_1 @ sk_A))),
% 0.38/0.59      inference('demod', [status(thm)], ['18', '19', '20', '21'])).
% 0.38/0.59  thf('23', plain, (~ (v2_funct_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('24', plain,
% 0.38/0.59      (((k5_relat_1 @ (k5_relat_1 @ (sk_B @ sk_A) @ sk_A) @ sk_B_1)
% 0.38/0.59         = (k5_relat_1 @ (sk_C @ sk_A) @ (k6_relat_1 @ (k1_relat_1 @ sk_A))))),
% 0.38/0.59      inference('clc', [status(thm)], ['22', '23'])).
% 0.38/0.59  thf('25', plain,
% 0.38/0.59      ((((k5_relat_1 @ (sk_B @ sk_A) @ (k5_relat_1 @ sk_A @ sk_B_1))
% 0.38/0.59          = (k5_relat_1 @ (sk_C @ sk_A) @ (k6_relat_1 @ (k1_relat_1 @ sk_A))))
% 0.38/0.59        | ~ (v1_relat_1 @ (sk_B @ sk_A))
% 0.38/0.59        | ~ (v1_relat_1 @ sk_B_1)
% 0.38/0.59        | ~ (v1_relat_1 @ sk_A))),
% 0.38/0.59      inference('sup+', [status(thm)], ['9', '24'])).
% 0.38/0.59  thf('26', plain,
% 0.38/0.59      (((k5_relat_1 @ sk_A @ sk_B_1) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('27', plain, ((v1_relat_1 @ sk_B_1)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('28', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('29', plain,
% 0.38/0.59      ((((k5_relat_1 @ (sk_B @ sk_A) @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 0.38/0.59          = (k5_relat_1 @ (sk_C @ sk_A) @ (k6_relat_1 @ (k1_relat_1 @ sk_A))))
% 0.38/0.59        | ~ (v1_relat_1 @ (sk_B @ sk_A)))),
% 0.38/0.59      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 0.38/0.59  thf('30', plain,
% 0.38/0.59      ((~ (v1_relat_1 @ sk_A)
% 0.38/0.59        | ~ (v1_funct_1 @ sk_A)
% 0.38/0.59        | (v2_funct_1 @ sk_A)
% 0.38/0.59        | ((k5_relat_1 @ (sk_B @ sk_A) @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 0.38/0.59            = (k5_relat_1 @ (sk_C @ sk_A) @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))))),
% 0.38/0.59      inference('sup-', [status(thm)], ['8', '29'])).
% 0.38/0.59  thf('31', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('32', plain, ((v1_funct_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('33', plain,
% 0.38/0.59      (((v2_funct_1 @ sk_A)
% 0.38/0.59        | ((k5_relat_1 @ (sk_B @ sk_A) @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 0.38/0.59            = (k5_relat_1 @ (sk_C @ sk_A) @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))))),
% 0.38/0.59      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.38/0.59  thf('34', plain, (~ (v2_funct_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('35', plain,
% 0.38/0.59      (((k5_relat_1 @ (sk_B @ sk_A) @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 0.38/0.59         = (k5_relat_1 @ (sk_C @ sk_A) @ (k6_relat_1 @ (k1_relat_1 @ sk_A))))),
% 0.38/0.59      inference('clc', [status(thm)], ['33', '34'])).
% 0.38/0.59  thf(t71_relat_1, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.38/0.59       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.38/0.59  thf('36', plain, (![X3 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X3)) = (X3))),
% 0.38/0.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.59  thf('37', plain,
% 0.38/0.59      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.38/0.59         (~ (v2_funct_1 @ X9)
% 0.38/0.59          | ~ (v1_relat_1 @ X10)
% 0.38/0.59          | ~ (v1_funct_1 @ X10)
% 0.38/0.59          | ((X11) = (X10))
% 0.38/0.59          | ((k5_relat_1 @ X11 @ X9) != (k5_relat_1 @ X10 @ X9))
% 0.38/0.59          | ((k1_relat_1 @ X11) != (k1_relat_1 @ X10))
% 0.38/0.59          | ~ (r1_tarski @ (k2_relat_1 @ X10) @ (k1_relat_1 @ X9))
% 0.38/0.59          | ~ (r1_tarski @ (k2_relat_1 @ X11) @ (k1_relat_1 @ X9))
% 0.38/0.59          | ~ (v1_funct_1 @ X11)
% 0.38/0.59          | ~ (v1_relat_1 @ X11)
% 0.38/0.59          | ~ (v1_funct_1 @ X9)
% 0.38/0.59          | ~ (v1_relat_1 @ X9))),
% 0.38/0.59      inference('cnf', [status(esa)], [t49_funct_1])).
% 0.38/0.59  thf('38', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.59         (~ (r1_tarski @ (k2_relat_1 @ X1) @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.38/0.59          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.38/0.59          | ~ (v1_relat_1 @ X2)
% 0.38/0.59          | ~ (v1_funct_1 @ X2)
% 0.38/0.59          | ~ (r1_tarski @ (k2_relat_1 @ X2) @ (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.38/0.59          | ((k1_relat_1 @ X2) != (k1_relat_1 @ X1))
% 0.38/0.59          | ((k5_relat_1 @ X2 @ (k6_relat_1 @ X0))
% 0.38/0.59              != (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.38/0.59          | ((X2) = (X1))
% 0.38/0.59          | ~ (v1_funct_1 @ X1)
% 0.38/0.59          | ~ (v1_relat_1 @ X1)
% 0.38/0.59          | ~ (v2_funct_1 @ (k6_relat_1 @ X0)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['36', '37'])).
% 0.38/0.59  thf(fc3_funct_1, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.38/0.59       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.38/0.59  thf('39', plain, (![X5 : $i]: (v1_relat_1 @ (k6_relat_1 @ X5))),
% 0.38/0.59      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.38/0.59  thf('40', plain, (![X6 : $i]: (v1_funct_1 @ (k6_relat_1 @ X6))),
% 0.38/0.59      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.38/0.59  thf('41', plain, (![X3 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X3)) = (X3))),
% 0.38/0.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.59  thf(fc4_funct_1, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.38/0.59       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.38/0.59  thf('42', plain, (![X8 : $i]: (v2_funct_1 @ (k6_relat_1 @ X8))),
% 0.38/0.59      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.38/0.59  thf('43', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.59         (~ (r1_tarski @ (k2_relat_1 @ X1) @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X2)
% 0.38/0.59          | ~ (v1_funct_1 @ X2)
% 0.38/0.59          | ~ (r1_tarski @ (k2_relat_1 @ X2) @ X0)
% 0.38/0.59          | ((k1_relat_1 @ X2) != (k1_relat_1 @ X1))
% 0.38/0.59          | ((k5_relat_1 @ X2 @ (k6_relat_1 @ X0))
% 0.38/0.59              != (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.38/0.59          | ((X2) = (X1))
% 0.38/0.59          | ~ (v1_funct_1 @ X1)
% 0.38/0.59          | ~ (v1_relat_1 @ X1))),
% 0.38/0.59      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 0.38/0.59  thf('44', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 0.38/0.59            != (k5_relat_1 @ (sk_B @ sk_A) @ (k6_relat_1 @ (k1_relat_1 @ sk_A))))
% 0.38/0.59          | ~ (v1_relat_1 @ (sk_C @ sk_A))
% 0.38/0.59          | ~ (v1_funct_1 @ (sk_C @ sk_A))
% 0.38/0.59          | ((X0) = (sk_C @ sk_A))
% 0.38/0.59          | ((k1_relat_1 @ X0) != (k1_relat_1 @ (sk_C @ sk_A)))
% 0.38/0.59          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ sk_A))
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X0)
% 0.38/0.59          | ~ (r1_tarski @ (k2_relat_1 @ (sk_C @ sk_A)) @ (k1_relat_1 @ sk_A)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['35', '43'])).
% 0.38/0.59  thf('45', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ sk_A)
% 0.38/0.59          | ~ (v1_funct_1 @ sk_A)
% 0.38/0.59          | (v2_funct_1 @ sk_A)
% 0.38/0.59          | ~ (v1_relat_1 @ X0)
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ sk_A))
% 0.38/0.59          | ((k1_relat_1 @ X0) != (k1_relat_1 @ (sk_C @ sk_A)))
% 0.38/0.59          | ((X0) = (sk_C @ sk_A))
% 0.38/0.59          | ~ (v1_funct_1 @ (sk_C @ sk_A))
% 0.38/0.59          | ~ (v1_relat_1 @ (sk_C @ sk_A))
% 0.38/0.59          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 0.38/0.59              != (k5_relat_1 @ (sk_B @ sk_A) @ 
% 0.38/0.59                  (k6_relat_1 @ (k1_relat_1 @ sk_A)))))),
% 0.38/0.59      inference('sup-', [status(thm)], ['7', '44'])).
% 0.38/0.59  thf('46', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('47', plain, ((v1_funct_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('48', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v2_funct_1 @ sk_A)
% 0.38/0.59          | ~ (v1_relat_1 @ X0)
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ sk_A))
% 0.38/0.59          | ((k1_relat_1 @ X0) != (k1_relat_1 @ (sk_C @ sk_A)))
% 0.38/0.59          | ((X0) = (sk_C @ sk_A))
% 0.38/0.59          | ~ (v1_funct_1 @ (sk_C @ sk_A))
% 0.38/0.59          | ~ (v1_relat_1 @ (sk_C @ sk_A))
% 0.38/0.59          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 0.38/0.59              != (k5_relat_1 @ (sk_B @ sk_A) @ 
% 0.38/0.59                  (k6_relat_1 @ (k1_relat_1 @ sk_A)))))),
% 0.38/0.59      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.38/0.59  thf('49', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ sk_A)
% 0.38/0.59          | ~ (v1_funct_1 @ sk_A)
% 0.38/0.59          | (v2_funct_1 @ sk_A)
% 0.38/0.59          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 0.38/0.59              != (k5_relat_1 @ (sk_B @ sk_A) @ 
% 0.38/0.59                  (k6_relat_1 @ (k1_relat_1 @ sk_A))))
% 0.38/0.59          | ~ (v1_relat_1 @ (sk_C @ sk_A))
% 0.38/0.59          | ((X0) = (sk_C @ sk_A))
% 0.38/0.59          | ((k1_relat_1 @ X0) != (k1_relat_1 @ (sk_C @ sk_A)))
% 0.38/0.59          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ sk_A))
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X0)
% 0.38/0.59          | (v2_funct_1 @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['6', '48'])).
% 0.38/0.59  thf('50', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('51', plain, ((v1_funct_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('52', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v2_funct_1 @ sk_A)
% 0.38/0.59          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 0.38/0.59              != (k5_relat_1 @ (sk_B @ sk_A) @ 
% 0.38/0.59                  (k6_relat_1 @ (k1_relat_1 @ sk_A))))
% 0.38/0.59          | ~ (v1_relat_1 @ (sk_C @ sk_A))
% 0.38/0.59          | ((X0) = (sk_C @ sk_A))
% 0.38/0.59          | ((k1_relat_1 @ X0) != (k1_relat_1 @ (sk_C @ sk_A)))
% 0.38/0.59          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ sk_A))
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X0)
% 0.38/0.59          | (v2_funct_1 @ sk_A))),
% 0.38/0.59      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.38/0.59  thf('53', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X0)
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ sk_A))
% 0.38/0.59          | ((k1_relat_1 @ X0) != (k1_relat_1 @ (sk_C @ sk_A)))
% 0.38/0.59          | ((X0) = (sk_C @ sk_A))
% 0.38/0.59          | ~ (v1_relat_1 @ (sk_C @ sk_A))
% 0.38/0.59          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 0.38/0.59              != (k5_relat_1 @ (sk_B @ sk_A) @ 
% 0.38/0.59                  (k6_relat_1 @ (k1_relat_1 @ sk_A))))
% 0.38/0.59          | (v2_funct_1 @ sk_A))),
% 0.38/0.59      inference('simplify', [status(thm)], ['52'])).
% 0.38/0.59  thf('54', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ sk_A)
% 0.38/0.59          | ~ (v1_funct_1 @ sk_A)
% 0.38/0.59          | (v2_funct_1 @ sk_A)
% 0.38/0.59          | (v2_funct_1 @ sk_A)
% 0.38/0.59          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 0.38/0.59              != (k5_relat_1 @ (sk_B @ sk_A) @ 
% 0.38/0.59                  (k6_relat_1 @ (k1_relat_1 @ sk_A))))
% 0.38/0.59          | ((X0) = (sk_C @ sk_A))
% 0.38/0.59          | ((k1_relat_1 @ X0) != (k1_relat_1 @ (sk_C @ sk_A)))
% 0.38/0.59          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ sk_A))
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['5', '53'])).
% 0.38/0.59  thf('55', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('56', plain, ((v1_funct_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('57', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v2_funct_1 @ sk_A)
% 0.38/0.59          | (v2_funct_1 @ sk_A)
% 0.38/0.59          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 0.38/0.59              != (k5_relat_1 @ (sk_B @ sk_A) @ 
% 0.38/0.59                  (k6_relat_1 @ (k1_relat_1 @ sk_A))))
% 0.38/0.59          | ((X0) = (sk_C @ sk_A))
% 0.38/0.59          | ((k1_relat_1 @ X0) != (k1_relat_1 @ (sk_C @ sk_A)))
% 0.38/0.59          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ sk_A))
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X0))),
% 0.38/0.59      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.38/0.59  thf('58', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X0)
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ sk_A))
% 0.38/0.59          | ((k1_relat_1 @ X0) != (k1_relat_1 @ (sk_C @ sk_A)))
% 0.38/0.59          | ((X0) = (sk_C @ sk_A))
% 0.38/0.59          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 0.38/0.59              != (k5_relat_1 @ (sk_B @ sk_A) @ 
% 0.38/0.59                  (k6_relat_1 @ (k1_relat_1 @ sk_A))))
% 0.38/0.59          | (v2_funct_1 @ sk_A))),
% 0.38/0.59      inference('simplify', [status(thm)], ['57'])).
% 0.38/0.59  thf('59', plain,
% 0.38/0.59      (((v2_funct_1 @ sk_A)
% 0.38/0.59        | ((sk_B @ sk_A) = (sk_C @ sk_A))
% 0.38/0.59        | ((k1_relat_1 @ (sk_B @ sk_A)) != (k1_relat_1 @ (sk_C @ sk_A)))
% 0.38/0.59        | ~ (r1_tarski @ (k2_relat_1 @ (sk_B @ sk_A)) @ (k1_relat_1 @ sk_A))
% 0.38/0.59        | ~ (v1_funct_1 @ (sk_B @ sk_A))
% 0.38/0.59        | ~ (v1_relat_1 @ (sk_B @ sk_A)))),
% 0.38/0.59      inference('eq_res', [status(thm)], ['58'])).
% 0.38/0.59  thf('60', plain,
% 0.38/0.59      ((~ (v1_relat_1 @ sk_A)
% 0.38/0.59        | ~ (v1_funct_1 @ sk_A)
% 0.38/0.59        | (v2_funct_1 @ sk_A)
% 0.38/0.59        | ~ (v1_relat_1 @ (sk_B @ sk_A))
% 0.38/0.59        | ~ (v1_funct_1 @ (sk_B @ sk_A))
% 0.38/0.59        | ((k1_relat_1 @ (sk_B @ sk_A)) != (k1_relat_1 @ (sk_C @ sk_A)))
% 0.38/0.59        | ((sk_B @ sk_A) = (sk_C @ sk_A))
% 0.38/0.59        | (v2_funct_1 @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['4', '59'])).
% 0.38/0.59  thf('61', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('62', plain, ((v1_funct_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('63', plain,
% 0.38/0.59      (((v2_funct_1 @ sk_A)
% 0.38/0.59        | ~ (v1_relat_1 @ (sk_B @ sk_A))
% 0.38/0.59        | ~ (v1_funct_1 @ (sk_B @ sk_A))
% 0.38/0.59        | ((k1_relat_1 @ (sk_B @ sk_A)) != (k1_relat_1 @ (sk_C @ sk_A)))
% 0.38/0.59        | ((sk_B @ sk_A) = (sk_C @ sk_A))
% 0.38/0.59        | (v2_funct_1 @ sk_A))),
% 0.38/0.59      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.38/0.59  thf('64', plain,
% 0.38/0.59      ((((sk_B @ sk_A) = (sk_C @ sk_A))
% 0.38/0.59        | ((k1_relat_1 @ (sk_B @ sk_A)) != (k1_relat_1 @ (sk_C @ sk_A)))
% 0.38/0.59        | ~ (v1_funct_1 @ (sk_B @ sk_A))
% 0.38/0.59        | ~ (v1_relat_1 @ (sk_B @ sk_A))
% 0.38/0.59        | (v2_funct_1 @ sk_A))),
% 0.38/0.59      inference('simplify', [status(thm)], ['63'])).
% 0.38/0.59  thf('65', plain,
% 0.38/0.59      ((~ (v1_relat_1 @ sk_A)
% 0.38/0.59        | ~ (v1_funct_1 @ sk_A)
% 0.38/0.59        | (v2_funct_1 @ sk_A)
% 0.38/0.59        | (v2_funct_1 @ sk_A)
% 0.38/0.59        | ~ (v1_relat_1 @ (sk_B @ sk_A))
% 0.38/0.59        | ((k1_relat_1 @ (sk_B @ sk_A)) != (k1_relat_1 @ (sk_C @ sk_A)))
% 0.38/0.59        | ((sk_B @ sk_A) = (sk_C @ sk_A)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['3', '64'])).
% 0.38/0.59  thf('66', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('67', plain, ((v1_funct_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('68', plain,
% 0.38/0.59      (((v2_funct_1 @ sk_A)
% 0.38/0.59        | (v2_funct_1 @ sk_A)
% 0.38/0.59        | ~ (v1_relat_1 @ (sk_B @ sk_A))
% 0.38/0.59        | ((k1_relat_1 @ (sk_B @ sk_A)) != (k1_relat_1 @ (sk_C @ sk_A)))
% 0.38/0.59        | ((sk_B @ sk_A) = (sk_C @ sk_A)))),
% 0.38/0.59      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.38/0.59  thf('69', plain,
% 0.38/0.59      ((((sk_B @ sk_A) = (sk_C @ sk_A))
% 0.38/0.59        | ((k1_relat_1 @ (sk_B @ sk_A)) != (k1_relat_1 @ (sk_C @ sk_A)))
% 0.38/0.59        | ~ (v1_relat_1 @ (sk_B @ sk_A))
% 0.38/0.59        | (v2_funct_1 @ sk_A))),
% 0.38/0.59      inference('simplify', [status(thm)], ['68'])).
% 0.38/0.59  thf('70', plain,
% 0.38/0.59      ((~ (v1_relat_1 @ sk_A)
% 0.38/0.59        | ~ (v1_funct_1 @ sk_A)
% 0.38/0.59        | (v2_funct_1 @ sk_A)
% 0.38/0.59        | (v2_funct_1 @ sk_A)
% 0.38/0.59        | ((k1_relat_1 @ (sk_B @ sk_A)) != (k1_relat_1 @ (sk_C @ sk_A)))
% 0.38/0.59        | ((sk_B @ sk_A) = (sk_C @ sk_A)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['2', '69'])).
% 0.38/0.59  thf('71', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('72', plain, ((v1_funct_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('73', plain,
% 0.38/0.59      (((v2_funct_1 @ sk_A)
% 0.38/0.59        | (v2_funct_1 @ sk_A)
% 0.38/0.59        | ((k1_relat_1 @ (sk_B @ sk_A)) != (k1_relat_1 @ (sk_C @ sk_A)))
% 0.38/0.59        | ((sk_B @ sk_A) = (sk_C @ sk_A)))),
% 0.38/0.59      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.38/0.59  thf('74', plain,
% 0.38/0.59      ((((sk_B @ sk_A) = (sk_C @ sk_A))
% 0.38/0.59        | ((k1_relat_1 @ (sk_B @ sk_A)) != (k1_relat_1 @ (sk_C @ sk_A)))
% 0.38/0.59        | (v2_funct_1 @ sk_A))),
% 0.38/0.59      inference('simplify', [status(thm)], ['73'])).
% 0.38/0.59  thf('75', plain, (~ (v2_funct_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('76', plain,
% 0.38/0.59      ((((k1_relat_1 @ (sk_B @ sk_A)) != (k1_relat_1 @ (sk_C @ sk_A)))
% 0.38/0.59        | ((sk_B @ sk_A) = (sk_C @ sk_A)))),
% 0.38/0.59      inference('clc', [status(thm)], ['74', '75'])).
% 0.38/0.59  thf('77', plain,
% 0.38/0.59      ((((k1_relat_1 @ (sk_B @ sk_A)) != (k1_relat_1 @ (sk_B @ sk_A)))
% 0.38/0.59        | ~ (v1_relat_1 @ sk_A)
% 0.38/0.59        | ~ (v1_funct_1 @ sk_A)
% 0.38/0.59        | (v2_funct_1 @ sk_A)
% 0.38/0.59        | ((sk_B @ sk_A) = (sk_C @ sk_A)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['1', '76'])).
% 0.38/0.59  thf('78', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('79', plain, ((v1_funct_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('80', plain,
% 0.38/0.59      ((((k1_relat_1 @ (sk_B @ sk_A)) != (k1_relat_1 @ (sk_B @ sk_A)))
% 0.38/0.59        | (v2_funct_1 @ sk_A)
% 0.38/0.59        | ((sk_B @ sk_A) = (sk_C @ sk_A)))),
% 0.38/0.59      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.38/0.59  thf('81', plain, ((((sk_B @ sk_A) = (sk_C @ sk_A)) | (v2_funct_1 @ sk_A))),
% 0.38/0.59      inference('simplify', [status(thm)], ['80'])).
% 0.38/0.59  thf('82', plain, (~ (v2_funct_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('83', plain, (((sk_B @ sk_A) = (sk_C @ sk_A))),
% 0.38/0.59      inference('clc', [status(thm)], ['81', '82'])).
% 0.38/0.59  thf('84', plain,
% 0.38/0.59      (![X9 : $i]:
% 0.38/0.59         (((sk_B @ X9) != (sk_C @ X9))
% 0.38/0.59          | (v2_funct_1 @ X9)
% 0.38/0.59          | ~ (v1_funct_1 @ X9)
% 0.38/0.59          | ~ (v1_relat_1 @ X9))),
% 0.38/0.59      inference('cnf', [status(esa)], [t49_funct_1])).
% 0.38/0.59  thf('85', plain,
% 0.38/0.59      ((((sk_B @ sk_A) != (sk_B @ sk_A))
% 0.38/0.59        | ~ (v1_relat_1 @ sk_A)
% 0.38/0.59        | ~ (v1_funct_1 @ sk_A)
% 0.38/0.59        | (v2_funct_1 @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['83', '84'])).
% 0.38/0.59  thf('86', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('87', plain, ((v1_funct_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('88', plain, ((((sk_B @ sk_A) != (sk_B @ sk_A)) | (v2_funct_1 @ sk_A))),
% 0.38/0.59      inference('demod', [status(thm)], ['85', '86', '87'])).
% 0.38/0.59  thf('89', plain, ((v2_funct_1 @ sk_A)),
% 0.38/0.59      inference('simplify', [status(thm)], ['88'])).
% 0.38/0.59  thf('90', plain, ($false), inference('demod', [status(thm)], ['0', '89'])).
% 0.38/0.59  
% 0.38/0.59  % SZS output end Refutation
% 0.38/0.59  
% 0.38/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
