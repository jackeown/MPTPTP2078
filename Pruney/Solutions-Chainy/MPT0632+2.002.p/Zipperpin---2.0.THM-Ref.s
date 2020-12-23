%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FD7kwpOxiJ

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:49 EST 2020

% Result     : Theorem 19.97s
% Output     : Refutation 19.97s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 338 expanded)
%              Number of leaves         :   22 ( 104 expanded)
%              Depth                    :   18
%              Number of atoms          : 1597 (4503 expanded)
%              Number of equality atoms :  203 ( 645 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t34_funct_1,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( B
            = ( k6_relat_1 @ A ) )
        <=> ( ( ( k1_relat_1 @ B )
              = A )
            & ! [C: $i] :
                ( ( r2_hidden @ C @ A )
               => ( ( k1_funct_1 @ B @ C )
                  = C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_funct_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_C_2 @ sk_A )
    | ( ( k1_relat_1 @ sk_B )
     != sk_A )
    | ( sk_B
     != ( k6_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_C_2 @ sk_A )
    | ( sk_B
     != ( k6_relat_1 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_B )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
    | ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
    | ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    ! [X20: $i] :
      ( ~ ( r2_hidden @ X20 @ sk_A )
      | ( ( k1_funct_1 @ sk_B @ X20 )
        = X20 )
      | ( sk_B
        = ( k6_relat_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ! [X20: $i] :
        ( ~ ( r2_hidden @ X20 @ sk_A )
        | ( ( k1_funct_1 @ sk_B @ X20 )
          = X20 ) )
    | ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

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
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( X19 = X18 )
      | ( r2_hidden @ ( sk_C_1 @ X18 @ X19 ) @ ( k1_relat_1 @ X19 ) )
      | ( ( k1_relat_1 @ X19 )
       != ( k1_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
       != ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ( ( k6_relat_1 @ X0 )
        = X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('11',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
       != ( k1_relat_1 @ X1 ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( ( k6_relat_1 @ X0 )
        = X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('14',plain,(
    ! [X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ X1 ) )
        = X1 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X14 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X14 @ X13 ) @ ( k2_relat_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('19',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('20',plain,(
    ! [X1: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X1 ) )
      = X1 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18','19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
        = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( sk_C_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,
    ( ( ( r2_hidden @ ( k1_funct_1 @ ( k6_relat_1 @ sk_A ) @ ( sk_C_1 @ sk_B @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ) ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) )
        = sk_B ) )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup+',[status(thm)],['6','22'])).

thf('24',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('25',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('29',plain,
    ( ( ( r2_hidden @ ( k1_funct_1 @ ( k6_relat_1 @ sk_A ) @ ( sk_C_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ) @ sk_A )
      | ( ( k6_relat_1 @ sk_A )
        = sk_B ) )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(demod,[status(thm)],['23','24','25','26','27','28'])).

thf('30',plain,
    ( ! [X20: $i] :
        ( ~ ( r2_hidden @ X20 @ sk_A )
        | ( ( k1_funct_1 @ sk_B @ X20 )
          = X20 ) )
   <= ! [X20: $i] :
        ( ~ ( r2_hidden @ X20 @ sk_A )
        | ( ( k1_funct_1 @ sk_B @ X20 )
          = X20 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('31',plain,
    ( ( ( ( k6_relat_1 @ sk_A )
        = sk_B )
      | ( ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k6_relat_1 @ sk_A ) @ ( sk_C_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ) )
        = ( k1_funct_1 @ ( k6_relat_1 @ sk_A ) @ ( sk_C_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ) ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X20: $i] :
          ( ~ ( r2_hidden @ X20 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X20 )
            = X20 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('33',plain,(
    ! [X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ X1 ) )
        = X1 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('34',plain,
    ( ( ( r2_hidden @ ( sk_C_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) @ ( k1_relat_1 @ sk_B ) )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) )
        = sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('36',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('37',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( r2_hidden @ ( sk_C_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) @ sk_A )
      | ( ( k6_relat_1 @ sk_A )
        = sk_B ) )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(demod,[status(thm)],['34','35','36','37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X16 @ X15 ) @ X17 )
        = ( k1_funct_1 @ X15 @ ( k1_funct_1 @ X16 @ X17 ) ) )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 )
        = ( k1_funct_1 @ X2 @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('44',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 )
        = ( k1_funct_1 @ X2 @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ( ( k6_relat_1 @ sk_A )
          = sk_B )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 ) @ ( sk_C_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) )
          = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k6_relat_1 @ sk_A ) @ ( sk_C_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ) ) ) )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,
    ( ( ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ ( sk_C_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) )
        = ( k1_funct_1 @ ( k6_relat_1 @ sk_A ) @ ( sk_C_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ) )
      | ( ( k6_relat_1 @ sk_A )
        = sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k6_relat_1 @ sk_A )
        = sk_B ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X20: $i] :
          ( ~ ( r2_hidden @ X20 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X20 )
            = X20 ) ) ) ),
    inference('sup+',[status(thm)],['31','46'])).

thf('48',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('49',plain,(
    ! [X2: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X2 ) ) @ X2 )
        = X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('50',plain,
    ( ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
        = sk_B )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
      = sk_B )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) )
        = ( k1_funct_1 @ ( k6_relat_1 @ sk_A ) @ ( sk_C_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ) )
      | ( ( k6_relat_1 @ sk_A )
        = sk_B )
      | ( ( k6_relat_1 @ sk_A )
        = sk_B ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X20: $i] :
          ( ~ ( r2_hidden @ X20 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X20 )
            = X20 ) ) ) ),
    inference(demod,[status(thm)],['47','52','53','54'])).

thf('56',plain,
    ( ( ( ( k6_relat_1 @ sk_A )
        = sk_B )
      | ( ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) )
        = ( k1_funct_1 @ ( k6_relat_1 @ sk_A ) @ ( sk_C_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ) ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X20: $i] :
          ( ~ ( r2_hidden @ X20 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X20 )
            = X20 ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) )
      = ( k1_funct_1 @ ( k6_relat_1 @ sk_A ) @ ( sk_C_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X20: $i] :
          ( ~ ( r2_hidden @ X20 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X20 )
            = X20 ) ) ) ),
    inference(condensation,[status(thm)],['56'])).

thf('58',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( X19 = X18 )
      | ( ( k1_funct_1 @ X19 @ ( sk_C_1 @ X18 @ X19 ) )
       != ( k1_funct_1 @ X18 @ ( sk_C_1 @ X18 @ X19 ) ) )
      | ( ( k1_relat_1 @ X19 )
       != ( k1_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('59',plain,
    ( ( ( ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) )
       != ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ sk_A ) )
      | ( ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) )
       != ( k1_relat_1 @ sk_B ) )
      | ( ( k6_relat_1 @ sk_A )
        = sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X20: $i] :
          ( ~ ( r2_hidden @ X20 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X20 )
            = X20 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('61',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('63',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('64',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( ( ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) )
       != ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ) )
      | ( sk_A != sk_A )
      | ( ( k6_relat_1 @ sk_A )
        = sk_B ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X20: $i] :
          ( ~ ( r2_hidden @ X20 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X20 )
            = X20 ) ) ) ),
    inference(demod,[status(thm)],['59','60','61','62','63','64','65'])).

thf('67',plain,
    ( ( ( k6_relat_1 @ sk_A )
      = sk_B )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X20: $i] :
          ( ~ ( r2_hidden @ X20 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X20 )
            = X20 ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_C_2 )
     != sk_C_2 )
    | ( ( k1_relat_1 @ sk_B )
     != sk_A )
    | ( sk_B
     != ( k6_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( sk_B
     != ( k6_relat_1 @ sk_A ) )
   <= ( sk_B
     != ( k6_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['68'])).

thf('70',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B
       != ( k6_relat_1 @ sk_A ) )
      & ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X20: $i] :
          ( ~ ( r2_hidden @ X20 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X20 )
            = X20 ) ) ) ),
    inference('sup-',[status(thm)],['67','69'])).

thf('71',plain,
    ( ~ ! [X20: $i] :
          ( ~ ( r2_hidden @ X20 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X20 )
            = X20 ) )
    | ( sk_B
      = ( k6_relat_1 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_B )
     != sk_A ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ( sk_B
      = ( k6_relat_1 @ sk_A ) )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('74',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( k1_relat_1 @ sk_B )
     != sk_A )
   <= ( ( k1_relat_1 @ sk_B )
     != sk_A ) ),
    inference(split,[status(esa)],['68'])).

thf('76',plain,
    ( ( sk_A != sk_A )
   <= ( ( ( k1_relat_1 @ sk_B )
       != sk_A )
      & ( sk_B
        = ( k6_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
    | ( sk_B
     != ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_C_2 )
     != sk_C_2 )
    | ( ( k1_relat_1 @ sk_B )
     != sk_A )
    | ( sk_B
     != ( k6_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['68'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('79',plain,(
    ! [X3: $i] :
      ( ( ( k5_relat_1 @ X3 @ ( k6_relat_1 @ ( k2_relat_1 @ X3 ) ) )
        = X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('80',plain,
    ( ( r2_hidden @ sk_C_2 @ sk_A )
   <= ( r2_hidden @ sk_C_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('81',plain,
    ( ( sk_B
      = ( k6_relat_1 @ sk_A ) )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('82',plain,(
    ! [X1: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X1 ) )
      = X1 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('83',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = sk_A )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

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

thf('84',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ( X7
       != ( k2_relat_1 @ X5 ) )
      | ( r2_hidden @ ( sk_D_1 @ X8 @ X5 ) @ ( k1_relat_1 @ X5 ) )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('85',plain,(
    ! [X5: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k2_relat_1 @ X5 ) )
      | ( r2_hidden @ ( sk_D_1 @ X8 @ X5 ) @ ( k1_relat_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
        | ~ ( v1_funct_1 @ sk_B )
        | ~ ( v1_relat_1 @ sk_B ) )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','85'])).

thf('87',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('88',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B ) @ sk_A ) )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf('91',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C_2 @ sk_B ) @ sk_A )
   <= ( ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      & ( r2_hidden @ sk_C_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 )
        = ( k1_funct_1 @ X2 @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('93',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 ) @ ( sk_D_1 @ sk_C_2 @ sk_B ) )
          = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k6_relat_1 @ sk_A ) @ ( sk_D_1 @ sk_C_2 @ sk_B ) ) ) ) )
   <= ( ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      & ( r2_hidden @ sk_C_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( sk_B
      = ( k6_relat_1 @ sk_A ) )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('95',plain,
    ( ( sk_B
      = ( k6_relat_1 @ sk_A ) )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('96',plain,
    ( ( r2_hidden @ sk_C_2 @ sk_A )
   <= ( r2_hidden @ sk_C_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('97',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = sk_A )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('98',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ( X7
       != ( k2_relat_1 @ X5 ) )
      | ( X8
        = ( k1_funct_1 @ X5 @ ( sk_D_1 @ X8 @ X5 ) ) )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('99',plain,(
    ! [X5: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k2_relat_1 @ X5 ) )
      | ( X8
        = ( k1_funct_1 @ X5 @ ( sk_D_1 @ X8 @ X5 ) ) ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ( X0
          = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ X0 @ sk_B ) ) )
        | ~ ( v1_funct_1 @ sk_B )
        | ~ ( v1_relat_1 @ sk_B ) )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['97','99'])).

thf('101',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ( X0
          = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ X0 @ sk_B ) ) ) )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,
    ( ( sk_C_2
      = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_C_2 @ sk_B ) ) )
   <= ( ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      & ( r2_hidden @ sk_C_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['96','103'])).

thf('105',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ X0 ) @ ( sk_D_1 @ sk_C_2 @ sk_B ) )
          = ( k1_funct_1 @ X0 @ sk_C_2 ) ) )
   <= ( ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      & ( r2_hidden @ sk_C_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['93','94','95','104'])).

thf('106',plain,
    ( ( ( ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_C_2 @ sk_B ) )
        = ( k1_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ sk_C_2 ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) )
   <= ( ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      & ( r2_hidden @ sk_C_2 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['79','105'])).

thf('107',plain,
    ( ( sk_C_2
      = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_C_2 @ sk_B ) ) )
   <= ( ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      & ( r2_hidden @ sk_C_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['96','103'])).

thf('108',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = sk_A )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('109',plain,
    ( ( sk_B
      = ( k6_relat_1 @ sk_A ) )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('110',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = sk_A )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('112',plain,
    ( ( sk_B
      = ( k6_relat_1 @ sk_A ) )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('113',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = sk_A )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('115',plain,
    ( ( sk_B
      = ( k6_relat_1 @ sk_A ) )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('116',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( sk_C_2
      = ( k1_funct_1 @ sk_B @ sk_C_2 ) )
   <= ( ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      & ( r2_hidden @ sk_C_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['106','107','108','109','110','111','112','113','114','115','116'])).

thf('118',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_C_2 )
     != sk_C_2 )
   <= ( ( k1_funct_1 @ sk_B @ sk_C_2 )
     != sk_C_2 ) ),
    inference(split,[status(esa)],['68'])).

thf('119',plain,
    ( ( sk_C_2 != sk_C_2 )
   <= ( ( ( k1_funct_1 @ sk_B @ sk_C_2 )
       != sk_C_2 )
      & ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      & ( r2_hidden @ sk_C_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_C_2 )
      = sk_C_2 )
    | ~ ( r2_hidden @ sk_C_2 @ sk_A )
    | ( sk_B
     != ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','71','77','78','120'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FD7kwpOxiJ
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:33:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 19.97/20.19  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 19.97/20.19  % Solved by: fo/fo7.sh
% 19.97/20.19  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 19.97/20.19  % done 9338 iterations in 19.725s
% 19.97/20.19  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 19.97/20.19  % SZS output start Refutation
% 19.97/20.19  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 19.97/20.19  thf(sk_B_type, type, sk_B: $i).
% 19.97/20.19  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 19.97/20.19  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 19.97/20.19  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 19.97/20.19  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 19.97/20.19  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 19.97/20.19  thf(sk_A_type, type, sk_A: $i).
% 19.97/20.19  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 19.97/20.19  thf(sk_C_2_type, type, sk_C_2: $i).
% 19.97/20.19  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 19.97/20.19  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 19.97/20.19  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 19.97/20.19  thf(t34_funct_1, conjecture,
% 19.97/20.19    (![A:$i,B:$i]:
% 19.97/20.19     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 19.97/20.19       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 19.97/20.19         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 19.97/20.19           ( ![C:$i]:
% 19.97/20.19             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 19.97/20.19  thf(zf_stmt_0, negated_conjecture,
% 19.97/20.19    (~( ![A:$i,B:$i]:
% 19.97/20.19        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 19.97/20.19          ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 19.97/20.19            ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 19.97/20.19              ( ![C:$i]:
% 19.97/20.19                ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ) )),
% 19.97/20.19    inference('cnf.neg', [status(esa)], [t34_funct_1])).
% 19.97/20.19  thf('0', plain,
% 19.97/20.19      (((r2_hidden @ sk_C_2 @ sk_A)
% 19.97/20.19        | ((k1_relat_1 @ sk_B) != (sk_A))
% 19.97/20.19        | ((sk_B) != (k6_relat_1 @ sk_A)))),
% 19.97/20.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.97/20.19  thf('1', plain,
% 19.97/20.19      (((r2_hidden @ sk_C_2 @ sk_A)) | ~ (((sk_B) = (k6_relat_1 @ sk_A))) | 
% 19.97/20.19       ~ (((k1_relat_1 @ sk_B) = (sk_A)))),
% 19.97/20.19      inference('split', [status(esa)], ['0'])).
% 19.97/20.19  thf('2', plain,
% 19.97/20.19      ((((k1_relat_1 @ sk_B) = (sk_A)) | ((sk_B) = (k6_relat_1 @ sk_A)))),
% 19.97/20.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.97/20.19  thf('3', plain,
% 19.97/20.19      ((((k1_relat_1 @ sk_B) = (sk_A))) | (((sk_B) = (k6_relat_1 @ sk_A)))),
% 19.97/20.19      inference('split', [status(esa)], ['2'])).
% 19.97/20.19  thf('4', plain,
% 19.97/20.19      (![X20 : $i]:
% 19.97/20.19         (~ (r2_hidden @ X20 @ sk_A)
% 19.97/20.19          | ((k1_funct_1 @ sk_B @ X20) = (X20))
% 19.97/20.19          | ((sk_B) = (k6_relat_1 @ sk_A)))),
% 19.97/20.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.97/20.19  thf('5', plain,
% 19.97/20.19      ((![X20 : $i]:
% 19.97/20.19          (~ (r2_hidden @ X20 @ sk_A) | ((k1_funct_1 @ sk_B @ X20) = (X20)))) | 
% 19.97/20.19       (((sk_B) = (k6_relat_1 @ sk_A)))),
% 19.97/20.19      inference('split', [status(esa)], ['4'])).
% 19.97/20.19  thf('6', plain,
% 19.97/20.19      ((((k1_relat_1 @ sk_B) = (sk_A))) <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 19.97/20.19      inference('split', [status(esa)], ['2'])).
% 19.97/20.19  thf(t71_relat_1, axiom,
% 19.97/20.19    (![A:$i]:
% 19.97/20.19     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 19.97/20.19       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 19.97/20.19  thf('7', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 19.97/20.19      inference('cnf', [status(esa)], [t71_relat_1])).
% 19.97/20.19  thf(t9_funct_1, axiom,
% 19.97/20.19    (![A:$i]:
% 19.97/20.19     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 19.97/20.19       ( ![B:$i]:
% 19.97/20.19         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 19.97/20.19           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 19.97/20.19               ( ![C:$i]:
% 19.97/20.19                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 19.97/20.19                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 19.97/20.19             ( ( A ) = ( B ) ) ) ) ) ))).
% 19.97/20.19  thf('8', plain,
% 19.97/20.19      (![X18 : $i, X19 : $i]:
% 19.97/20.19         (~ (v1_relat_1 @ X18)
% 19.97/20.19          | ~ (v1_funct_1 @ X18)
% 19.97/20.19          | ((X19) = (X18))
% 19.97/20.19          | (r2_hidden @ (sk_C_1 @ X18 @ X19) @ (k1_relat_1 @ X19))
% 19.97/20.19          | ((k1_relat_1 @ X19) != (k1_relat_1 @ X18))
% 19.97/20.19          | ~ (v1_funct_1 @ X19)
% 19.97/20.19          | ~ (v1_relat_1 @ X19))),
% 19.97/20.19      inference('cnf', [status(esa)], [t9_funct_1])).
% 19.97/20.19  thf('9', plain,
% 19.97/20.19      (![X0 : $i, X1 : $i]:
% 19.97/20.19         (((X0) != (k1_relat_1 @ X1))
% 19.97/20.19          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 19.97/20.19          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 19.97/20.19          | (r2_hidden @ (sk_C_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 19.97/20.19             (k1_relat_1 @ (k6_relat_1 @ X0)))
% 19.97/20.19          | ((k6_relat_1 @ X0) = (X1))
% 19.97/20.19          | ~ (v1_funct_1 @ X1)
% 19.97/20.19          | ~ (v1_relat_1 @ X1))),
% 19.97/20.19      inference('sup-', [status(thm)], ['7', '8'])).
% 19.97/20.19  thf(fc3_funct_1, axiom,
% 19.97/20.19    (![A:$i]:
% 19.97/20.19     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 19.97/20.19       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 19.97/20.19  thf('10', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 19.97/20.19      inference('cnf', [status(esa)], [fc3_funct_1])).
% 19.97/20.19  thf('11', plain, (![X12 : $i]: (v1_funct_1 @ (k6_relat_1 @ X12))),
% 19.97/20.19      inference('cnf', [status(esa)], [fc3_funct_1])).
% 19.97/20.19  thf('12', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 19.97/20.19      inference('cnf', [status(esa)], [t71_relat_1])).
% 19.97/20.19  thf('13', plain,
% 19.97/20.19      (![X0 : $i, X1 : $i]:
% 19.97/20.19         (((X0) != (k1_relat_1 @ X1))
% 19.97/20.19          | (r2_hidden @ (sk_C_1 @ X1 @ (k6_relat_1 @ X0)) @ X0)
% 19.97/20.19          | ((k6_relat_1 @ X0) = (X1))
% 19.97/20.19          | ~ (v1_funct_1 @ X1)
% 19.97/20.19          | ~ (v1_relat_1 @ X1))),
% 19.97/20.19      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 19.97/20.19  thf('14', plain,
% 19.97/20.19      (![X1 : $i]:
% 19.97/20.19         (~ (v1_relat_1 @ X1)
% 19.97/20.19          | ~ (v1_funct_1 @ X1)
% 19.97/20.19          | ((k6_relat_1 @ (k1_relat_1 @ X1)) = (X1))
% 19.97/20.19          | (r2_hidden @ (sk_C_1 @ X1 @ (k6_relat_1 @ (k1_relat_1 @ X1))) @ 
% 19.97/20.19             (k1_relat_1 @ X1)))),
% 19.97/20.19      inference('simplify', [status(thm)], ['13'])).
% 19.97/20.19  thf('15', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 19.97/20.19      inference('cnf', [status(esa)], [t71_relat_1])).
% 19.97/20.19  thf(t12_funct_1, axiom,
% 19.97/20.19    (![A:$i,B:$i]:
% 19.97/20.19     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 19.97/20.19       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 19.97/20.19         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 19.97/20.19  thf('16', plain,
% 19.97/20.19      (![X13 : $i, X14 : $i]:
% 19.97/20.19         (~ (r2_hidden @ X13 @ (k1_relat_1 @ X14))
% 19.97/20.19          | (r2_hidden @ (k1_funct_1 @ X14 @ X13) @ (k2_relat_1 @ X14))
% 19.97/20.19          | ~ (v1_funct_1 @ X14)
% 19.97/20.19          | ~ (v1_relat_1 @ X14))),
% 19.97/20.19      inference('cnf', [status(esa)], [t12_funct_1])).
% 19.97/20.19  thf('17', plain,
% 19.97/20.19      (![X0 : $i, X1 : $i]:
% 19.97/20.19         (~ (r2_hidden @ X1 @ X0)
% 19.97/20.19          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 19.97/20.19          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 19.97/20.19          | (r2_hidden @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 19.97/20.19             (k2_relat_1 @ (k6_relat_1 @ X0))))),
% 19.97/20.19      inference('sup-', [status(thm)], ['15', '16'])).
% 19.97/20.19  thf('18', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 19.97/20.19      inference('cnf', [status(esa)], [fc3_funct_1])).
% 19.97/20.19  thf('19', plain, (![X12 : $i]: (v1_funct_1 @ (k6_relat_1 @ X12))),
% 19.97/20.19      inference('cnf', [status(esa)], [fc3_funct_1])).
% 19.97/20.19  thf('20', plain, (![X1 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X1)) = (X1))),
% 19.97/20.19      inference('cnf', [status(esa)], [t71_relat_1])).
% 19.97/20.19  thf('21', plain,
% 19.97/20.19      (![X0 : $i, X1 : $i]:
% 19.97/20.19         (~ (r2_hidden @ X1 @ X0)
% 19.97/20.19          | (r2_hidden @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X1) @ X0))),
% 19.97/20.19      inference('demod', [status(thm)], ['17', '18', '19', '20'])).
% 19.97/20.19  thf('22', plain,
% 19.97/20.19      (![X0 : $i]:
% 19.97/20.19         (((k6_relat_1 @ (k1_relat_1 @ X0)) = (X0))
% 19.97/20.19          | ~ (v1_funct_1 @ X0)
% 19.97/20.19          | ~ (v1_relat_1 @ X0)
% 19.97/20.19          | (r2_hidden @ 
% 19.97/20.19             (k1_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 19.97/20.19              (sk_C_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ X0)))) @ 
% 19.97/20.19             (k1_relat_1 @ X0)))),
% 19.97/20.19      inference('sup-', [status(thm)], ['14', '21'])).
% 19.97/20.19  thf('23', plain,
% 19.97/20.19      ((((r2_hidden @ 
% 19.97/20.19          (k1_funct_1 @ (k6_relat_1 @ sk_A) @ 
% 19.97/20.19           (sk_C_1 @ sk_B @ (k6_relat_1 @ (k1_relat_1 @ sk_B)))) @ 
% 19.97/20.19          (k1_relat_1 @ sk_B))
% 19.97/20.19         | ~ (v1_relat_1 @ sk_B)
% 19.97/20.19         | ~ (v1_funct_1 @ sk_B)
% 19.97/20.19         | ((k6_relat_1 @ (k1_relat_1 @ sk_B)) = (sk_B))))
% 19.97/20.19         <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 19.97/20.19      inference('sup+', [status(thm)], ['6', '22'])).
% 19.97/20.19  thf('24', plain,
% 19.97/20.19      ((((k1_relat_1 @ sk_B) = (sk_A))) <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 19.97/20.19      inference('split', [status(esa)], ['2'])).
% 19.97/20.19  thf('25', plain,
% 19.97/20.19      ((((k1_relat_1 @ sk_B) = (sk_A))) <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 19.97/20.19      inference('split', [status(esa)], ['2'])).
% 19.97/20.19  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 19.97/20.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.97/20.19  thf('27', plain, ((v1_funct_1 @ sk_B)),
% 19.97/20.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.97/20.19  thf('28', plain,
% 19.97/20.19      ((((k1_relat_1 @ sk_B) = (sk_A))) <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 19.97/20.19      inference('split', [status(esa)], ['2'])).
% 19.97/20.19  thf('29', plain,
% 19.97/20.19      ((((r2_hidden @ 
% 19.97/20.19          (k1_funct_1 @ (k6_relat_1 @ sk_A) @ 
% 19.97/20.19           (sk_C_1 @ sk_B @ (k6_relat_1 @ sk_A))) @ 
% 19.97/20.19          sk_A)
% 19.97/20.19         | ((k6_relat_1 @ sk_A) = (sk_B))))
% 19.97/20.19         <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 19.97/20.19      inference('demod', [status(thm)], ['23', '24', '25', '26', '27', '28'])).
% 19.97/20.19  thf('30', plain,
% 19.97/20.19      ((![X20 : $i]:
% 19.97/20.19          (~ (r2_hidden @ X20 @ sk_A) | ((k1_funct_1 @ sk_B @ X20) = (X20))))
% 19.97/20.19         <= ((![X20 : $i]:
% 19.97/20.19                (~ (r2_hidden @ X20 @ sk_A)
% 19.97/20.19                 | ((k1_funct_1 @ sk_B @ X20) = (X20)))))),
% 19.97/20.19      inference('split', [status(esa)], ['4'])).
% 19.97/20.19  thf('31', plain,
% 19.97/20.19      (((((k6_relat_1 @ sk_A) = (sk_B))
% 19.97/20.19         | ((k1_funct_1 @ sk_B @ 
% 19.97/20.19             (k1_funct_1 @ (k6_relat_1 @ sk_A) @ 
% 19.97/20.19              (sk_C_1 @ sk_B @ (k6_relat_1 @ sk_A))))
% 19.97/20.19             = (k1_funct_1 @ (k6_relat_1 @ sk_A) @ 
% 19.97/20.19                (sk_C_1 @ sk_B @ (k6_relat_1 @ sk_A))))))
% 19.97/20.19         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 19.97/20.19             (![X20 : $i]:
% 19.97/20.19                (~ (r2_hidden @ X20 @ sk_A)
% 19.97/20.19                 | ((k1_funct_1 @ sk_B @ X20) = (X20)))))),
% 19.97/20.19      inference('sup-', [status(thm)], ['29', '30'])).
% 19.97/20.19  thf('32', plain,
% 19.97/20.19      ((((k1_relat_1 @ sk_B) = (sk_A))) <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 19.97/20.19      inference('split', [status(esa)], ['2'])).
% 19.97/20.19  thf('33', plain,
% 19.97/20.19      (![X1 : $i]:
% 19.97/20.19         (~ (v1_relat_1 @ X1)
% 19.97/20.19          | ~ (v1_funct_1 @ X1)
% 19.97/20.19          | ((k6_relat_1 @ (k1_relat_1 @ X1)) = (X1))
% 19.97/20.19          | (r2_hidden @ (sk_C_1 @ X1 @ (k6_relat_1 @ (k1_relat_1 @ X1))) @ 
% 19.97/20.19             (k1_relat_1 @ X1)))),
% 19.97/20.19      inference('simplify', [status(thm)], ['13'])).
% 19.97/20.19  thf('34', plain,
% 19.97/20.19      ((((r2_hidden @ (sk_C_1 @ sk_B @ (k6_relat_1 @ sk_A)) @ 
% 19.97/20.19          (k1_relat_1 @ sk_B))
% 19.97/20.19         | ((k6_relat_1 @ (k1_relat_1 @ sk_B)) = (sk_B))
% 19.97/20.19         | ~ (v1_funct_1 @ sk_B)
% 19.97/20.19         | ~ (v1_relat_1 @ sk_B))) <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 19.97/20.19      inference('sup+', [status(thm)], ['32', '33'])).
% 19.97/20.19  thf('35', plain,
% 19.97/20.19      ((((k1_relat_1 @ sk_B) = (sk_A))) <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 19.97/20.19      inference('split', [status(esa)], ['2'])).
% 19.97/20.19  thf('36', plain,
% 19.97/20.19      ((((k1_relat_1 @ sk_B) = (sk_A))) <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 19.97/20.19      inference('split', [status(esa)], ['2'])).
% 19.97/20.19  thf('37', plain, ((v1_funct_1 @ sk_B)),
% 19.97/20.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.97/20.19  thf('38', plain, ((v1_relat_1 @ sk_B)),
% 19.97/20.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.97/20.19  thf('39', plain,
% 19.97/20.19      ((((r2_hidden @ (sk_C_1 @ sk_B @ (k6_relat_1 @ sk_A)) @ sk_A)
% 19.97/20.19         | ((k6_relat_1 @ sk_A) = (sk_B))))
% 19.97/20.19         <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 19.97/20.19      inference('demod', [status(thm)], ['34', '35', '36', '37', '38'])).
% 19.97/20.19  thf('40', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 19.97/20.19      inference('cnf', [status(esa)], [t71_relat_1])).
% 19.97/20.19  thf(t23_funct_1, axiom,
% 19.97/20.19    (![A:$i,B:$i]:
% 19.97/20.19     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 19.97/20.19       ( ![C:$i]:
% 19.97/20.19         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 19.97/20.19           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 19.97/20.19             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 19.97/20.19               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 19.97/20.19  thf('41', plain,
% 19.97/20.19      (![X15 : $i, X16 : $i, X17 : $i]:
% 19.97/20.19         (~ (v1_relat_1 @ X15)
% 19.97/20.19          | ~ (v1_funct_1 @ X15)
% 19.97/20.19          | ((k1_funct_1 @ (k5_relat_1 @ X16 @ X15) @ X17)
% 19.97/20.19              = (k1_funct_1 @ X15 @ (k1_funct_1 @ X16 @ X17)))
% 19.97/20.19          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ X16))
% 19.97/20.19          | ~ (v1_funct_1 @ X16)
% 19.97/20.19          | ~ (v1_relat_1 @ X16))),
% 19.97/20.19      inference('cnf', [status(esa)], [t23_funct_1])).
% 19.97/20.19  thf('42', plain,
% 19.97/20.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.97/20.19         (~ (r2_hidden @ X1 @ X0)
% 19.97/20.19          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 19.97/20.19          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 19.97/20.19          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1)
% 19.97/20.19              = (k1_funct_1 @ X2 @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X1)))
% 19.97/20.19          | ~ (v1_funct_1 @ X2)
% 19.97/20.19          | ~ (v1_relat_1 @ X2))),
% 19.97/20.19      inference('sup-', [status(thm)], ['40', '41'])).
% 19.97/20.19  thf('43', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 19.97/20.19      inference('cnf', [status(esa)], [fc3_funct_1])).
% 19.97/20.19  thf('44', plain, (![X12 : $i]: (v1_funct_1 @ (k6_relat_1 @ X12))),
% 19.97/20.19      inference('cnf', [status(esa)], [fc3_funct_1])).
% 19.97/20.19  thf('45', plain,
% 19.97/20.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.97/20.19         (~ (r2_hidden @ X1 @ X0)
% 19.97/20.19          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1)
% 19.97/20.19              = (k1_funct_1 @ X2 @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X1)))
% 19.97/20.19          | ~ (v1_funct_1 @ X2)
% 19.97/20.19          | ~ (v1_relat_1 @ X2))),
% 19.97/20.19      inference('demod', [status(thm)], ['42', '43', '44'])).
% 19.97/20.19  thf('46', plain,
% 19.97/20.19      ((![X0 : $i]:
% 19.97/20.19          (((k6_relat_1 @ sk_A) = (sk_B))
% 19.97/20.19           | ~ (v1_relat_1 @ X0)
% 19.97/20.19           | ~ (v1_funct_1 @ X0)
% 19.97/20.19           | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ X0) @ 
% 19.97/20.19               (sk_C_1 @ sk_B @ (k6_relat_1 @ sk_A)))
% 19.97/20.19               = (k1_funct_1 @ X0 @ 
% 19.97/20.19                  (k1_funct_1 @ (k6_relat_1 @ sk_A) @ 
% 19.97/20.19                   (sk_C_1 @ sk_B @ (k6_relat_1 @ sk_A)))))))
% 19.97/20.19         <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 19.97/20.19      inference('sup-', [status(thm)], ['39', '45'])).
% 19.97/20.19  thf('47', plain,
% 19.97/20.19      (((((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ 
% 19.97/20.19           (sk_C_1 @ sk_B @ (k6_relat_1 @ sk_A)))
% 19.97/20.19           = (k1_funct_1 @ (k6_relat_1 @ sk_A) @ 
% 19.97/20.19              (sk_C_1 @ sk_B @ (k6_relat_1 @ sk_A))))
% 19.97/20.19         | ((k6_relat_1 @ sk_A) = (sk_B))
% 19.97/20.19         | ~ (v1_funct_1 @ sk_B)
% 19.97/20.19         | ~ (v1_relat_1 @ sk_B)
% 19.97/20.19         | ((k6_relat_1 @ sk_A) = (sk_B))))
% 19.97/20.19         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 19.97/20.19             (![X20 : $i]:
% 19.97/20.19                (~ (r2_hidden @ X20 @ sk_A)
% 19.97/20.19                 | ((k1_funct_1 @ sk_B @ X20) = (X20)))))),
% 19.97/20.19      inference('sup+', [status(thm)], ['31', '46'])).
% 19.97/20.19  thf('48', plain,
% 19.97/20.19      ((((k1_relat_1 @ sk_B) = (sk_A))) <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 19.97/20.19      inference('split', [status(esa)], ['2'])).
% 19.97/20.19  thf(t78_relat_1, axiom,
% 19.97/20.19    (![A:$i]:
% 19.97/20.19     ( ( v1_relat_1 @ A ) =>
% 19.97/20.19       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 19.97/20.19  thf('49', plain,
% 19.97/20.19      (![X2 : $i]:
% 19.97/20.19         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X2)) @ X2) = (X2))
% 19.97/20.19          | ~ (v1_relat_1 @ X2))),
% 19.97/20.19      inference('cnf', [status(esa)], [t78_relat_1])).
% 19.97/20.19  thf('50', plain,
% 19.97/20.19      (((((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (sk_B))
% 19.97/20.19         | ~ (v1_relat_1 @ sk_B))) <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 19.97/20.19      inference('sup+', [status(thm)], ['48', '49'])).
% 19.97/20.19  thf('51', plain, ((v1_relat_1 @ sk_B)),
% 19.97/20.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.97/20.19  thf('52', plain,
% 19.97/20.19      ((((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (sk_B)))
% 19.97/20.19         <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 19.97/20.19      inference('demod', [status(thm)], ['50', '51'])).
% 19.97/20.19  thf('53', plain, ((v1_funct_1 @ sk_B)),
% 19.97/20.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.97/20.19  thf('54', plain, ((v1_relat_1 @ sk_B)),
% 19.97/20.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.97/20.19  thf('55', plain,
% 19.97/20.19      (((((k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ (k6_relat_1 @ sk_A)))
% 19.97/20.19           = (k1_funct_1 @ (k6_relat_1 @ sk_A) @ 
% 19.97/20.19              (sk_C_1 @ sk_B @ (k6_relat_1 @ sk_A))))
% 19.97/20.19         | ((k6_relat_1 @ sk_A) = (sk_B))
% 19.97/20.19         | ((k6_relat_1 @ sk_A) = (sk_B))))
% 19.97/20.19         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 19.97/20.19             (![X20 : $i]:
% 19.97/20.19                (~ (r2_hidden @ X20 @ sk_A)
% 19.97/20.19                 | ((k1_funct_1 @ sk_B @ X20) = (X20)))))),
% 19.97/20.19      inference('demod', [status(thm)], ['47', '52', '53', '54'])).
% 19.97/20.19  thf('56', plain,
% 19.97/20.19      (((((k6_relat_1 @ sk_A) = (sk_B))
% 19.97/20.19         | ((k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ (k6_relat_1 @ sk_A)))
% 19.97/20.19             = (k1_funct_1 @ (k6_relat_1 @ sk_A) @ 
% 19.97/20.19                (sk_C_1 @ sk_B @ (k6_relat_1 @ sk_A))))))
% 19.97/20.19         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 19.97/20.19             (![X20 : $i]:
% 19.97/20.19                (~ (r2_hidden @ X20 @ sk_A)
% 19.97/20.19                 | ((k1_funct_1 @ sk_B @ X20) = (X20)))))),
% 19.97/20.19      inference('simplify', [status(thm)], ['55'])).
% 19.97/20.19  thf('57', plain,
% 19.97/20.19      ((((k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ (k6_relat_1 @ sk_A)))
% 19.97/20.19          = (k1_funct_1 @ (k6_relat_1 @ sk_A) @ 
% 19.97/20.19             (sk_C_1 @ sk_B @ (k6_relat_1 @ sk_A)))))
% 19.97/20.19         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 19.97/20.19             (![X20 : $i]:
% 19.97/20.19                (~ (r2_hidden @ X20 @ sk_A)
% 19.97/20.19                 | ((k1_funct_1 @ sk_B @ X20) = (X20)))))),
% 19.97/20.19      inference('condensation', [status(thm)], ['56'])).
% 19.97/20.19  thf('58', plain,
% 19.97/20.19      (![X18 : $i, X19 : $i]:
% 19.97/20.19         (~ (v1_relat_1 @ X18)
% 19.97/20.19          | ~ (v1_funct_1 @ X18)
% 19.97/20.19          | ((X19) = (X18))
% 19.97/20.19          | ((k1_funct_1 @ X19 @ (sk_C_1 @ X18 @ X19))
% 19.97/20.19              != (k1_funct_1 @ X18 @ (sk_C_1 @ X18 @ X19)))
% 19.97/20.19          | ((k1_relat_1 @ X19) != (k1_relat_1 @ X18))
% 19.97/20.19          | ~ (v1_funct_1 @ X19)
% 19.97/20.19          | ~ (v1_relat_1 @ X19))),
% 19.97/20.19      inference('cnf', [status(esa)], [t9_funct_1])).
% 19.97/20.19  thf('59', plain,
% 19.97/20.19      (((((k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ (k6_relat_1 @ sk_A)))
% 19.97/20.19           != (k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ (k6_relat_1 @ sk_A))))
% 19.97/20.19         | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 19.97/20.19         | ~ (v1_funct_1 @ (k6_relat_1 @ sk_A))
% 19.97/20.19         | ((k1_relat_1 @ (k6_relat_1 @ sk_A)) != (k1_relat_1 @ sk_B))
% 19.97/20.19         | ((k6_relat_1 @ sk_A) = (sk_B))
% 19.97/20.19         | ~ (v1_funct_1 @ sk_B)
% 19.97/20.19         | ~ (v1_relat_1 @ sk_B)))
% 19.97/20.19         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 19.97/20.19             (![X20 : $i]:
% 19.97/20.19                (~ (r2_hidden @ X20 @ sk_A)
% 19.97/20.19                 | ((k1_funct_1 @ sk_B @ X20) = (X20)))))),
% 19.97/20.19      inference('sup-', [status(thm)], ['57', '58'])).
% 19.97/20.19  thf('60', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 19.97/20.19      inference('cnf', [status(esa)], [fc3_funct_1])).
% 19.97/20.19  thf('61', plain, (![X12 : $i]: (v1_funct_1 @ (k6_relat_1 @ X12))),
% 19.97/20.19      inference('cnf', [status(esa)], [fc3_funct_1])).
% 19.97/20.19  thf('62', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 19.97/20.19      inference('cnf', [status(esa)], [t71_relat_1])).
% 19.97/20.19  thf('63', plain,
% 19.97/20.19      ((((k1_relat_1 @ sk_B) = (sk_A))) <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 19.97/20.19      inference('split', [status(esa)], ['2'])).
% 19.97/20.19  thf('64', plain, ((v1_funct_1 @ sk_B)),
% 19.97/20.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.97/20.19  thf('65', plain, ((v1_relat_1 @ sk_B)),
% 19.97/20.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.97/20.19  thf('66', plain,
% 19.97/20.19      (((((k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ (k6_relat_1 @ sk_A)))
% 19.97/20.19           != (k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ (k6_relat_1 @ sk_A))))
% 19.97/20.19         | ((sk_A) != (sk_A))
% 19.97/20.19         | ((k6_relat_1 @ sk_A) = (sk_B))))
% 19.97/20.19         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 19.97/20.19             (![X20 : $i]:
% 19.97/20.19                (~ (r2_hidden @ X20 @ sk_A)
% 19.97/20.19                 | ((k1_funct_1 @ sk_B @ X20) = (X20)))))),
% 19.97/20.19      inference('demod', [status(thm)],
% 19.97/20.19                ['59', '60', '61', '62', '63', '64', '65'])).
% 19.97/20.19  thf('67', plain,
% 19.97/20.19      ((((k6_relat_1 @ sk_A) = (sk_B)))
% 19.97/20.19         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 19.97/20.19             (![X20 : $i]:
% 19.97/20.19                (~ (r2_hidden @ X20 @ sk_A)
% 19.97/20.19                 | ((k1_funct_1 @ sk_B @ X20) = (X20)))))),
% 19.97/20.19      inference('simplify', [status(thm)], ['66'])).
% 19.97/20.19  thf('68', plain,
% 19.97/20.19      ((((k1_funct_1 @ sk_B @ sk_C_2) != (sk_C_2))
% 19.97/20.19        | ((k1_relat_1 @ sk_B) != (sk_A))
% 19.97/20.19        | ((sk_B) != (k6_relat_1 @ sk_A)))),
% 19.97/20.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.97/20.19  thf('69', plain,
% 19.97/20.19      ((((sk_B) != (k6_relat_1 @ sk_A)))
% 19.97/20.19         <= (~ (((sk_B) = (k6_relat_1 @ sk_A))))),
% 19.97/20.19      inference('split', [status(esa)], ['68'])).
% 19.97/20.19  thf('70', plain,
% 19.97/20.19      ((((sk_B) != (sk_B)))
% 19.97/20.19         <= (~ (((sk_B) = (k6_relat_1 @ sk_A))) & 
% 19.97/20.19             (((k1_relat_1 @ sk_B) = (sk_A))) & 
% 19.97/20.19             (![X20 : $i]:
% 19.97/20.19                (~ (r2_hidden @ X20 @ sk_A)
% 19.97/20.19                 | ((k1_funct_1 @ sk_B @ X20) = (X20)))))),
% 19.97/20.19      inference('sup-', [status(thm)], ['67', '69'])).
% 19.97/20.19  thf('71', plain,
% 19.97/20.19      (~
% 19.97/20.19       (![X20 : $i]:
% 19.97/20.19          (~ (r2_hidden @ X20 @ sk_A) | ((k1_funct_1 @ sk_B @ X20) = (X20)))) | 
% 19.97/20.19       (((sk_B) = (k6_relat_1 @ sk_A))) | ~ (((k1_relat_1 @ sk_B) = (sk_A)))),
% 19.97/20.19      inference('simplify', [status(thm)], ['70'])).
% 19.97/20.19  thf('72', plain,
% 19.97/20.19      ((((sk_B) = (k6_relat_1 @ sk_A))) <= ((((sk_B) = (k6_relat_1 @ sk_A))))),
% 19.97/20.19      inference('split', [status(esa)], ['2'])).
% 19.97/20.19  thf('73', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 19.97/20.19      inference('cnf', [status(esa)], [t71_relat_1])).
% 19.97/20.19  thf('74', plain,
% 19.97/20.19      ((((k1_relat_1 @ sk_B) = (sk_A))) <= ((((sk_B) = (k6_relat_1 @ sk_A))))),
% 19.97/20.19      inference('sup+', [status(thm)], ['72', '73'])).
% 19.97/20.19  thf('75', plain,
% 19.97/20.19      ((((k1_relat_1 @ sk_B) != (sk_A)))
% 19.97/20.19         <= (~ (((k1_relat_1 @ sk_B) = (sk_A))))),
% 19.97/20.19      inference('split', [status(esa)], ['68'])).
% 19.97/20.19  thf('76', plain,
% 19.97/20.19      ((((sk_A) != (sk_A)))
% 19.97/20.19         <= (~ (((k1_relat_1 @ sk_B) = (sk_A))) & 
% 19.97/20.19             (((sk_B) = (k6_relat_1 @ sk_A))))),
% 19.97/20.19      inference('sup-', [status(thm)], ['74', '75'])).
% 19.97/20.19  thf('77', plain,
% 19.97/20.19      ((((k1_relat_1 @ sk_B) = (sk_A))) | ~ (((sk_B) = (k6_relat_1 @ sk_A)))),
% 19.97/20.19      inference('simplify', [status(thm)], ['76'])).
% 19.97/20.19  thf('78', plain,
% 19.97/20.19      (~ (((k1_funct_1 @ sk_B @ sk_C_2) = (sk_C_2))) | 
% 19.97/20.19       ~ (((k1_relat_1 @ sk_B) = (sk_A))) | ~ (((sk_B) = (k6_relat_1 @ sk_A)))),
% 19.97/20.19      inference('split', [status(esa)], ['68'])).
% 19.97/20.19  thf(t80_relat_1, axiom,
% 19.97/20.19    (![A:$i]:
% 19.97/20.19     ( ( v1_relat_1 @ A ) =>
% 19.97/20.19       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 19.97/20.19  thf('79', plain,
% 19.97/20.19      (![X3 : $i]:
% 19.97/20.19         (((k5_relat_1 @ X3 @ (k6_relat_1 @ (k2_relat_1 @ X3))) = (X3))
% 19.97/20.19          | ~ (v1_relat_1 @ X3))),
% 19.97/20.19      inference('cnf', [status(esa)], [t80_relat_1])).
% 19.97/20.19  thf('80', plain,
% 19.97/20.19      (((r2_hidden @ sk_C_2 @ sk_A)) <= (((r2_hidden @ sk_C_2 @ sk_A)))),
% 19.97/20.19      inference('split', [status(esa)], ['0'])).
% 19.97/20.19  thf('81', plain,
% 19.97/20.19      ((((sk_B) = (k6_relat_1 @ sk_A))) <= ((((sk_B) = (k6_relat_1 @ sk_A))))),
% 19.97/20.19      inference('split', [status(esa)], ['2'])).
% 19.97/20.19  thf('82', plain, (![X1 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X1)) = (X1))),
% 19.97/20.19      inference('cnf', [status(esa)], [t71_relat_1])).
% 19.97/20.19  thf('83', plain,
% 19.97/20.19      ((((k2_relat_1 @ sk_B) = (sk_A))) <= ((((sk_B) = (k6_relat_1 @ sk_A))))),
% 19.97/20.19      inference('sup+', [status(thm)], ['81', '82'])).
% 19.97/20.19  thf(d5_funct_1, axiom,
% 19.97/20.19    (![A:$i]:
% 19.97/20.19     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 19.97/20.19       ( ![B:$i]:
% 19.97/20.19         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 19.97/20.19           ( ![C:$i]:
% 19.97/20.19             ( ( r2_hidden @ C @ B ) <=>
% 19.97/20.19               ( ?[D:$i]:
% 19.97/20.19                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 19.97/20.19                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 19.97/20.19  thf('84', plain,
% 19.97/20.19      (![X5 : $i, X7 : $i, X8 : $i]:
% 19.97/20.19         (((X7) != (k2_relat_1 @ X5))
% 19.97/20.19          | (r2_hidden @ (sk_D_1 @ X8 @ X5) @ (k1_relat_1 @ X5))
% 19.97/20.19          | ~ (r2_hidden @ X8 @ X7)
% 19.97/20.19          | ~ (v1_funct_1 @ X5)
% 19.97/20.19          | ~ (v1_relat_1 @ X5))),
% 19.97/20.19      inference('cnf', [status(esa)], [d5_funct_1])).
% 19.97/20.19  thf('85', plain,
% 19.97/20.19      (![X5 : $i, X8 : $i]:
% 19.97/20.19         (~ (v1_relat_1 @ X5)
% 19.97/20.19          | ~ (v1_funct_1 @ X5)
% 19.97/20.19          | ~ (r2_hidden @ X8 @ (k2_relat_1 @ X5))
% 19.97/20.19          | (r2_hidden @ (sk_D_1 @ X8 @ X5) @ (k1_relat_1 @ X5)))),
% 19.97/20.19      inference('simplify', [status(thm)], ['84'])).
% 19.97/20.19  thf('86', plain,
% 19.97/20.19      ((![X0 : $i]:
% 19.97/20.19          (~ (r2_hidden @ X0 @ sk_A)
% 19.97/20.19           | (r2_hidden @ (sk_D_1 @ X0 @ sk_B) @ (k1_relat_1 @ sk_B))
% 19.97/20.19           | ~ (v1_funct_1 @ sk_B)
% 19.97/20.19           | ~ (v1_relat_1 @ sk_B)))
% 19.97/20.19         <= ((((sk_B) = (k6_relat_1 @ sk_A))))),
% 19.97/20.19      inference('sup-', [status(thm)], ['83', '85'])).
% 19.97/20.19  thf('87', plain,
% 19.97/20.19      ((((k1_relat_1 @ sk_B) = (sk_A))) <= ((((sk_B) = (k6_relat_1 @ sk_A))))),
% 19.97/20.19      inference('sup+', [status(thm)], ['72', '73'])).
% 19.97/20.19  thf('88', plain, ((v1_funct_1 @ sk_B)),
% 19.97/20.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.97/20.19  thf('89', plain, ((v1_relat_1 @ sk_B)),
% 19.97/20.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.97/20.19  thf('90', plain,
% 19.97/20.19      ((![X0 : $i]:
% 19.97/20.19          (~ (r2_hidden @ X0 @ sk_A)
% 19.97/20.19           | (r2_hidden @ (sk_D_1 @ X0 @ sk_B) @ sk_A)))
% 19.97/20.19         <= ((((sk_B) = (k6_relat_1 @ sk_A))))),
% 19.97/20.19      inference('demod', [status(thm)], ['86', '87', '88', '89'])).
% 19.97/20.19  thf('91', plain,
% 19.97/20.19      (((r2_hidden @ (sk_D_1 @ sk_C_2 @ sk_B) @ sk_A))
% 19.97/20.19         <= ((((sk_B) = (k6_relat_1 @ sk_A))) & ((r2_hidden @ sk_C_2 @ sk_A)))),
% 19.97/20.19      inference('sup-', [status(thm)], ['80', '90'])).
% 19.97/20.19  thf('92', plain,
% 19.97/20.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.97/20.19         (~ (r2_hidden @ X1 @ X0)
% 19.97/20.19          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1)
% 19.97/20.19              = (k1_funct_1 @ X2 @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X1)))
% 19.97/20.19          | ~ (v1_funct_1 @ X2)
% 19.97/20.19          | ~ (v1_relat_1 @ X2))),
% 19.97/20.19      inference('demod', [status(thm)], ['42', '43', '44'])).
% 19.97/20.19  thf('93', plain,
% 19.97/20.19      ((![X0 : $i]:
% 19.97/20.19          (~ (v1_relat_1 @ X0)
% 19.97/20.19           | ~ (v1_funct_1 @ X0)
% 19.97/20.19           | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ X0) @ 
% 19.97/20.19               (sk_D_1 @ sk_C_2 @ sk_B))
% 19.97/20.19               = (k1_funct_1 @ X0 @ 
% 19.97/20.19                  (k1_funct_1 @ (k6_relat_1 @ sk_A) @ (sk_D_1 @ sk_C_2 @ sk_B))))))
% 19.97/20.19         <= ((((sk_B) = (k6_relat_1 @ sk_A))) & ((r2_hidden @ sk_C_2 @ sk_A)))),
% 19.97/20.19      inference('sup-', [status(thm)], ['91', '92'])).
% 19.97/20.19  thf('94', plain,
% 19.97/20.19      ((((sk_B) = (k6_relat_1 @ sk_A))) <= ((((sk_B) = (k6_relat_1 @ sk_A))))),
% 19.97/20.19      inference('split', [status(esa)], ['2'])).
% 19.97/20.19  thf('95', plain,
% 19.97/20.19      ((((sk_B) = (k6_relat_1 @ sk_A))) <= ((((sk_B) = (k6_relat_1 @ sk_A))))),
% 19.97/20.19      inference('split', [status(esa)], ['2'])).
% 19.97/20.19  thf('96', plain,
% 19.97/20.19      (((r2_hidden @ sk_C_2 @ sk_A)) <= (((r2_hidden @ sk_C_2 @ sk_A)))),
% 19.97/20.19      inference('split', [status(esa)], ['0'])).
% 19.97/20.19  thf('97', plain,
% 19.97/20.19      ((((k2_relat_1 @ sk_B) = (sk_A))) <= ((((sk_B) = (k6_relat_1 @ sk_A))))),
% 19.97/20.19      inference('sup+', [status(thm)], ['81', '82'])).
% 19.97/20.19  thf('98', plain,
% 19.97/20.19      (![X5 : $i, X7 : $i, X8 : $i]:
% 19.97/20.19         (((X7) != (k2_relat_1 @ X5))
% 19.97/20.19          | ((X8) = (k1_funct_1 @ X5 @ (sk_D_1 @ X8 @ X5)))
% 19.97/20.19          | ~ (r2_hidden @ X8 @ X7)
% 19.97/20.19          | ~ (v1_funct_1 @ X5)
% 19.97/20.19          | ~ (v1_relat_1 @ X5))),
% 19.97/20.19      inference('cnf', [status(esa)], [d5_funct_1])).
% 19.97/20.19  thf('99', plain,
% 19.97/20.19      (![X5 : $i, X8 : $i]:
% 19.97/20.19         (~ (v1_relat_1 @ X5)
% 19.97/20.19          | ~ (v1_funct_1 @ X5)
% 19.97/20.19          | ~ (r2_hidden @ X8 @ (k2_relat_1 @ X5))
% 19.97/20.19          | ((X8) = (k1_funct_1 @ X5 @ (sk_D_1 @ X8 @ X5))))),
% 19.97/20.19      inference('simplify', [status(thm)], ['98'])).
% 19.97/20.19  thf('100', plain,
% 19.97/20.19      ((![X0 : $i]:
% 19.97/20.19          (~ (r2_hidden @ X0 @ sk_A)
% 19.97/20.19           | ((X0) = (k1_funct_1 @ sk_B @ (sk_D_1 @ X0 @ sk_B)))
% 19.97/20.19           | ~ (v1_funct_1 @ sk_B)
% 19.97/20.19           | ~ (v1_relat_1 @ sk_B)))
% 19.97/20.19         <= ((((sk_B) = (k6_relat_1 @ sk_A))))),
% 19.97/20.19      inference('sup-', [status(thm)], ['97', '99'])).
% 19.97/20.19  thf('101', plain, ((v1_funct_1 @ sk_B)),
% 19.97/20.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.97/20.19  thf('102', plain, ((v1_relat_1 @ sk_B)),
% 19.97/20.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.97/20.19  thf('103', plain,
% 19.97/20.19      ((![X0 : $i]:
% 19.97/20.19          (~ (r2_hidden @ X0 @ sk_A)
% 19.97/20.19           | ((X0) = (k1_funct_1 @ sk_B @ (sk_D_1 @ X0 @ sk_B)))))
% 19.97/20.19         <= ((((sk_B) = (k6_relat_1 @ sk_A))))),
% 19.97/20.19      inference('demod', [status(thm)], ['100', '101', '102'])).
% 19.97/20.19  thf('104', plain,
% 19.97/20.19      ((((sk_C_2) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_C_2 @ sk_B))))
% 19.97/20.19         <= ((((sk_B) = (k6_relat_1 @ sk_A))) & ((r2_hidden @ sk_C_2 @ sk_A)))),
% 19.97/20.19      inference('sup-', [status(thm)], ['96', '103'])).
% 19.97/20.19  thf('105', plain,
% 19.97/20.19      ((![X0 : $i]:
% 19.97/20.19          (~ (v1_relat_1 @ X0)
% 19.97/20.19           | ~ (v1_funct_1 @ X0)
% 19.97/20.19           | ((k1_funct_1 @ (k5_relat_1 @ sk_B @ X0) @ (sk_D_1 @ sk_C_2 @ sk_B))
% 19.97/20.19               = (k1_funct_1 @ X0 @ sk_C_2))))
% 19.97/20.19         <= ((((sk_B) = (k6_relat_1 @ sk_A))) & ((r2_hidden @ sk_C_2 @ sk_A)))),
% 19.97/20.19      inference('demod', [status(thm)], ['93', '94', '95', '104'])).
% 19.97/20.19  thf('106', plain,
% 19.97/20.19      (((((k1_funct_1 @ sk_B @ (sk_D_1 @ sk_C_2 @ sk_B))
% 19.97/20.19           = (k1_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ sk_C_2))
% 19.97/20.19         | ~ (v1_relat_1 @ sk_B)
% 19.97/20.19         | ~ (v1_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 19.97/20.19         | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))))
% 19.97/20.19         <= ((((sk_B) = (k6_relat_1 @ sk_A))) & ((r2_hidden @ sk_C_2 @ sk_A)))),
% 19.97/20.19      inference('sup+', [status(thm)], ['79', '105'])).
% 19.97/20.19  thf('107', plain,
% 19.97/20.19      ((((sk_C_2) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_C_2 @ sk_B))))
% 19.97/20.19         <= ((((sk_B) = (k6_relat_1 @ sk_A))) & ((r2_hidden @ sk_C_2 @ sk_A)))),
% 19.97/20.19      inference('sup-', [status(thm)], ['96', '103'])).
% 19.97/20.19  thf('108', plain,
% 19.97/20.19      ((((k2_relat_1 @ sk_B) = (sk_A))) <= ((((sk_B) = (k6_relat_1 @ sk_A))))),
% 19.97/20.19      inference('sup+', [status(thm)], ['81', '82'])).
% 19.97/20.19  thf('109', plain,
% 19.97/20.19      ((((sk_B) = (k6_relat_1 @ sk_A))) <= ((((sk_B) = (k6_relat_1 @ sk_A))))),
% 19.97/20.19      inference('split', [status(esa)], ['2'])).
% 19.97/20.19  thf('110', plain, ((v1_relat_1 @ sk_B)),
% 19.97/20.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.97/20.19  thf('111', plain,
% 19.97/20.19      ((((k2_relat_1 @ sk_B) = (sk_A))) <= ((((sk_B) = (k6_relat_1 @ sk_A))))),
% 19.97/20.19      inference('sup+', [status(thm)], ['81', '82'])).
% 19.97/20.19  thf('112', plain,
% 19.97/20.19      ((((sk_B) = (k6_relat_1 @ sk_A))) <= ((((sk_B) = (k6_relat_1 @ sk_A))))),
% 19.97/20.19      inference('split', [status(esa)], ['2'])).
% 19.97/20.19  thf('113', plain, ((v1_funct_1 @ sk_B)),
% 19.97/20.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.97/20.19  thf('114', plain,
% 19.97/20.19      ((((k2_relat_1 @ sk_B) = (sk_A))) <= ((((sk_B) = (k6_relat_1 @ sk_A))))),
% 19.97/20.19      inference('sup+', [status(thm)], ['81', '82'])).
% 19.97/20.19  thf('115', plain,
% 19.97/20.19      ((((sk_B) = (k6_relat_1 @ sk_A))) <= ((((sk_B) = (k6_relat_1 @ sk_A))))),
% 19.97/20.19      inference('split', [status(esa)], ['2'])).
% 19.97/20.19  thf('116', plain, ((v1_relat_1 @ sk_B)),
% 19.97/20.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.97/20.19  thf('117', plain,
% 19.97/20.19      ((((sk_C_2) = (k1_funct_1 @ sk_B @ sk_C_2)))
% 19.97/20.19         <= ((((sk_B) = (k6_relat_1 @ sk_A))) & ((r2_hidden @ sk_C_2 @ sk_A)))),
% 19.97/20.19      inference('demod', [status(thm)],
% 19.97/20.19                ['106', '107', '108', '109', '110', '111', '112', '113', 
% 19.97/20.19                 '114', '115', '116'])).
% 19.97/20.19  thf('118', plain,
% 19.97/20.19      ((((k1_funct_1 @ sk_B @ sk_C_2) != (sk_C_2)))
% 19.97/20.19         <= (~ (((k1_funct_1 @ sk_B @ sk_C_2) = (sk_C_2))))),
% 19.97/20.19      inference('split', [status(esa)], ['68'])).
% 19.97/20.19  thf('119', plain,
% 19.97/20.19      ((((sk_C_2) != (sk_C_2)))
% 19.97/20.19         <= (~ (((k1_funct_1 @ sk_B @ sk_C_2) = (sk_C_2))) & 
% 19.97/20.19             (((sk_B) = (k6_relat_1 @ sk_A))) & 
% 19.97/20.19             ((r2_hidden @ sk_C_2 @ sk_A)))),
% 19.97/20.19      inference('sup-', [status(thm)], ['117', '118'])).
% 19.97/20.19  thf('120', plain,
% 19.97/20.19      ((((k1_funct_1 @ sk_B @ sk_C_2) = (sk_C_2))) | 
% 19.97/20.19       ~ ((r2_hidden @ sk_C_2 @ sk_A)) | ~ (((sk_B) = (k6_relat_1 @ sk_A)))),
% 19.97/20.19      inference('simplify', [status(thm)], ['119'])).
% 19.97/20.19  thf('121', plain, ($false),
% 19.97/20.19      inference('sat_resolution*', [status(thm)],
% 19.97/20.19                ['1', '3', '5', '71', '77', '78', '120'])).
% 19.97/20.19  
% 19.97/20.19  % SZS output end Refutation
% 19.97/20.19  
% 20.03/20.20  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
