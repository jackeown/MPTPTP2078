%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.E5GQSTo0Ar

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:49 EST 2020

% Result     : Theorem 25.64s
% Output     : Refutation 25.64s
% Verified   : 
% Statistics : Number of formulae       :  250 (1158 expanded)
%              Number of leaves         :   24 ( 390 expanded)
%              Depth                    :   33
%              Number of atoms          : 3319 (14982 expanded)
%              Number of equality atoms :  351 (1578 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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
    ! [X21: $i] :
      ( ~ ( r2_hidden @ X21 @ sk_A )
      | ( ( k1_funct_1 @ sk_B @ X21 )
        = X21 )
      | ( sk_B
        = ( k6_relat_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ! [X21: $i] :
        ( ~ ( r2_hidden @ X21 @ sk_A )
        | ( ( k1_funct_1 @ sk_B @ X21 )
          = X21 ) )
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
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( X20 = X19 )
      | ( r2_hidden @ ( sk_C_1 @ X19 @ X20 ) @ ( k1_relat_1 @ X20 ) )
      | ( ( k1_relat_1 @ X20 )
       != ( k1_relat_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
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

thf('15',plain,
    ( ( ( r2_hidden @ ( sk_C_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) @ ( k1_relat_1 @ sk_B ) )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) )
        = sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup+',[status(thm)],['6','14'])).

thf('16',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('17',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('18',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( r2_hidden @ ( sk_C_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) @ sk_A )
      | ( ( k6_relat_1 @ sk_A )
        = sk_B ) )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf('21',plain,
    ( ! [X21: $i] :
        ( ~ ( r2_hidden @ X21 @ sk_A )
        | ( ( k1_funct_1 @ sk_B @ X21 )
          = X21 ) )
   <= ! [X21: $i] :
        ( ~ ( r2_hidden @ X21 @ sk_A )
        | ( ( k1_funct_1 @ sk_B @ X21 )
          = X21 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('22',plain,
    ( ( ( ( k6_relat_1 @ sk_A )
        = sk_B )
      | ( ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) )
        = ( sk_C_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X21: $i] :
          ( ~ ( r2_hidden @ X21 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X21 )
            = X21 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('24',plain,(
    ! [X3: $i] :
      ( ( ( k5_relat_1 @ X3 @ ( k6_relat_1 @ ( k2_relat_1 @ X3 ) ) )
        = X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('25',plain,(
    ! [X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ X1 ) )
        = X1 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

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

thf('26',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X17 @ X16 ) @ X18 )
        = ( k1_funct_1 @ X16 @ ( k1_funct_1 @ X17 @ X18 ) ) )
      | ~ ( r2_hidden @ X18 @ ( k1_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
        = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_C_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_C_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ X0 @ ( sk_C_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) )
        = ( k1_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
        = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['24','28'])).

thf('30',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('31',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ X0 @ ( sk_C_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) )
        = ( k1_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
        = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
        = X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ ( sk_C_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) )
        = ( k1_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( ( ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ) )
        = ( k1_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) )
        = sk_B )
      | ~ ( v1_funct_1 @ sk_B ) )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup+',[status(thm)],['23','33'])).

thf('35',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('36',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('38',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) )
        = ( k1_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ) ) )
      | ( ( k6_relat_1 @ sk_A )
        = sk_B ) )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(demod,[status(thm)],['34','35','36','37','38'])).

thf('40',plain,
    ( ( ( ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) )
        = ( k1_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( sk_C_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ) )
      | ( ( k6_relat_1 @ sk_A )
        = sk_B )
      | ( ( k6_relat_1 @ sk_A )
        = sk_B ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X21: $i] :
          ( ~ ( r2_hidden @ X21 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X21 )
            = X21 ) ) ) ),
    inference('sup+',[status(thm)],['22','39'])).

thf('41',plain,
    ( ( ( ( k6_relat_1 @ sk_A )
        = sk_B )
      | ( ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) )
        = ( k1_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( sk_C_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ) ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X21: $i] :
          ( ~ ( r2_hidden @ X21 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X21 )
            = X21 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

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

thf('42',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ ( sk_C @ X4 @ X5 ) @ X4 )
      | ( ( sk_C @ X4 @ X5 )
        = ( k1_funct_1 @ X5 @ ( sk_D @ X4 @ X5 ) ) )
      | ( X4
        = ( k2_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('44',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ ( sk_C @ X4 @ X5 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X4 @ X5 ) @ ( k1_relat_1 @ X5 ) )
      | ( X4
        = ( k2_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( X1
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k6_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('47',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('48',plain,(
    ! [X1: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X1 ) )
      = X1 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k6_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['45','46','47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('51',plain,(
    ! [X2: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X2 ) ) @ X2 )
        = X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf(t21_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
          <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
              & ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) )).

thf('55',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ ( k5_relat_1 @ X13 @ X15 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X13 @ X14 ) @ ( k1_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('58',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('59',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('61',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('62',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57','58','59','60','61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k6_relat_1 @ X0 ) ) @ X1 )
      | ( X1 = X0 )
      | ( r2_hidden @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ ( sk_D @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( X1
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k6_relat_1 @ X0 ) ) @ X1 )
      | ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k6_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['42','64'])).

thf('66',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('67',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('68',plain,(
    ! [X1: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X1 ) )
      = X1 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k6_relat_1 @ X0 ) ) @ X1 )
      | ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k6_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['65','66','67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k6_relat_1 @ X0 ) ) @ X1 )
      | ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ! [X21: $i] :
        ( ~ ( r2_hidden @ X21 @ sk_A )
        | ( ( k1_funct_1 @ sk_B @ X21 )
          = X21 ) )
   <= ! [X21: $i] :
        ( ~ ( r2_hidden @ X21 @ sk_A )
        | ( ( k1_funct_1 @ sk_B @ X21 )
          = X21 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('72',plain,
    ( ! [X0: $i] :
        ( ( X0 = sk_A )
        | ( r2_hidden @ ( sk_C @ X0 @ ( k6_relat_1 @ sk_A ) ) @ X0 )
        | ( ( k1_funct_1 @ sk_B @ ( sk_C @ X0 @ ( k6_relat_1 @ sk_A ) ) )
          = ( sk_C @ X0 @ ( k6_relat_1 @ sk_A ) ) ) )
   <= ! [X21: $i] :
        ( ~ ( r2_hidden @ X21 @ sk_A )
        | ( ( k1_funct_1 @ sk_B @ X21 )
          = X21 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k6_relat_1 @ X0 ) ) @ X1 )
      | ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('74',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('75',plain,(
    ! [X3: $i] :
      ( ( ( k5_relat_1 @ X3 @ ( k6_relat_1 @ ( k2_relat_1 @ X3 ) ) )
        = X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('76',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ ( k5_relat_1 @ X13 @ X15 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X13 @ X14 ) @ ( k1_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ ( k1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('79',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','78','79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( v1_relat_1 @ sk_B )
        | ( r2_hidden @ ( k1_funct_1 @ sk_B @ X0 ) @ ( k2_relat_1 @ sk_B ) )
        | ~ ( v1_funct_1 @ sk_B ) )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['74','82'])).

thf('84',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ( r2_hidden @ ( k1_funct_1 @ sk_B @ X0 ) @ ( k2_relat_1 @ sk_B ) ) )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ! [X0: $i] :
        ( ( X0 = sk_A )
        | ( r2_hidden @ ( sk_C @ X0 @ ( k6_relat_1 @ sk_A ) ) @ X0 )
        | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_C @ X0 @ ( k6_relat_1 @ sk_A ) ) ) @ ( k2_relat_1 @ sk_B ) ) )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['73','86'])).

thf('88',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C @ X0 @ ( k6_relat_1 @ sk_A ) ) @ ( k2_relat_1 @ sk_B ) )
        | ( r2_hidden @ ( sk_C @ X0 @ ( k6_relat_1 @ sk_A ) ) @ X0 )
        | ( X0 = sk_A )
        | ( r2_hidden @ ( sk_C @ X0 @ ( k6_relat_1 @ sk_A ) ) @ X0 )
        | ( X0 = sk_A ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X21: $i] :
          ( ~ ( r2_hidden @ X21 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X21 )
            = X21 ) ) ) ),
    inference('sup+',[status(thm)],['72','87'])).

thf('89',plain,
    ( ! [X0: $i] :
        ( ( X0 = sk_A )
        | ( r2_hidden @ ( sk_C @ X0 @ ( k6_relat_1 @ sk_A ) ) @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ ( k6_relat_1 @ sk_A ) ) @ ( k2_relat_1 @ sk_B ) ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X21: $i] :
          ( ~ ( r2_hidden @ X21 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X21 )
            = X21 ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,
    ( ( ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) @ ( k2_relat_1 @ sk_B ) )
      | ( ( k2_relat_1 @ sk_B )
        = sk_A ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X21: $i] :
          ( ~ ( r2_hidden @ X21 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X21 )
            = X21 ) ) ) ),
    inference(eq_fact,[status(thm)],['89'])).

thf('91',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ( X7
       != ( k2_relat_1 @ X5 ) )
      | ( X8
        = ( k1_funct_1 @ X5 @ ( sk_D_1 @ X8 @ X5 ) ) )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('92',plain,(
    ! [X5: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k2_relat_1 @ X5 ) )
      | ( X8
        = ( k1_funct_1 @ X5 @ ( sk_D_1 @ X8 @ X5 ) ) ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ( ( ( k2_relat_1 @ sk_B )
        = sk_A )
      | ( ( sk_C @ ( k2_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
        = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ ( sk_C @ ( k2_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) @ sk_B ) ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X21: $i] :
          ( ~ ( r2_hidden @ X21 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X21 )
            = X21 ) ) ) ),
    inference('sup-',[status(thm)],['90','92'])).

thf('94',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( ( ( k2_relat_1 @ sk_B )
        = sk_A )
      | ( ( sk_C @ ( k2_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
        = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ ( sk_C @ ( k2_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) @ sk_B ) ) ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X21: $i] :
          ( ~ ( r2_hidden @ X21 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X21 )
            = X21 ) ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,
    ( ( ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) @ ( k2_relat_1 @ sk_B ) )
      | ( ( k2_relat_1 @ sk_B )
        = sk_A ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X21: $i] :
          ( ~ ( r2_hidden @ X21 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X21 )
            = X21 ) ) ) ),
    inference(eq_fact,[status(thm)],['89'])).

thf('98',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ( X7
       != ( k2_relat_1 @ X5 ) )
      | ( r2_hidden @ ( sk_D_1 @ X8 @ X5 ) @ ( k1_relat_1 @ X5 ) )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('99',plain,(
    ! [X5: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k2_relat_1 @ X5 ) )
      | ( r2_hidden @ ( sk_D_1 @ X8 @ X5 ) @ ( k1_relat_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,
    ( ( ( ( k2_relat_1 @ sk_B )
        = sk_A )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ ( k2_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X21: $i] :
          ( ~ ( r2_hidden @ X21 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X21 )
            = X21 ) ) ) ),
    inference('sup-',[status(thm)],['97','99'])).

thf('101',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('102',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( ( ( k2_relat_1 @ sk_B )
        = sk_A )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ ( k2_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) @ sk_B ) @ sk_A ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X21: $i] :
          ( ~ ( r2_hidden @ X21 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X21 )
            = X21 ) ) ) ),
    inference(demod,[status(thm)],['100','101','102','103'])).

thf('105',plain,
    ( ! [X21: $i] :
        ( ~ ( r2_hidden @ X21 @ sk_A )
        | ( ( k1_funct_1 @ sk_B @ X21 )
          = X21 ) )
   <= ! [X21: $i] :
        ( ~ ( r2_hidden @ X21 @ sk_A )
        | ( ( k1_funct_1 @ sk_B @ X21 )
          = X21 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('106',plain,
    ( ( ( ( k2_relat_1 @ sk_B )
        = sk_A )
      | ( ( k1_funct_1 @ sk_B @ ( sk_D_1 @ ( sk_C @ ( k2_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) @ sk_B ) )
        = ( sk_D_1 @ ( sk_C @ ( k2_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) @ sk_B ) ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X21: $i] :
          ( ~ ( r2_hidden @ X21 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X21 )
            = X21 ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( ( ( sk_C @ ( k2_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
        = ( sk_D_1 @ ( sk_C @ ( k2_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) @ sk_B ) )
      | ( ( k2_relat_1 @ sk_B )
        = sk_A )
      | ( ( k2_relat_1 @ sk_B )
        = sk_A ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X21: $i] :
          ( ~ ( r2_hidden @ X21 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X21 )
            = X21 ) ) ) ),
    inference('sup+',[status(thm)],['96','106'])).

thf('108',plain,
    ( ( ( ( k2_relat_1 @ sk_B )
        = sk_A )
      | ( ( sk_C @ ( k2_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
        = ( sk_D_1 @ ( sk_C @ ( k2_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) @ sk_B ) ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X21: $i] :
          ( ~ ( r2_hidden @ X21 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X21 )
            = X21 ) ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ ( sk_C @ X4 @ X5 ) @ X4 )
      | ( ( sk_C @ X4 @ X5 )
        = ( k1_funct_1 @ X5 @ ( sk_D @ X4 @ X5 ) ) )
      | ( X4
        = ( k2_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('110',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ ( sk_C @ X4 @ X5 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X4 @ X5 ) @ ( k1_relat_1 @ X5 ) )
      | ( X4
        = ( k2_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_D @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_D @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['109','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ! [X5: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k2_relat_1 @ X5 ) )
      | ( r2_hidden @ ( sk_D_1 @ X8 @ X5 ) @ ( k1_relat_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ ( k2_relat_1 @ X0 ) @ X1 ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) @ ( k1_relat_1 @ sk_B ) )
      | ( ( k2_relat_1 @ sk_B )
        = sk_A )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k2_relat_1 @ sk_B )
        = ( k2_relat_1 @ ( k6_relat_1 @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) @ ( k2_relat_1 @ ( k6_relat_1 @ sk_A ) ) ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X21: $i] :
          ( ~ ( r2_hidden @ X21 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X21 )
            = X21 ) ) ) ),
    inference('sup+',[status(thm)],['108','117'])).

thf('119',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('120',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X1: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X1 ) )
      = X1 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('123',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('124',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('125',plain,(
    ! [X1: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X1 ) )
      = X1 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('126',plain,
    ( ( ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) @ sk_A )
      | ( ( k2_relat_1 @ sk_B )
        = sk_A )
      | ( ( k2_relat_1 @ sk_B )
        = sk_A )
      | ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) @ sk_A ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X21: $i] :
          ( ~ ( r2_hidden @ X21 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X21 )
            = X21 ) ) ) ),
    inference(demod,[status(thm)],['118','119','120','121','122','123','124','125'])).

thf('127',plain,
    ( ( ( ( k2_relat_1 @ sk_B )
        = sk_A )
      | ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) @ sk_A ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X21: $i] :
          ( ~ ( r2_hidden @ X21 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X21 )
            = X21 ) ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    ! [X1: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X1 ) )
      = X1 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('129',plain,(
    ! [X5: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k2_relat_1 @ X5 ) )
      | ( X8
        = ( k1_funct_1 @ X5 @ ( sk_D_1 @ X8 @ X5 ) ) ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( X1
        = ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ ( sk_D_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('132',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( X1
        = ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ ( sk_D_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('134',plain,
    ( ( ( ( k2_relat_1 @ sk_B )
        = sk_A )
      | ( ( sk_C @ ( k2_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
        = ( k1_funct_1 @ ( k6_relat_1 @ sk_A ) @ ( sk_D_1 @ ( sk_C @ ( k2_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) @ ( k6_relat_1 @ sk_A ) ) ) ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X21: $i] :
          ( ~ ( r2_hidden @ X21 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X21 )
            = X21 ) ) ) ),
    inference('sup-',[status(thm)],['127','133'])).

thf('135',plain,
    ( ( ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) @ ( k2_relat_1 @ sk_B ) )
      | ( ( k2_relat_1 @ sk_B )
        = sk_A ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X21: $i] :
          ( ~ ( r2_hidden @ X21 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X21 )
            = X21 ) ) ) ),
    inference(eq_fact,[status(thm)],['89'])).

thf('136',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X4 @ X5 ) @ X4 )
      | ( ( sk_C @ X4 @ X5 )
       != ( k1_funct_1 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ X5 ) )
      | ( X4
        = ( k2_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('137',plain,
    ( ! [X0: $i] :
        ( ( ( k2_relat_1 @ sk_B )
          = sk_A )
        | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
        | ~ ( v1_funct_1 @ ( k6_relat_1 @ sk_A ) )
        | ( ( k2_relat_1 @ sk_B )
          = ( k2_relat_1 @ ( k6_relat_1 @ sk_A ) ) )
        | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) ) )
        | ( ( sk_C @ ( k2_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
         != ( k1_funct_1 @ ( k6_relat_1 @ sk_A ) @ X0 ) ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X21: $i] :
          ( ~ ( r2_hidden @ X21 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X21 )
            = X21 ) ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('139',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('140',plain,(
    ! [X1: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X1 ) )
      = X1 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('142',plain,
    ( ! [X0: $i] :
        ( ( ( k2_relat_1 @ sk_B )
          = sk_A )
        | ( ( k2_relat_1 @ sk_B )
          = sk_A )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( ( sk_C @ ( k2_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
         != ( k1_funct_1 @ ( k6_relat_1 @ sk_A ) @ X0 ) ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X21: $i] :
          ( ~ ( r2_hidden @ X21 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X21 )
            = X21 ) ) ) ),
    inference(demod,[status(thm)],['137','138','139','140','141'])).

thf('143',plain,
    ( ! [X0: $i] :
        ( ( ( sk_C @ ( k2_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
         != ( k1_funct_1 @ ( k6_relat_1 @ sk_A ) @ X0 ) )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( ( k2_relat_1 @ sk_B )
          = sk_A ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X21: $i] :
          ( ~ ( r2_hidden @ X21 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X21 )
            = X21 ) ) ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,
    ( ( ( ( sk_C @ ( k2_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
       != ( sk_C @ ( k2_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) )
      | ( ( k2_relat_1 @ sk_B )
        = sk_A )
      | ( ( k2_relat_1 @ sk_B )
        = sk_A )
      | ~ ( r2_hidden @ ( sk_D_1 @ ( sk_C @ ( k2_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) @ ( k6_relat_1 @ sk_A ) ) @ sk_A ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X21: $i] :
          ( ~ ( r2_hidden @ X21 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X21 )
            = X21 ) ) ) ),
    inference('sup-',[status(thm)],['134','143'])).

thf('145',plain,
    ( ( ~ ( r2_hidden @ ( sk_D_1 @ ( sk_C @ ( k2_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) @ ( k6_relat_1 @ sk_A ) ) @ sk_A )
      | ( ( k2_relat_1 @ sk_B )
        = sk_A ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X21: $i] :
          ( ~ ( r2_hidden @ X21 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X21 )
            = X21 ) ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,
    ( ( ( ( k2_relat_1 @ sk_B )
        = sk_A )
      | ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) @ sk_A ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X21: $i] :
          ( ~ ( r2_hidden @ X21 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X21 )
            = X21 ) ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('147',plain,(
    ! [X1: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X1 ) )
      = X1 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('148',plain,(
    ! [X5: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k2_relat_1 @ X5 ) )
      | ( r2_hidden @ ( sk_D_1 @ X8 @ X5 ) @ ( k1_relat_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('151',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('152',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['149','150','151','152'])).

thf('154',plain,
    ( ( ( ( k2_relat_1 @ sk_B )
        = sk_A )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ ( k2_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) @ ( k6_relat_1 @ sk_A ) ) @ sk_A ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X21: $i] :
          ( ~ ( r2_hidden @ X21 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X21 )
            = X21 ) ) ) ),
    inference('sup-',[status(thm)],['146','153'])).

thf('155',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = sk_A )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X21: $i] :
          ( ~ ( r2_hidden @ X21 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X21 )
            = X21 ) ) ) ),
    inference(clc,[status(thm)],['145','154'])).

thf('156',plain,
    ( ( ( ( k6_relat_1 @ sk_A )
        = sk_B )
      | ( ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) )
        = ( k1_funct_1 @ ( k6_relat_1 @ sk_A ) @ ( sk_C_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ) ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X21: $i] :
          ( ~ ( r2_hidden @ X21 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X21 )
            = X21 ) ) ) ),
    inference(demod,[status(thm)],['41','155'])).

thf('157',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) )
      = ( k1_funct_1 @ ( k6_relat_1 @ sk_A ) @ ( sk_C_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X21: $i] :
          ( ~ ( r2_hidden @ X21 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X21 )
            = X21 ) ) ) ),
    inference(condensation,[status(thm)],['156'])).

thf('158',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( X20 = X19 )
      | ( ( k1_funct_1 @ X20 @ ( sk_C_1 @ X19 @ X20 ) )
       != ( k1_funct_1 @ X19 @ ( sk_C_1 @ X19 @ X20 ) ) )
      | ( ( k1_relat_1 @ X20 )
       != ( k1_relat_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('159',plain,
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
      & ! [X21: $i] :
          ( ~ ( r2_hidden @ X21 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X21 )
            = X21 ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('161',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('163',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('164',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( ( ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) )
       != ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ) )
      | ( sk_A != sk_A )
      | ( ( k6_relat_1 @ sk_A )
        = sk_B ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X21: $i] :
          ( ~ ( r2_hidden @ X21 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X21 )
            = X21 ) ) ) ),
    inference(demod,[status(thm)],['159','160','161','162','163','164','165'])).

thf('167',plain,
    ( ( ( k6_relat_1 @ sk_A )
      = sk_B )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X21: $i] :
          ( ~ ( r2_hidden @ X21 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X21 )
            = X21 ) ) ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_C_2 )
     != sk_C_2 )
    | ( ( k1_relat_1 @ sk_B )
     != sk_A )
    | ( sk_B
     != ( k6_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( sk_B
     != ( k6_relat_1 @ sk_A ) )
   <= ( sk_B
     != ( k6_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['168'])).

thf('170',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B
       != ( k6_relat_1 @ sk_A ) )
      & ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X21: $i] :
          ( ~ ( r2_hidden @ X21 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X21 )
            = X21 ) ) ) ),
    inference('sup-',[status(thm)],['167','169'])).

thf('171',plain,
    ( ~ ! [X21: $i] :
          ( ~ ( r2_hidden @ X21 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X21 )
            = X21 ) )
    | ( sk_B
      = ( k6_relat_1 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_B )
     != sk_A ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,
    ( ( sk_B
      = ( k6_relat_1 @ sk_A ) )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('174',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['172','173'])).

thf('175',plain,
    ( ( ( k1_relat_1 @ sk_B )
     != sk_A )
   <= ( ( k1_relat_1 @ sk_B )
     != sk_A ) ),
    inference(split,[status(esa)],['168'])).

thf('176',plain,
    ( ( sk_A != sk_A )
   <= ( ( ( k1_relat_1 @ sk_B )
       != sk_A )
      & ( sk_B
        = ( k6_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
    | ( sk_B
     != ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_C_2 )
     != sk_C_2 )
    | ( ( k1_relat_1 @ sk_B )
     != sk_A )
    | ( sk_B
     != ( k6_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['168'])).

thf('179',plain,(
    ! [X3: $i] :
      ( ( ( k5_relat_1 @ X3 @ ( k6_relat_1 @ ( k2_relat_1 @ X3 ) ) )
        = X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('180',plain,
    ( ( r2_hidden @ sk_C_2 @ sk_A )
   <= ( r2_hidden @ sk_C_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('181',plain,
    ( ( sk_B
      = ( k6_relat_1 @ sk_A ) )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('182',plain,(
    ! [X1: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X1 ) )
      = X1 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('183',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = sk_A )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['181','182'])).

thf('184',plain,(
    ! [X5: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k2_relat_1 @ X5 ) )
      | ( r2_hidden @ ( sk_D_1 @ X8 @ X5 ) @ ( k1_relat_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('185',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
        | ~ ( v1_funct_1 @ sk_B )
        | ~ ( v1_relat_1 @ sk_B ) )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['172','173'])).

thf('187',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B ) @ sk_A ) )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['185','186','187','188'])).

thf('190',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C_2 @ sk_B ) @ sk_A )
   <= ( ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      & ( r2_hidden @ sk_C_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['180','189'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('192',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X17 @ X16 ) @ X18 )
        = ( k1_funct_1 @ X16 @ ( k1_funct_1 @ X17 @ X18 ) ) )
      | ~ ( r2_hidden @ X18 @ ( k1_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('193',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 )
        = ( k1_funct_1 @ X2 @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('195',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('196',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 )
        = ( k1_funct_1 @ X2 @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['193','194','195'])).

thf('197',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 ) @ ( sk_D_1 @ sk_C_2 @ sk_B ) )
          = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k6_relat_1 @ sk_A ) @ ( sk_D_1 @ sk_C_2 @ sk_B ) ) ) ) )
   <= ( ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      & ( r2_hidden @ sk_C_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['190','196'])).

thf('198',plain,
    ( ( sk_B
      = ( k6_relat_1 @ sk_A ) )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('199',plain,
    ( ( sk_B
      = ( k6_relat_1 @ sk_A ) )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('200',plain,
    ( ( r2_hidden @ sk_C_2 @ sk_A )
   <= ( r2_hidden @ sk_C_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('201',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = sk_A )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['181','182'])).

thf('202',plain,(
    ! [X5: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k2_relat_1 @ X5 ) )
      | ( X8
        = ( k1_funct_1 @ X5 @ ( sk_D_1 @ X8 @ X5 ) ) ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('203',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ( X0
          = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ X0 @ sk_B ) ) )
        | ~ ( v1_funct_1 @ sk_B )
        | ~ ( v1_relat_1 @ sk_B ) )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ( X0
          = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ X0 @ sk_B ) ) ) )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['203','204','205'])).

thf('207',plain,
    ( ( sk_C_2
      = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_C_2 @ sk_B ) ) )
   <= ( ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      & ( r2_hidden @ sk_C_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['200','206'])).

thf('208',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ X0 ) @ ( sk_D_1 @ sk_C_2 @ sk_B ) )
          = ( k1_funct_1 @ X0 @ sk_C_2 ) ) )
   <= ( ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      & ( r2_hidden @ sk_C_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['197','198','199','207'])).

thf('209',plain,
    ( ( ( ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_C_2 @ sk_B ) )
        = ( k1_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ sk_C_2 ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) )
   <= ( ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      & ( r2_hidden @ sk_C_2 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['179','208'])).

thf('210',plain,
    ( ( sk_C_2
      = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_C_2 @ sk_B ) ) )
   <= ( ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      & ( r2_hidden @ sk_C_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['200','206'])).

thf('211',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = sk_A )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['181','182'])).

thf('212',plain,
    ( ( sk_B
      = ( k6_relat_1 @ sk_A ) )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('213',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = sk_A )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['181','182'])).

thf('215',plain,
    ( ( sk_B
      = ( k6_relat_1 @ sk_A ) )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('216',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = sk_A )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['181','182'])).

thf('218',plain,
    ( ( sk_B
      = ( k6_relat_1 @ sk_A ) )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('219',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,
    ( ( sk_C_2
      = ( k1_funct_1 @ sk_B @ sk_C_2 ) )
   <= ( ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      & ( r2_hidden @ sk_C_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['209','210','211','212','213','214','215','216','217','218','219'])).

thf('221',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_C_2 )
     != sk_C_2 )
   <= ( ( k1_funct_1 @ sk_B @ sk_C_2 )
     != sk_C_2 ) ),
    inference(split,[status(esa)],['168'])).

thf('222',plain,
    ( ( sk_C_2 != sk_C_2 )
   <= ( ( ( k1_funct_1 @ sk_B @ sk_C_2 )
       != sk_C_2 )
      & ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      & ( r2_hidden @ sk_C_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['220','221'])).

thf('223',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_C_2 )
      = sk_C_2 )
    | ~ ( r2_hidden @ sk_C_2 @ sk_A )
    | ( sk_B
     != ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['222'])).

thf('224',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','171','177','178','223'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.E5GQSTo0Ar
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:04:02 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 25.64/25.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 25.64/25.88  % Solved by: fo/fo7.sh
% 25.64/25.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 25.64/25.88  % done 11933 iterations in 25.416s
% 25.64/25.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 25.64/25.88  % SZS output start Refutation
% 25.64/25.88  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 25.64/25.88  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 25.64/25.88  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 25.64/25.88  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 25.64/25.88  thf(sk_C_2_type, type, sk_C_2: $i).
% 25.64/25.88  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 25.64/25.88  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 25.64/25.88  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 25.64/25.88  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 25.64/25.88  thf(sk_B_type, type, sk_B: $i).
% 25.64/25.88  thf(sk_A_type, type, sk_A: $i).
% 25.64/25.88  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 25.64/25.88  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 25.64/25.88  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 25.64/25.88  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 25.64/25.88  thf(t34_funct_1, conjecture,
% 25.64/25.88    (![A:$i,B:$i]:
% 25.64/25.88     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 25.64/25.88       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 25.64/25.88         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 25.64/25.88           ( ![C:$i]:
% 25.64/25.88             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 25.64/25.88  thf(zf_stmt_0, negated_conjecture,
% 25.64/25.88    (~( ![A:$i,B:$i]:
% 25.64/25.88        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 25.64/25.88          ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 25.64/25.88            ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 25.64/25.88              ( ![C:$i]:
% 25.64/25.88                ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ) )),
% 25.64/25.88    inference('cnf.neg', [status(esa)], [t34_funct_1])).
% 25.64/25.88  thf('0', plain,
% 25.64/25.88      (((r2_hidden @ sk_C_2 @ sk_A)
% 25.64/25.88        | ((k1_relat_1 @ sk_B) != (sk_A))
% 25.64/25.88        | ((sk_B) != (k6_relat_1 @ sk_A)))),
% 25.64/25.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.64/25.88  thf('1', plain,
% 25.64/25.88      (((r2_hidden @ sk_C_2 @ sk_A)) | ~ (((sk_B) = (k6_relat_1 @ sk_A))) | 
% 25.64/25.88       ~ (((k1_relat_1 @ sk_B) = (sk_A)))),
% 25.64/25.88      inference('split', [status(esa)], ['0'])).
% 25.64/25.88  thf('2', plain,
% 25.64/25.88      ((((k1_relat_1 @ sk_B) = (sk_A)) | ((sk_B) = (k6_relat_1 @ sk_A)))),
% 25.64/25.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.64/25.88  thf('3', plain,
% 25.64/25.88      ((((k1_relat_1 @ sk_B) = (sk_A))) | (((sk_B) = (k6_relat_1 @ sk_A)))),
% 25.64/25.88      inference('split', [status(esa)], ['2'])).
% 25.64/25.88  thf('4', plain,
% 25.64/25.88      (![X21 : $i]:
% 25.64/25.88         (~ (r2_hidden @ X21 @ sk_A)
% 25.64/25.88          | ((k1_funct_1 @ sk_B @ X21) = (X21))
% 25.64/25.88          | ((sk_B) = (k6_relat_1 @ sk_A)))),
% 25.64/25.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.64/25.88  thf('5', plain,
% 25.64/25.88      ((![X21 : $i]:
% 25.64/25.88          (~ (r2_hidden @ X21 @ sk_A) | ((k1_funct_1 @ sk_B @ X21) = (X21)))) | 
% 25.64/25.88       (((sk_B) = (k6_relat_1 @ sk_A)))),
% 25.64/25.88      inference('split', [status(esa)], ['4'])).
% 25.64/25.88  thf('6', plain,
% 25.64/25.88      ((((k1_relat_1 @ sk_B) = (sk_A))) <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 25.64/25.88      inference('split', [status(esa)], ['2'])).
% 25.64/25.88  thf(t71_relat_1, axiom,
% 25.64/25.88    (![A:$i]:
% 25.64/25.88     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 25.64/25.88       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 25.64/25.88  thf('7', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 25.64/25.88      inference('cnf', [status(esa)], [t71_relat_1])).
% 25.64/25.88  thf(t9_funct_1, axiom,
% 25.64/25.88    (![A:$i]:
% 25.64/25.88     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 25.64/25.88       ( ![B:$i]:
% 25.64/25.88         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 25.64/25.88           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 25.64/25.88               ( ![C:$i]:
% 25.64/25.88                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 25.64/25.88                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 25.64/25.88             ( ( A ) = ( B ) ) ) ) ) ))).
% 25.64/25.88  thf('8', plain,
% 25.64/25.88      (![X19 : $i, X20 : $i]:
% 25.64/25.88         (~ (v1_relat_1 @ X19)
% 25.64/25.88          | ~ (v1_funct_1 @ X19)
% 25.64/25.88          | ((X20) = (X19))
% 25.64/25.88          | (r2_hidden @ (sk_C_1 @ X19 @ X20) @ (k1_relat_1 @ X20))
% 25.64/25.88          | ((k1_relat_1 @ X20) != (k1_relat_1 @ X19))
% 25.64/25.88          | ~ (v1_funct_1 @ X20)
% 25.64/25.88          | ~ (v1_relat_1 @ X20))),
% 25.64/25.88      inference('cnf', [status(esa)], [t9_funct_1])).
% 25.64/25.88  thf('9', plain,
% 25.64/25.88      (![X0 : $i, X1 : $i]:
% 25.64/25.88         (((X0) != (k1_relat_1 @ X1))
% 25.64/25.88          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 25.64/25.88          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 25.64/25.88          | (r2_hidden @ (sk_C_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 25.64/25.88             (k1_relat_1 @ (k6_relat_1 @ X0)))
% 25.64/25.88          | ((k6_relat_1 @ X0) = (X1))
% 25.64/25.88          | ~ (v1_funct_1 @ X1)
% 25.64/25.88          | ~ (v1_relat_1 @ X1))),
% 25.64/25.88      inference('sup-', [status(thm)], ['7', '8'])).
% 25.64/25.88  thf(fc3_funct_1, axiom,
% 25.64/25.88    (![A:$i]:
% 25.64/25.88     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 25.64/25.88       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 25.64/25.88  thf('10', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 25.64/25.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 25.64/25.88  thf('11', plain, (![X12 : $i]: (v1_funct_1 @ (k6_relat_1 @ X12))),
% 25.64/25.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 25.64/25.88  thf('12', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 25.64/25.88      inference('cnf', [status(esa)], [t71_relat_1])).
% 25.64/25.88  thf('13', plain,
% 25.64/25.88      (![X0 : $i, X1 : $i]:
% 25.64/25.88         (((X0) != (k1_relat_1 @ X1))
% 25.64/25.88          | (r2_hidden @ (sk_C_1 @ X1 @ (k6_relat_1 @ X0)) @ X0)
% 25.64/25.88          | ((k6_relat_1 @ X0) = (X1))
% 25.64/25.88          | ~ (v1_funct_1 @ X1)
% 25.64/25.88          | ~ (v1_relat_1 @ X1))),
% 25.64/25.88      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 25.64/25.88  thf('14', plain,
% 25.64/25.88      (![X1 : $i]:
% 25.64/25.88         (~ (v1_relat_1 @ X1)
% 25.64/25.88          | ~ (v1_funct_1 @ X1)
% 25.64/25.88          | ((k6_relat_1 @ (k1_relat_1 @ X1)) = (X1))
% 25.64/25.88          | (r2_hidden @ (sk_C_1 @ X1 @ (k6_relat_1 @ (k1_relat_1 @ X1))) @ 
% 25.64/25.88             (k1_relat_1 @ X1)))),
% 25.64/25.88      inference('simplify', [status(thm)], ['13'])).
% 25.64/25.88  thf('15', plain,
% 25.64/25.88      ((((r2_hidden @ (sk_C_1 @ sk_B @ (k6_relat_1 @ sk_A)) @ 
% 25.64/25.88          (k1_relat_1 @ sk_B))
% 25.64/25.88         | ((k6_relat_1 @ (k1_relat_1 @ sk_B)) = (sk_B))
% 25.64/25.88         | ~ (v1_funct_1 @ sk_B)
% 25.64/25.88         | ~ (v1_relat_1 @ sk_B))) <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 25.64/25.88      inference('sup+', [status(thm)], ['6', '14'])).
% 25.64/25.88  thf('16', plain,
% 25.64/25.88      ((((k1_relat_1 @ sk_B) = (sk_A))) <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 25.64/25.88      inference('split', [status(esa)], ['2'])).
% 25.64/25.88  thf('17', plain,
% 25.64/25.88      ((((k1_relat_1 @ sk_B) = (sk_A))) <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 25.64/25.88      inference('split', [status(esa)], ['2'])).
% 25.64/25.88  thf('18', plain, ((v1_funct_1 @ sk_B)),
% 25.64/25.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.64/25.88  thf('19', plain, ((v1_relat_1 @ sk_B)),
% 25.64/25.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.64/25.88  thf('20', plain,
% 25.64/25.88      ((((r2_hidden @ (sk_C_1 @ sk_B @ (k6_relat_1 @ sk_A)) @ sk_A)
% 25.64/25.88         | ((k6_relat_1 @ sk_A) = (sk_B))))
% 25.64/25.88         <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 25.64/25.88      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 25.64/25.88  thf('21', plain,
% 25.64/25.88      ((![X21 : $i]:
% 25.64/25.88          (~ (r2_hidden @ X21 @ sk_A) | ((k1_funct_1 @ sk_B @ X21) = (X21))))
% 25.64/25.88         <= ((![X21 : $i]:
% 25.64/25.88                (~ (r2_hidden @ X21 @ sk_A)
% 25.64/25.88                 | ((k1_funct_1 @ sk_B @ X21) = (X21)))))),
% 25.64/25.88      inference('split', [status(esa)], ['4'])).
% 25.64/25.88  thf('22', plain,
% 25.64/25.88      (((((k6_relat_1 @ sk_A) = (sk_B))
% 25.64/25.88         | ((k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ (k6_relat_1 @ sk_A)))
% 25.64/25.88             = (sk_C_1 @ sk_B @ (k6_relat_1 @ sk_A)))))
% 25.64/25.88         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 25.64/25.88             (![X21 : $i]:
% 25.64/25.88                (~ (r2_hidden @ X21 @ sk_A)
% 25.64/25.88                 | ((k1_funct_1 @ sk_B @ X21) = (X21)))))),
% 25.64/25.88      inference('sup-', [status(thm)], ['20', '21'])).
% 25.64/25.88  thf('23', plain,
% 25.64/25.88      ((((k1_relat_1 @ sk_B) = (sk_A))) <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 25.64/25.88      inference('split', [status(esa)], ['2'])).
% 25.64/25.88  thf(t80_relat_1, axiom,
% 25.64/25.88    (![A:$i]:
% 25.64/25.88     ( ( v1_relat_1 @ A ) =>
% 25.64/25.88       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 25.64/25.88  thf('24', plain,
% 25.64/25.88      (![X3 : $i]:
% 25.64/25.88         (((k5_relat_1 @ X3 @ (k6_relat_1 @ (k2_relat_1 @ X3))) = (X3))
% 25.64/25.88          | ~ (v1_relat_1 @ X3))),
% 25.64/25.88      inference('cnf', [status(esa)], [t80_relat_1])).
% 25.64/25.88  thf('25', plain,
% 25.64/25.88      (![X1 : $i]:
% 25.64/25.88         (~ (v1_relat_1 @ X1)
% 25.64/25.88          | ~ (v1_funct_1 @ X1)
% 25.64/25.88          | ((k6_relat_1 @ (k1_relat_1 @ X1)) = (X1))
% 25.64/25.88          | (r2_hidden @ (sk_C_1 @ X1 @ (k6_relat_1 @ (k1_relat_1 @ X1))) @ 
% 25.64/25.88             (k1_relat_1 @ X1)))),
% 25.64/25.88      inference('simplify', [status(thm)], ['13'])).
% 25.64/25.88  thf(t23_funct_1, axiom,
% 25.64/25.88    (![A:$i,B:$i]:
% 25.64/25.88     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 25.64/25.88       ( ![C:$i]:
% 25.64/25.88         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 25.64/25.88           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 25.64/25.88             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 25.64/25.88               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 25.64/25.88  thf('26', plain,
% 25.64/25.88      (![X16 : $i, X17 : $i, X18 : $i]:
% 25.64/25.88         (~ (v1_relat_1 @ X16)
% 25.64/25.88          | ~ (v1_funct_1 @ X16)
% 25.64/25.88          | ((k1_funct_1 @ (k5_relat_1 @ X17 @ X16) @ X18)
% 25.64/25.88              = (k1_funct_1 @ X16 @ (k1_funct_1 @ X17 @ X18)))
% 25.64/25.88          | ~ (r2_hidden @ X18 @ (k1_relat_1 @ X17))
% 25.64/25.88          | ~ (v1_funct_1 @ X17)
% 25.64/25.88          | ~ (v1_relat_1 @ X17))),
% 25.64/25.88      inference('cnf', [status(esa)], [t23_funct_1])).
% 25.64/25.88  thf('27', plain,
% 25.64/25.88      (![X0 : $i, X1 : $i]:
% 25.64/25.88         (((k6_relat_1 @ (k1_relat_1 @ X0)) = (X0))
% 25.64/25.88          | ~ (v1_funct_1 @ X0)
% 25.64/25.88          | ~ (v1_relat_1 @ X0)
% 25.64/25.88          | ~ (v1_relat_1 @ X0)
% 25.64/25.88          | ~ (v1_funct_1 @ X0)
% 25.64/25.88          | ((k1_funct_1 @ (k5_relat_1 @ X0 @ X1) @ 
% 25.64/25.88              (sk_C_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ X0))))
% 25.64/25.88              = (k1_funct_1 @ X1 @ 
% 25.64/25.88                 (k1_funct_1 @ X0 @ 
% 25.64/25.88                  (sk_C_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ X0))))))
% 25.64/25.88          | ~ (v1_funct_1 @ X1)
% 25.64/25.88          | ~ (v1_relat_1 @ X1))),
% 25.64/25.88      inference('sup-', [status(thm)], ['25', '26'])).
% 25.64/25.88  thf('28', plain,
% 25.64/25.88      (![X0 : $i, X1 : $i]:
% 25.64/25.88         (~ (v1_relat_1 @ X1)
% 25.64/25.88          | ~ (v1_funct_1 @ X1)
% 25.64/25.88          | ((k1_funct_1 @ (k5_relat_1 @ X0 @ X1) @ 
% 25.64/25.88              (sk_C_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ X0))))
% 25.64/25.88              = (k1_funct_1 @ X1 @ 
% 25.64/25.88                 (k1_funct_1 @ X0 @ 
% 25.64/25.88                  (sk_C_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ X0))))))
% 25.64/25.88          | ~ (v1_relat_1 @ X0)
% 25.64/25.88          | ~ (v1_funct_1 @ X0)
% 25.64/25.88          | ((k6_relat_1 @ (k1_relat_1 @ X0)) = (X0)))),
% 25.64/25.88      inference('simplify', [status(thm)], ['27'])).
% 25.64/25.88  thf('29', plain,
% 25.64/25.88      (![X0 : $i]:
% 25.64/25.88         (((k1_funct_1 @ X0 @ (sk_C_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ X0))))
% 25.64/25.88            = (k1_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ 
% 25.64/25.88               (k1_funct_1 @ X0 @ 
% 25.64/25.88                (sk_C_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ X0))))))
% 25.64/25.88          | ~ (v1_relat_1 @ X0)
% 25.64/25.88          | ((k6_relat_1 @ (k1_relat_1 @ X0)) = (X0))
% 25.64/25.88          | ~ (v1_funct_1 @ X0)
% 25.64/25.88          | ~ (v1_relat_1 @ X0)
% 25.64/25.88          | ~ (v1_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 25.64/25.88          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))),
% 25.64/25.88      inference('sup+', [status(thm)], ['24', '28'])).
% 25.64/25.88  thf('30', plain, (![X12 : $i]: (v1_funct_1 @ (k6_relat_1 @ X12))),
% 25.64/25.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 25.64/25.88  thf('31', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 25.64/25.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 25.64/25.88  thf('32', plain,
% 25.64/25.88      (![X0 : $i]:
% 25.64/25.88         (((k1_funct_1 @ X0 @ (sk_C_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ X0))))
% 25.64/25.88            = (k1_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ 
% 25.64/25.88               (k1_funct_1 @ X0 @ 
% 25.64/25.88                (sk_C_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ X0))))))
% 25.64/25.88          | ~ (v1_relat_1 @ X0)
% 25.64/25.88          | ((k6_relat_1 @ (k1_relat_1 @ X0)) = (X0))
% 25.64/25.88          | ~ (v1_funct_1 @ X0)
% 25.64/25.88          | ~ (v1_relat_1 @ X0))),
% 25.64/25.88      inference('demod', [status(thm)], ['29', '30', '31'])).
% 25.64/25.88  thf('33', plain,
% 25.64/25.88      (![X0 : $i]:
% 25.64/25.88         (~ (v1_funct_1 @ X0)
% 25.64/25.88          | ((k6_relat_1 @ (k1_relat_1 @ X0)) = (X0))
% 25.64/25.88          | ~ (v1_relat_1 @ X0)
% 25.64/25.88          | ((k1_funct_1 @ X0 @ 
% 25.64/25.88              (sk_C_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ X0))))
% 25.64/25.88              = (k1_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ 
% 25.64/25.88                 (k1_funct_1 @ X0 @ 
% 25.64/25.88                  (sk_C_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ X0)))))))),
% 25.64/25.88      inference('simplify', [status(thm)], ['32'])).
% 25.64/25.88  thf('34', plain,
% 25.64/25.88      (((((k1_funct_1 @ sk_B @ 
% 25.64/25.88           (sk_C_1 @ sk_B @ (k6_relat_1 @ (k1_relat_1 @ sk_B))))
% 25.64/25.88           = (k1_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 25.64/25.88              (k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ (k6_relat_1 @ sk_A)))))
% 25.64/25.88         | ~ (v1_relat_1 @ sk_B)
% 25.64/25.88         | ((k6_relat_1 @ (k1_relat_1 @ sk_B)) = (sk_B))
% 25.64/25.88         | ~ (v1_funct_1 @ sk_B))) <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 25.64/25.88      inference('sup+', [status(thm)], ['23', '33'])).
% 25.64/25.88  thf('35', plain,
% 25.64/25.88      ((((k1_relat_1 @ sk_B) = (sk_A))) <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 25.64/25.88      inference('split', [status(esa)], ['2'])).
% 25.64/25.88  thf('36', plain, ((v1_relat_1 @ sk_B)),
% 25.64/25.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.64/25.88  thf('37', plain,
% 25.64/25.88      ((((k1_relat_1 @ sk_B) = (sk_A))) <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 25.64/25.88      inference('split', [status(esa)], ['2'])).
% 25.64/25.88  thf('38', plain, ((v1_funct_1 @ sk_B)),
% 25.64/25.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.64/25.88  thf('39', plain,
% 25.64/25.88      (((((k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ (k6_relat_1 @ sk_A)))
% 25.64/25.88           = (k1_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 25.64/25.88              (k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ (k6_relat_1 @ sk_A)))))
% 25.64/25.88         | ((k6_relat_1 @ sk_A) = (sk_B))))
% 25.64/25.88         <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 25.64/25.88      inference('demod', [status(thm)], ['34', '35', '36', '37', '38'])).
% 25.64/25.88  thf('40', plain,
% 25.64/25.88      (((((k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ (k6_relat_1 @ sk_A)))
% 25.64/25.88           = (k1_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 25.64/25.88              (sk_C_1 @ sk_B @ (k6_relat_1 @ sk_A))))
% 25.64/25.88         | ((k6_relat_1 @ sk_A) = (sk_B))
% 25.64/25.88         | ((k6_relat_1 @ sk_A) = (sk_B))))
% 25.64/25.88         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 25.64/25.88             (![X21 : $i]:
% 25.64/25.88                (~ (r2_hidden @ X21 @ sk_A)
% 25.64/25.88                 | ((k1_funct_1 @ sk_B @ X21) = (X21)))))),
% 25.64/25.88      inference('sup+', [status(thm)], ['22', '39'])).
% 25.64/25.88  thf('41', plain,
% 25.64/25.88      (((((k6_relat_1 @ sk_A) = (sk_B))
% 25.64/25.88         | ((k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ (k6_relat_1 @ sk_A)))
% 25.64/25.88             = (k1_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 25.64/25.88                (sk_C_1 @ sk_B @ (k6_relat_1 @ sk_A))))))
% 25.64/25.88         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 25.64/25.88             (![X21 : $i]:
% 25.64/25.88                (~ (r2_hidden @ X21 @ sk_A)
% 25.64/25.88                 | ((k1_funct_1 @ sk_B @ X21) = (X21)))))),
% 25.64/25.88      inference('simplify', [status(thm)], ['40'])).
% 25.64/25.88  thf(d5_funct_1, axiom,
% 25.64/25.88    (![A:$i]:
% 25.64/25.88     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 25.64/25.88       ( ![B:$i]:
% 25.64/25.88         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 25.64/25.88           ( ![C:$i]:
% 25.64/25.88             ( ( r2_hidden @ C @ B ) <=>
% 25.64/25.88               ( ?[D:$i]:
% 25.64/25.88                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 25.64/25.88                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 25.64/25.88  thf('42', plain,
% 25.64/25.88      (![X4 : $i, X5 : $i]:
% 25.64/25.88         ((r2_hidden @ (sk_C @ X4 @ X5) @ X4)
% 25.64/25.88          | ((sk_C @ X4 @ X5) = (k1_funct_1 @ X5 @ (sk_D @ X4 @ X5)))
% 25.64/25.88          | ((X4) = (k2_relat_1 @ X5))
% 25.64/25.88          | ~ (v1_funct_1 @ X5)
% 25.64/25.88          | ~ (v1_relat_1 @ X5))),
% 25.64/25.88      inference('cnf', [status(esa)], [d5_funct_1])).
% 25.64/25.88  thf('43', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 25.64/25.88      inference('cnf', [status(esa)], [t71_relat_1])).
% 25.64/25.88  thf('44', plain,
% 25.64/25.88      (![X4 : $i, X5 : $i]:
% 25.64/25.88         ((r2_hidden @ (sk_C @ X4 @ X5) @ X4)
% 25.64/25.88          | (r2_hidden @ (sk_D @ X4 @ X5) @ (k1_relat_1 @ X5))
% 25.64/25.88          | ((X4) = (k2_relat_1 @ X5))
% 25.64/25.88          | ~ (v1_funct_1 @ X5)
% 25.64/25.88          | ~ (v1_relat_1 @ X5))),
% 25.64/25.88      inference('cnf', [status(esa)], [d5_funct_1])).
% 25.64/25.88  thf('45', plain,
% 25.64/25.88      (![X0 : $i, X1 : $i]:
% 25.64/25.88         ((r2_hidden @ (sk_D @ X1 @ (k6_relat_1 @ X0)) @ X0)
% 25.64/25.88          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 25.64/25.88          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 25.64/25.88          | ((X1) = (k2_relat_1 @ (k6_relat_1 @ X0)))
% 25.64/25.88          | (r2_hidden @ (sk_C @ X1 @ (k6_relat_1 @ X0)) @ X1))),
% 25.64/25.88      inference('sup+', [status(thm)], ['43', '44'])).
% 25.64/25.88  thf('46', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 25.64/25.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 25.64/25.88  thf('47', plain, (![X12 : $i]: (v1_funct_1 @ (k6_relat_1 @ X12))),
% 25.64/25.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 25.64/25.88  thf('48', plain, (![X1 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X1)) = (X1))),
% 25.64/25.88      inference('cnf', [status(esa)], [t71_relat_1])).
% 25.64/25.88  thf('49', plain,
% 25.64/25.88      (![X0 : $i, X1 : $i]:
% 25.64/25.88         ((r2_hidden @ (sk_D @ X1 @ (k6_relat_1 @ X0)) @ X0)
% 25.64/25.88          | ((X1) = (X0))
% 25.64/25.88          | (r2_hidden @ (sk_C @ X1 @ (k6_relat_1 @ X0)) @ X1))),
% 25.64/25.88      inference('demod', [status(thm)], ['45', '46', '47', '48'])).
% 25.64/25.88  thf('50', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 25.64/25.88      inference('cnf', [status(esa)], [t71_relat_1])).
% 25.64/25.88  thf(t78_relat_1, axiom,
% 25.64/25.88    (![A:$i]:
% 25.64/25.88     ( ( v1_relat_1 @ A ) =>
% 25.64/25.88       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 25.64/25.88  thf('51', plain,
% 25.64/25.88      (![X2 : $i]:
% 25.64/25.88         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X2)) @ X2) = (X2))
% 25.64/25.88          | ~ (v1_relat_1 @ X2))),
% 25.64/25.88      inference('cnf', [status(esa)], [t78_relat_1])).
% 25.64/25.88  thf('52', plain,
% 25.64/25.88      (![X0 : $i]:
% 25.64/25.88         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 25.64/25.88            = (k6_relat_1 @ X0))
% 25.64/25.88          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 25.64/25.88      inference('sup+', [status(thm)], ['50', '51'])).
% 25.64/25.88  thf('53', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 25.64/25.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 25.64/25.88  thf('54', plain,
% 25.64/25.88      (![X0 : $i]:
% 25.64/25.88         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 25.64/25.88           = (k6_relat_1 @ X0))),
% 25.64/25.88      inference('demod', [status(thm)], ['52', '53'])).
% 25.64/25.88  thf(t21_funct_1, axiom,
% 25.64/25.88    (![A:$i,B:$i]:
% 25.64/25.88     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 25.64/25.88       ( ![C:$i]:
% 25.64/25.88         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 25.64/25.88           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) <=>
% 25.64/25.88             ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 25.64/25.88               ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 25.64/25.88  thf('55', plain,
% 25.64/25.88      (![X13 : $i, X14 : $i, X15 : $i]:
% 25.64/25.88         (~ (v1_relat_1 @ X13)
% 25.64/25.88          | ~ (v1_funct_1 @ X13)
% 25.64/25.88          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ (k5_relat_1 @ X13 @ X15)))
% 25.64/25.88          | (r2_hidden @ (k1_funct_1 @ X13 @ X14) @ (k1_relat_1 @ X15))
% 25.64/25.88          | ~ (v1_funct_1 @ X15)
% 25.64/25.88          | ~ (v1_relat_1 @ X15))),
% 25.64/25.88      inference('cnf', [status(esa)], [t21_funct_1])).
% 25.64/25.88  thf('56', plain,
% 25.64/25.88      (![X0 : $i, X1 : $i]:
% 25.64/25.88         (~ (r2_hidden @ X1 @ (k1_relat_1 @ (k6_relat_1 @ X0)))
% 25.64/25.88          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 25.64/25.88          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 25.64/25.88          | (r2_hidden @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 25.64/25.88             (k1_relat_1 @ (k6_relat_1 @ X0)))
% 25.64/25.88          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 25.64/25.88          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 25.64/25.88      inference('sup-', [status(thm)], ['54', '55'])).
% 25.64/25.88  thf('57', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 25.64/25.88      inference('cnf', [status(esa)], [t71_relat_1])).
% 25.64/25.88  thf('58', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 25.64/25.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 25.64/25.88  thf('59', plain, (![X12 : $i]: (v1_funct_1 @ (k6_relat_1 @ X12))),
% 25.64/25.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 25.64/25.88  thf('60', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 25.64/25.88      inference('cnf', [status(esa)], [t71_relat_1])).
% 25.64/25.88  thf('61', plain, (![X12 : $i]: (v1_funct_1 @ (k6_relat_1 @ X12))),
% 25.64/25.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 25.64/25.88  thf('62', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 25.64/25.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 25.64/25.88  thf('63', plain,
% 25.64/25.88      (![X0 : $i, X1 : $i]:
% 25.64/25.88         (~ (r2_hidden @ X1 @ X0)
% 25.64/25.88          | (r2_hidden @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X1) @ X0))),
% 25.64/25.88      inference('demod', [status(thm)],
% 25.64/25.88                ['56', '57', '58', '59', '60', '61', '62'])).
% 25.64/25.88  thf('64', plain,
% 25.64/25.88      (![X0 : $i, X1 : $i]:
% 25.64/25.88         ((r2_hidden @ (sk_C @ X1 @ (k6_relat_1 @ X0)) @ X1)
% 25.64/25.88          | ((X1) = (X0))
% 25.64/25.88          | (r2_hidden @ 
% 25.64/25.88             (k1_funct_1 @ (k6_relat_1 @ X0) @ (sk_D @ X1 @ (k6_relat_1 @ X0))) @ 
% 25.64/25.88             X0))),
% 25.64/25.88      inference('sup-', [status(thm)], ['49', '63'])).
% 25.64/25.88  thf('65', plain,
% 25.64/25.88      (![X0 : $i, X1 : $i]:
% 25.64/25.88         ((r2_hidden @ (sk_C @ X1 @ (k6_relat_1 @ X0)) @ X0)
% 25.64/25.88          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 25.64/25.88          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 25.64/25.88          | ((X1) = (k2_relat_1 @ (k6_relat_1 @ X0)))
% 25.64/25.88          | (r2_hidden @ (sk_C @ X1 @ (k6_relat_1 @ X0)) @ X1)
% 25.64/25.88          | ((X1) = (X0))
% 25.64/25.88          | (r2_hidden @ (sk_C @ X1 @ (k6_relat_1 @ X0)) @ X1))),
% 25.64/25.88      inference('sup+', [status(thm)], ['42', '64'])).
% 25.64/25.88  thf('66', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 25.64/25.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 25.64/25.88  thf('67', plain, (![X12 : $i]: (v1_funct_1 @ (k6_relat_1 @ X12))),
% 25.64/25.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 25.64/25.88  thf('68', plain, (![X1 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X1)) = (X1))),
% 25.64/25.88      inference('cnf', [status(esa)], [t71_relat_1])).
% 25.64/25.88  thf('69', plain,
% 25.64/25.88      (![X0 : $i, X1 : $i]:
% 25.64/25.88         ((r2_hidden @ (sk_C @ X1 @ (k6_relat_1 @ X0)) @ X0)
% 25.64/25.88          | ((X1) = (X0))
% 25.64/25.88          | (r2_hidden @ (sk_C @ X1 @ (k6_relat_1 @ X0)) @ X1)
% 25.64/25.88          | ((X1) = (X0))
% 25.64/25.88          | (r2_hidden @ (sk_C @ X1 @ (k6_relat_1 @ X0)) @ X1))),
% 25.64/25.88      inference('demod', [status(thm)], ['65', '66', '67', '68'])).
% 25.64/25.88  thf('70', plain,
% 25.64/25.88      (![X0 : $i, X1 : $i]:
% 25.64/25.88         ((r2_hidden @ (sk_C @ X1 @ (k6_relat_1 @ X0)) @ X1)
% 25.64/25.88          | ((X1) = (X0))
% 25.64/25.88          | (r2_hidden @ (sk_C @ X1 @ (k6_relat_1 @ X0)) @ X0))),
% 25.64/25.88      inference('simplify', [status(thm)], ['69'])).
% 25.64/25.88  thf('71', plain,
% 25.64/25.88      ((![X21 : $i]:
% 25.64/25.88          (~ (r2_hidden @ X21 @ sk_A) | ((k1_funct_1 @ sk_B @ X21) = (X21))))
% 25.64/25.88         <= ((![X21 : $i]:
% 25.64/25.88                (~ (r2_hidden @ X21 @ sk_A)
% 25.64/25.88                 | ((k1_funct_1 @ sk_B @ X21) = (X21)))))),
% 25.64/25.88      inference('split', [status(esa)], ['4'])).
% 25.64/25.88  thf('72', plain,
% 25.64/25.88      ((![X0 : $i]:
% 25.64/25.88          (((X0) = (sk_A))
% 25.64/25.88           | (r2_hidden @ (sk_C @ X0 @ (k6_relat_1 @ sk_A)) @ X0)
% 25.64/25.88           | ((k1_funct_1 @ sk_B @ (sk_C @ X0 @ (k6_relat_1 @ sk_A)))
% 25.64/25.88               = (sk_C @ X0 @ (k6_relat_1 @ sk_A)))))
% 25.64/25.88         <= ((![X21 : $i]:
% 25.64/25.88                (~ (r2_hidden @ X21 @ sk_A)
% 25.64/25.88                 | ((k1_funct_1 @ sk_B @ X21) = (X21)))))),
% 25.64/25.88      inference('sup-', [status(thm)], ['70', '71'])).
% 25.64/25.88  thf('73', plain,
% 25.64/25.88      (![X0 : $i, X1 : $i]:
% 25.64/25.88         ((r2_hidden @ (sk_C @ X1 @ (k6_relat_1 @ X0)) @ X1)
% 25.64/25.88          | ((X1) = (X0))
% 25.64/25.88          | (r2_hidden @ (sk_C @ X1 @ (k6_relat_1 @ X0)) @ X0))),
% 25.64/25.88      inference('simplify', [status(thm)], ['69'])).
% 25.64/25.88  thf('74', plain,
% 25.64/25.88      ((((k1_relat_1 @ sk_B) = (sk_A))) <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 25.64/25.88      inference('split', [status(esa)], ['2'])).
% 25.64/25.88  thf('75', plain,
% 25.64/25.88      (![X3 : $i]:
% 25.64/25.88         (((k5_relat_1 @ X3 @ (k6_relat_1 @ (k2_relat_1 @ X3))) = (X3))
% 25.64/25.88          | ~ (v1_relat_1 @ X3))),
% 25.64/25.88      inference('cnf', [status(esa)], [t80_relat_1])).
% 25.64/25.88  thf('76', plain,
% 25.64/25.88      (![X13 : $i, X14 : $i, X15 : $i]:
% 25.64/25.88         (~ (v1_relat_1 @ X13)
% 25.64/25.88          | ~ (v1_funct_1 @ X13)
% 25.64/25.88          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ (k5_relat_1 @ X13 @ X15)))
% 25.64/25.88          | (r2_hidden @ (k1_funct_1 @ X13 @ X14) @ (k1_relat_1 @ X15))
% 25.64/25.88          | ~ (v1_funct_1 @ X15)
% 25.64/25.88          | ~ (v1_relat_1 @ X15))),
% 25.64/25.88      inference('cnf', [status(esa)], [t21_funct_1])).
% 25.64/25.88  thf('77', plain,
% 25.64/25.88      (![X0 : $i, X1 : $i]:
% 25.64/25.88         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 25.64/25.88          | ~ (v1_relat_1 @ X0)
% 25.64/25.88          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 25.64/25.88          | ~ (v1_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 25.64/25.88          | (r2_hidden @ (k1_funct_1 @ X0 @ X1) @ 
% 25.64/25.88             (k1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))
% 25.64/25.88          | ~ (v1_funct_1 @ X0)
% 25.64/25.88          | ~ (v1_relat_1 @ X0))),
% 25.64/25.88      inference('sup-', [status(thm)], ['75', '76'])).
% 25.64/25.88  thf('78', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 25.64/25.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 25.64/25.88  thf('79', plain, (![X12 : $i]: (v1_funct_1 @ (k6_relat_1 @ X12))),
% 25.64/25.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 25.64/25.88  thf('80', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 25.64/25.88      inference('cnf', [status(esa)], [t71_relat_1])).
% 25.64/25.88  thf('81', plain,
% 25.64/25.88      (![X0 : $i, X1 : $i]:
% 25.64/25.88         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 25.64/25.88          | ~ (v1_relat_1 @ X0)
% 25.64/25.88          | (r2_hidden @ (k1_funct_1 @ X0 @ X1) @ (k2_relat_1 @ X0))
% 25.64/25.88          | ~ (v1_funct_1 @ X0)
% 25.64/25.88          | ~ (v1_relat_1 @ X0))),
% 25.64/25.88      inference('demod', [status(thm)], ['77', '78', '79', '80'])).
% 25.64/25.88  thf('82', plain,
% 25.64/25.88      (![X0 : $i, X1 : $i]:
% 25.64/25.88         (~ (v1_funct_1 @ X0)
% 25.64/25.88          | (r2_hidden @ (k1_funct_1 @ X0 @ X1) @ (k2_relat_1 @ X0))
% 25.64/25.88          | ~ (v1_relat_1 @ X0)
% 25.64/25.88          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 25.64/25.88      inference('simplify', [status(thm)], ['81'])).
% 25.64/25.88  thf('83', plain,
% 25.64/25.88      ((![X0 : $i]:
% 25.64/25.88          (~ (r2_hidden @ X0 @ sk_A)
% 25.64/25.88           | ~ (v1_relat_1 @ sk_B)
% 25.64/25.88           | (r2_hidden @ (k1_funct_1 @ sk_B @ X0) @ (k2_relat_1 @ sk_B))
% 25.64/25.88           | ~ (v1_funct_1 @ sk_B)))
% 25.64/25.88         <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 25.64/25.88      inference('sup-', [status(thm)], ['74', '82'])).
% 25.64/25.88  thf('84', plain, ((v1_relat_1 @ sk_B)),
% 25.64/25.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.64/25.88  thf('85', plain, ((v1_funct_1 @ sk_B)),
% 25.64/25.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.64/25.88  thf('86', plain,
% 25.64/25.88      ((![X0 : $i]:
% 25.64/25.88          (~ (r2_hidden @ X0 @ sk_A)
% 25.64/25.88           | (r2_hidden @ (k1_funct_1 @ sk_B @ X0) @ (k2_relat_1 @ sk_B))))
% 25.64/25.88         <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 25.64/25.88      inference('demod', [status(thm)], ['83', '84', '85'])).
% 25.64/25.88  thf('87', plain,
% 25.64/25.88      ((![X0 : $i]:
% 25.64/25.88          (((X0) = (sk_A))
% 25.64/25.88           | (r2_hidden @ (sk_C @ X0 @ (k6_relat_1 @ sk_A)) @ X0)
% 25.64/25.88           | (r2_hidden @ 
% 25.64/25.88              (k1_funct_1 @ sk_B @ (sk_C @ X0 @ (k6_relat_1 @ sk_A))) @ 
% 25.64/25.88              (k2_relat_1 @ sk_B))))
% 25.64/25.88         <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 25.64/25.88      inference('sup-', [status(thm)], ['73', '86'])).
% 25.64/25.88  thf('88', plain,
% 25.64/25.88      ((![X0 : $i]:
% 25.64/25.88          ((r2_hidden @ (sk_C @ X0 @ (k6_relat_1 @ sk_A)) @ (k2_relat_1 @ sk_B))
% 25.64/25.88           | (r2_hidden @ (sk_C @ X0 @ (k6_relat_1 @ sk_A)) @ X0)
% 25.64/25.88           | ((X0) = (sk_A))
% 25.64/25.88           | (r2_hidden @ (sk_C @ X0 @ (k6_relat_1 @ sk_A)) @ X0)
% 25.64/25.88           | ((X0) = (sk_A))))
% 25.64/25.88         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 25.64/25.88             (![X21 : $i]:
% 25.64/25.88                (~ (r2_hidden @ X21 @ sk_A)
% 25.64/25.88                 | ((k1_funct_1 @ sk_B @ X21) = (X21)))))),
% 25.64/25.88      inference('sup+', [status(thm)], ['72', '87'])).
% 25.64/25.88  thf('89', plain,
% 25.64/25.88      ((![X0 : $i]:
% 25.64/25.88          (((X0) = (sk_A))
% 25.64/25.88           | (r2_hidden @ (sk_C @ X0 @ (k6_relat_1 @ sk_A)) @ X0)
% 25.64/25.88           | (r2_hidden @ (sk_C @ X0 @ (k6_relat_1 @ sk_A)) @ 
% 25.64/25.88              (k2_relat_1 @ sk_B))))
% 25.64/25.88         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 25.64/25.88             (![X21 : $i]:
% 25.64/25.88                (~ (r2_hidden @ X21 @ sk_A)
% 25.64/25.88                 | ((k1_funct_1 @ sk_B @ X21) = (X21)))))),
% 25.64/25.88      inference('simplify', [status(thm)], ['88'])).
% 25.64/25.88  thf('90', plain,
% 25.64/25.88      ((((r2_hidden @ (sk_C @ (k2_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A)) @ 
% 25.64/25.88          (k2_relat_1 @ sk_B))
% 25.64/25.88         | ((k2_relat_1 @ sk_B) = (sk_A))))
% 25.64/25.88         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 25.64/25.88             (![X21 : $i]:
% 25.64/25.88                (~ (r2_hidden @ X21 @ sk_A)
% 25.64/25.88                 | ((k1_funct_1 @ sk_B @ X21) = (X21)))))),
% 25.64/25.88      inference('eq_fact', [status(thm)], ['89'])).
% 25.64/25.88  thf('91', plain,
% 25.64/25.88      (![X5 : $i, X7 : $i, X8 : $i]:
% 25.64/25.88         (((X7) != (k2_relat_1 @ X5))
% 25.64/25.88          | ((X8) = (k1_funct_1 @ X5 @ (sk_D_1 @ X8 @ X5)))
% 25.64/25.88          | ~ (r2_hidden @ X8 @ X7)
% 25.64/25.88          | ~ (v1_funct_1 @ X5)
% 25.64/25.88          | ~ (v1_relat_1 @ X5))),
% 25.64/25.88      inference('cnf', [status(esa)], [d5_funct_1])).
% 25.64/25.88  thf('92', plain,
% 25.64/25.88      (![X5 : $i, X8 : $i]:
% 25.64/25.88         (~ (v1_relat_1 @ X5)
% 25.64/25.88          | ~ (v1_funct_1 @ X5)
% 25.64/25.88          | ~ (r2_hidden @ X8 @ (k2_relat_1 @ X5))
% 25.64/25.88          | ((X8) = (k1_funct_1 @ X5 @ (sk_D_1 @ X8 @ X5))))),
% 25.64/25.88      inference('simplify', [status(thm)], ['91'])).
% 25.64/25.88  thf('93', plain,
% 25.64/25.88      (((((k2_relat_1 @ sk_B) = (sk_A))
% 25.64/25.88         | ((sk_C @ (k2_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 25.64/25.88             = (k1_funct_1 @ sk_B @ 
% 25.64/25.88                (sk_D_1 @ (sk_C @ (k2_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A)) @ 
% 25.64/25.88                 sk_B)))
% 25.64/25.88         | ~ (v1_funct_1 @ sk_B)
% 25.64/25.88         | ~ (v1_relat_1 @ sk_B)))
% 25.64/25.88         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 25.64/25.88             (![X21 : $i]:
% 25.64/25.88                (~ (r2_hidden @ X21 @ sk_A)
% 25.64/25.88                 | ((k1_funct_1 @ sk_B @ X21) = (X21)))))),
% 25.64/25.88      inference('sup-', [status(thm)], ['90', '92'])).
% 25.64/25.88  thf('94', plain, ((v1_funct_1 @ sk_B)),
% 25.64/25.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.64/25.88  thf('95', plain, ((v1_relat_1 @ sk_B)),
% 25.64/25.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.64/25.88  thf('96', plain,
% 25.64/25.88      (((((k2_relat_1 @ sk_B) = (sk_A))
% 25.64/25.88         | ((sk_C @ (k2_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 25.64/25.88             = (k1_funct_1 @ sk_B @ 
% 25.64/25.88                (sk_D_1 @ (sk_C @ (k2_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A)) @ 
% 25.64/25.88                 sk_B)))))
% 25.64/25.88         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 25.64/25.88             (![X21 : $i]:
% 25.64/25.88                (~ (r2_hidden @ X21 @ sk_A)
% 25.64/25.88                 | ((k1_funct_1 @ sk_B @ X21) = (X21)))))),
% 25.64/25.88      inference('demod', [status(thm)], ['93', '94', '95'])).
% 25.64/25.88  thf('97', plain,
% 25.64/25.88      ((((r2_hidden @ (sk_C @ (k2_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A)) @ 
% 25.64/25.88          (k2_relat_1 @ sk_B))
% 25.64/25.88         | ((k2_relat_1 @ sk_B) = (sk_A))))
% 25.64/25.88         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 25.64/25.88             (![X21 : $i]:
% 25.64/25.88                (~ (r2_hidden @ X21 @ sk_A)
% 25.64/25.88                 | ((k1_funct_1 @ sk_B @ X21) = (X21)))))),
% 25.64/25.88      inference('eq_fact', [status(thm)], ['89'])).
% 25.64/25.88  thf('98', plain,
% 25.64/25.88      (![X5 : $i, X7 : $i, X8 : $i]:
% 25.64/25.88         (((X7) != (k2_relat_1 @ X5))
% 25.64/25.88          | (r2_hidden @ (sk_D_1 @ X8 @ X5) @ (k1_relat_1 @ X5))
% 25.64/25.88          | ~ (r2_hidden @ X8 @ X7)
% 25.64/25.88          | ~ (v1_funct_1 @ X5)
% 25.64/25.88          | ~ (v1_relat_1 @ X5))),
% 25.64/25.88      inference('cnf', [status(esa)], [d5_funct_1])).
% 25.64/25.88  thf('99', plain,
% 25.64/25.88      (![X5 : $i, X8 : $i]:
% 25.64/25.88         (~ (v1_relat_1 @ X5)
% 25.64/25.88          | ~ (v1_funct_1 @ X5)
% 25.64/25.88          | ~ (r2_hidden @ X8 @ (k2_relat_1 @ X5))
% 25.64/25.88          | (r2_hidden @ (sk_D_1 @ X8 @ X5) @ (k1_relat_1 @ X5)))),
% 25.64/25.88      inference('simplify', [status(thm)], ['98'])).
% 25.64/25.88  thf('100', plain,
% 25.64/25.88      (((((k2_relat_1 @ sk_B) = (sk_A))
% 25.64/25.88         | (r2_hidden @ 
% 25.64/25.88            (sk_D_1 @ (sk_C @ (k2_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A)) @ sk_B) @ 
% 25.64/25.88            (k1_relat_1 @ sk_B))
% 25.64/25.88         | ~ (v1_funct_1 @ sk_B)
% 25.64/25.88         | ~ (v1_relat_1 @ sk_B)))
% 25.64/25.88         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 25.64/25.88             (![X21 : $i]:
% 25.64/25.88                (~ (r2_hidden @ X21 @ sk_A)
% 25.64/25.88                 | ((k1_funct_1 @ sk_B @ X21) = (X21)))))),
% 25.64/25.88      inference('sup-', [status(thm)], ['97', '99'])).
% 25.64/25.88  thf('101', plain,
% 25.64/25.88      ((((k1_relat_1 @ sk_B) = (sk_A))) <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 25.64/25.88      inference('split', [status(esa)], ['2'])).
% 25.64/25.88  thf('102', plain, ((v1_funct_1 @ sk_B)),
% 25.64/25.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.64/25.88  thf('103', plain, ((v1_relat_1 @ sk_B)),
% 25.64/25.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.64/25.88  thf('104', plain,
% 25.64/25.88      (((((k2_relat_1 @ sk_B) = (sk_A))
% 25.64/25.88         | (r2_hidden @ 
% 25.64/25.88            (sk_D_1 @ (sk_C @ (k2_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A)) @ sk_B) @ 
% 25.64/25.88            sk_A)))
% 25.64/25.88         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 25.64/25.88             (![X21 : $i]:
% 25.64/25.88                (~ (r2_hidden @ X21 @ sk_A)
% 25.64/25.88                 | ((k1_funct_1 @ sk_B @ X21) = (X21)))))),
% 25.64/25.88      inference('demod', [status(thm)], ['100', '101', '102', '103'])).
% 25.64/25.88  thf('105', plain,
% 25.64/25.88      ((![X21 : $i]:
% 25.64/25.88          (~ (r2_hidden @ X21 @ sk_A) | ((k1_funct_1 @ sk_B @ X21) = (X21))))
% 25.64/25.88         <= ((![X21 : $i]:
% 25.64/25.88                (~ (r2_hidden @ X21 @ sk_A)
% 25.64/25.88                 | ((k1_funct_1 @ sk_B @ X21) = (X21)))))),
% 25.64/25.88      inference('split', [status(esa)], ['4'])).
% 25.64/25.88  thf('106', plain,
% 25.64/25.88      (((((k2_relat_1 @ sk_B) = (sk_A))
% 25.64/25.88         | ((k1_funct_1 @ sk_B @ 
% 25.64/25.88             (sk_D_1 @ (sk_C @ (k2_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A)) @ 
% 25.64/25.88              sk_B))
% 25.64/25.88             = (sk_D_1 @ (sk_C @ (k2_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A)) @ 
% 25.64/25.88                sk_B))))
% 25.64/25.88         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 25.64/25.88             (![X21 : $i]:
% 25.64/25.88                (~ (r2_hidden @ X21 @ sk_A)
% 25.64/25.88                 | ((k1_funct_1 @ sk_B @ X21) = (X21)))))),
% 25.64/25.88      inference('sup-', [status(thm)], ['104', '105'])).
% 25.64/25.88  thf('107', plain,
% 25.64/25.88      (((((sk_C @ (k2_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 25.64/25.88           = (sk_D_1 @ (sk_C @ (k2_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A)) @ 
% 25.64/25.88              sk_B))
% 25.64/25.88         | ((k2_relat_1 @ sk_B) = (sk_A))
% 25.64/25.88         | ((k2_relat_1 @ sk_B) = (sk_A))))
% 25.64/25.88         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 25.64/25.88             (![X21 : $i]:
% 25.64/25.88                (~ (r2_hidden @ X21 @ sk_A)
% 25.64/25.88                 | ((k1_funct_1 @ sk_B @ X21) = (X21)))))),
% 25.64/25.88      inference('sup+', [status(thm)], ['96', '106'])).
% 25.64/25.88  thf('108', plain,
% 25.64/25.88      (((((k2_relat_1 @ sk_B) = (sk_A))
% 25.64/25.88         | ((sk_C @ (k2_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 25.64/25.88             = (sk_D_1 @ (sk_C @ (k2_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A)) @ 
% 25.64/25.88                sk_B))))
% 25.64/25.88         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 25.64/25.88             (![X21 : $i]:
% 25.64/25.88                (~ (r2_hidden @ X21 @ sk_A)
% 25.64/25.88                 | ((k1_funct_1 @ sk_B @ X21) = (X21)))))),
% 25.64/25.88      inference('simplify', [status(thm)], ['107'])).
% 25.64/25.88  thf('109', plain,
% 25.64/25.88      (![X4 : $i, X5 : $i]:
% 25.64/25.88         ((r2_hidden @ (sk_C @ X4 @ X5) @ X4)
% 25.64/25.88          | ((sk_C @ X4 @ X5) = (k1_funct_1 @ X5 @ (sk_D @ X4 @ X5)))
% 25.64/25.88          | ((X4) = (k2_relat_1 @ X5))
% 25.64/25.88          | ~ (v1_funct_1 @ X5)
% 25.64/25.88          | ~ (v1_relat_1 @ X5))),
% 25.64/25.88      inference('cnf', [status(esa)], [d5_funct_1])).
% 25.64/25.88  thf('110', plain,
% 25.64/25.88      (![X4 : $i, X5 : $i]:
% 25.64/25.88         ((r2_hidden @ (sk_C @ X4 @ X5) @ X4)
% 25.64/25.88          | (r2_hidden @ (sk_D @ X4 @ X5) @ (k1_relat_1 @ X5))
% 25.64/25.88          | ((X4) = (k2_relat_1 @ X5))
% 25.64/25.88          | ~ (v1_funct_1 @ X5)
% 25.64/25.88          | ~ (v1_relat_1 @ X5))),
% 25.64/25.88      inference('cnf', [status(esa)], [d5_funct_1])).
% 25.64/25.88  thf('111', plain,
% 25.64/25.88      (![X0 : $i, X1 : $i]:
% 25.64/25.88         (~ (v1_funct_1 @ X0)
% 25.64/25.88          | (r2_hidden @ (k1_funct_1 @ X0 @ X1) @ (k2_relat_1 @ X0))
% 25.64/25.88          | ~ (v1_relat_1 @ X0)
% 25.64/25.88          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 25.64/25.88      inference('simplify', [status(thm)], ['81'])).
% 25.64/25.88  thf('112', plain,
% 25.64/25.88      (![X0 : $i, X1 : $i]:
% 25.64/25.88         (~ (v1_relat_1 @ X0)
% 25.64/25.88          | ~ (v1_funct_1 @ X0)
% 25.64/25.88          | ((X1) = (k2_relat_1 @ X0))
% 25.64/25.88          | (r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 25.64/25.88          | ~ (v1_relat_1 @ X0)
% 25.64/25.88          | (r2_hidden @ (k1_funct_1 @ X0 @ (sk_D @ X1 @ X0)) @ 
% 25.64/25.88             (k2_relat_1 @ X0))
% 25.64/25.88          | ~ (v1_funct_1 @ X0))),
% 25.64/25.88      inference('sup-', [status(thm)], ['110', '111'])).
% 25.64/25.88  thf('113', plain,
% 25.64/25.88      (![X0 : $i, X1 : $i]:
% 25.64/25.88         ((r2_hidden @ (k1_funct_1 @ X0 @ (sk_D @ X1 @ X0)) @ (k2_relat_1 @ X0))
% 25.64/25.88          | (r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 25.64/25.88          | ((X1) = (k2_relat_1 @ X0))
% 25.64/25.88          | ~ (v1_funct_1 @ X0)
% 25.64/25.88          | ~ (v1_relat_1 @ X0))),
% 25.64/25.88      inference('simplify', [status(thm)], ['112'])).
% 25.64/25.88  thf('114', plain,
% 25.64/25.88      (![X0 : $i, X1 : $i]:
% 25.64/25.88         ((r2_hidden @ (sk_C @ X1 @ X0) @ (k2_relat_1 @ X0))
% 25.64/25.88          | ~ (v1_relat_1 @ X0)
% 25.64/25.88          | ~ (v1_funct_1 @ X0)
% 25.64/25.88          | ((X1) = (k2_relat_1 @ X0))
% 25.64/25.88          | (r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 25.64/25.89          | ~ (v1_relat_1 @ X0)
% 25.64/25.89          | ~ (v1_funct_1 @ X0)
% 25.64/25.89          | ((X1) = (k2_relat_1 @ X0))
% 25.64/25.89          | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 25.64/25.89      inference('sup+', [status(thm)], ['109', '113'])).
% 25.64/25.89  thf('115', plain,
% 25.64/25.89      (![X0 : $i, X1 : $i]:
% 25.64/25.89         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 25.64/25.89          | ((X1) = (k2_relat_1 @ X0))
% 25.64/25.89          | ~ (v1_funct_1 @ X0)
% 25.64/25.89          | ~ (v1_relat_1 @ X0)
% 25.64/25.89          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 25.64/25.89      inference('simplify', [status(thm)], ['114'])).
% 25.64/25.89  thf('116', plain,
% 25.64/25.89      (![X5 : $i, X8 : $i]:
% 25.64/25.89         (~ (v1_relat_1 @ X5)
% 25.64/25.89          | ~ (v1_funct_1 @ X5)
% 25.64/25.89          | ~ (r2_hidden @ X8 @ (k2_relat_1 @ X5))
% 25.64/25.89          | (r2_hidden @ (sk_D_1 @ X8 @ X5) @ (k1_relat_1 @ X5)))),
% 25.64/25.89      inference('simplify', [status(thm)], ['98'])).
% 25.64/25.89  thf('117', plain,
% 25.64/25.89      (![X0 : $i, X1 : $i]:
% 25.64/25.89         ((r2_hidden @ (sk_C @ (k2_relat_1 @ X0) @ X1) @ (k2_relat_1 @ X1))
% 25.64/25.89          | ~ (v1_relat_1 @ X1)
% 25.64/25.89          | ~ (v1_funct_1 @ X1)
% 25.64/25.89          | ((k2_relat_1 @ X0) = (k2_relat_1 @ X1))
% 25.64/25.89          | (r2_hidden @ (sk_D_1 @ (sk_C @ (k2_relat_1 @ X0) @ X1) @ X0) @ 
% 25.64/25.89             (k1_relat_1 @ X0))
% 25.64/25.89          | ~ (v1_funct_1 @ X0)
% 25.64/25.89          | ~ (v1_relat_1 @ X0))),
% 25.64/25.89      inference('sup-', [status(thm)], ['115', '116'])).
% 25.64/25.89  thf('118', plain,
% 25.64/25.89      ((((r2_hidden @ (sk_C @ (k2_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A)) @ 
% 25.64/25.89          (k1_relat_1 @ sk_B))
% 25.64/25.89         | ((k2_relat_1 @ sk_B) = (sk_A))
% 25.64/25.89         | ~ (v1_relat_1 @ sk_B)
% 25.64/25.89         | ~ (v1_funct_1 @ sk_B)
% 25.64/25.89         | ((k2_relat_1 @ sk_B) = (k2_relat_1 @ (k6_relat_1 @ sk_A)))
% 25.64/25.89         | ~ (v1_funct_1 @ (k6_relat_1 @ sk_A))
% 25.64/25.89         | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 25.64/25.89         | (r2_hidden @ (sk_C @ (k2_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A)) @ 
% 25.64/25.89            (k2_relat_1 @ (k6_relat_1 @ sk_A)))))
% 25.64/25.89         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 25.64/25.89             (![X21 : $i]:
% 25.64/25.89                (~ (r2_hidden @ X21 @ sk_A)
% 25.64/25.89                 | ((k1_funct_1 @ sk_B @ X21) = (X21)))))),
% 25.64/25.89      inference('sup+', [status(thm)], ['108', '117'])).
% 25.64/25.89  thf('119', plain,
% 25.64/25.89      ((((k1_relat_1 @ sk_B) = (sk_A))) <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 25.64/25.89      inference('split', [status(esa)], ['2'])).
% 25.64/25.89  thf('120', plain, ((v1_relat_1 @ sk_B)),
% 25.64/25.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.64/25.89  thf('121', plain, ((v1_funct_1 @ sk_B)),
% 25.64/25.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.64/25.89  thf('122', plain, (![X1 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X1)) = (X1))),
% 25.64/25.89      inference('cnf', [status(esa)], [t71_relat_1])).
% 25.64/25.89  thf('123', plain, (![X12 : $i]: (v1_funct_1 @ (k6_relat_1 @ X12))),
% 25.64/25.89      inference('cnf', [status(esa)], [fc3_funct_1])).
% 25.64/25.89  thf('124', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 25.64/25.89      inference('cnf', [status(esa)], [fc3_funct_1])).
% 25.64/25.89  thf('125', plain, (![X1 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X1)) = (X1))),
% 25.64/25.89      inference('cnf', [status(esa)], [t71_relat_1])).
% 25.64/25.89  thf('126', plain,
% 25.64/25.89      ((((r2_hidden @ (sk_C @ (k2_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A)) @ sk_A)
% 25.64/25.89         | ((k2_relat_1 @ sk_B) = (sk_A))
% 25.64/25.89         | ((k2_relat_1 @ sk_B) = (sk_A))
% 25.64/25.89         | (r2_hidden @ (sk_C @ (k2_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A)) @ 
% 25.64/25.89            sk_A)))
% 25.64/25.89         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 25.64/25.89             (![X21 : $i]:
% 25.64/25.89                (~ (r2_hidden @ X21 @ sk_A)
% 25.64/25.89                 | ((k1_funct_1 @ sk_B @ X21) = (X21)))))),
% 25.64/25.89      inference('demod', [status(thm)],
% 25.64/25.89                ['118', '119', '120', '121', '122', '123', '124', '125'])).
% 25.64/25.89  thf('127', plain,
% 25.64/25.89      (((((k2_relat_1 @ sk_B) = (sk_A))
% 25.64/25.89         | (r2_hidden @ (sk_C @ (k2_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A)) @ 
% 25.64/25.89            sk_A)))
% 25.64/25.89         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 25.64/25.89             (![X21 : $i]:
% 25.64/25.89                (~ (r2_hidden @ X21 @ sk_A)
% 25.64/25.89                 | ((k1_funct_1 @ sk_B @ X21) = (X21)))))),
% 25.64/25.89      inference('simplify', [status(thm)], ['126'])).
% 25.64/25.89  thf('128', plain, (![X1 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X1)) = (X1))),
% 25.64/25.89      inference('cnf', [status(esa)], [t71_relat_1])).
% 25.64/25.89  thf('129', plain,
% 25.64/25.89      (![X5 : $i, X8 : $i]:
% 25.64/25.89         (~ (v1_relat_1 @ X5)
% 25.64/25.89          | ~ (v1_funct_1 @ X5)
% 25.64/25.89          | ~ (r2_hidden @ X8 @ (k2_relat_1 @ X5))
% 25.64/25.89          | ((X8) = (k1_funct_1 @ X5 @ (sk_D_1 @ X8 @ X5))))),
% 25.64/25.89      inference('simplify', [status(thm)], ['91'])).
% 25.64/25.89  thf('130', plain,
% 25.64/25.89      (![X0 : $i, X1 : $i]:
% 25.64/25.89         (~ (r2_hidden @ X1 @ X0)
% 25.64/25.89          | ((X1)
% 25.64/25.89              = (k1_funct_1 @ (k6_relat_1 @ X0) @ 
% 25.64/25.89                 (sk_D_1 @ X1 @ (k6_relat_1 @ X0))))
% 25.64/25.89          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 25.64/25.89          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 25.64/25.89      inference('sup-', [status(thm)], ['128', '129'])).
% 25.64/25.89  thf('131', plain, (![X12 : $i]: (v1_funct_1 @ (k6_relat_1 @ X12))),
% 25.64/25.89      inference('cnf', [status(esa)], [fc3_funct_1])).
% 25.64/25.89  thf('132', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 25.64/25.89      inference('cnf', [status(esa)], [fc3_funct_1])).
% 25.64/25.89  thf('133', plain,
% 25.64/25.89      (![X0 : $i, X1 : $i]:
% 25.64/25.89         (~ (r2_hidden @ X1 @ X0)
% 25.64/25.89          | ((X1)
% 25.64/25.89              = (k1_funct_1 @ (k6_relat_1 @ X0) @ 
% 25.64/25.89                 (sk_D_1 @ X1 @ (k6_relat_1 @ X0)))))),
% 25.64/25.89      inference('demod', [status(thm)], ['130', '131', '132'])).
% 25.64/25.89  thf('134', plain,
% 25.64/25.89      (((((k2_relat_1 @ sk_B) = (sk_A))
% 25.64/25.89         | ((sk_C @ (k2_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 25.64/25.89             = (k1_funct_1 @ (k6_relat_1 @ sk_A) @ 
% 25.64/25.89                (sk_D_1 @ (sk_C @ (k2_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A)) @ 
% 25.64/25.89                 (k6_relat_1 @ sk_A))))))
% 25.64/25.89         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 25.64/25.89             (![X21 : $i]:
% 25.64/25.89                (~ (r2_hidden @ X21 @ sk_A)
% 25.64/25.89                 | ((k1_funct_1 @ sk_B @ X21) = (X21)))))),
% 25.64/25.89      inference('sup-', [status(thm)], ['127', '133'])).
% 25.64/25.89  thf('135', plain,
% 25.64/25.89      ((((r2_hidden @ (sk_C @ (k2_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A)) @ 
% 25.64/25.89          (k2_relat_1 @ sk_B))
% 25.64/25.89         | ((k2_relat_1 @ sk_B) = (sk_A))))
% 25.64/25.89         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 25.64/25.89             (![X21 : $i]:
% 25.64/25.89                (~ (r2_hidden @ X21 @ sk_A)
% 25.64/25.89                 | ((k1_funct_1 @ sk_B @ X21) = (X21)))))),
% 25.64/25.89      inference('eq_fact', [status(thm)], ['89'])).
% 25.64/25.89  thf('136', plain,
% 25.64/25.89      (![X4 : $i, X5 : $i, X6 : $i]:
% 25.64/25.89         (~ (r2_hidden @ (sk_C @ X4 @ X5) @ X4)
% 25.64/25.89          | ((sk_C @ X4 @ X5) != (k1_funct_1 @ X5 @ X6))
% 25.64/25.89          | ~ (r2_hidden @ X6 @ (k1_relat_1 @ X5))
% 25.64/25.89          | ((X4) = (k2_relat_1 @ X5))
% 25.64/25.89          | ~ (v1_funct_1 @ X5)
% 25.64/25.89          | ~ (v1_relat_1 @ X5))),
% 25.64/25.89      inference('cnf', [status(esa)], [d5_funct_1])).
% 25.64/25.89  thf('137', plain,
% 25.64/25.89      ((![X0 : $i]:
% 25.64/25.89          (((k2_relat_1 @ sk_B) = (sk_A))
% 25.64/25.89           | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 25.64/25.89           | ~ (v1_funct_1 @ (k6_relat_1 @ sk_A))
% 25.64/25.89           | ((k2_relat_1 @ sk_B) = (k2_relat_1 @ (k6_relat_1 @ sk_A)))
% 25.64/25.89           | ~ (r2_hidden @ X0 @ (k1_relat_1 @ (k6_relat_1 @ sk_A)))
% 25.64/25.89           | ((sk_C @ (k2_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 25.64/25.89               != (k1_funct_1 @ (k6_relat_1 @ sk_A) @ X0))))
% 25.64/25.89         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 25.64/25.89             (![X21 : $i]:
% 25.64/25.89                (~ (r2_hidden @ X21 @ sk_A)
% 25.64/25.89                 | ((k1_funct_1 @ sk_B @ X21) = (X21)))))),
% 25.64/25.89      inference('sup-', [status(thm)], ['135', '136'])).
% 25.64/25.89  thf('138', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 25.64/25.89      inference('cnf', [status(esa)], [fc3_funct_1])).
% 25.64/25.89  thf('139', plain, (![X12 : $i]: (v1_funct_1 @ (k6_relat_1 @ X12))),
% 25.64/25.89      inference('cnf', [status(esa)], [fc3_funct_1])).
% 25.64/25.89  thf('140', plain, (![X1 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X1)) = (X1))),
% 25.64/25.89      inference('cnf', [status(esa)], [t71_relat_1])).
% 25.64/25.89  thf('141', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 25.64/25.89      inference('cnf', [status(esa)], [t71_relat_1])).
% 25.64/25.89  thf('142', plain,
% 25.64/25.89      ((![X0 : $i]:
% 25.64/25.89          (((k2_relat_1 @ sk_B) = (sk_A))
% 25.64/25.89           | ((k2_relat_1 @ sk_B) = (sk_A))
% 25.64/25.89           | ~ (r2_hidden @ X0 @ sk_A)
% 25.64/25.89           | ((sk_C @ (k2_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 25.64/25.89               != (k1_funct_1 @ (k6_relat_1 @ sk_A) @ X0))))
% 25.64/25.89         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 25.64/25.89             (![X21 : $i]:
% 25.64/25.89                (~ (r2_hidden @ X21 @ sk_A)
% 25.64/25.89                 | ((k1_funct_1 @ sk_B @ X21) = (X21)))))),
% 25.64/25.89      inference('demod', [status(thm)], ['137', '138', '139', '140', '141'])).
% 25.64/25.89  thf('143', plain,
% 25.64/25.89      ((![X0 : $i]:
% 25.64/25.89          (((sk_C @ (k2_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 25.64/25.89             != (k1_funct_1 @ (k6_relat_1 @ sk_A) @ X0))
% 25.64/25.89           | ~ (r2_hidden @ X0 @ sk_A)
% 25.64/25.89           | ((k2_relat_1 @ sk_B) = (sk_A))))
% 25.64/25.89         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 25.64/25.89             (![X21 : $i]:
% 25.64/25.89                (~ (r2_hidden @ X21 @ sk_A)
% 25.64/25.89                 | ((k1_funct_1 @ sk_B @ X21) = (X21)))))),
% 25.64/25.89      inference('simplify', [status(thm)], ['142'])).
% 25.64/25.89  thf('144', plain,
% 25.64/25.89      (((((sk_C @ (k2_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 25.64/25.89           != (sk_C @ (k2_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A)))
% 25.64/25.89         | ((k2_relat_1 @ sk_B) = (sk_A))
% 25.64/25.89         | ((k2_relat_1 @ sk_B) = (sk_A))
% 25.64/25.89         | ~ (r2_hidden @ 
% 25.64/25.89              (sk_D_1 @ (sk_C @ (k2_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A)) @ 
% 25.64/25.89               (k6_relat_1 @ sk_A)) @ 
% 25.64/25.89              sk_A)))
% 25.64/25.89         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 25.64/25.89             (![X21 : $i]:
% 25.64/25.89                (~ (r2_hidden @ X21 @ sk_A)
% 25.64/25.89                 | ((k1_funct_1 @ sk_B @ X21) = (X21)))))),
% 25.64/25.89      inference('sup-', [status(thm)], ['134', '143'])).
% 25.64/25.89  thf('145', plain,
% 25.64/25.89      (((~ (r2_hidden @ 
% 25.64/25.89            (sk_D_1 @ (sk_C @ (k2_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A)) @ 
% 25.64/25.89             (k6_relat_1 @ sk_A)) @ 
% 25.64/25.89            sk_A)
% 25.64/25.89         | ((k2_relat_1 @ sk_B) = (sk_A))))
% 25.64/25.89         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 25.64/25.89             (![X21 : $i]:
% 25.64/25.89                (~ (r2_hidden @ X21 @ sk_A)
% 25.64/25.89                 | ((k1_funct_1 @ sk_B @ X21) = (X21)))))),
% 25.64/25.89      inference('simplify', [status(thm)], ['144'])).
% 25.64/25.89  thf('146', plain,
% 25.64/25.89      (((((k2_relat_1 @ sk_B) = (sk_A))
% 25.64/25.89         | (r2_hidden @ (sk_C @ (k2_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A)) @ 
% 25.64/25.89            sk_A)))
% 25.64/25.89         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 25.64/25.89             (![X21 : $i]:
% 25.64/25.89                (~ (r2_hidden @ X21 @ sk_A)
% 25.64/25.89                 | ((k1_funct_1 @ sk_B @ X21) = (X21)))))),
% 25.64/25.89      inference('simplify', [status(thm)], ['126'])).
% 25.64/25.89  thf('147', plain, (![X1 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X1)) = (X1))),
% 25.64/25.89      inference('cnf', [status(esa)], [t71_relat_1])).
% 25.64/25.89  thf('148', plain,
% 25.64/25.89      (![X5 : $i, X8 : $i]:
% 25.64/25.89         (~ (v1_relat_1 @ X5)
% 25.64/25.89          | ~ (v1_funct_1 @ X5)
% 25.64/25.89          | ~ (r2_hidden @ X8 @ (k2_relat_1 @ X5))
% 25.64/25.89          | (r2_hidden @ (sk_D_1 @ X8 @ X5) @ (k1_relat_1 @ X5)))),
% 25.64/25.89      inference('simplify', [status(thm)], ['98'])).
% 25.64/25.89  thf('149', plain,
% 25.64/25.89      (![X0 : $i, X1 : $i]:
% 25.64/25.89         (~ (r2_hidden @ X1 @ X0)
% 25.64/25.89          | (r2_hidden @ (sk_D_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 25.64/25.89             (k1_relat_1 @ (k6_relat_1 @ X0)))
% 25.64/25.89          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 25.64/25.89          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 25.64/25.89      inference('sup-', [status(thm)], ['147', '148'])).
% 25.64/25.89  thf('150', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 25.64/25.89      inference('cnf', [status(esa)], [t71_relat_1])).
% 25.64/25.89  thf('151', plain, (![X12 : $i]: (v1_funct_1 @ (k6_relat_1 @ X12))),
% 25.64/25.89      inference('cnf', [status(esa)], [fc3_funct_1])).
% 25.64/25.89  thf('152', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 25.64/25.89      inference('cnf', [status(esa)], [fc3_funct_1])).
% 25.64/25.89  thf('153', plain,
% 25.64/25.89      (![X0 : $i, X1 : $i]:
% 25.64/25.89         (~ (r2_hidden @ X1 @ X0)
% 25.64/25.89          | (r2_hidden @ (sk_D_1 @ X1 @ (k6_relat_1 @ X0)) @ X0))),
% 25.64/25.89      inference('demod', [status(thm)], ['149', '150', '151', '152'])).
% 25.64/25.89  thf('154', plain,
% 25.64/25.89      (((((k2_relat_1 @ sk_B) = (sk_A))
% 25.64/25.89         | (r2_hidden @ 
% 25.64/25.89            (sk_D_1 @ (sk_C @ (k2_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A)) @ 
% 25.64/25.89             (k6_relat_1 @ sk_A)) @ 
% 25.64/25.89            sk_A)))
% 25.64/25.89         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 25.64/25.89             (![X21 : $i]:
% 25.64/25.89                (~ (r2_hidden @ X21 @ sk_A)
% 25.64/25.89                 | ((k1_funct_1 @ sk_B @ X21) = (X21)))))),
% 25.64/25.89      inference('sup-', [status(thm)], ['146', '153'])).
% 25.64/25.89  thf('155', plain,
% 25.64/25.89      ((((k2_relat_1 @ sk_B) = (sk_A)))
% 25.64/25.89         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 25.64/25.89             (![X21 : $i]:
% 25.64/25.89                (~ (r2_hidden @ X21 @ sk_A)
% 25.64/25.89                 | ((k1_funct_1 @ sk_B @ X21) = (X21)))))),
% 25.64/25.89      inference('clc', [status(thm)], ['145', '154'])).
% 25.64/25.89  thf('156', plain,
% 25.64/25.89      (((((k6_relat_1 @ sk_A) = (sk_B))
% 25.64/25.89         | ((k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ (k6_relat_1 @ sk_A)))
% 25.64/25.89             = (k1_funct_1 @ (k6_relat_1 @ sk_A) @ 
% 25.64/25.89                (sk_C_1 @ sk_B @ (k6_relat_1 @ sk_A))))))
% 25.64/25.89         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 25.64/25.89             (![X21 : $i]:
% 25.64/25.89                (~ (r2_hidden @ X21 @ sk_A)
% 25.64/25.89                 | ((k1_funct_1 @ sk_B @ X21) = (X21)))))),
% 25.64/25.89      inference('demod', [status(thm)], ['41', '155'])).
% 25.64/25.89  thf('157', plain,
% 25.64/25.89      ((((k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ (k6_relat_1 @ sk_A)))
% 25.64/25.89          = (k1_funct_1 @ (k6_relat_1 @ sk_A) @ 
% 25.64/25.89             (sk_C_1 @ sk_B @ (k6_relat_1 @ sk_A)))))
% 25.64/25.89         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 25.64/25.89             (![X21 : $i]:
% 25.64/25.89                (~ (r2_hidden @ X21 @ sk_A)
% 25.64/25.89                 | ((k1_funct_1 @ sk_B @ X21) = (X21)))))),
% 25.64/25.89      inference('condensation', [status(thm)], ['156'])).
% 25.64/25.89  thf('158', plain,
% 25.64/25.89      (![X19 : $i, X20 : $i]:
% 25.64/25.89         (~ (v1_relat_1 @ X19)
% 25.64/25.89          | ~ (v1_funct_1 @ X19)
% 25.64/25.89          | ((X20) = (X19))
% 25.64/25.89          | ((k1_funct_1 @ X20 @ (sk_C_1 @ X19 @ X20))
% 25.64/25.89              != (k1_funct_1 @ X19 @ (sk_C_1 @ X19 @ X20)))
% 25.64/25.89          | ((k1_relat_1 @ X20) != (k1_relat_1 @ X19))
% 25.64/25.89          | ~ (v1_funct_1 @ X20)
% 25.64/25.89          | ~ (v1_relat_1 @ X20))),
% 25.64/25.89      inference('cnf', [status(esa)], [t9_funct_1])).
% 25.64/25.89  thf('159', plain,
% 25.64/25.89      (((((k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ (k6_relat_1 @ sk_A)))
% 25.64/25.89           != (k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ (k6_relat_1 @ sk_A))))
% 25.64/25.89         | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 25.64/25.89         | ~ (v1_funct_1 @ (k6_relat_1 @ sk_A))
% 25.64/25.89         | ((k1_relat_1 @ (k6_relat_1 @ sk_A)) != (k1_relat_1 @ sk_B))
% 25.64/25.89         | ((k6_relat_1 @ sk_A) = (sk_B))
% 25.64/25.89         | ~ (v1_funct_1 @ sk_B)
% 25.64/25.89         | ~ (v1_relat_1 @ sk_B)))
% 25.64/25.89         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 25.64/25.89             (![X21 : $i]:
% 25.64/25.89                (~ (r2_hidden @ X21 @ sk_A)
% 25.64/25.89                 | ((k1_funct_1 @ sk_B @ X21) = (X21)))))),
% 25.64/25.89      inference('sup-', [status(thm)], ['157', '158'])).
% 25.64/25.89  thf('160', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 25.64/25.89      inference('cnf', [status(esa)], [fc3_funct_1])).
% 25.64/25.89  thf('161', plain, (![X12 : $i]: (v1_funct_1 @ (k6_relat_1 @ X12))),
% 25.64/25.89      inference('cnf', [status(esa)], [fc3_funct_1])).
% 25.64/25.89  thf('162', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 25.64/25.89      inference('cnf', [status(esa)], [t71_relat_1])).
% 25.64/25.89  thf('163', plain,
% 25.64/25.89      ((((k1_relat_1 @ sk_B) = (sk_A))) <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 25.64/25.89      inference('split', [status(esa)], ['2'])).
% 25.64/25.89  thf('164', plain, ((v1_funct_1 @ sk_B)),
% 25.64/25.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.64/25.89  thf('165', plain, ((v1_relat_1 @ sk_B)),
% 25.64/25.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.64/25.89  thf('166', plain,
% 25.64/25.89      (((((k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ (k6_relat_1 @ sk_A)))
% 25.64/25.89           != (k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ (k6_relat_1 @ sk_A))))
% 25.64/25.89         | ((sk_A) != (sk_A))
% 25.64/25.89         | ((k6_relat_1 @ sk_A) = (sk_B))))
% 25.64/25.89         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 25.64/25.89             (![X21 : $i]:
% 25.64/25.89                (~ (r2_hidden @ X21 @ sk_A)
% 25.64/25.89                 | ((k1_funct_1 @ sk_B @ X21) = (X21)))))),
% 25.64/25.89      inference('demod', [status(thm)],
% 25.64/25.89                ['159', '160', '161', '162', '163', '164', '165'])).
% 25.64/25.89  thf('167', plain,
% 25.64/25.89      ((((k6_relat_1 @ sk_A) = (sk_B)))
% 25.64/25.89         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 25.64/25.89             (![X21 : $i]:
% 25.64/25.89                (~ (r2_hidden @ X21 @ sk_A)
% 25.64/25.89                 | ((k1_funct_1 @ sk_B @ X21) = (X21)))))),
% 25.64/25.89      inference('simplify', [status(thm)], ['166'])).
% 25.64/25.89  thf('168', plain,
% 25.64/25.89      ((((k1_funct_1 @ sk_B @ sk_C_2) != (sk_C_2))
% 25.64/25.89        | ((k1_relat_1 @ sk_B) != (sk_A))
% 25.64/25.89        | ((sk_B) != (k6_relat_1 @ sk_A)))),
% 25.64/25.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.64/25.89  thf('169', plain,
% 25.64/25.89      ((((sk_B) != (k6_relat_1 @ sk_A)))
% 25.64/25.89         <= (~ (((sk_B) = (k6_relat_1 @ sk_A))))),
% 25.64/25.89      inference('split', [status(esa)], ['168'])).
% 25.64/25.89  thf('170', plain,
% 25.64/25.89      ((((sk_B) != (sk_B)))
% 25.64/25.89         <= (~ (((sk_B) = (k6_relat_1 @ sk_A))) & 
% 25.64/25.89             (((k1_relat_1 @ sk_B) = (sk_A))) & 
% 25.64/25.89             (![X21 : $i]:
% 25.64/25.89                (~ (r2_hidden @ X21 @ sk_A)
% 25.64/25.89                 | ((k1_funct_1 @ sk_B @ X21) = (X21)))))),
% 25.64/25.89      inference('sup-', [status(thm)], ['167', '169'])).
% 25.64/25.89  thf('171', plain,
% 25.64/25.89      (~
% 25.64/25.89       (![X21 : $i]:
% 25.64/25.89          (~ (r2_hidden @ X21 @ sk_A) | ((k1_funct_1 @ sk_B @ X21) = (X21)))) | 
% 25.64/25.89       (((sk_B) = (k6_relat_1 @ sk_A))) | ~ (((k1_relat_1 @ sk_B) = (sk_A)))),
% 25.64/25.89      inference('simplify', [status(thm)], ['170'])).
% 25.64/25.89  thf('172', plain,
% 25.64/25.89      ((((sk_B) = (k6_relat_1 @ sk_A))) <= ((((sk_B) = (k6_relat_1 @ sk_A))))),
% 25.64/25.89      inference('split', [status(esa)], ['2'])).
% 25.64/25.89  thf('173', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 25.64/25.89      inference('cnf', [status(esa)], [t71_relat_1])).
% 25.64/25.89  thf('174', plain,
% 25.64/25.89      ((((k1_relat_1 @ sk_B) = (sk_A))) <= ((((sk_B) = (k6_relat_1 @ sk_A))))),
% 25.64/25.89      inference('sup+', [status(thm)], ['172', '173'])).
% 25.64/25.89  thf('175', plain,
% 25.64/25.89      ((((k1_relat_1 @ sk_B) != (sk_A)))
% 25.64/25.89         <= (~ (((k1_relat_1 @ sk_B) = (sk_A))))),
% 25.64/25.89      inference('split', [status(esa)], ['168'])).
% 25.64/25.89  thf('176', plain,
% 25.64/25.89      ((((sk_A) != (sk_A)))
% 25.64/25.89         <= (~ (((k1_relat_1 @ sk_B) = (sk_A))) & 
% 25.64/25.89             (((sk_B) = (k6_relat_1 @ sk_A))))),
% 25.64/25.89      inference('sup-', [status(thm)], ['174', '175'])).
% 25.64/25.89  thf('177', plain,
% 25.64/25.89      ((((k1_relat_1 @ sk_B) = (sk_A))) | ~ (((sk_B) = (k6_relat_1 @ sk_A)))),
% 25.64/25.89      inference('simplify', [status(thm)], ['176'])).
% 25.64/25.89  thf('178', plain,
% 25.64/25.89      (~ (((k1_funct_1 @ sk_B @ sk_C_2) = (sk_C_2))) | 
% 25.64/25.89       ~ (((k1_relat_1 @ sk_B) = (sk_A))) | ~ (((sk_B) = (k6_relat_1 @ sk_A)))),
% 25.64/25.89      inference('split', [status(esa)], ['168'])).
% 25.64/25.89  thf('179', plain,
% 25.64/25.89      (![X3 : $i]:
% 25.64/25.89         (((k5_relat_1 @ X3 @ (k6_relat_1 @ (k2_relat_1 @ X3))) = (X3))
% 25.64/25.89          | ~ (v1_relat_1 @ X3))),
% 25.64/25.89      inference('cnf', [status(esa)], [t80_relat_1])).
% 25.64/25.89  thf('180', plain,
% 25.64/25.89      (((r2_hidden @ sk_C_2 @ sk_A)) <= (((r2_hidden @ sk_C_2 @ sk_A)))),
% 25.64/25.89      inference('split', [status(esa)], ['0'])).
% 25.64/25.89  thf('181', plain,
% 25.64/25.89      ((((sk_B) = (k6_relat_1 @ sk_A))) <= ((((sk_B) = (k6_relat_1 @ sk_A))))),
% 25.64/25.89      inference('split', [status(esa)], ['2'])).
% 25.64/25.89  thf('182', plain, (![X1 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X1)) = (X1))),
% 25.64/25.89      inference('cnf', [status(esa)], [t71_relat_1])).
% 25.64/25.89  thf('183', plain,
% 25.64/25.89      ((((k2_relat_1 @ sk_B) = (sk_A))) <= ((((sk_B) = (k6_relat_1 @ sk_A))))),
% 25.64/25.89      inference('sup+', [status(thm)], ['181', '182'])).
% 25.64/25.89  thf('184', plain,
% 25.64/25.89      (![X5 : $i, X8 : $i]:
% 25.64/25.89         (~ (v1_relat_1 @ X5)
% 25.64/25.89          | ~ (v1_funct_1 @ X5)
% 25.64/25.89          | ~ (r2_hidden @ X8 @ (k2_relat_1 @ X5))
% 25.64/25.89          | (r2_hidden @ (sk_D_1 @ X8 @ X5) @ (k1_relat_1 @ X5)))),
% 25.64/25.89      inference('simplify', [status(thm)], ['98'])).
% 25.64/25.89  thf('185', plain,
% 25.64/25.89      ((![X0 : $i]:
% 25.64/25.89          (~ (r2_hidden @ X0 @ sk_A)
% 25.64/25.89           | (r2_hidden @ (sk_D_1 @ X0 @ sk_B) @ (k1_relat_1 @ sk_B))
% 25.64/25.89           | ~ (v1_funct_1 @ sk_B)
% 25.64/25.89           | ~ (v1_relat_1 @ sk_B)))
% 25.64/25.89         <= ((((sk_B) = (k6_relat_1 @ sk_A))))),
% 25.64/25.89      inference('sup-', [status(thm)], ['183', '184'])).
% 25.64/25.89  thf('186', plain,
% 25.64/25.89      ((((k1_relat_1 @ sk_B) = (sk_A))) <= ((((sk_B) = (k6_relat_1 @ sk_A))))),
% 25.64/25.89      inference('sup+', [status(thm)], ['172', '173'])).
% 25.64/25.89  thf('187', plain, ((v1_funct_1 @ sk_B)),
% 25.64/25.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.64/25.89  thf('188', plain, ((v1_relat_1 @ sk_B)),
% 25.64/25.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.64/25.89  thf('189', plain,
% 25.64/25.89      ((![X0 : $i]:
% 25.64/25.89          (~ (r2_hidden @ X0 @ sk_A)
% 25.64/25.89           | (r2_hidden @ (sk_D_1 @ X0 @ sk_B) @ sk_A)))
% 25.64/25.89         <= ((((sk_B) = (k6_relat_1 @ sk_A))))),
% 25.64/25.89      inference('demod', [status(thm)], ['185', '186', '187', '188'])).
% 25.64/25.89  thf('190', plain,
% 25.64/25.89      (((r2_hidden @ (sk_D_1 @ sk_C_2 @ sk_B) @ sk_A))
% 25.64/25.89         <= ((((sk_B) = (k6_relat_1 @ sk_A))) & ((r2_hidden @ sk_C_2 @ sk_A)))),
% 25.64/25.89      inference('sup-', [status(thm)], ['180', '189'])).
% 25.64/25.89  thf('191', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 25.64/25.89      inference('cnf', [status(esa)], [t71_relat_1])).
% 25.64/25.89  thf('192', plain,
% 25.64/25.89      (![X16 : $i, X17 : $i, X18 : $i]:
% 25.64/25.89         (~ (v1_relat_1 @ X16)
% 25.64/25.89          | ~ (v1_funct_1 @ X16)
% 25.64/25.89          | ((k1_funct_1 @ (k5_relat_1 @ X17 @ X16) @ X18)
% 25.64/25.89              = (k1_funct_1 @ X16 @ (k1_funct_1 @ X17 @ X18)))
% 25.64/25.89          | ~ (r2_hidden @ X18 @ (k1_relat_1 @ X17))
% 25.64/25.89          | ~ (v1_funct_1 @ X17)
% 25.64/25.89          | ~ (v1_relat_1 @ X17))),
% 25.64/25.89      inference('cnf', [status(esa)], [t23_funct_1])).
% 25.64/25.89  thf('193', plain,
% 25.64/25.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.64/25.89         (~ (r2_hidden @ X1 @ X0)
% 25.64/25.89          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 25.64/25.89          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 25.64/25.89          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1)
% 25.64/25.89              = (k1_funct_1 @ X2 @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X1)))
% 25.64/25.89          | ~ (v1_funct_1 @ X2)
% 25.64/25.89          | ~ (v1_relat_1 @ X2))),
% 25.64/25.89      inference('sup-', [status(thm)], ['191', '192'])).
% 25.64/25.89  thf('194', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 25.64/25.89      inference('cnf', [status(esa)], [fc3_funct_1])).
% 25.64/25.89  thf('195', plain, (![X12 : $i]: (v1_funct_1 @ (k6_relat_1 @ X12))),
% 25.64/25.89      inference('cnf', [status(esa)], [fc3_funct_1])).
% 25.64/25.89  thf('196', plain,
% 25.64/25.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.64/25.89         (~ (r2_hidden @ X1 @ X0)
% 25.64/25.89          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1)
% 25.64/25.89              = (k1_funct_1 @ X2 @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X1)))
% 25.64/25.89          | ~ (v1_funct_1 @ X2)
% 25.64/25.89          | ~ (v1_relat_1 @ X2))),
% 25.64/25.89      inference('demod', [status(thm)], ['193', '194', '195'])).
% 25.64/25.89  thf('197', plain,
% 25.64/25.89      ((![X0 : $i]:
% 25.64/25.89          (~ (v1_relat_1 @ X0)
% 25.64/25.89           | ~ (v1_funct_1 @ X0)
% 25.64/25.89           | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ X0) @ 
% 25.64/25.89               (sk_D_1 @ sk_C_2 @ sk_B))
% 25.64/25.89               = (k1_funct_1 @ X0 @ 
% 25.64/25.89                  (k1_funct_1 @ (k6_relat_1 @ sk_A) @ (sk_D_1 @ sk_C_2 @ sk_B))))))
% 25.64/25.89         <= ((((sk_B) = (k6_relat_1 @ sk_A))) & ((r2_hidden @ sk_C_2 @ sk_A)))),
% 25.64/25.89      inference('sup-', [status(thm)], ['190', '196'])).
% 25.64/25.89  thf('198', plain,
% 25.64/25.89      ((((sk_B) = (k6_relat_1 @ sk_A))) <= ((((sk_B) = (k6_relat_1 @ sk_A))))),
% 25.64/25.89      inference('split', [status(esa)], ['2'])).
% 25.64/25.89  thf('199', plain,
% 25.64/25.89      ((((sk_B) = (k6_relat_1 @ sk_A))) <= ((((sk_B) = (k6_relat_1 @ sk_A))))),
% 25.64/25.89      inference('split', [status(esa)], ['2'])).
% 25.64/25.89  thf('200', plain,
% 25.64/25.89      (((r2_hidden @ sk_C_2 @ sk_A)) <= (((r2_hidden @ sk_C_2 @ sk_A)))),
% 25.64/25.89      inference('split', [status(esa)], ['0'])).
% 25.64/25.89  thf('201', plain,
% 25.64/25.89      ((((k2_relat_1 @ sk_B) = (sk_A))) <= ((((sk_B) = (k6_relat_1 @ sk_A))))),
% 25.64/25.89      inference('sup+', [status(thm)], ['181', '182'])).
% 25.64/25.89  thf('202', plain,
% 25.64/25.89      (![X5 : $i, X8 : $i]:
% 25.64/25.89         (~ (v1_relat_1 @ X5)
% 25.64/25.89          | ~ (v1_funct_1 @ X5)
% 25.64/25.89          | ~ (r2_hidden @ X8 @ (k2_relat_1 @ X5))
% 25.64/25.89          | ((X8) = (k1_funct_1 @ X5 @ (sk_D_1 @ X8 @ X5))))),
% 25.64/25.89      inference('simplify', [status(thm)], ['91'])).
% 25.64/25.89  thf('203', plain,
% 25.64/25.89      ((![X0 : $i]:
% 25.64/25.89          (~ (r2_hidden @ X0 @ sk_A)
% 25.64/25.89           | ((X0) = (k1_funct_1 @ sk_B @ (sk_D_1 @ X0 @ sk_B)))
% 25.64/25.89           | ~ (v1_funct_1 @ sk_B)
% 25.64/25.89           | ~ (v1_relat_1 @ sk_B)))
% 25.64/25.89         <= ((((sk_B) = (k6_relat_1 @ sk_A))))),
% 25.64/25.89      inference('sup-', [status(thm)], ['201', '202'])).
% 25.64/25.89  thf('204', plain, ((v1_funct_1 @ sk_B)),
% 25.64/25.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.64/25.89  thf('205', plain, ((v1_relat_1 @ sk_B)),
% 25.64/25.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.64/25.89  thf('206', plain,
% 25.64/25.89      ((![X0 : $i]:
% 25.64/25.89          (~ (r2_hidden @ X0 @ sk_A)
% 25.64/25.89           | ((X0) = (k1_funct_1 @ sk_B @ (sk_D_1 @ X0 @ sk_B)))))
% 25.64/25.89         <= ((((sk_B) = (k6_relat_1 @ sk_A))))),
% 25.64/25.89      inference('demod', [status(thm)], ['203', '204', '205'])).
% 25.64/25.89  thf('207', plain,
% 25.64/25.89      ((((sk_C_2) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_C_2 @ sk_B))))
% 25.64/25.89         <= ((((sk_B) = (k6_relat_1 @ sk_A))) & ((r2_hidden @ sk_C_2 @ sk_A)))),
% 25.64/25.89      inference('sup-', [status(thm)], ['200', '206'])).
% 25.64/25.89  thf('208', plain,
% 25.64/25.89      ((![X0 : $i]:
% 25.64/25.89          (~ (v1_relat_1 @ X0)
% 25.64/25.89           | ~ (v1_funct_1 @ X0)
% 25.64/25.89           | ((k1_funct_1 @ (k5_relat_1 @ sk_B @ X0) @ (sk_D_1 @ sk_C_2 @ sk_B))
% 25.64/25.89               = (k1_funct_1 @ X0 @ sk_C_2))))
% 25.64/25.89         <= ((((sk_B) = (k6_relat_1 @ sk_A))) & ((r2_hidden @ sk_C_2 @ sk_A)))),
% 25.64/25.89      inference('demod', [status(thm)], ['197', '198', '199', '207'])).
% 25.64/25.89  thf('209', plain,
% 25.64/25.89      (((((k1_funct_1 @ sk_B @ (sk_D_1 @ sk_C_2 @ sk_B))
% 25.64/25.89           = (k1_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ sk_C_2))
% 25.64/25.89         | ~ (v1_relat_1 @ sk_B)
% 25.64/25.89         | ~ (v1_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 25.64/25.89         | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))))
% 25.64/25.89         <= ((((sk_B) = (k6_relat_1 @ sk_A))) & ((r2_hidden @ sk_C_2 @ sk_A)))),
% 25.64/25.89      inference('sup+', [status(thm)], ['179', '208'])).
% 25.64/25.89  thf('210', plain,
% 25.64/25.89      ((((sk_C_2) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_C_2 @ sk_B))))
% 25.64/25.89         <= ((((sk_B) = (k6_relat_1 @ sk_A))) & ((r2_hidden @ sk_C_2 @ sk_A)))),
% 25.64/25.89      inference('sup-', [status(thm)], ['200', '206'])).
% 25.64/25.89  thf('211', plain,
% 25.64/25.89      ((((k2_relat_1 @ sk_B) = (sk_A))) <= ((((sk_B) = (k6_relat_1 @ sk_A))))),
% 25.64/25.89      inference('sup+', [status(thm)], ['181', '182'])).
% 25.64/25.89  thf('212', plain,
% 25.64/25.89      ((((sk_B) = (k6_relat_1 @ sk_A))) <= ((((sk_B) = (k6_relat_1 @ sk_A))))),
% 25.64/25.89      inference('split', [status(esa)], ['2'])).
% 25.64/25.89  thf('213', plain, ((v1_relat_1 @ sk_B)),
% 25.64/25.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.64/25.89  thf('214', plain,
% 25.64/25.89      ((((k2_relat_1 @ sk_B) = (sk_A))) <= ((((sk_B) = (k6_relat_1 @ sk_A))))),
% 25.64/25.89      inference('sup+', [status(thm)], ['181', '182'])).
% 25.64/25.89  thf('215', plain,
% 25.64/25.89      ((((sk_B) = (k6_relat_1 @ sk_A))) <= ((((sk_B) = (k6_relat_1 @ sk_A))))),
% 25.64/25.89      inference('split', [status(esa)], ['2'])).
% 25.64/25.89  thf('216', plain, ((v1_funct_1 @ sk_B)),
% 25.64/25.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.64/25.89  thf('217', plain,
% 25.64/25.89      ((((k2_relat_1 @ sk_B) = (sk_A))) <= ((((sk_B) = (k6_relat_1 @ sk_A))))),
% 25.64/25.89      inference('sup+', [status(thm)], ['181', '182'])).
% 25.64/25.89  thf('218', plain,
% 25.64/25.89      ((((sk_B) = (k6_relat_1 @ sk_A))) <= ((((sk_B) = (k6_relat_1 @ sk_A))))),
% 25.64/25.89      inference('split', [status(esa)], ['2'])).
% 25.64/25.89  thf('219', plain, ((v1_relat_1 @ sk_B)),
% 25.64/25.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.64/25.89  thf('220', plain,
% 25.64/25.89      ((((sk_C_2) = (k1_funct_1 @ sk_B @ sk_C_2)))
% 25.64/25.89         <= ((((sk_B) = (k6_relat_1 @ sk_A))) & ((r2_hidden @ sk_C_2 @ sk_A)))),
% 25.64/25.89      inference('demod', [status(thm)],
% 25.64/25.89                ['209', '210', '211', '212', '213', '214', '215', '216', 
% 25.64/25.89                 '217', '218', '219'])).
% 25.64/25.89  thf('221', plain,
% 25.64/25.89      ((((k1_funct_1 @ sk_B @ sk_C_2) != (sk_C_2)))
% 25.64/25.89         <= (~ (((k1_funct_1 @ sk_B @ sk_C_2) = (sk_C_2))))),
% 25.64/25.89      inference('split', [status(esa)], ['168'])).
% 25.64/25.89  thf('222', plain,
% 25.64/25.89      ((((sk_C_2) != (sk_C_2)))
% 25.64/25.89         <= (~ (((k1_funct_1 @ sk_B @ sk_C_2) = (sk_C_2))) & 
% 25.64/25.89             (((sk_B) = (k6_relat_1 @ sk_A))) & 
% 25.64/25.89             ((r2_hidden @ sk_C_2 @ sk_A)))),
% 25.64/25.89      inference('sup-', [status(thm)], ['220', '221'])).
% 25.64/25.89  thf('223', plain,
% 25.64/25.89      ((((k1_funct_1 @ sk_B @ sk_C_2) = (sk_C_2))) | 
% 25.64/25.89       ~ ((r2_hidden @ sk_C_2 @ sk_A)) | ~ (((sk_B) = (k6_relat_1 @ sk_A)))),
% 25.64/25.89      inference('simplify', [status(thm)], ['222'])).
% 25.64/25.89  thf('224', plain, ($false),
% 25.64/25.89      inference('sat_resolution*', [status(thm)],
% 25.64/25.89                ['1', '3', '5', '171', '177', '178', '223'])).
% 25.64/25.89  
% 25.64/25.89  % SZS output end Refutation
% 25.64/25.89  
% 25.64/25.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
