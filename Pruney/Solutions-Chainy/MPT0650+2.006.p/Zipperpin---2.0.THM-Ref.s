%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lYtYT6WC9N

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 204 expanded)
%              Number of leaves         :   22 (  67 expanded)
%              Depth                    :   15
%              Number of atoms          :  754 (2984 expanded)
%              Number of equality atoms :   49 ( 210 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X14: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('1',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t57_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( v2_funct_1 @ B )
          & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) )
       => ( ( A
            = ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) )
          & ( A
            = ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( v2_funct_1 @ B )
            & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) )
         => ( ( A
              = ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) )
            & ( A
              = ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t57_funct_1])).

thf('2',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relat_1 @ X18 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ X4 @ ( sk_D_1 @ X4 @ X2 ) ) @ X2 )
      | ( X3
       != ( k1_relat_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('5',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X4 @ ( sk_D_1 @ X4 @ X2 ) ) @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k1_relat_1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_D_1 @ X1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_1 @ sk_A @ ( k2_funct_1 @ sk_B ) ) ) @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf('8',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_1 @ sk_A @ ( k2_funct_1 @ sk_B ) ) ) @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k1_relat_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ X2 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

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

thf('15',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X16 @ X15 ) @ X17 )
        = ( k1_funct_1 @ X15 @ ( k1_funct_1 @ X16 @ X17 ) ) )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('18',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X11 @ X9 ) @ X11 ) @ X9 )
      | ( X10
       != ( k2_relat_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('19',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X11 @ X9 ) @ X11 ) @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k2_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_3 @ sk_A @ sk_B ) @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ X2 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('22',plain,(
    r2_hidden @ ( sk_D_3 @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

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

thf('23',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ X19 ) )
      | ( X20
        = ( k1_funct_1 @ ( k2_funct_1 @ X19 ) @ ( k1_funct_1 @ X19 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t56_funct_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( sk_D_3 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ ( sk_D_3 @ sk_A @ sk_B ) ) ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_3 @ sk_A @ sk_B ) @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['17','19'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('28',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X21 @ X23 ) @ X22 )
      | ( X23
        = ( k1_funct_1 @ X22 @ X21 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( sk_A
      = ( k1_funct_1 @ sk_B @ ( sk_D_3 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_3 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( sk_D_3 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','26','32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( sk_D_3 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( sk_D_3 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['1','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( sk_D_3 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( sk_D_3 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( sk_D_3 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
    | ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(split,[status(esa)],['44'])).

thf('46',plain,
    ( ( sk_D_3 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','26','32','33'])).

thf('47',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['44'])).

thf('48',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( sk_D_3 @ sk_A @ sk_B ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_3 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('50',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) )
    | ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['44'])).

thf('53',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['51','52'])).

thf('54',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['45','53'])).

thf('55',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( sk_D_3 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['43','54'])).

thf('56',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_3 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('57',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['55','56','57','58'])).

thf('60',plain,(
    $false ),
    inference(simplify,[status(thm)],['59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lYtYT6WC9N
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:54:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.59  % Solved by: fo/fo7.sh
% 0.21/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.59  % done 126 iterations in 0.155s
% 0.21/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.59  % SZS output start Refutation
% 0.21/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.59  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.59  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.21/0.59  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.59  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.59  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i).
% 0.21/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.59  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.59  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.59  thf(dt_k2_funct_1, axiom,
% 0.21/0.59    (![A:$i]:
% 0.21/0.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.59       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.21/0.59         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.21/0.59  thf('0', plain,
% 0.21/0.59      (![X14 : $i]:
% 0.21/0.59         ((v1_funct_1 @ (k2_funct_1 @ X14))
% 0.21/0.59          | ~ (v1_funct_1 @ X14)
% 0.21/0.59          | ~ (v1_relat_1 @ X14))),
% 0.21/0.59      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.59  thf('1', plain,
% 0.21/0.59      (![X14 : $i]:
% 0.21/0.59         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 0.21/0.59          | ~ (v1_funct_1 @ X14)
% 0.21/0.59          | ~ (v1_relat_1 @ X14))),
% 0.21/0.59      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.59  thf(t57_funct_1, conjecture,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.59       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 0.21/0.59         ( ( ( A ) =
% 0.21/0.59             ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 0.21/0.59           ( ( A ) =
% 0.21/0.59             ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ))).
% 0.21/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.59    (~( ![A:$i,B:$i]:
% 0.21/0.59        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.59          ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 0.21/0.59            ( ( ( A ) =
% 0.21/0.59                ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 0.21/0.59              ( ( A ) =
% 0.21/0.59                ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) )),
% 0.21/0.59    inference('cnf.neg', [status(esa)], [t57_funct_1])).
% 0.21/0.59  thf('2', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf(t55_funct_1, axiom,
% 0.21/0.59    (![A:$i]:
% 0.21/0.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.59       ( ( v2_funct_1 @ A ) =>
% 0.21/0.59         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.21/0.59           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.21/0.59  thf('3', plain,
% 0.21/0.59      (![X18 : $i]:
% 0.21/0.59         (~ (v2_funct_1 @ X18)
% 0.21/0.59          | ((k2_relat_1 @ X18) = (k1_relat_1 @ (k2_funct_1 @ X18)))
% 0.21/0.59          | ~ (v1_funct_1 @ X18)
% 0.21/0.59          | ~ (v1_relat_1 @ X18))),
% 0.21/0.59      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.21/0.59  thf(d4_relat_1, axiom,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.21/0.59       ( ![C:$i]:
% 0.21/0.59         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.59           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.21/0.59  thf('4', plain,
% 0.21/0.59      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.59         (~ (r2_hidden @ X4 @ X3)
% 0.21/0.59          | (r2_hidden @ (k4_tarski @ X4 @ (sk_D_1 @ X4 @ X2)) @ X2)
% 0.21/0.59          | ((X3) != (k1_relat_1 @ X2)))),
% 0.21/0.59      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.21/0.59  thf('5', plain,
% 0.21/0.59      (![X2 : $i, X4 : $i]:
% 0.21/0.59         ((r2_hidden @ (k4_tarski @ X4 @ (sk_D_1 @ X4 @ X2)) @ X2)
% 0.21/0.59          | ~ (r2_hidden @ X4 @ (k1_relat_1 @ X2)))),
% 0.21/0.59      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.59  thf('6', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.21/0.59          | ~ (v1_relat_1 @ X0)
% 0.21/0.59          | ~ (v1_funct_1 @ X0)
% 0.21/0.59          | ~ (v2_funct_1 @ X0)
% 0.21/0.59          | (r2_hidden @ 
% 0.21/0.59             (k4_tarski @ X1 @ (sk_D_1 @ X1 @ (k2_funct_1 @ X0))) @ 
% 0.21/0.59             (k2_funct_1 @ X0)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['3', '5'])).
% 0.21/0.59  thf('7', plain,
% 0.21/0.59      (((r2_hidden @ 
% 0.21/0.59         (k4_tarski @ sk_A @ (sk_D_1 @ sk_A @ (k2_funct_1 @ sk_B))) @ 
% 0.21/0.59         (k2_funct_1 @ sk_B))
% 0.21/0.59        | ~ (v2_funct_1 @ sk_B)
% 0.21/0.59        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.59        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.59      inference('sup-', [status(thm)], ['2', '6'])).
% 0.21/0.59  thf('8', plain, ((v2_funct_1 @ sk_B)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('9', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('10', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('11', plain,
% 0.21/0.59      ((r2_hidden @ 
% 0.21/0.59        (k4_tarski @ sk_A @ (sk_D_1 @ sk_A @ (k2_funct_1 @ sk_B))) @ 
% 0.21/0.59        (k2_funct_1 @ sk_B))),
% 0.21/0.59      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 0.21/0.59  thf('12', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.59         (~ (r2_hidden @ (k4_tarski @ X0 @ X1) @ X2)
% 0.21/0.59          | (r2_hidden @ X0 @ X3)
% 0.21/0.59          | ((X3) != (k1_relat_1 @ X2)))),
% 0.21/0.59      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.21/0.59  thf('13', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.59         ((r2_hidden @ X0 @ (k1_relat_1 @ X2))
% 0.21/0.59          | ~ (r2_hidden @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.21/0.59      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.59  thf('14', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['11', '13'])).
% 0.21/0.59  thf(t23_funct_1, axiom,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.59       ( ![C:$i]:
% 0.21/0.59         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.59           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.59             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.21/0.59               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 0.21/0.59  thf('15', plain,
% 0.21/0.59      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.59         (~ (v1_relat_1 @ X15)
% 0.21/0.59          | ~ (v1_funct_1 @ X15)
% 0.21/0.59          | ((k1_funct_1 @ (k5_relat_1 @ X16 @ X15) @ X17)
% 0.21/0.59              = (k1_funct_1 @ X15 @ (k1_funct_1 @ X16 @ X17)))
% 0.21/0.59          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ X16))
% 0.21/0.59          | ~ (v1_funct_1 @ X16)
% 0.21/0.59          | ~ (v1_relat_1 @ X16))),
% 0.21/0.59      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.21/0.59  thf('16', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         (~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.21/0.59          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.21/0.59          | ((k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ sk_A)
% 0.21/0.59              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))
% 0.21/0.59          | ~ (v1_funct_1 @ X0)
% 0.21/0.59          | ~ (v1_relat_1 @ X0))),
% 0.21/0.59      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.59  thf('17', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf(d5_relat_1, axiom,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.21/0.59       ( ![C:$i]:
% 0.21/0.59         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.59           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.21/0.59  thf('18', plain,
% 0.21/0.59      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.59         (~ (r2_hidden @ X11 @ X10)
% 0.21/0.59          | (r2_hidden @ (k4_tarski @ (sk_D_3 @ X11 @ X9) @ X11) @ X9)
% 0.21/0.59          | ((X10) != (k2_relat_1 @ X9)))),
% 0.21/0.59      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.21/0.59  thf('19', plain,
% 0.21/0.59      (![X9 : $i, X11 : $i]:
% 0.21/0.59         ((r2_hidden @ (k4_tarski @ (sk_D_3 @ X11 @ X9) @ X11) @ X9)
% 0.21/0.59          | ~ (r2_hidden @ X11 @ (k2_relat_1 @ X9)))),
% 0.21/0.59      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.59  thf('20', plain,
% 0.21/0.59      ((r2_hidden @ (k4_tarski @ (sk_D_3 @ sk_A @ sk_B) @ sk_A) @ sk_B)),
% 0.21/0.59      inference('sup-', [status(thm)], ['17', '19'])).
% 0.21/0.59  thf('21', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.59         ((r2_hidden @ X0 @ (k1_relat_1 @ X2))
% 0.21/0.59          | ~ (r2_hidden @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.21/0.59      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.59  thf('22', plain,
% 0.21/0.59      ((r2_hidden @ (sk_D_3 @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B))),
% 0.21/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.59  thf(t56_funct_1, axiom,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.59       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) ) =>
% 0.21/0.59         ( ( ( A ) =
% 0.21/0.59             ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) ) & 
% 0.21/0.59           ( ( A ) =
% 0.21/0.59             ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ))).
% 0.21/0.59  thf('23', plain,
% 0.21/0.59      (![X19 : $i, X20 : $i]:
% 0.21/0.59         (~ (v2_funct_1 @ X19)
% 0.21/0.59          | ~ (r2_hidden @ X20 @ (k1_relat_1 @ X19))
% 0.21/0.59          | ((X20)
% 0.21/0.59              = (k1_funct_1 @ (k2_funct_1 @ X19) @ (k1_funct_1 @ X19 @ X20)))
% 0.21/0.59          | ~ (v1_funct_1 @ X19)
% 0.21/0.59          | ~ (v1_relat_1 @ X19))),
% 0.21/0.59      inference('cnf', [status(esa)], [t56_funct_1])).
% 0.21/0.59  thf('24', plain,
% 0.21/0.59      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.59        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.59        | ((sk_D_3 @ sk_A @ sk_B)
% 0.21/0.59            = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ 
% 0.21/0.59               (k1_funct_1 @ sk_B @ (sk_D_3 @ sk_A @ sk_B))))
% 0.21/0.59        | ~ (v2_funct_1 @ sk_B))),
% 0.21/0.59      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.59  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('26', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('27', plain,
% 0.21/0.59      ((r2_hidden @ (k4_tarski @ (sk_D_3 @ sk_A @ sk_B) @ sk_A) @ sk_B)),
% 0.21/0.59      inference('sup-', [status(thm)], ['17', '19'])).
% 0.21/0.59  thf(t8_funct_1, axiom,
% 0.21/0.59    (![A:$i,B:$i,C:$i]:
% 0.21/0.59     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.59       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.21/0.59         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.21/0.59           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.21/0.59  thf('28', plain,
% 0.21/0.59      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.59         (~ (r2_hidden @ (k4_tarski @ X21 @ X23) @ X22)
% 0.21/0.59          | ((X23) = (k1_funct_1 @ X22 @ X21))
% 0.21/0.59          | ~ (v1_funct_1 @ X22)
% 0.21/0.59          | ~ (v1_relat_1 @ X22))),
% 0.21/0.59      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.21/0.59  thf('29', plain,
% 0.21/0.59      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.59        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.59        | ((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_3 @ sk_A @ sk_B))))),
% 0.21/0.59      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.59  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('31', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('32', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_3 @ sk_A @ sk_B)))),
% 0.21/0.59      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.21/0.59  thf('33', plain, ((v2_funct_1 @ sk_B)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('34', plain,
% 0.21/0.59      (((sk_D_3 @ sk_A @ sk_B) = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))),
% 0.21/0.59      inference('demod', [status(thm)], ['24', '25', '26', '32', '33'])).
% 0.21/0.59  thf('35', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         (~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.21/0.59          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.21/0.59          | ((k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ sk_A)
% 0.21/0.59              = (k1_funct_1 @ X0 @ (sk_D_3 @ sk_A @ sk_B)))
% 0.21/0.59          | ~ (v1_funct_1 @ X0)
% 0.21/0.59          | ~ (v1_relat_1 @ X0))),
% 0.21/0.59      inference('demod', [status(thm)], ['16', '34'])).
% 0.21/0.59  thf('36', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         (~ (v1_relat_1 @ sk_B)
% 0.21/0.59          | ~ (v1_funct_1 @ sk_B)
% 0.21/0.59          | ~ (v1_relat_1 @ X0)
% 0.21/0.59          | ~ (v1_funct_1 @ X0)
% 0.21/0.59          | ((k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ sk_A)
% 0.21/0.59              = (k1_funct_1 @ X0 @ (sk_D_3 @ sk_A @ sk_B)))
% 0.21/0.59          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['1', '35'])).
% 0.21/0.59  thf('37', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('38', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('39', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         (~ (v1_relat_1 @ X0)
% 0.21/0.59          | ~ (v1_funct_1 @ X0)
% 0.21/0.59          | ((k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ sk_A)
% 0.21/0.59              = (k1_funct_1 @ X0 @ (sk_D_3 @ sk_A @ sk_B)))
% 0.21/0.59          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.21/0.59      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.21/0.59  thf('40', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         (~ (v1_relat_1 @ sk_B)
% 0.21/0.59          | ~ (v1_funct_1 @ sk_B)
% 0.21/0.59          | ((k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ sk_A)
% 0.21/0.59              = (k1_funct_1 @ X0 @ (sk_D_3 @ sk_A @ sk_B)))
% 0.21/0.59          | ~ (v1_funct_1 @ X0)
% 0.21/0.59          | ~ (v1_relat_1 @ X0))),
% 0.21/0.59      inference('sup-', [status(thm)], ['0', '39'])).
% 0.21/0.59  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('42', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('43', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         (((k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ sk_A)
% 0.21/0.59            = (k1_funct_1 @ X0 @ (sk_D_3 @ sk_A @ sk_B)))
% 0.21/0.59          | ~ (v1_funct_1 @ X0)
% 0.21/0.59          | ~ (v1_relat_1 @ X0))),
% 0.21/0.59      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.21/0.59  thf('44', plain,
% 0.21/0.59      ((((sk_A)
% 0.21/0.59          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))
% 0.21/0.59        | ((sk_A)
% 0.21/0.59            != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('45', plain,
% 0.21/0.59      ((((sk_A)
% 0.21/0.59          != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))
% 0.21/0.59         <= (~
% 0.21/0.59             (((sk_A)
% 0.21/0.59                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.21/0.59                   sk_A))))),
% 0.21/0.59      inference('split', [status(esa)], ['44'])).
% 0.21/0.59  thf('46', plain,
% 0.21/0.59      (((sk_D_3 @ sk_A @ sk_B) = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))),
% 0.21/0.59      inference('demod', [status(thm)], ['24', '25', '26', '32', '33'])).
% 0.21/0.59  thf('47', plain,
% 0.21/0.59      ((((sk_A)
% 0.21/0.59          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))
% 0.21/0.59         <= (~
% 0.21/0.59             (((sk_A)
% 0.21/0.59                = (k1_funct_1 @ sk_B @ 
% 0.21/0.59                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.21/0.59      inference('split', [status(esa)], ['44'])).
% 0.21/0.59  thf('48', plain,
% 0.21/0.59      ((((sk_A) != (k1_funct_1 @ sk_B @ (sk_D_3 @ sk_A @ sk_B))))
% 0.21/0.59         <= (~
% 0.21/0.59             (((sk_A)
% 0.21/0.59                = (k1_funct_1 @ sk_B @ 
% 0.21/0.59                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.21/0.59      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.59  thf('49', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_3 @ sk_A @ sk_B)))),
% 0.21/0.59      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.21/0.59  thf('50', plain,
% 0.21/0.59      ((((sk_A) != (sk_A)))
% 0.21/0.59         <= (~
% 0.21/0.59             (((sk_A)
% 0.21/0.59                = (k1_funct_1 @ sk_B @ 
% 0.21/0.59                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.21/0.59      inference('demod', [status(thm)], ['48', '49'])).
% 0.21/0.59  thf('51', plain,
% 0.21/0.59      ((((sk_A)
% 0.21/0.59          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.21/0.59      inference('simplify', [status(thm)], ['50'])).
% 0.21/0.59  thf('52', plain,
% 0.21/0.59      (~
% 0.21/0.59       (((sk_A)
% 0.21/0.59          = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A))) | 
% 0.21/0.59       ~
% 0.21/0.59       (((sk_A)
% 0.21/0.59          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.21/0.59      inference('split', [status(esa)], ['44'])).
% 0.21/0.59  thf('53', plain,
% 0.21/0.59      (~
% 0.21/0.59       (((sk_A)
% 0.21/0.59          = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 0.21/0.59      inference('sat_resolution*', [status(thm)], ['51', '52'])).
% 0.21/0.59  thf('54', plain,
% 0.21/0.59      (((sk_A)
% 0.21/0.59         != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A))),
% 0.21/0.59      inference('simpl_trail', [status(thm)], ['45', '53'])).
% 0.21/0.59  thf('55', plain,
% 0.21/0.59      ((((sk_A) != (k1_funct_1 @ sk_B @ (sk_D_3 @ sk_A @ sk_B)))
% 0.21/0.59        | ~ (v1_relat_1 @ sk_B)
% 0.21/0.59        | ~ (v1_funct_1 @ sk_B))),
% 0.21/0.59      inference('sup-', [status(thm)], ['43', '54'])).
% 0.21/0.59  thf('56', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_3 @ sk_A @ sk_B)))),
% 0.21/0.59      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.21/0.59  thf('57', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('58', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('59', plain, (((sk_A) != (sk_A))),
% 0.21/0.59      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 0.21/0.59  thf('60', plain, ($false), inference('simplify', [status(thm)], ['59'])).
% 0.21/0.59  
% 0.21/0.59  % SZS output end Refutation
% 0.21/0.59  
% 0.43/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
