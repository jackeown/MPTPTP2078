%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.j7X6ZCh6sy

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:21 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 281 expanded)
%              Number of leaves         :   23 (  90 expanded)
%              Depth                    :   20
%              Number of atoms          : 1046 (4122 expanded)
%              Number of equality atoms :   60 ( 282 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_funct_1 @ X11 )
        = ( k4_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_funct_1 @ X11 )
        = ( k4_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('5',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('9',plain,(
    ! [X10: $i] :
      ( ( ( k1_relat_1 @ X10 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

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

thf('10',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('12',plain,(
    ! [X10: $i] :
      ( ( ( k2_relat_1 @ X10 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('13',plain,(
    ! [X10: $i] :
      ( ( ( k1_relat_1 @ X10 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X4 @ X2 ) @ X4 ) @ X2 )
      | ( X3
       != ( k2_relat_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('15',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X4 @ X2 ) @ X4 ) @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k2_relat_1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X1 @ ( k4_relat_1 @ X0 ) ) @ X1 ) @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) @ X1 ) @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) @ X1 ) @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) @ X1 ) @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_A @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) @ sk_A ) @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_A @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) @ sk_A ) @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ X1 @ X3 )
      | ( X3
       != ( k2_relat_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ ( k2_relat_1 @ X2 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['9','27'])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

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

thf('34',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X14 @ X13 ) @ X15 )
        = ( k1_funct_1 @ X13 @ ( k1_funct_1 @ X14 @ X15 ) ) )
      | ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['36','37','38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('46',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_funct_1 @ X11 )
        = ( k4_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('47',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
    | ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(split,[status(esa)],['47'])).

thf('49',plain,
    ( ( ( sk_A
       != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50','51','52'])).

thf('54',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X4 @ X2 ) @ X4 ) @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k2_relat_1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('56',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_A @ sk_B ) @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['54','55'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('57',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X9 )
      | ( r2_hidden @ X7 @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('58',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['58','59'])).

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

thf('61',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X16 ) )
      | ( X17
        = ( k1_funct_1 @ ( k2_funct_1 @ X16 ) @ ( k1_funct_1 @ X16 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t56_funct_1])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_A @ sk_B ) @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['54','55'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('66',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X18 @ X20 ) @ X19 )
      | ( X20
        = ( k1_funct_1 @ X19 @ X18 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('67',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( sk_A
      = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['62','63','64','70','71'])).

thf('73',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['47'])).

thf('74',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('76',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) )
    | ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['47'])).

thf('79',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['77','78'])).

thf('80',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['53','79'])).

thf('81',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['45','80'])).

thf('82',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('83',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_funct_1 @ X11 )
        = ( k4_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('84',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['62','63','64','70','71'])).

thf('85',plain,
    ( ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['85','86','87','88'])).

thf('90',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','89'])).

thf('91',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['81','90','91','92'])).

thf('94',plain,(
    $false ),
    inference(simplify,[status(thm)],['93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.j7X6ZCh6sy
% 0.13/0.36  % Computer   : n024.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 14:52:06 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.38/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.57  % Solved by: fo/fo7.sh
% 0.38/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.57  % done 117 iterations in 0.120s
% 0.38/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.57  % SZS output start Refutation
% 0.38/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.57  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.38/0.57  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.38/0.57  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.38/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.57  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.38/0.57  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.38/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.57  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.38/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.57  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.38/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.57  thf(d9_funct_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.57       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.38/0.57  thf('0', plain,
% 0.38/0.57      (![X11 : $i]:
% 0.38/0.57         (~ (v2_funct_1 @ X11)
% 0.38/0.57          | ((k2_funct_1 @ X11) = (k4_relat_1 @ X11))
% 0.38/0.57          | ~ (v1_funct_1 @ X11)
% 0.38/0.57          | ~ (v1_relat_1 @ X11))),
% 0.38/0.57      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.38/0.57  thf(dt_k2_funct_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.57       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.38/0.57         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.38/0.57  thf('1', plain,
% 0.38/0.57      (![X12 : $i]:
% 0.38/0.57         ((v1_funct_1 @ (k2_funct_1 @ X12))
% 0.38/0.57          | ~ (v1_funct_1 @ X12)
% 0.38/0.57          | ~ (v1_relat_1 @ X12))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.38/0.57  thf('2', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((v1_funct_1 @ (k4_relat_1 @ X0))
% 0.38/0.57          | ~ (v1_relat_1 @ X0)
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | ~ (v2_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_relat_1 @ X0)
% 0.38/0.57          | ~ (v1_funct_1 @ X0))),
% 0.38/0.57      inference('sup+', [status(thm)], ['0', '1'])).
% 0.38/0.57  thf('3', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (v2_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_relat_1 @ X0)
% 0.38/0.57          | (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['2'])).
% 0.38/0.57  thf('4', plain,
% 0.38/0.57      (![X11 : $i]:
% 0.38/0.57         (~ (v2_funct_1 @ X11)
% 0.38/0.57          | ((k2_funct_1 @ X11) = (k4_relat_1 @ X11))
% 0.38/0.57          | ~ (v1_funct_1 @ X11)
% 0.38/0.57          | ~ (v1_relat_1 @ X11))),
% 0.38/0.57      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.38/0.57  thf('5', plain,
% 0.38/0.57      (![X12 : $i]:
% 0.38/0.57         ((v1_relat_1 @ (k2_funct_1 @ X12))
% 0.38/0.57          | ~ (v1_funct_1 @ X12)
% 0.38/0.57          | ~ (v1_relat_1 @ X12))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.38/0.57  thf('6', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((v1_relat_1 @ (k4_relat_1 @ X0))
% 0.38/0.57          | ~ (v1_relat_1 @ X0)
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | ~ (v2_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_relat_1 @ X0)
% 0.38/0.57          | ~ (v1_funct_1 @ X0))),
% 0.38/0.57      inference('sup+', [status(thm)], ['4', '5'])).
% 0.38/0.57  thf('7', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (v2_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_relat_1 @ X0)
% 0.38/0.57          | (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['6'])).
% 0.38/0.57  thf('8', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (v2_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_relat_1 @ X0)
% 0.38/0.57          | (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['6'])).
% 0.38/0.57  thf(t37_relat_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( v1_relat_1 @ A ) =>
% 0.38/0.57       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.38/0.57         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.38/0.57  thf('9', plain,
% 0.38/0.57      (![X10 : $i]:
% 0.38/0.57         (((k1_relat_1 @ X10) = (k2_relat_1 @ (k4_relat_1 @ X10)))
% 0.38/0.57          | ~ (v1_relat_1 @ X10))),
% 0.38/0.57      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.38/0.57  thf(t57_funct_1, conjecture,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.57       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 0.38/0.57         ( ( ( A ) =
% 0.38/0.57             ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 0.38/0.57           ( ( A ) =
% 0.38/0.57             ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ))).
% 0.38/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.57    (~( ![A:$i,B:$i]:
% 0.38/0.57        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.57          ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 0.38/0.57            ( ( ( A ) =
% 0.38/0.57                ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 0.38/0.57              ( ( A ) =
% 0.38/0.57                ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) )),
% 0.38/0.57    inference('cnf.neg', [status(esa)], [t57_funct_1])).
% 0.38/0.57  thf('10', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('11', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (v2_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_relat_1 @ X0)
% 0.38/0.57          | (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['6'])).
% 0.38/0.57  thf('12', plain,
% 0.38/0.57      (![X10 : $i]:
% 0.38/0.57         (((k2_relat_1 @ X10) = (k1_relat_1 @ (k4_relat_1 @ X10)))
% 0.38/0.57          | ~ (v1_relat_1 @ X10))),
% 0.38/0.57      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.38/0.57  thf('13', plain,
% 0.38/0.57      (![X10 : $i]:
% 0.38/0.57         (((k1_relat_1 @ X10) = (k2_relat_1 @ (k4_relat_1 @ X10)))
% 0.38/0.57          | ~ (v1_relat_1 @ X10))),
% 0.38/0.57      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.38/0.57  thf(d5_relat_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.38/0.57       ( ![C:$i]:
% 0.38/0.57         ( ( r2_hidden @ C @ B ) <=>
% 0.38/0.57           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.38/0.57  thf('14', plain,
% 0.38/0.57      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.57         (~ (r2_hidden @ X4 @ X3)
% 0.38/0.57          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X4 @ X2) @ X4) @ X2)
% 0.38/0.57          | ((X3) != (k2_relat_1 @ X2)))),
% 0.38/0.57      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.38/0.57  thf('15', plain,
% 0.38/0.57      (![X2 : $i, X4 : $i]:
% 0.38/0.57         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X4 @ X2) @ X4) @ X2)
% 0.38/0.57          | ~ (r2_hidden @ X4 @ (k2_relat_1 @ X2)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['14'])).
% 0.38/0.57  thf('16', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.38/0.57          | ~ (v1_relat_1 @ X0)
% 0.38/0.57          | (r2_hidden @ 
% 0.38/0.57             (k4_tarski @ (sk_D_1 @ X1 @ (k4_relat_1 @ X0)) @ X1) @ 
% 0.38/0.57             (k4_relat_1 @ X0)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['13', '15'])).
% 0.38/0.57  thf('17', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.38/0.57          | ~ (v1_relat_1 @ X0)
% 0.38/0.57          | (r2_hidden @ 
% 0.38/0.57             (k4_tarski @ (sk_D_1 @ X1 @ (k4_relat_1 @ (k4_relat_1 @ X0))) @ X1) @ 
% 0.38/0.57             (k4_relat_1 @ (k4_relat_1 @ X0)))
% 0.38/0.57          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['12', '16'])).
% 0.38/0.57  thf('18', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (~ (v1_relat_1 @ X0)
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | ~ (v2_funct_1 @ X0)
% 0.38/0.57          | (r2_hidden @ 
% 0.38/0.57             (k4_tarski @ (sk_D_1 @ X1 @ (k4_relat_1 @ (k4_relat_1 @ X0))) @ X1) @ 
% 0.38/0.57             (k4_relat_1 @ (k4_relat_1 @ X0)))
% 0.38/0.57          | ~ (v1_relat_1 @ X0)
% 0.38/0.57          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['11', '17'])).
% 0.38/0.57  thf('19', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.38/0.57          | (r2_hidden @ 
% 0.38/0.57             (k4_tarski @ (sk_D_1 @ X1 @ (k4_relat_1 @ (k4_relat_1 @ X0))) @ X1) @ 
% 0.38/0.57             (k4_relat_1 @ (k4_relat_1 @ X0)))
% 0.38/0.57          | ~ (v2_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_relat_1 @ X0))),
% 0.38/0.57      inference('simplify', [status(thm)], ['18'])).
% 0.38/0.57  thf('20', plain,
% 0.38/0.57      ((~ (v1_relat_1 @ sk_B)
% 0.38/0.57        | ~ (v1_funct_1 @ sk_B)
% 0.38/0.57        | ~ (v2_funct_1 @ sk_B)
% 0.38/0.57        | (r2_hidden @ 
% 0.38/0.57           (k4_tarski @ (sk_D_1 @ sk_A @ (k4_relat_1 @ (k4_relat_1 @ sk_B))) @ 
% 0.38/0.57            sk_A) @ 
% 0.38/0.57           (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['10', '19'])).
% 0.38/0.57  thf('21', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('22', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('23', plain, ((v2_funct_1 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('24', plain,
% 0.38/0.57      ((r2_hidden @ 
% 0.38/0.57        (k4_tarski @ (sk_D_1 @ sk_A @ (k4_relat_1 @ (k4_relat_1 @ sk_B))) @ 
% 0.38/0.57         sk_A) @ 
% 0.38/0.57        (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 0.38/0.57      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 0.38/0.57  thf('25', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.57         (~ (r2_hidden @ (k4_tarski @ X0 @ X1) @ X2)
% 0.38/0.57          | (r2_hidden @ X1 @ X3)
% 0.38/0.57          | ((X3) != (k2_relat_1 @ X2)))),
% 0.38/0.57      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.38/0.57  thf('26', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.57         ((r2_hidden @ X1 @ (k2_relat_1 @ X2))
% 0.38/0.57          | ~ (r2_hidden @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.38/0.57      inference('simplify', [status(thm)], ['25'])).
% 0.38/0.57  thf('27', plain,
% 0.38/0.57      ((r2_hidden @ sk_A @ (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['24', '26'])).
% 0.38/0.57  thf('28', plain,
% 0.38/0.57      (((r2_hidden @ sk_A @ (k1_relat_1 @ (k4_relat_1 @ sk_B)))
% 0.38/0.57        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 0.38/0.57      inference('sup+', [status(thm)], ['9', '27'])).
% 0.38/0.57  thf('29', plain,
% 0.38/0.57      ((~ (v1_relat_1 @ sk_B)
% 0.38/0.57        | ~ (v1_funct_1 @ sk_B)
% 0.38/0.57        | ~ (v2_funct_1 @ sk_B)
% 0.38/0.57        | (r2_hidden @ sk_A @ (k1_relat_1 @ (k4_relat_1 @ sk_B))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['8', '28'])).
% 0.38/0.57  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('31', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('32', plain, ((v2_funct_1 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('33', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 0.38/0.57      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.38/0.57  thf(t23_funct_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.57       ( ![C:$i]:
% 0.38/0.57         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.38/0.57           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.38/0.57             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.38/0.57               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 0.38/0.57  thf('34', plain,
% 0.38/0.57      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.38/0.57         (~ (v1_relat_1 @ X13)
% 0.38/0.57          | ~ (v1_funct_1 @ X13)
% 0.38/0.57          | ((k1_funct_1 @ (k5_relat_1 @ X14 @ X13) @ X15)
% 0.38/0.57              = (k1_funct_1 @ X13 @ (k1_funct_1 @ X14 @ X15)))
% 0.38/0.57          | ~ (r2_hidden @ X15 @ (k1_relat_1 @ X14))
% 0.38/0.57          | ~ (v1_funct_1 @ X14)
% 0.38/0.57          | ~ (v1_relat_1 @ X14))),
% 0.38/0.57      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.38/0.57  thf('35', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.38/0.57          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.38/0.57          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.38/0.57              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_relat_1 @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['33', '34'])).
% 0.38/0.57  thf('36', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (v1_relat_1 @ sk_B)
% 0.38/0.57          | ~ (v1_funct_1 @ sk_B)
% 0.38/0.57          | ~ (v2_funct_1 @ sk_B)
% 0.38/0.57          | ~ (v1_relat_1 @ X0)
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.38/0.57              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))
% 0.38/0.57          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['7', '35'])).
% 0.38/0.57  thf('37', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('38', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('39', plain, ((v2_funct_1 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('40', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (v1_relat_1 @ X0)
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.38/0.57              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))
% 0.38/0.57          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.38/0.57      inference('demod', [status(thm)], ['36', '37', '38', '39'])).
% 0.38/0.57  thf('41', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (v1_relat_1 @ sk_B)
% 0.38/0.57          | ~ (v1_funct_1 @ sk_B)
% 0.38/0.57          | ~ (v2_funct_1 @ sk_B)
% 0.38/0.57          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.38/0.57              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_relat_1 @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['3', '40'])).
% 0.38/0.57  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('43', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('44', plain, ((v2_funct_1 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('45', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.38/0.57            = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_relat_1 @ X0))),
% 0.38/0.57      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 0.38/0.57  thf('46', plain,
% 0.38/0.57      (![X11 : $i]:
% 0.38/0.57         (~ (v2_funct_1 @ X11)
% 0.38/0.57          | ((k2_funct_1 @ X11) = (k4_relat_1 @ X11))
% 0.38/0.57          | ~ (v1_funct_1 @ X11)
% 0.38/0.57          | ~ (v1_relat_1 @ X11))),
% 0.38/0.57      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.38/0.57  thf('47', plain,
% 0.38/0.57      ((((sk_A)
% 0.38/0.57          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))
% 0.38/0.57        | ((sk_A)
% 0.38/0.57            != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('48', plain,
% 0.38/0.57      ((((sk_A)
% 0.38/0.57          != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))
% 0.38/0.57         <= (~
% 0.38/0.57             (((sk_A)
% 0.38/0.57                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.38/0.57                   sk_A))))),
% 0.38/0.57      inference('split', [status(esa)], ['47'])).
% 0.38/0.57  thf('49', plain,
% 0.38/0.57      (((((sk_A)
% 0.38/0.57           != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A))
% 0.38/0.57         | ~ (v1_relat_1 @ sk_B)
% 0.38/0.57         | ~ (v1_funct_1 @ sk_B)
% 0.38/0.57         | ~ (v2_funct_1 @ sk_B)))
% 0.38/0.57         <= (~
% 0.38/0.57             (((sk_A)
% 0.38/0.57                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.38/0.57                   sk_A))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['46', '48'])).
% 0.38/0.57  thf('50', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('51', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('52', plain, ((v2_funct_1 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('53', plain,
% 0.38/0.57      ((((sk_A)
% 0.38/0.57          != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A)))
% 0.38/0.57         <= (~
% 0.38/0.57             (((sk_A)
% 0.38/0.57                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.38/0.57                   sk_A))))),
% 0.38/0.57      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 0.38/0.57  thf('54', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('55', plain,
% 0.38/0.57      (![X2 : $i, X4 : $i]:
% 0.38/0.57         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X4 @ X2) @ X4) @ X2)
% 0.38/0.57          | ~ (r2_hidden @ X4 @ (k2_relat_1 @ X2)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['14'])).
% 0.38/0.57  thf('56', plain,
% 0.38/0.57      ((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_A @ sk_B) @ sk_A) @ sk_B)),
% 0.38/0.57      inference('sup-', [status(thm)], ['54', '55'])).
% 0.38/0.57  thf(t20_relat_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( v1_relat_1 @ C ) =>
% 0.38/0.57       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.38/0.57         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.38/0.57           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.38/0.57  thf('57', plain,
% 0.38/0.57      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.38/0.57         (~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ X9)
% 0.38/0.57          | (r2_hidden @ X7 @ (k1_relat_1 @ X9))
% 0.38/0.57          | ~ (v1_relat_1 @ X9))),
% 0.38/0.57      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.38/0.57  thf('58', plain,
% 0.38/0.57      ((~ (v1_relat_1 @ sk_B)
% 0.38/0.57        | (r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['56', '57'])).
% 0.38/0.57  thf('59', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('60', plain,
% 0.38/0.57      ((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B))),
% 0.38/0.57      inference('demod', [status(thm)], ['58', '59'])).
% 0.38/0.57  thf(t56_funct_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.57       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) ) =>
% 0.38/0.57         ( ( ( A ) =
% 0.38/0.57             ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) ) & 
% 0.38/0.57           ( ( A ) =
% 0.38/0.57             ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ))).
% 0.38/0.57  thf('61', plain,
% 0.38/0.57      (![X16 : $i, X17 : $i]:
% 0.38/0.57         (~ (v2_funct_1 @ X16)
% 0.38/0.57          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ X16))
% 0.38/0.57          | ((X17)
% 0.38/0.57              = (k1_funct_1 @ (k2_funct_1 @ X16) @ (k1_funct_1 @ X16 @ X17)))
% 0.38/0.57          | ~ (v1_funct_1 @ X16)
% 0.38/0.57          | ~ (v1_relat_1 @ X16))),
% 0.38/0.57      inference('cnf', [status(esa)], [t56_funct_1])).
% 0.38/0.57  thf('62', plain,
% 0.38/0.57      ((~ (v1_relat_1 @ sk_B)
% 0.38/0.57        | ~ (v1_funct_1 @ sk_B)
% 0.38/0.57        | ((sk_D_1 @ sk_A @ sk_B)
% 0.38/0.57            = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ 
% 0.38/0.57               (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B))))
% 0.38/0.57        | ~ (v2_funct_1 @ sk_B))),
% 0.38/0.57      inference('sup-', [status(thm)], ['60', '61'])).
% 0.38/0.57  thf('63', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('64', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('65', plain,
% 0.38/0.57      ((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_A @ sk_B) @ sk_A) @ sk_B)),
% 0.38/0.57      inference('sup-', [status(thm)], ['54', '55'])).
% 0.38/0.57  thf(t8_funct_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.38/0.57       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.38/0.57         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.38/0.57           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.38/0.57  thf('66', plain,
% 0.38/0.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.38/0.57         (~ (r2_hidden @ (k4_tarski @ X18 @ X20) @ X19)
% 0.38/0.57          | ((X20) = (k1_funct_1 @ X19 @ X18))
% 0.38/0.57          | ~ (v1_funct_1 @ X19)
% 0.38/0.57          | ~ (v1_relat_1 @ X19))),
% 0.38/0.57      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.38/0.57  thf('67', plain,
% 0.38/0.57      ((~ (v1_relat_1 @ sk_B)
% 0.38/0.57        | ~ (v1_funct_1 @ sk_B)
% 0.38/0.57        | ((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['65', '66'])).
% 0.38/0.57  thf('68', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('69', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('70', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))),
% 0.38/0.57      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.38/0.57  thf('71', plain, ((v2_funct_1 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('72', plain,
% 0.38/0.57      (((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['62', '63', '64', '70', '71'])).
% 0.38/0.57  thf('73', plain,
% 0.38/0.57      ((((sk_A)
% 0.38/0.57          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))
% 0.38/0.57         <= (~
% 0.38/0.57             (((sk_A)
% 0.38/0.57                = (k1_funct_1 @ sk_B @ 
% 0.38/0.57                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.38/0.57      inference('split', [status(esa)], ['47'])).
% 0.38/0.57  thf('74', plain,
% 0.38/0.57      ((((sk_A) != (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B))))
% 0.38/0.57         <= (~
% 0.38/0.57             (((sk_A)
% 0.38/0.57                = (k1_funct_1 @ sk_B @ 
% 0.38/0.57                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['72', '73'])).
% 0.38/0.57  thf('75', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))),
% 0.38/0.57      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.38/0.57  thf('76', plain,
% 0.38/0.57      ((((sk_A) != (sk_A)))
% 0.38/0.57         <= (~
% 0.38/0.57             (((sk_A)
% 0.38/0.57                = (k1_funct_1 @ sk_B @ 
% 0.38/0.57                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.38/0.57      inference('demod', [status(thm)], ['74', '75'])).
% 0.38/0.57  thf('77', plain,
% 0.38/0.57      ((((sk_A)
% 0.38/0.57          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.38/0.57      inference('simplify', [status(thm)], ['76'])).
% 0.38/0.57  thf('78', plain,
% 0.38/0.57      (~
% 0.38/0.57       (((sk_A)
% 0.38/0.57          = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A))) | 
% 0.38/0.57       ~
% 0.38/0.57       (((sk_A)
% 0.38/0.57          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.38/0.57      inference('split', [status(esa)], ['47'])).
% 0.38/0.57  thf('79', plain,
% 0.38/0.57      (~
% 0.38/0.57       (((sk_A)
% 0.38/0.57          = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 0.38/0.57      inference('sat_resolution*', [status(thm)], ['77', '78'])).
% 0.38/0.57  thf('80', plain,
% 0.38/0.57      (((sk_A)
% 0.38/0.57         != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A))),
% 0.38/0.57      inference('simpl_trail', [status(thm)], ['53', '79'])).
% 0.38/0.57  thf('81', plain,
% 0.38/0.57      ((((sk_A)
% 0.38/0.57          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))
% 0.38/0.57        | ~ (v1_relat_1 @ sk_B)
% 0.38/0.57        | ~ (v1_funct_1 @ sk_B))),
% 0.38/0.57      inference('sup-', [status(thm)], ['45', '80'])).
% 0.38/0.57  thf('82', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))),
% 0.38/0.57      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.38/0.57  thf('83', plain,
% 0.38/0.57      (![X11 : $i]:
% 0.38/0.57         (~ (v2_funct_1 @ X11)
% 0.38/0.57          | ((k2_funct_1 @ X11) = (k4_relat_1 @ X11))
% 0.38/0.57          | ~ (v1_funct_1 @ X11)
% 0.38/0.57          | ~ (v1_relat_1 @ X11))),
% 0.38/0.57      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.38/0.57  thf('84', plain,
% 0.38/0.57      (((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['62', '63', '64', '70', '71'])).
% 0.38/0.57  thf('85', plain,
% 0.38/0.57      ((((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))
% 0.38/0.57        | ~ (v1_relat_1 @ sk_B)
% 0.38/0.57        | ~ (v1_funct_1 @ sk_B)
% 0.38/0.57        | ~ (v2_funct_1 @ sk_B))),
% 0.38/0.57      inference('sup+', [status(thm)], ['83', '84'])).
% 0.38/0.57  thf('86', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('87', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('88', plain, ((v2_funct_1 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('89', plain,
% 0.38/0.57      (((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['85', '86', '87', '88'])).
% 0.38/0.57  thf('90', plain,
% 0.38/0.57      (((sk_A)
% 0.38/0.57         = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))),
% 0.38/0.57      inference('demod', [status(thm)], ['82', '89'])).
% 0.38/0.57  thf('91', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('92', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('93', plain, (((sk_A) != (sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['81', '90', '91', '92'])).
% 0.38/0.57  thf('94', plain, ($false), inference('simplify', [status(thm)], ['93'])).
% 0.38/0.57  
% 0.38/0.57  % SZS output end Refutation
% 0.38/0.57  
% 0.38/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
