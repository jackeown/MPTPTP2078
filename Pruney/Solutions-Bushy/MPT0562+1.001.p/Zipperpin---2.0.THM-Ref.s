%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0562+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oE2ByXkF3u

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 115 expanded)
%              Number of leaves         :   13 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :  671 (1589 expanded)
%              Number of equality atoms :    6 (  10 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(t166_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ B )
              & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
              & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t166_relat_1])).

thf('0',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_D_3 ) @ sk_C_1 )
    | ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_D_3 ) @ sk_C_1 )
    | ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( r2_hidden @ sk_D_3 @ sk_B )
    | ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf(d14_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k10_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ B )
                  & ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X1: $i,X2: $i,X4: $i,X5: $i] :
      ( ( X4
       != ( k10_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ X5 @ ( sk_E_1 @ X5 @ X1 @ X2 ) ) @ X2 )
      | ~ ( r2_hidden @ X5 @ X4 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('7',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ X5 @ ( k10_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ X5 @ ( sk_E_1 @ X5 @ X1 @ X2 ) ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_E_1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_E_1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 )
   <= ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X10 )
      | ( r2_hidden @ X9 @ X11 )
      | ( X11
       != ( k2_relat_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('12',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ ( k2_relat_1 @ X10 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X10 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( r2_hidden @ ( sk_E_1 @ sk_A @ sk_B @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_E_1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 )
   <= ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('15',plain,(
    ! [X15: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X15 ) @ sk_C_1 )
      | ~ ( r2_hidden @ X15 @ sk_B )
      | ~ ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ! [X15: $i] :
        ( ~ ( r2_hidden @ X15 @ ( k2_relat_1 @ sk_C_1 ) )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X15 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X15 @ sk_B ) )
   <= ! [X15: $i] :
        ( ~ ( r2_hidden @ X15 @ ( k2_relat_1 @ sk_C_1 ) )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X15 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X15 @ sk_B ) ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,
    ( ( ~ ( r2_hidden @ ( sk_E_1 @ sk_A @ sk_B @ sk_C_1 ) @ sk_B )
      | ~ ( r2_hidden @ ( sk_E_1 @ sk_A @ sk_B @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) ) )
   <= ( ! [X15: $i] :
          ( ~ ( r2_hidden @ X15 @ ( k2_relat_1 @ sk_C_1 ) )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X15 ) @ sk_C_1 )
          | ~ ( r2_hidden @ X15 @ sk_B ) )
      & ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,
    ( ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf('19',plain,(
    ! [X1: $i,X2: $i,X4: $i,X5: $i] :
      ( ( X4
       != ( k10_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( sk_E_1 @ X5 @ X1 @ X2 ) @ X1 )
      | ~ ( r2_hidden @ X5 @ X4 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('20',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ X5 @ ( k10_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( sk_E_1 @ X5 @ X1 @ X2 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( ( r2_hidden @ ( sk_E_1 @ sk_A @ sk_B @ sk_C_1 ) @ sk_B )
      | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( r2_hidden @ ( sk_E_1 @ sk_A @ sk_B @ sk_C_1 ) @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( r2_hidden @ ( sk_E_1 @ sk_A @ sk_B @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( ! [X15: $i] :
          ( ~ ( r2_hidden @ X15 @ ( k2_relat_1 @ sk_C_1 ) )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X15 ) @ sk_C_1 )
          | ~ ( r2_hidden @ X15 @ sk_B ) )
      & ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['17','23'])).

thf('25',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C_1 @ sk_B ) )
    | ~ ! [X15: $i] :
          ( ~ ( r2_hidden @ X15 @ ( k2_relat_1 @ sk_C_1 ) )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X15 ) @ sk_C_1 )
          | ~ ( r2_hidden @ X15 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','24'])).

thf('26',plain,
    ( ( r2_hidden @ sk_D_3 @ sk_B )
   <= ( r2_hidden @ sk_D_3 @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('27',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_3 @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('28',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_D_3 ) @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_D_3 ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,
    ( ! [X15: $i] :
        ( ~ ( r2_hidden @ X15 @ ( k2_relat_1 @ sk_C_1 ) )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X15 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X15 @ sk_B ) )
   <= ! [X15: $i] :
        ( ~ ( r2_hidden @ X15 @ ( k2_relat_1 @ sk_C_1 ) )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X15 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X15 @ sk_B ) ) ),
    inference(split,[status(esa)],['15'])).

thf('30',plain,
    ( ( ~ ( r2_hidden @ sk_D_3 @ sk_B )
      | ~ ( r2_hidden @ sk_D_3 @ ( k2_relat_1 @ sk_C_1 ) ) )
   <= ( ! [X15: $i] :
          ( ~ ( r2_hidden @ X15 @ ( k2_relat_1 @ sk_C_1 ) )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X15 ) @ sk_C_1 )
          | ~ ( r2_hidden @ X15 @ sk_B ) )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_D_3 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( r2_hidden @ sk_D_3 @ sk_B )
   <= ( ! [X15: $i] :
          ( ~ ( r2_hidden @ X15 @ ( k2_relat_1 @ sk_C_1 ) )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X15 ) @ sk_C_1 )
          | ~ ( r2_hidden @ X15 @ sk_B ) )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_D_3 ) @ sk_C_1 )
      & ( r2_hidden @ sk_D_3 @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_D_3 ) @ sk_C_1 )
    | ~ ! [X15: $i] :
          ( ~ ( r2_hidden @ X15 @ ( k2_relat_1 @ sk_C_1 ) )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X15 ) @ sk_C_1 )
          | ~ ( r2_hidden @ X15 @ sk_B ) )
    | ~ ( r2_hidden @ sk_D_3 @ ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_D_3 @ sk_B ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C_1 @ sk_B ) )
    | ! [X15: $i] :
        ( ~ ( r2_hidden @ X15 @ ( k2_relat_1 @ sk_C_1 ) )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X15 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X15 @ sk_B ) ) ),
    inference(split,[status(esa)],['15'])).

thf('34',plain,
    ( ( r2_hidden @ sk_D_3 @ sk_B )
    | ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf('35',plain,
    ( ( r2_hidden @ sk_D_3 @ sk_B )
   <= ( r2_hidden @ sk_D_3 @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('36',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_D_3 ) @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_D_3 ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,(
    ! [X1: $i,X2: $i,X4: $i,X6: $i,X7: $i] :
      ( ( X4
       != ( k10_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X7 ) @ X2 )
      | ~ ( r2_hidden @ X7 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('38',plain,(
    ! [X1: $i,X2: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ X7 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X7 ) @ X2 )
      | ( r2_hidden @ X6 @ ( k10_relat_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_D_3 @ X0 )
        | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_D_3 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_D_3 @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_D_3 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C_1 @ sk_B ) )
   <= ( ( r2_hidden @ sk_D_3 @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_D_3 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['35','41'])).

thf('43',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['15'])).

thf('44',plain,
    ( ~ ( r2_hidden @ sk_D_3 @ sk_B )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_D_3 ) @ sk_C_1 )
    | ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','25','32','33','34','44'])).


%------------------------------------------------------------------------------
