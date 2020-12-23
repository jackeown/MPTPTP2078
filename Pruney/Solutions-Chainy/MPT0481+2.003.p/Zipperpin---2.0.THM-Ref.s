%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nVGrcscVO4

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:57 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 (  80 expanded)
%              Number of leaves         :   16 (  29 expanded)
%              Depth                    :   16
%              Number of atoms          :  635 ( 849 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf(t75_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( v1_relat_1 @ D )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k5_relat_1 @ D @ ( k6_relat_1 @ C ) ) )
      <=> ( ( r2_hidden @ B @ C )
          & ( r2_hidden @ ( k4_tarski @ A @ B ) @ D ) ) ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X14 @ X12 ) @ ( k5_relat_1 @ X15 @ ( k6_relat_1 @ X13 ) ) )
      | ( r2_hidden @ ( k4_tarski @ X14 @ X12 ) @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t75_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('6',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X0 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf('13',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t76_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
          & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_relat_1])).

thf('16',plain,
    ( ~ ( r1_tarski @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) @ sk_B )
    | ~ ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( r1_tarski @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) @ sk_B )
   <= ~ ( r1_tarski @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) @ sk_B ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('19',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf(t74_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( v1_relat_1 @ D )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k5_relat_1 @ ( k6_relat_1 @ C ) @ D ) )
      <=> ( ( r2_hidden @ A @ C )
          & ( r2_hidden @ ( k4_tarski @ A @ B ) @ D ) ) ) ) )).

thf('21',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X8 @ X10 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X9 ) @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ X8 @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t74_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ ( sk_D @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ ( sk_D @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ ( sk_D @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ ( sk_D @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X0 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','29'])).

thf('31',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ~ ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ sk_B )
   <= ~ ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['16'])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ sk_B )
   <= ~ ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( r1_tarski @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) @ sk_B )
    | ~ ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['16'])).

thf('39',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['17','39'])).

thf('41',plain,(
    ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['15','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    $false ),
    inference(demod,[status(thm)],['41','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nVGrcscVO4
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:54:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 45 iterations in 0.044s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.49  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.20/0.49  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.49  thf(dt_k5_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.20/0.49       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X5)
% 0.20/0.49          | ~ (v1_relat_1 @ X6)
% 0.20/0.49          | (v1_relat_1 @ (k5_relat_1 @ X5 @ X6)))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X5)
% 0.20/0.49          | ~ (v1_relat_1 @ X6)
% 0.20/0.49          | (v1_relat_1 @ (k5_relat_1 @ X5 @ X6)))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.20/0.49  thf(d3_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.49           ( ![C:$i,D:$i]:
% 0.20/0.49             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 0.20/0.49               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ X1)
% 0.20/0.49          | (r1_tarski @ X1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.20/0.49  thf(t75_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ D ) =>
% 0.20/0.49       ( ( r2_hidden @
% 0.20/0.49           ( k4_tarski @ A @ B ) @ ( k5_relat_1 @ D @ ( k6_relat_1 @ C ) ) ) <=>
% 0.20/0.49         ( ( r2_hidden @ B @ C ) & ( r2_hidden @ ( k4_tarski @ A @ B ) @ D ) ) ) ))).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.49         (~ (r2_hidden @ (k4_tarski @ X14 @ X12) @ 
% 0.20/0.49             (k5_relat_1 @ X15 @ (k6_relat_1 @ X13)))
% 0.20/0.49          | (r2_hidden @ (k4_tarski @ X14 @ X12) @ X15)
% 0.20/0.49          | ~ (v1_relat_1 @ X15))),
% 0.20/0.49      inference('cnf', [status(esa)], [t75_relat_1])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.20/0.49          | (r1_tarski @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 0.20/0.49          | ~ (v1_relat_1 @ X1)
% 0.20/0.49          | (r2_hidden @ 
% 0.20/0.49             (k4_tarski @ 
% 0.20/0.49              (sk_C @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.20/0.49              (sk_D @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))) @ 
% 0.20/0.49             X1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.49          | ~ (v1_relat_1 @ X1)
% 0.20/0.49          | (r2_hidden @ 
% 0.20/0.49             (k4_tarski @ 
% 0.20/0.49              (sk_C @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.20/0.49              (sk_D @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))) @ 
% 0.20/0.49             X1)
% 0.20/0.49          | ~ (v1_relat_1 @ X1)
% 0.20/0.49          | (r1_tarski @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '4'])).
% 0.20/0.49  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.20/0.49  thf('6', plain, (![X7 : $i]: (v1_relat_1 @ (k6_relat_1 @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X1)
% 0.20/0.49          | (r2_hidden @ 
% 0.20/0.49             (k4_tarski @ 
% 0.20/0.49              (sk_C @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.20/0.49              (sk_D @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))) @ 
% 0.20/0.49             X1)
% 0.20/0.49          | ~ (v1_relat_1 @ X1)
% 0.20/0.49          | (r1_tarski @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2))),
% 0.20/0.49      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         ((r1_tarski @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 0.20/0.49          | (r2_hidden @ 
% 0.20/0.49             (k4_tarski @ 
% 0.20/0.49              (sk_C @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.20/0.49              (sk_D @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))) @ 
% 0.20/0.49             X1)
% 0.20/0.49          | ~ (v1_relat_1 @ X1))),
% 0.20/0.49      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ X0)
% 0.20/0.49          | (r1_tarski @ X1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X0)
% 0.20/0.49          | (r1_tarski @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.20/0.49          | (r1_tarski @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.20/0.49          | (r1_tarski @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.49          | ~ (v1_relat_1 @ X1)
% 0.20/0.49          | ~ (v1_relat_1 @ X1)
% 0.20/0.49          | (r1_tarski @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '11'])).
% 0.20/0.49  thf('13', plain, (![X7 : $i]: (v1_relat_1 @ (k6_relat_1 @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X1)
% 0.20/0.49          | ~ (v1_relat_1 @ X1)
% 0.20/0.49          | (r1_tarski @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X1))),
% 0.20/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((r1_tarski @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X1)
% 0.20/0.49          | ~ (v1_relat_1 @ X1))),
% 0.20/0.49      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.49  thf(t76_relat_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) =>
% 0.20/0.49       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 0.20/0.49         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i]:
% 0.20/0.49        ( ( v1_relat_1 @ B ) =>
% 0.20/0.49          ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 0.20/0.49            ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t76_relat_1])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      ((~ (r1_tarski @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)) @ sk_B)
% 0.20/0.49        | ~ (r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      ((~ (r1_tarski @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)) @ sk_B))
% 0.20/0.49         <= (~ ((r1_tarski @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)) @ sk_B)))),
% 0.20/0.49      inference('split', [status(esa)], ['16'])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X5)
% 0.20/0.49          | ~ (v1_relat_1 @ X6)
% 0.20/0.49          | (v1_relat_1 @ (k5_relat_1 @ X5 @ X6)))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X5)
% 0.20/0.49          | ~ (v1_relat_1 @ X6)
% 0.20/0.49          | (v1_relat_1 @ (k5_relat_1 @ X5 @ X6)))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ X1)
% 0.20/0.49          | (r1_tarski @ X1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.20/0.49  thf(t74_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ D ) =>
% 0.20/0.49       ( ( r2_hidden @
% 0.20/0.49           ( k4_tarski @ A @ B ) @ ( k5_relat_1 @ ( k6_relat_1 @ C ) @ D ) ) <=>
% 0.20/0.49         ( ( r2_hidden @ A @ C ) & ( r2_hidden @ ( k4_tarski @ A @ B ) @ D ) ) ) ))).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.49         (~ (r2_hidden @ (k4_tarski @ X8 @ X10) @ 
% 0.20/0.49             (k5_relat_1 @ (k6_relat_1 @ X9) @ X11))
% 0.20/0.49          | (r2_hidden @ (k4_tarski @ X8 @ X10) @ X11)
% 0.20/0.49          | ~ (v1_relat_1 @ X11))),
% 0.20/0.49      inference('cnf', [status(esa)], [t74_relat_1])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.20/0.49          | (r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 0.20/0.49          | ~ (v1_relat_1 @ X0)
% 0.20/0.49          | (r2_hidden @ 
% 0.20/0.49             (k4_tarski @ 
% 0.20/0.49              (sk_C @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 0.20/0.49              (sk_D @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 0.20/0.49             X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.20/0.49          | (r2_hidden @ 
% 0.20/0.49             (k4_tarski @ 
% 0.20/0.49              (sk_C @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 0.20/0.49              (sk_D @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 0.20/0.49             X0)
% 0.20/0.49          | ~ (v1_relat_1 @ X0)
% 0.20/0.49          | (r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2))),
% 0.20/0.49      inference('sup-', [status(thm)], ['19', '22'])).
% 0.20/0.49  thf('24', plain, (![X7 : $i]: (v1_relat_1 @ (k6_relat_1 @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X0)
% 0.20/0.49          | (r2_hidden @ 
% 0.20/0.49             (k4_tarski @ 
% 0.20/0.49              (sk_C @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 0.20/0.49              (sk_D @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 0.20/0.49             X0)
% 0.20/0.49          | ~ (v1_relat_1 @ X0)
% 0.20/0.49          | (r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2))),
% 0.20/0.49      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         ((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 0.20/0.49          | (r2_hidden @ 
% 0.20/0.49             (k4_tarski @ 
% 0.20/0.49              (sk_C @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 0.20/0.49              (sk_D @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 0.20/0.49             X0)
% 0.20/0.49          | ~ (v1_relat_1 @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ X0)
% 0.20/0.49          | (r1_tarski @ X1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X0)
% 0.20/0.49          | (r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.20/0.49          | (r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.20/0.49          | (r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.20/0.49          | ~ (v1_relat_1 @ X0)
% 0.20/0.49          | (r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['18', '29'])).
% 0.20/0.49  thf('31', plain, (![X7 : $i]: (v1_relat_1 @ (k6_relat_1 @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ X0)
% 0.20/0.49          | (r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      ((~ (r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ sk_B))
% 0.20/0.49         <= (~ ((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ sk_B)))),
% 0.20/0.49      inference('split', [status(esa)], ['16'])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ sk_B))
% 0.20/0.49         <= (~ ((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.49  thf('36', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      (((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (~ ((r1_tarski @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)) @ sk_B)) | 
% 0.20/0.49       ~ ((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ sk_B))),
% 0.20/0.49      inference('split', [status(esa)], ['16'])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      (~ ((r1_tarski @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)) @ sk_B))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['37', '38'])).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      (~ (r1_tarski @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)) @ sk_B)),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['17', '39'])).
% 0.20/0.49  thf('41', plain, (~ (v1_relat_1 @ sk_B)),
% 0.20/0.49      inference('sup-', [status(thm)], ['15', '40'])).
% 0.20/0.49  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('43', plain, ($false), inference('demod', [status(thm)], ['41', '42'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
