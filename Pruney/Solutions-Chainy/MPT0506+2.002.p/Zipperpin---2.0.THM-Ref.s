%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YSW25jJ8Rq

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:20 EST 2020

% Result     : Theorem 11.05s
% Output     : Refutation 11.05s
% Verified   : 
% Statistics : Number of formulae       :   57 (  69 expanded)
%              Number of leaves         :   15 (  25 expanded)
%              Depth                    :   17
%              Number of atoms          :  717 ( 863 expanded)
%              Number of equality atoms :    7 (   9 expanded)
%              Maximal formula depth    :   16 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X6 @ X7 ) @ ( sk_D_1 @ X6 @ X7 ) ) @ X7 )
      | ( r1_tarski @ X7 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t104_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( r1_tarski @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t104_relat_1])).

thf('3',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t102_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = ( k7_relat_1 @ C @ A ) ) ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X15 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X15 @ X13 ) @ X14 )
        = ( k7_relat_1 @ X15 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t102_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) @ sk_B )
        = ( k7_relat_1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( C
              = ( k7_relat_1 @ A @ B ) )
          <=> ! [D: $i,E: $i] :
                ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
              <=> ( ( r2_hidden @ D @ B )
                  & ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
       != ( k7_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ X3 @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d11_relat_1])).

thf('7',plain,(
    ! [X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k7_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ X3 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k7_relat_1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) @ sk_B ) )
      | ( r2_hidden @ X2 @ sk_B )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ ( k7_relat_1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ ( k7_relat_1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ sk_A ) @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k7_relat_1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k7_relat_1 @ X0 @ sk_A ) ) @ sk_B )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ sk_A ) @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ sk_A ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k7_relat_1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k7_relat_1 @ X0 @ sk_A ) ) @ sk_B )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ sk_A ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('16',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X6 @ X7 ) @ ( sk_D_1 @ X6 @ X7 ) ) @ X7 )
      | ( r1_tarski @ X7 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
       != ( k7_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d11_relat_1])).

thf('18',plain,(
    ! [X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k7_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ X1 )
      | ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ X1 )
      | ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
       != ( k7_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d11_relat_1])).

thf('25',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ ( k7_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ X1 )
      | ~ ( r2_hidden @ X3 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( sk_D_1 @ X2 @ ( k7_relat_1 @ X0 @ X1 ) ) ) @ ( k7_relat_1 @ X0 @ X3 ) )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k7_relat_1 @ X0 @ X1 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X2 @ ( k7_relat_1 @ X0 @ X1 ) ) @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( sk_D_1 @ X2 @ ( k7_relat_1 @ X0 @ X1 ) ) ) @ ( k7_relat_1 @ X0 @ X3 ) )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ sk_A ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ sk_A ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k7_relat_1 @ X0 @ sk_A ) ) @ ( sk_D_1 @ X1 @ ( k7_relat_1 @ X0 @ sk_A ) ) ) @ ( k7_relat_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['14','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k7_relat_1 @ X0 @ sk_A ) ) @ ( sk_D_1 @ X1 @ ( k7_relat_1 @ X0 @ sk_A ) ) ) @ ( k7_relat_1 @ X0 @ sk_B ) )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ sk_A ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X6 @ X7 ) @ ( sk_D_1 @ X6 @ X7 ) ) @ X6 )
      | ( r1_tarski @ X7 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ sk_A ) @ ( k7_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ sk_A ) @ ( k7_relat_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ sk_A ) @ ( k7_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ sk_A ) @ ( k7_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( r1_tarski @ ( k7_relat_1 @ sk_C_1 @ sk_A ) @ ( k7_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['38','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YSW25jJ8Rq
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % DateTime   : Tue Dec  1 16:01:52 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 11.05/11.23  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 11.05/11.23  % Solved by: fo/fo7.sh
% 11.05/11.23  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 11.05/11.23  % done 3981 iterations in 10.771s
% 11.05/11.23  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 11.05/11.23  % SZS output start Refutation
% 11.05/11.23  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 11.05/11.23  thf(sk_B_type, type, sk_B: $i).
% 11.05/11.23  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 11.05/11.23  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 11.05/11.23  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 11.05/11.23  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 11.05/11.23  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 11.05/11.23  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 11.05/11.23  thf(sk_C_1_type, type, sk_C_1: $i).
% 11.05/11.23  thf(sk_A_type, type, sk_A: $i).
% 11.05/11.23  thf(dt_k7_relat_1, axiom,
% 11.05/11.23    (![A:$i,B:$i]:
% 11.05/11.23     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 11.05/11.23  thf('0', plain,
% 11.05/11.23      (![X11 : $i, X12 : $i]:
% 11.05/11.23         (~ (v1_relat_1 @ X11) | (v1_relat_1 @ (k7_relat_1 @ X11 @ X12)))),
% 11.05/11.23      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 11.05/11.23  thf(d3_relat_1, axiom,
% 11.05/11.23    (![A:$i]:
% 11.05/11.23     ( ( v1_relat_1 @ A ) =>
% 11.05/11.23       ( ![B:$i]:
% 11.05/11.23         ( ( r1_tarski @ A @ B ) <=>
% 11.05/11.23           ( ![C:$i,D:$i]:
% 11.05/11.23             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 11.05/11.23               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 11.05/11.23  thf('1', plain,
% 11.05/11.23      (![X6 : $i, X7 : $i]:
% 11.05/11.23         ((r2_hidden @ (k4_tarski @ (sk_C @ X6 @ X7) @ (sk_D_1 @ X6 @ X7)) @ X7)
% 11.05/11.23          | (r1_tarski @ X7 @ X6)
% 11.05/11.23          | ~ (v1_relat_1 @ X7))),
% 11.05/11.23      inference('cnf', [status(esa)], [d3_relat_1])).
% 11.05/11.23  thf('2', plain,
% 11.05/11.23      (![X11 : $i, X12 : $i]:
% 11.05/11.23         (~ (v1_relat_1 @ X11) | (v1_relat_1 @ (k7_relat_1 @ X11 @ X12)))),
% 11.05/11.23      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 11.05/11.23  thf(t104_relat_1, conjecture,
% 11.05/11.23    (![A:$i,B:$i,C:$i]:
% 11.05/11.23     ( ( v1_relat_1 @ C ) =>
% 11.05/11.23       ( ( r1_tarski @ A @ B ) =>
% 11.05/11.23         ( r1_tarski @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ C @ B ) ) ) ))).
% 11.05/11.23  thf(zf_stmt_0, negated_conjecture,
% 11.05/11.23    (~( ![A:$i,B:$i,C:$i]:
% 11.05/11.23        ( ( v1_relat_1 @ C ) =>
% 11.05/11.23          ( ( r1_tarski @ A @ B ) =>
% 11.05/11.23            ( r1_tarski @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ C @ B ) ) ) ) )),
% 11.05/11.23    inference('cnf.neg', [status(esa)], [t104_relat_1])).
% 11.05/11.23  thf('3', plain, ((r1_tarski @ sk_A @ sk_B)),
% 11.05/11.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.05/11.23  thf(t102_relat_1, axiom,
% 11.05/11.23    (![A:$i,B:$i,C:$i]:
% 11.05/11.23     ( ( v1_relat_1 @ C ) =>
% 11.05/11.23       ( ( r1_tarski @ A @ B ) =>
% 11.05/11.23         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k7_relat_1 @ C @ A ) ) ) ))).
% 11.05/11.23  thf('4', plain,
% 11.05/11.23      (![X13 : $i, X14 : $i, X15 : $i]:
% 11.05/11.23         (~ (r1_tarski @ X13 @ X14)
% 11.05/11.23          | ~ (v1_relat_1 @ X15)
% 11.05/11.23          | ((k7_relat_1 @ (k7_relat_1 @ X15 @ X13) @ X14)
% 11.05/11.23              = (k7_relat_1 @ X15 @ X13)))),
% 11.05/11.23      inference('cnf', [status(esa)], [t102_relat_1])).
% 11.05/11.23  thf('5', plain,
% 11.05/11.23      (![X0 : $i]:
% 11.05/11.23         (((k7_relat_1 @ (k7_relat_1 @ X0 @ sk_A) @ sk_B)
% 11.05/11.23            = (k7_relat_1 @ X0 @ sk_A))
% 11.05/11.23          | ~ (v1_relat_1 @ X0))),
% 11.05/11.23      inference('sup-', [status(thm)], ['3', '4'])).
% 11.05/11.23  thf(d11_relat_1, axiom,
% 11.05/11.23    (![A:$i]:
% 11.05/11.23     ( ( v1_relat_1 @ A ) =>
% 11.05/11.23       ( ![B:$i,C:$i]:
% 11.05/11.23         ( ( v1_relat_1 @ C ) =>
% 11.05/11.23           ( ( ( C ) = ( k7_relat_1 @ A @ B ) ) <=>
% 11.05/11.23             ( ![D:$i,E:$i]:
% 11.05/11.23               ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 11.05/11.23                 ( ( r2_hidden @ D @ B ) & 
% 11.05/11.23                   ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) ) ) ))).
% 11.05/11.23  thf('6', plain,
% 11.05/11.23      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 11.05/11.23         (~ (v1_relat_1 @ X0)
% 11.05/11.23          | ((X0) != (k7_relat_1 @ X1 @ X2))
% 11.05/11.23          | (r2_hidden @ X3 @ X2)
% 11.05/11.23          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ X0)
% 11.05/11.23          | ~ (v1_relat_1 @ X1))),
% 11.05/11.23      inference('cnf', [status(esa)], [d11_relat_1])).
% 11.05/11.23  thf('7', plain,
% 11.05/11.23      (![X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 11.05/11.23         (~ (v1_relat_1 @ X1)
% 11.05/11.23          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (k7_relat_1 @ X1 @ X2))
% 11.05/11.23          | (r2_hidden @ X3 @ X2)
% 11.05/11.23          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2)))),
% 11.05/11.23      inference('simplify', [status(thm)], ['6'])).
% 11.05/11.23  thf('8', plain,
% 11.05/11.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.05/11.23         (~ (r2_hidden @ (k4_tarski @ X2 @ X1) @ (k7_relat_1 @ X0 @ sk_A))
% 11.05/11.23          | ~ (v1_relat_1 @ X0)
% 11.05/11.23          | ~ (v1_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X0 @ sk_A) @ sk_B))
% 11.05/11.23          | (r2_hidden @ X2 @ sk_B)
% 11.05/11.23          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ sk_A)))),
% 11.05/11.23      inference('sup-', [status(thm)], ['5', '7'])).
% 11.05/11.23  thf('9', plain,
% 11.05/11.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.05/11.23         (~ (v1_relat_1 @ (k7_relat_1 @ X0 @ sk_A))
% 11.05/11.23          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ sk_A))
% 11.05/11.23          | (r2_hidden @ X1 @ sk_B)
% 11.05/11.23          | ~ (v1_relat_1 @ X0)
% 11.05/11.23          | ~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ (k7_relat_1 @ X0 @ sk_A)))),
% 11.05/11.23      inference('sup-', [status(thm)], ['2', '8'])).
% 11.05/11.23  thf('10', plain,
% 11.05/11.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.05/11.23         (~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ (k7_relat_1 @ X0 @ sk_A))
% 11.05/11.23          | ~ (v1_relat_1 @ X0)
% 11.05/11.23          | (r2_hidden @ X1 @ sk_B)
% 11.05/11.23          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ sk_A)))),
% 11.05/11.23      inference('simplify', [status(thm)], ['9'])).
% 11.05/11.23  thf('11', plain,
% 11.05/11.23      (![X0 : $i, X1 : $i]:
% 11.05/11.23         (~ (v1_relat_1 @ (k7_relat_1 @ X0 @ sk_A))
% 11.05/11.23          | (r1_tarski @ (k7_relat_1 @ X0 @ sk_A) @ X1)
% 11.05/11.23          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ sk_A))
% 11.05/11.23          | (r2_hidden @ (sk_C @ X1 @ (k7_relat_1 @ X0 @ sk_A)) @ sk_B)
% 11.05/11.23          | ~ (v1_relat_1 @ X0))),
% 11.05/11.23      inference('sup-', [status(thm)], ['1', '10'])).
% 11.05/11.23  thf('12', plain,
% 11.05/11.23      (![X0 : $i, X1 : $i]:
% 11.05/11.23         (~ (v1_relat_1 @ X0)
% 11.05/11.23          | (r2_hidden @ (sk_C @ X1 @ (k7_relat_1 @ X0 @ sk_A)) @ sk_B)
% 11.05/11.23          | (r1_tarski @ (k7_relat_1 @ X0 @ sk_A) @ X1)
% 11.05/11.23          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ sk_A)))),
% 11.05/11.23      inference('simplify', [status(thm)], ['11'])).
% 11.05/11.23  thf('13', plain,
% 11.05/11.23      (![X0 : $i, X1 : $i]:
% 11.05/11.23         (~ (v1_relat_1 @ X0)
% 11.05/11.23          | (r1_tarski @ (k7_relat_1 @ X0 @ sk_A) @ X1)
% 11.05/11.23          | (r2_hidden @ (sk_C @ X1 @ (k7_relat_1 @ X0 @ sk_A)) @ sk_B)
% 11.05/11.23          | ~ (v1_relat_1 @ X0))),
% 11.05/11.23      inference('sup-', [status(thm)], ['0', '12'])).
% 11.05/11.23  thf('14', plain,
% 11.05/11.23      (![X0 : $i, X1 : $i]:
% 11.05/11.23         ((r2_hidden @ (sk_C @ X1 @ (k7_relat_1 @ X0 @ sk_A)) @ sk_B)
% 11.05/11.23          | (r1_tarski @ (k7_relat_1 @ X0 @ sk_A) @ X1)
% 11.05/11.23          | ~ (v1_relat_1 @ X0))),
% 11.05/11.23      inference('simplify', [status(thm)], ['13'])).
% 11.05/11.23  thf('15', plain,
% 11.05/11.23      (![X11 : $i, X12 : $i]:
% 11.05/11.23         (~ (v1_relat_1 @ X11) | (v1_relat_1 @ (k7_relat_1 @ X11 @ X12)))),
% 11.05/11.23      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 11.05/11.23  thf('16', plain,
% 11.05/11.23      (![X6 : $i, X7 : $i]:
% 11.05/11.23         ((r2_hidden @ (k4_tarski @ (sk_C @ X6 @ X7) @ (sk_D_1 @ X6 @ X7)) @ X7)
% 11.05/11.23          | (r1_tarski @ X7 @ X6)
% 11.05/11.23          | ~ (v1_relat_1 @ X7))),
% 11.05/11.23      inference('cnf', [status(esa)], [d3_relat_1])).
% 11.05/11.23  thf('17', plain,
% 11.05/11.23      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 11.05/11.23         (~ (v1_relat_1 @ X0)
% 11.05/11.23          | ((X0) != (k7_relat_1 @ X1 @ X2))
% 11.05/11.23          | (r2_hidden @ (k4_tarski @ X3 @ X5) @ X1)
% 11.05/11.23          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ X0)
% 11.05/11.23          | ~ (v1_relat_1 @ X1))),
% 11.05/11.23      inference('cnf', [status(esa)], [d11_relat_1])).
% 11.05/11.23  thf('18', plain,
% 11.05/11.23      (![X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 11.05/11.23         (~ (v1_relat_1 @ X1)
% 11.05/11.23          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (k7_relat_1 @ X1 @ X2))
% 11.05/11.23          | (r2_hidden @ (k4_tarski @ X3 @ X5) @ X1)
% 11.05/11.23          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2)))),
% 11.05/11.23      inference('simplify', [status(thm)], ['17'])).
% 11.05/11.23  thf('19', plain,
% 11.05/11.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.05/11.23         (~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 11.05/11.23          | (r1_tarski @ (k7_relat_1 @ X1 @ X0) @ X2)
% 11.05/11.23          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 11.05/11.23          | (r2_hidden @ 
% 11.05/11.23             (k4_tarski @ (sk_C @ X2 @ (k7_relat_1 @ X1 @ X0)) @ 
% 11.05/11.23              (sk_D_1 @ X2 @ (k7_relat_1 @ X1 @ X0))) @ 
% 11.05/11.23             X1)
% 11.05/11.23          | ~ (v1_relat_1 @ X1))),
% 11.05/11.23      inference('sup-', [status(thm)], ['16', '18'])).
% 11.05/11.23  thf('20', plain,
% 11.05/11.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.05/11.23         (~ (v1_relat_1 @ X1)
% 11.05/11.23          | (r2_hidden @ 
% 11.05/11.23             (k4_tarski @ (sk_C @ X2 @ (k7_relat_1 @ X1 @ X0)) @ 
% 11.05/11.23              (sk_D_1 @ X2 @ (k7_relat_1 @ X1 @ X0))) @ 
% 11.05/11.23             X1)
% 11.05/11.23          | (r1_tarski @ (k7_relat_1 @ X1 @ X0) @ X2)
% 11.05/11.23          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 11.05/11.23      inference('simplify', [status(thm)], ['19'])).
% 11.05/11.23  thf('21', plain,
% 11.05/11.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.05/11.23         (~ (v1_relat_1 @ X1)
% 11.05/11.23          | (r1_tarski @ (k7_relat_1 @ X1 @ X0) @ X2)
% 11.05/11.23          | (r2_hidden @ 
% 11.05/11.23             (k4_tarski @ (sk_C @ X2 @ (k7_relat_1 @ X1 @ X0)) @ 
% 11.05/11.23              (sk_D_1 @ X2 @ (k7_relat_1 @ X1 @ X0))) @ 
% 11.05/11.23             X1)
% 11.05/11.23          | ~ (v1_relat_1 @ X1))),
% 11.05/11.23      inference('sup-', [status(thm)], ['15', '20'])).
% 11.05/11.23  thf('22', plain,
% 11.05/11.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.05/11.23         ((r2_hidden @ 
% 11.05/11.23           (k4_tarski @ (sk_C @ X2 @ (k7_relat_1 @ X1 @ X0)) @ 
% 11.05/11.23            (sk_D_1 @ X2 @ (k7_relat_1 @ X1 @ X0))) @ 
% 11.05/11.23           X1)
% 11.05/11.23          | (r1_tarski @ (k7_relat_1 @ X1 @ X0) @ X2)
% 11.05/11.23          | ~ (v1_relat_1 @ X1))),
% 11.05/11.23      inference('simplify', [status(thm)], ['21'])).
% 11.05/11.23  thf('23', plain,
% 11.05/11.23      (![X11 : $i, X12 : $i]:
% 11.05/11.23         (~ (v1_relat_1 @ X11) | (v1_relat_1 @ (k7_relat_1 @ X11 @ X12)))),
% 11.05/11.23      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 11.05/11.23  thf('24', plain,
% 11.05/11.23      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 11.05/11.23         (~ (v1_relat_1 @ X0)
% 11.05/11.23          | ((X0) != (k7_relat_1 @ X1 @ X2))
% 11.05/11.23          | (r2_hidden @ (k4_tarski @ X3 @ X4) @ X0)
% 11.05/11.23          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X1)
% 11.05/11.23          | ~ (r2_hidden @ X3 @ X2)
% 11.05/11.23          | ~ (v1_relat_1 @ X1))),
% 11.05/11.23      inference('cnf', [status(esa)], [d11_relat_1])).
% 11.05/11.23  thf('25', plain,
% 11.05/11.23      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 11.05/11.23         (~ (v1_relat_1 @ X1)
% 11.05/11.23          | ~ (r2_hidden @ X3 @ X2)
% 11.05/11.23          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X1)
% 11.05/11.23          | (r2_hidden @ (k4_tarski @ X3 @ X4) @ (k7_relat_1 @ X1 @ X2))
% 11.05/11.23          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2)))),
% 11.05/11.23      inference('simplify', [status(thm)], ['24'])).
% 11.05/11.23  thf('26', plain,
% 11.05/11.23      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.05/11.23         (~ (v1_relat_1 @ X1)
% 11.05/11.23          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k7_relat_1 @ X1 @ X0))
% 11.05/11.23          | ~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ X1)
% 11.05/11.23          | ~ (r2_hidden @ X3 @ X0)
% 11.05/11.23          | ~ (v1_relat_1 @ X1))),
% 11.05/11.23      inference('sup-', [status(thm)], ['23', '25'])).
% 11.05/11.23  thf('27', plain,
% 11.05/11.23      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.05/11.23         (~ (r2_hidden @ X3 @ X0)
% 11.05/11.23          | ~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ X1)
% 11.05/11.23          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k7_relat_1 @ X1 @ X0))
% 11.05/11.23          | ~ (v1_relat_1 @ X1))),
% 11.05/11.23      inference('simplify', [status(thm)], ['26'])).
% 11.05/11.23  thf('28', plain,
% 11.05/11.23      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.05/11.23         (~ (v1_relat_1 @ X0)
% 11.05/11.23          | (r1_tarski @ (k7_relat_1 @ X0 @ X1) @ X2)
% 11.05/11.23          | ~ (v1_relat_1 @ X0)
% 11.05/11.23          | (r2_hidden @ 
% 11.05/11.23             (k4_tarski @ (sk_C @ X2 @ (k7_relat_1 @ X0 @ X1)) @ 
% 11.05/11.23              (sk_D_1 @ X2 @ (k7_relat_1 @ X0 @ X1))) @ 
% 11.05/11.23             (k7_relat_1 @ X0 @ X3))
% 11.05/11.23          | ~ (r2_hidden @ (sk_C @ X2 @ (k7_relat_1 @ X0 @ X1)) @ X3))),
% 11.05/11.23      inference('sup-', [status(thm)], ['22', '27'])).
% 11.05/11.23  thf('29', plain,
% 11.05/11.23      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.05/11.23         (~ (r2_hidden @ (sk_C @ X2 @ (k7_relat_1 @ X0 @ X1)) @ X3)
% 11.05/11.23          | (r2_hidden @ 
% 11.05/11.23             (k4_tarski @ (sk_C @ X2 @ (k7_relat_1 @ X0 @ X1)) @ 
% 11.05/11.23              (sk_D_1 @ X2 @ (k7_relat_1 @ X0 @ X1))) @ 
% 11.05/11.23             (k7_relat_1 @ X0 @ X3))
% 11.05/11.23          | (r1_tarski @ (k7_relat_1 @ X0 @ X1) @ X2)
% 11.05/11.23          | ~ (v1_relat_1 @ X0))),
% 11.05/11.23      inference('simplify', [status(thm)], ['28'])).
% 11.05/11.23  thf('30', plain,
% 11.05/11.23      (![X0 : $i, X1 : $i]:
% 11.05/11.23         (~ (v1_relat_1 @ X0)
% 11.05/11.23          | (r1_tarski @ (k7_relat_1 @ X0 @ sk_A) @ X1)
% 11.05/11.23          | ~ (v1_relat_1 @ X0)
% 11.05/11.23          | (r1_tarski @ (k7_relat_1 @ X0 @ sk_A) @ X1)
% 11.05/11.23          | (r2_hidden @ 
% 11.05/11.23             (k4_tarski @ (sk_C @ X1 @ (k7_relat_1 @ X0 @ sk_A)) @ 
% 11.05/11.23              (sk_D_1 @ X1 @ (k7_relat_1 @ X0 @ sk_A))) @ 
% 11.05/11.23             (k7_relat_1 @ X0 @ sk_B)))),
% 11.05/11.23      inference('sup-', [status(thm)], ['14', '29'])).
% 11.05/11.23  thf('31', plain,
% 11.05/11.23      (![X0 : $i, X1 : $i]:
% 11.05/11.23         ((r2_hidden @ 
% 11.05/11.23           (k4_tarski @ (sk_C @ X1 @ (k7_relat_1 @ X0 @ sk_A)) @ 
% 11.05/11.23            (sk_D_1 @ X1 @ (k7_relat_1 @ X0 @ sk_A))) @ 
% 11.05/11.23           (k7_relat_1 @ X0 @ sk_B))
% 11.05/11.23          | (r1_tarski @ (k7_relat_1 @ X0 @ sk_A) @ X1)
% 11.05/11.23          | ~ (v1_relat_1 @ X0))),
% 11.05/11.23      inference('simplify', [status(thm)], ['30'])).
% 11.05/11.23  thf('32', plain,
% 11.05/11.23      (![X6 : $i, X7 : $i]:
% 11.05/11.23         (~ (r2_hidden @ (k4_tarski @ (sk_C @ X6 @ X7) @ (sk_D_1 @ X6 @ X7)) @ 
% 11.05/11.23             X6)
% 11.05/11.23          | (r1_tarski @ X7 @ X6)
% 11.05/11.23          | ~ (v1_relat_1 @ X7))),
% 11.05/11.23      inference('cnf', [status(esa)], [d3_relat_1])).
% 11.05/11.23  thf('33', plain,
% 11.05/11.23      (![X0 : $i]:
% 11.05/11.23         (~ (v1_relat_1 @ X0)
% 11.05/11.23          | (r1_tarski @ (k7_relat_1 @ X0 @ sk_A) @ (k7_relat_1 @ X0 @ sk_B))
% 11.05/11.23          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ sk_A))
% 11.05/11.23          | (r1_tarski @ (k7_relat_1 @ X0 @ sk_A) @ (k7_relat_1 @ X0 @ sk_B)))),
% 11.05/11.23      inference('sup-', [status(thm)], ['31', '32'])).
% 11.05/11.23  thf('34', plain,
% 11.05/11.23      (![X0 : $i]:
% 11.05/11.23         (~ (v1_relat_1 @ (k7_relat_1 @ X0 @ sk_A))
% 11.05/11.23          | (r1_tarski @ (k7_relat_1 @ X0 @ sk_A) @ (k7_relat_1 @ X0 @ sk_B))
% 11.05/11.23          | ~ (v1_relat_1 @ X0))),
% 11.05/11.23      inference('simplify', [status(thm)], ['33'])).
% 11.05/11.23  thf('35', plain,
% 11.05/11.23      (![X11 : $i, X12 : $i]:
% 11.05/11.23         (~ (v1_relat_1 @ X11) | (v1_relat_1 @ (k7_relat_1 @ X11 @ X12)))),
% 11.05/11.23      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 11.05/11.23  thf('36', plain,
% 11.05/11.23      (![X0 : $i]:
% 11.05/11.23         (~ (v1_relat_1 @ X0)
% 11.05/11.23          | (r1_tarski @ (k7_relat_1 @ X0 @ sk_A) @ (k7_relat_1 @ X0 @ sk_B)))),
% 11.05/11.23      inference('clc', [status(thm)], ['34', '35'])).
% 11.05/11.23  thf('37', plain,
% 11.05/11.23      (~ (r1_tarski @ (k7_relat_1 @ sk_C_1 @ sk_A) @ 
% 11.05/11.23          (k7_relat_1 @ sk_C_1 @ sk_B))),
% 11.05/11.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.05/11.23  thf('38', plain, (~ (v1_relat_1 @ sk_C_1)),
% 11.05/11.23      inference('sup-', [status(thm)], ['36', '37'])).
% 11.05/11.23  thf('39', plain, ((v1_relat_1 @ sk_C_1)),
% 11.05/11.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.05/11.23  thf('40', plain, ($false), inference('demod', [status(thm)], ['38', '39'])).
% 11.05/11.23  
% 11.05/11.23  % SZS output end Refutation
% 11.05/11.23  
% 11.05/11.24  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
