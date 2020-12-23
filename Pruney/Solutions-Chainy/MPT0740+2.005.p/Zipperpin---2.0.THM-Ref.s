%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pJ0h4vKHss

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:49 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   65 (  83 expanded)
%              Number of leaves         :   21 (  33 expanded)
%              Depth                    :   19
%              Number of atoms          :  407 ( 552 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('0',plain,(
    ! [X19: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X19 ) )
      | ~ ( v3_ordinal1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('1',plain,(
    ! [X19: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X19 ) )
      | ~ ( v3_ordinal1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('2',plain,(
    ! [X13: $i] :
      ( r2_hidden @ X13 @ ( k1_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X12: $i] :
      ( ( v1_ordinal1 @ X12 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf(t94_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k3_tarski @ A ) @ B ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X4 ) @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ( r1_tarski @ X10 @ X11 )
      | ~ ( v1_ordinal1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ~ ( v1_ordinal1 @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X4 ) @ X5 )
      | ~ ( r1_tarski @ ( sk_C_1 @ X5 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ( r1_tarski @ ( k3_tarski @ X0 ) @ X0 )
      | ( r1_tarski @ ( k3_tarski @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X0 )
      | ~ ( v1_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( k3_tarski @ X0 ) ) @ X0 )
      | ~ ( v1_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','11'])).

thf('13',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t56_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B )
        & ( r2_hidden @ C @ A ) )
     => ( r1_tarski @ C @ B ) ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ X6 ) @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t56_setfam_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k3_tarski @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ( r1_tarski @ ( sk_B @ ( k3_tarski @ X0 ) ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,(
    ! [X12: $i] :
      ( ( v1_ordinal1 @ X12 )
      | ~ ( r1_tarski @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ~ ( v1_ordinal1 @ X0 ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X0 )
      | ~ ( v1_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t22_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ! [C: $i] :
              ( ( v3_ordinal1 @ C )
             => ( ( ( r1_tarski @ A @ B )
                  & ( r2_hidden @ B @ C ) )
               => ( r2_hidden @ A @ C ) ) ) ) ) )).

thf('23',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v3_ordinal1 @ X14 )
      | ~ ( r1_tarski @ X15 @ X14 )
      | ~ ( r2_hidden @ X14 @ X16 )
      | ( r2_hidden @ X15 @ X16 )
      | ~ ( v3_ordinal1 @ X16 )
      | ~ ( v1_ordinal1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t22_ordinal1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ~ ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ ( k3_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ ( k3_tarski @ X0 ) @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v1_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ ( k3_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ ( k3_tarski @ X0 ) @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ ( k3_tarski @ X0 ) @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ( r2_hidden @ ( k3_tarski @ X0 ) @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('30',plain,(
    ! [X9: $i] :
      ( ( v1_ordinal1 @ X9 )
      | ~ ( v3_ordinal1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ ( k3_tarski @ X0 ) @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf(t23_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v3_ordinal1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( v3_ordinal1 @ A ) ) ) )).

thf('32',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v3_ordinal1 @ X17 )
      | ~ ( v3_ordinal1 @ X18 )
      | ~ ( r2_hidden @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) )
      | ( v3_ordinal1 @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X13: $i] :
      ( r2_hidden @ X13 @ ( k1_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('35',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v3_ordinal1 @ X17 )
      | ~ ( v3_ordinal1 @ X18 )
      | ~ ( r2_hidden @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) )
      | ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v3_ordinal1 @ ( k3_tarski @ X0 ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v3_ordinal1 @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','37'])).

thf(t30_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k3_tarski @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ( v3_ordinal1 @ ( k3_tarski @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t30_ordinal1])).

thf('39',plain,(
    ~ ( v3_ordinal1 @ ( k3_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['40','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pJ0h4vKHss
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:10:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.41/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.61  % Solved by: fo/fo7.sh
% 0.41/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.61  % done 111 iterations in 0.148s
% 0.41/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.61  % SZS output start Refutation
% 0.41/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.61  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.41/0.61  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.41/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.41/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.61  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.41/0.61  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.41/0.61  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.41/0.61  thf(sk_B_type, type, sk_B: $i > $i).
% 0.41/0.61  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.41/0.61  thf(t29_ordinal1, axiom,
% 0.41/0.61    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 0.41/0.61  thf('0', plain,
% 0.41/0.61      (![X19 : $i]:
% 0.41/0.61         ((v3_ordinal1 @ (k1_ordinal1 @ X19)) | ~ (v3_ordinal1 @ X19))),
% 0.41/0.61      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.41/0.61  thf('1', plain,
% 0.41/0.61      (![X19 : $i]:
% 0.41/0.61         ((v3_ordinal1 @ (k1_ordinal1 @ X19)) | ~ (v3_ordinal1 @ X19))),
% 0.41/0.61      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.41/0.61  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.41/0.61  thf('2', plain, (![X13 : $i]: (r2_hidden @ X13 @ (k1_ordinal1 @ X13))),
% 0.41/0.61      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.41/0.61  thf(d2_ordinal1, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( v1_ordinal1 @ A ) <=>
% 0.41/0.61       ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( r1_tarski @ B @ A ) ) ) ))).
% 0.41/0.61  thf('3', plain,
% 0.41/0.61      (![X12 : $i]: ((v1_ordinal1 @ X12) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.41/0.61      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.41/0.61  thf(t94_zfmisc_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ C @ B ) ) ) =>
% 0.41/0.61       ( r1_tarski @ ( k3_tarski @ A ) @ B ) ))).
% 0.41/0.61  thf('4', plain,
% 0.41/0.61      (![X4 : $i, X5 : $i]:
% 0.41/0.61         ((r1_tarski @ (k3_tarski @ X4) @ X5)
% 0.41/0.61          | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X4))),
% 0.41/0.61      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.41/0.61  thf('5', plain,
% 0.41/0.61      (![X10 : $i, X11 : $i]:
% 0.41/0.61         (~ (r2_hidden @ X10 @ X11)
% 0.41/0.61          | (r1_tarski @ X10 @ X11)
% 0.41/0.61          | ~ (v1_ordinal1 @ X11))),
% 0.41/0.61      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.41/0.61  thf('6', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         ((r1_tarski @ (k3_tarski @ X0) @ X1)
% 0.41/0.61          | ~ (v1_ordinal1 @ X0)
% 0.41/0.61          | (r1_tarski @ (sk_C_1 @ X1 @ X0) @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.41/0.61  thf('7', plain,
% 0.41/0.61      (![X4 : $i, X5 : $i]:
% 0.41/0.61         ((r1_tarski @ (k3_tarski @ X4) @ X5)
% 0.41/0.61          | ~ (r1_tarski @ (sk_C_1 @ X5 @ X4) @ X5))),
% 0.41/0.61      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.41/0.61  thf('8', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (v1_ordinal1 @ X0)
% 0.41/0.61          | (r1_tarski @ (k3_tarski @ X0) @ X0)
% 0.41/0.61          | (r1_tarski @ (k3_tarski @ X0) @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['6', '7'])).
% 0.41/0.61  thf('9', plain,
% 0.41/0.61      (![X0 : $i]: ((r1_tarski @ (k3_tarski @ X0) @ X0) | ~ (v1_ordinal1 @ X0))),
% 0.41/0.61      inference('simplify', [status(thm)], ['8'])).
% 0.41/0.61  thf(d3_tarski, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( r1_tarski @ A @ B ) <=>
% 0.41/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.41/0.61  thf('10', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         (~ (r2_hidden @ X0 @ X1)
% 0.41/0.61          | (r2_hidden @ X0 @ X2)
% 0.41/0.61          | ~ (r1_tarski @ X1 @ X2))),
% 0.41/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.61  thf('11', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         (~ (v1_ordinal1 @ X0)
% 0.41/0.61          | (r2_hidden @ X1 @ X0)
% 0.41/0.61          | ~ (r2_hidden @ X1 @ (k3_tarski @ X0)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['9', '10'])).
% 0.41/0.61  thf('12', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v1_ordinal1 @ (k3_tarski @ X0))
% 0.41/0.61          | (r2_hidden @ (sk_B @ (k3_tarski @ X0)) @ X0)
% 0.41/0.61          | ~ (v1_ordinal1 @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['3', '11'])).
% 0.41/0.61  thf('13', plain,
% 0.41/0.61      (![X1 : $i, X3 : $i]:
% 0.41/0.61         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.41/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.61  thf('14', plain,
% 0.41/0.61      (![X1 : $i, X3 : $i]:
% 0.41/0.61         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.41/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.61  thf('15', plain,
% 0.41/0.61      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['13', '14'])).
% 0.41/0.61  thf('16', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.41/0.61      inference('simplify', [status(thm)], ['15'])).
% 0.41/0.61  thf(t56_setfam_1, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B ) & ( r2_hidden @ C @ A ) ) =>
% 0.41/0.61       ( r1_tarski @ C @ B ) ))).
% 0.41/0.61  thf('17', plain,
% 0.41/0.61      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.41/0.61         (~ (r1_tarski @ (k3_tarski @ X6) @ X7)
% 0.41/0.61          | ~ (r2_hidden @ X8 @ X6)
% 0.41/0.61          | (r1_tarski @ X8 @ X7))),
% 0.41/0.61      inference('cnf', [status(esa)], [t56_setfam_1])).
% 0.41/0.61  thf('18', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         ((r1_tarski @ X1 @ (k3_tarski @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['16', '17'])).
% 0.41/0.61  thf('19', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (v1_ordinal1 @ X0)
% 0.41/0.61          | (v1_ordinal1 @ (k3_tarski @ X0))
% 0.41/0.61          | (r1_tarski @ (sk_B @ (k3_tarski @ X0)) @ (k3_tarski @ X0)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['12', '18'])).
% 0.41/0.61  thf('20', plain,
% 0.41/0.61      (![X12 : $i]: ((v1_ordinal1 @ X12) | ~ (r1_tarski @ (sk_B @ X12) @ X12))),
% 0.41/0.61      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.41/0.61  thf('21', plain,
% 0.41/0.61      (![X0 : $i]: ((v1_ordinal1 @ (k3_tarski @ X0)) | ~ (v1_ordinal1 @ X0))),
% 0.41/0.61      inference('clc', [status(thm)], ['19', '20'])).
% 0.41/0.61  thf('22', plain,
% 0.41/0.61      (![X0 : $i]: ((r1_tarski @ (k3_tarski @ X0) @ X0) | ~ (v1_ordinal1 @ X0))),
% 0.41/0.61      inference('simplify', [status(thm)], ['8'])).
% 0.41/0.61  thf(t22_ordinal1, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( v1_ordinal1 @ A ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( v3_ordinal1 @ B ) =>
% 0.41/0.61           ( ![C:$i]:
% 0.41/0.61             ( ( v3_ordinal1 @ C ) =>
% 0.41/0.61               ( ( ( r1_tarski @ A @ B ) & ( r2_hidden @ B @ C ) ) =>
% 0.41/0.61                 ( r2_hidden @ A @ C ) ) ) ) ) ) ))).
% 0.41/0.61  thf('23', plain,
% 0.41/0.61      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.41/0.61         (~ (v3_ordinal1 @ X14)
% 0.41/0.61          | ~ (r1_tarski @ X15 @ X14)
% 0.41/0.61          | ~ (r2_hidden @ X14 @ X16)
% 0.41/0.61          | (r2_hidden @ X15 @ X16)
% 0.41/0.61          | ~ (v3_ordinal1 @ X16)
% 0.41/0.61          | ~ (v1_ordinal1 @ X15))),
% 0.41/0.61      inference('cnf', [status(esa)], [t22_ordinal1])).
% 0.41/0.61  thf('24', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         (~ (v1_ordinal1 @ X0)
% 0.41/0.61          | ~ (v1_ordinal1 @ (k3_tarski @ X0))
% 0.41/0.61          | ~ (v3_ordinal1 @ X1)
% 0.41/0.61          | (r2_hidden @ (k3_tarski @ X0) @ X1)
% 0.41/0.61          | ~ (r2_hidden @ X0 @ X1)
% 0.41/0.61          | ~ (v3_ordinal1 @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['22', '23'])).
% 0.41/0.61  thf('25', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         (~ (v1_ordinal1 @ X0)
% 0.41/0.61          | ~ (v3_ordinal1 @ X0)
% 0.41/0.61          | ~ (r2_hidden @ X0 @ X1)
% 0.41/0.61          | (r2_hidden @ (k3_tarski @ X0) @ X1)
% 0.41/0.61          | ~ (v3_ordinal1 @ X1)
% 0.41/0.61          | ~ (v1_ordinal1 @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['21', '24'])).
% 0.41/0.61  thf('26', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         (~ (v3_ordinal1 @ X1)
% 0.41/0.61          | (r2_hidden @ (k3_tarski @ X0) @ X1)
% 0.41/0.61          | ~ (r2_hidden @ X0 @ X1)
% 0.41/0.61          | ~ (v3_ordinal1 @ X0)
% 0.41/0.61          | ~ (v1_ordinal1 @ X0))),
% 0.41/0.61      inference('simplify', [status(thm)], ['25'])).
% 0.41/0.61  thf('27', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (v1_ordinal1 @ X0)
% 0.41/0.61          | ~ (v3_ordinal1 @ X0)
% 0.41/0.61          | (r2_hidden @ (k3_tarski @ X0) @ (k1_ordinal1 @ X0))
% 0.41/0.61          | ~ (v3_ordinal1 @ (k1_ordinal1 @ X0)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['2', '26'])).
% 0.41/0.61  thf('28', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (v3_ordinal1 @ X0)
% 0.41/0.61          | (r2_hidden @ (k3_tarski @ X0) @ (k1_ordinal1 @ X0))
% 0.41/0.61          | ~ (v3_ordinal1 @ X0)
% 0.41/0.61          | ~ (v1_ordinal1 @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['1', '27'])).
% 0.41/0.61  thf('29', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (v1_ordinal1 @ X0)
% 0.41/0.61          | (r2_hidden @ (k3_tarski @ X0) @ (k1_ordinal1 @ X0))
% 0.41/0.61          | ~ (v3_ordinal1 @ X0))),
% 0.41/0.61      inference('simplify', [status(thm)], ['28'])).
% 0.41/0.61  thf(cc1_ordinal1, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 0.41/0.61  thf('30', plain, (![X9 : $i]: ((v1_ordinal1 @ X9) | ~ (v3_ordinal1 @ X9))),
% 0.41/0.61      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.41/0.61  thf('31', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (v3_ordinal1 @ X0)
% 0.41/0.61          | (r2_hidden @ (k3_tarski @ X0) @ (k1_ordinal1 @ X0)))),
% 0.41/0.61      inference('clc', [status(thm)], ['29', '30'])).
% 0.41/0.61  thf(t23_ordinal1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( v3_ordinal1 @ B ) => ( ( r2_hidden @ A @ B ) => ( v3_ordinal1 @ A ) ) ))).
% 0.41/0.61  thf('32', plain,
% 0.41/0.61      (![X17 : $i, X18 : $i]:
% 0.41/0.61         ((v3_ordinal1 @ X17)
% 0.41/0.61          | ~ (v3_ordinal1 @ X18)
% 0.41/0.61          | ~ (r2_hidden @ X17 @ X18))),
% 0.41/0.61      inference('cnf', [status(esa)], [t23_ordinal1])).
% 0.41/0.61  thf('33', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (v3_ordinal1 @ X0)
% 0.41/0.61          | ~ (v3_ordinal1 @ (k1_ordinal1 @ X0))
% 0.41/0.61          | (v3_ordinal1 @ (k3_tarski @ X0)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['31', '32'])).
% 0.41/0.61  thf('34', plain, (![X13 : $i]: (r2_hidden @ X13 @ (k1_ordinal1 @ X13))),
% 0.41/0.61      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.41/0.61  thf('35', plain,
% 0.41/0.61      (![X17 : $i, X18 : $i]:
% 0.41/0.61         ((v3_ordinal1 @ X17)
% 0.41/0.61          | ~ (v3_ordinal1 @ X18)
% 0.41/0.61          | ~ (r2_hidden @ X17 @ X18))),
% 0.41/0.61      inference('cnf', [status(esa)], [t23_ordinal1])).
% 0.41/0.61  thf('36', plain,
% 0.41/0.61      (![X0 : $i]: (~ (v3_ordinal1 @ (k1_ordinal1 @ X0)) | (v3_ordinal1 @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['34', '35'])).
% 0.41/0.61  thf('37', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v3_ordinal1 @ (k3_tarski @ X0))
% 0.41/0.61          | ~ (v3_ordinal1 @ (k1_ordinal1 @ X0)))),
% 0.41/0.61      inference('clc', [status(thm)], ['33', '36'])).
% 0.41/0.61  thf('38', plain,
% 0.41/0.61      (![X0 : $i]: (~ (v3_ordinal1 @ X0) | (v3_ordinal1 @ (k3_tarski @ X0)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['0', '37'])).
% 0.41/0.61  thf(t30_ordinal1, conjecture,
% 0.41/0.61    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k3_tarski @ A ) ) ))).
% 0.41/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.61    (~( ![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k3_tarski @ A ) ) ) )),
% 0.41/0.61    inference('cnf.neg', [status(esa)], [t30_ordinal1])).
% 0.41/0.61  thf('39', plain, (~ (v3_ordinal1 @ (k3_tarski @ sk_A))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('40', plain, (~ (v3_ordinal1 @ sk_A)),
% 0.41/0.61      inference('sup-', [status(thm)], ['38', '39'])).
% 0.41/0.61  thf('41', plain, ((v3_ordinal1 @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('42', plain, ($false), inference('demod', [status(thm)], ['40', '41'])).
% 0.41/0.61  
% 0.41/0.61  % SZS output end Refutation
% 0.41/0.61  
% 0.44/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
