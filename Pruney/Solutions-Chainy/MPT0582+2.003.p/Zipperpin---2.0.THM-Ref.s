%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nxLpLVlZEi

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:25 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 151 expanded)
%              Number of leaves         :   16 (  49 expanded)
%              Depth                    :   22
%              Number of atoms          :  620 (1727 expanded)
%              Number of equality atoms :    9 (  28 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(t186_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
              & ( r1_tarski @ C @ B ) )
           => ( r1_tarski @ C @ ( k7_relat_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ! [C: $i] :
            ( ( v1_relat_1 @ C )
           => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
                & ( r1_tarski @ C @ B ) )
             => ( r1_tarski @ C @ ( k7_relat_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t186_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_C_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ( ( k7_relat_1 @ X16 @ X17 )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k7_relat_1 @ sk_C_1 @ sk_A )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( k7_relat_1 @ sk_C_1 @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['4','5'])).

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

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
       != ( k7_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ X3 @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d11_relat_1])).

thf('8',plain,(
    ! [X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k7_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ X3 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C_1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C_1 @ sk_A ) )
      | ( r2_hidden @ X1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,
    ( ( k7_relat_1 @ sk_C_1 @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['4','5'])).

thf('11',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C_1 )
      | ( r2_hidden @ X1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r1_tarski @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('19',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X6 @ X7 ) @ ( sk_D_1 @ X6 @ X7 ) ) @ X7 )
      | ( r1_tarski @ X7 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
       != ( k7_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d11_relat_1])).

thf('22',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ ( k7_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ X1 )
      | ~ ( r2_hidden @ X3 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D_1 @ X1 @ X0 ) ) @ ( k7_relat_1 @ X0 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D_1 @ X1 @ X0 ) ) @ ( k7_relat_1 @ X0 @ X2 ) )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( r1_tarski @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_C_1 ) @ ( sk_D_1 @ X0 @ sk_C_1 ) ) @ ( k7_relat_1 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k7_relat_1 @ sk_C_1 @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['4','5'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( r1_tarski @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_C_1 ) @ ( sk_D_1 @ X0 @ sk_C_1 ) ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_C_1 ) @ ( sk_D_1 @ X0 @ sk_C_1 ) ) @ sk_C_1 )
      | ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_C_1 ) @ ( sk_D_1 @ X0 @ sk_C_1 ) ) @ X1 )
      | ~ ( r1_tarski @ sk_C_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_C_1 ) @ ( sk_D_1 @ X0 @ sk_C_1 ) ) @ X1 )
      | ~ ( r1_tarski @ sk_C_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_C_1 ) @ ( sk_D_1 @ X0 @ sk_C_1 ) ) @ sk_B )
      | ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_C_1 ) @ ( sk_D_1 @ X0 @ sk_C_1 ) ) @ ( k7_relat_1 @ sk_B @ X1 ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_C_1 ) @ ( sk_D_1 @ X0 @ sk_C_1 ) ) @ ( k7_relat_1 @ sk_B @ X1 ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_C_1 ) @ ( sk_D_1 @ X0 @ sk_C_1 ) ) @ ( k7_relat_1 @ sk_B @ sk_A ) )
      | ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_C_1 ) @ ( sk_D_1 @ X0 @ sk_C_1 ) ) @ ( k7_relat_1 @ sk_B @ sk_A ) )
      | ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X6 @ X7 ) @ ( sk_D_1 @ X6 @ X7 ) ) @ X6 )
      | ( r1_tarski @ X7 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('44',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ sk_C_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    | ( r1_tarski @ sk_C_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    r1_tarski @ sk_C_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['0','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nxLpLVlZEi
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:55:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.76/0.95  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.76/0.95  % Solved by: fo/fo7.sh
% 0.76/0.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.95  % done 863 iterations in 0.491s
% 0.76/0.95  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.76/0.95  % SZS output start Refutation
% 0.76/0.95  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.76/0.95  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.76/0.95  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.76/0.95  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.76/0.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.95  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.95  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.76/0.95  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.76/0.95  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.76/0.95  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.95  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.76/0.95  thf(t186_relat_1, conjecture,
% 0.76/0.95    (![A:$i,B:$i]:
% 0.76/0.95     ( ( v1_relat_1 @ B ) =>
% 0.76/0.95       ( ![C:$i]:
% 0.76/0.95         ( ( v1_relat_1 @ C ) =>
% 0.76/0.95           ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & ( r1_tarski @ C @ B ) ) =>
% 0.76/0.95             ( r1_tarski @ C @ ( k7_relat_1 @ B @ A ) ) ) ) ) ))).
% 0.76/0.95  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.95    (~( ![A:$i,B:$i]:
% 0.76/0.95        ( ( v1_relat_1 @ B ) =>
% 0.76/0.95          ( ![C:$i]:
% 0.76/0.95            ( ( v1_relat_1 @ C ) =>
% 0.76/0.95              ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.76/0.95                  ( r1_tarski @ C @ B ) ) =>
% 0.76/0.95                ( r1_tarski @ C @ ( k7_relat_1 @ B @ A ) ) ) ) ) ) )),
% 0.76/0.95    inference('cnf.neg', [status(esa)], [t186_relat_1])).
% 0.76/0.95  thf('0', plain, (~ (r1_tarski @ sk_C_1 @ (k7_relat_1 @ sk_B @ sk_A))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf(d3_relat_1, axiom,
% 0.76/0.95    (![A:$i]:
% 0.76/0.95     ( ( v1_relat_1 @ A ) =>
% 0.76/0.95       ( ![B:$i]:
% 0.76/0.95         ( ( r1_tarski @ A @ B ) <=>
% 0.76/0.95           ( ![C:$i,D:$i]:
% 0.76/0.95             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 0.76/0.95               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 0.76/0.95  thf('1', plain,
% 0.76/0.95      (![X6 : $i, X7 : $i]:
% 0.76/0.95         ((r2_hidden @ (k4_tarski @ (sk_C @ X6 @ X7) @ (sk_D_1 @ X6 @ X7)) @ X7)
% 0.76/0.95          | (r1_tarski @ X7 @ X6)
% 0.76/0.95          | ~ (v1_relat_1 @ X7))),
% 0.76/0.95      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.76/0.95  thf('2', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf(t97_relat_1, axiom,
% 0.76/0.95    (![A:$i,B:$i]:
% 0.76/0.95     ( ( v1_relat_1 @ B ) =>
% 0.76/0.95       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.76/0.95         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.76/0.95  thf('3', plain,
% 0.76/0.95      (![X16 : $i, X17 : $i]:
% 0.76/0.95         (~ (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 0.76/0.95          | ((k7_relat_1 @ X16 @ X17) = (X16))
% 0.76/0.95          | ~ (v1_relat_1 @ X16))),
% 0.76/0.95      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.76/0.95  thf('4', plain,
% 0.76/0.95      ((~ (v1_relat_1 @ sk_C_1) | ((k7_relat_1 @ sk_C_1 @ sk_A) = (sk_C_1)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['2', '3'])).
% 0.76/0.95  thf('5', plain, ((v1_relat_1 @ sk_C_1)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('6', plain, (((k7_relat_1 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 0.76/0.95      inference('demod', [status(thm)], ['4', '5'])).
% 0.76/0.95  thf(d11_relat_1, axiom,
% 0.76/0.95    (![A:$i]:
% 0.76/0.95     ( ( v1_relat_1 @ A ) =>
% 0.76/0.95       ( ![B:$i,C:$i]:
% 0.76/0.95         ( ( v1_relat_1 @ C ) =>
% 0.76/0.95           ( ( ( C ) = ( k7_relat_1 @ A @ B ) ) <=>
% 0.76/0.95             ( ![D:$i,E:$i]:
% 0.76/0.95               ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 0.76/0.95                 ( ( r2_hidden @ D @ B ) & 
% 0.76/0.95                   ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) ) ) ))).
% 0.76/0.95  thf('7', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 0.76/0.95         (~ (v1_relat_1 @ X0)
% 0.76/0.95          | ((X0) != (k7_relat_1 @ X1 @ X2))
% 0.76/0.95          | (r2_hidden @ X3 @ X2)
% 0.76/0.95          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ X0)
% 0.76/0.95          | ~ (v1_relat_1 @ X1))),
% 0.76/0.95      inference('cnf', [status(esa)], [d11_relat_1])).
% 0.76/0.95  thf('8', plain,
% 0.76/0.95      (![X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 0.76/0.95         (~ (v1_relat_1 @ X1)
% 0.76/0.95          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (k7_relat_1 @ X1 @ X2))
% 0.76/0.95          | (r2_hidden @ X3 @ X2)
% 0.76/0.95          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2)))),
% 0.76/0.95      inference('simplify', [status(thm)], ['7'])).
% 0.76/0.95  thf('9', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C_1)
% 0.76/0.95          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C_1 @ sk_A))
% 0.76/0.95          | (r2_hidden @ X1 @ sk_A)
% 0.76/0.95          | ~ (v1_relat_1 @ sk_C_1))),
% 0.76/0.95      inference('sup-', [status(thm)], ['6', '8'])).
% 0.76/0.95  thf('10', plain, (((k7_relat_1 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 0.76/0.95      inference('demod', [status(thm)], ['4', '5'])).
% 0.76/0.95  thf('11', plain, ((v1_relat_1 @ sk_C_1)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('12', plain, ((v1_relat_1 @ sk_C_1)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('13', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C_1)
% 0.76/0.95          | (r2_hidden @ X1 @ sk_A))),
% 0.76/0.95      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.76/0.95  thf('14', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         (~ (v1_relat_1 @ sk_C_1)
% 0.76/0.95          | (r1_tarski @ sk_C_1 @ X0)
% 0.76/0.95          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_A))),
% 0.76/0.95      inference('sup-', [status(thm)], ['1', '13'])).
% 0.76/0.95  thf('15', plain, ((v1_relat_1 @ sk_C_1)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('16', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((r1_tarski @ sk_C_1 @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_A))),
% 0.76/0.95      inference('demod', [status(thm)], ['14', '15'])).
% 0.76/0.95  thf('17', plain, ((r1_tarski @ sk_C_1 @ sk_B)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('18', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((r1_tarski @ sk_C_1 @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_A))),
% 0.76/0.95      inference('demod', [status(thm)], ['14', '15'])).
% 0.76/0.95  thf('19', plain,
% 0.76/0.95      (![X6 : $i, X7 : $i]:
% 0.76/0.95         ((r2_hidden @ (k4_tarski @ (sk_C @ X6 @ X7) @ (sk_D_1 @ X6 @ X7)) @ X7)
% 0.76/0.95          | (r1_tarski @ X7 @ X6)
% 0.76/0.95          | ~ (v1_relat_1 @ X7))),
% 0.76/0.95      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.76/0.95  thf(dt_k7_relat_1, axiom,
% 0.76/0.95    (![A:$i,B:$i]:
% 0.76/0.95     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.76/0.95  thf('20', plain,
% 0.76/0.95      (![X11 : $i, X12 : $i]:
% 0.76/0.95         (~ (v1_relat_1 @ X11) | (v1_relat_1 @ (k7_relat_1 @ X11 @ X12)))),
% 0.76/0.95      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.76/0.95  thf('21', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.76/0.95         (~ (v1_relat_1 @ X0)
% 0.76/0.95          | ((X0) != (k7_relat_1 @ X1 @ X2))
% 0.76/0.95          | (r2_hidden @ (k4_tarski @ X3 @ X4) @ X0)
% 0.76/0.95          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X1)
% 0.76/0.95          | ~ (r2_hidden @ X3 @ X2)
% 0.76/0.95          | ~ (v1_relat_1 @ X1))),
% 0.76/0.95      inference('cnf', [status(esa)], [d11_relat_1])).
% 0.76/0.95  thf('22', plain,
% 0.76/0.95      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.76/0.95         (~ (v1_relat_1 @ X1)
% 0.76/0.95          | ~ (r2_hidden @ X3 @ X2)
% 0.76/0.95          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X1)
% 0.76/0.95          | (r2_hidden @ (k4_tarski @ X3 @ X4) @ (k7_relat_1 @ X1 @ X2))
% 0.76/0.95          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2)))),
% 0.76/0.95      inference('simplify', [status(thm)], ['21'])).
% 0.76/0.95  thf('23', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.76/0.95         (~ (v1_relat_1 @ X1)
% 0.76/0.95          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k7_relat_1 @ X1 @ X0))
% 0.76/0.95          | ~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ X1)
% 0.76/0.95          | ~ (r2_hidden @ X3 @ X0)
% 0.76/0.95          | ~ (v1_relat_1 @ X1))),
% 0.76/0.95      inference('sup-', [status(thm)], ['20', '22'])).
% 0.76/0.95  thf('24', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.76/0.95         (~ (r2_hidden @ X3 @ X0)
% 0.76/0.95          | ~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ X1)
% 0.76/0.95          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k7_relat_1 @ X1 @ X0))
% 0.76/0.95          | ~ (v1_relat_1 @ X1))),
% 0.76/0.95      inference('simplify', [status(thm)], ['23'])).
% 0.76/0.95  thf('25', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.95         (~ (v1_relat_1 @ X0)
% 0.76/0.95          | (r1_tarski @ X0 @ X1)
% 0.76/0.95          | ~ (v1_relat_1 @ X0)
% 0.76/0.95          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_D_1 @ X1 @ X0)) @ 
% 0.76/0.95             (k7_relat_1 @ X0 @ X2))
% 0.76/0.95          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.76/0.95      inference('sup-', [status(thm)], ['19', '24'])).
% 0.76/0.95  thf('26', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.95         (~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 0.76/0.95          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_D_1 @ X1 @ X0)) @ 
% 0.76/0.95             (k7_relat_1 @ X0 @ X2))
% 0.76/0.95          | (r1_tarski @ X0 @ X1)
% 0.76/0.95          | ~ (v1_relat_1 @ X0))),
% 0.76/0.95      inference('simplify', [status(thm)], ['25'])).
% 0.76/0.95  thf('27', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((r1_tarski @ sk_C_1 @ X0)
% 0.76/0.95          | ~ (v1_relat_1 @ sk_C_1)
% 0.76/0.95          | (r1_tarski @ sk_C_1 @ X0)
% 0.76/0.95          | (r2_hidden @ 
% 0.76/0.95             (k4_tarski @ (sk_C @ X0 @ sk_C_1) @ (sk_D_1 @ X0 @ sk_C_1)) @ 
% 0.76/0.95             (k7_relat_1 @ sk_C_1 @ sk_A)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['18', '26'])).
% 0.76/0.95  thf('28', plain, ((v1_relat_1 @ sk_C_1)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('29', plain, (((k7_relat_1 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 0.76/0.95      inference('demod', [status(thm)], ['4', '5'])).
% 0.76/0.95  thf('30', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((r1_tarski @ sk_C_1 @ X0)
% 0.76/0.95          | (r1_tarski @ sk_C_1 @ X0)
% 0.76/0.95          | (r2_hidden @ 
% 0.76/0.95             (k4_tarski @ (sk_C @ X0 @ sk_C_1) @ (sk_D_1 @ X0 @ sk_C_1)) @ 
% 0.76/0.95             sk_C_1))),
% 0.76/0.95      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.76/0.95  thf('31', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((r2_hidden @ 
% 0.76/0.95           (k4_tarski @ (sk_C @ X0 @ sk_C_1) @ (sk_D_1 @ X0 @ sk_C_1)) @ sk_C_1)
% 0.76/0.95          | (r1_tarski @ sk_C_1 @ X0))),
% 0.76/0.95      inference('simplify', [status(thm)], ['30'])).
% 0.76/0.95  thf('32', plain,
% 0.76/0.95      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.76/0.95         (~ (r1_tarski @ X7 @ X8)
% 0.76/0.95          | (r2_hidden @ (k4_tarski @ X9 @ X10) @ X8)
% 0.76/0.95          | ~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ X7)
% 0.76/0.95          | ~ (v1_relat_1 @ X7))),
% 0.76/0.95      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.76/0.95  thf('33', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((r1_tarski @ sk_C_1 @ X0)
% 0.76/0.95          | ~ (v1_relat_1 @ sk_C_1)
% 0.76/0.95          | (r2_hidden @ 
% 0.76/0.95             (k4_tarski @ (sk_C @ X0 @ sk_C_1) @ (sk_D_1 @ X0 @ sk_C_1)) @ X1)
% 0.76/0.95          | ~ (r1_tarski @ sk_C_1 @ X1))),
% 0.76/0.95      inference('sup-', [status(thm)], ['31', '32'])).
% 0.76/0.95  thf('34', plain, ((v1_relat_1 @ sk_C_1)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('35', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((r1_tarski @ sk_C_1 @ X0)
% 0.76/0.95          | (r2_hidden @ 
% 0.76/0.95             (k4_tarski @ (sk_C @ X0 @ sk_C_1) @ (sk_D_1 @ X0 @ sk_C_1)) @ X1)
% 0.76/0.95          | ~ (r1_tarski @ sk_C_1 @ X1))),
% 0.76/0.95      inference('demod', [status(thm)], ['33', '34'])).
% 0.76/0.95  thf('36', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((r2_hidden @ 
% 0.76/0.95           (k4_tarski @ (sk_C @ X0 @ sk_C_1) @ (sk_D_1 @ X0 @ sk_C_1)) @ sk_B)
% 0.76/0.95          | (r1_tarski @ sk_C_1 @ X0))),
% 0.76/0.95      inference('sup-', [status(thm)], ['17', '35'])).
% 0.76/0.95  thf('37', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.76/0.95         (~ (r2_hidden @ X3 @ X0)
% 0.76/0.95          | ~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ X1)
% 0.76/0.95          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k7_relat_1 @ X1 @ X0))
% 0.76/0.95          | ~ (v1_relat_1 @ X1))),
% 0.76/0.95      inference('simplify', [status(thm)], ['23'])).
% 0.76/0.95  thf('38', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((r1_tarski @ sk_C_1 @ X0)
% 0.76/0.95          | ~ (v1_relat_1 @ sk_B)
% 0.76/0.95          | (r2_hidden @ 
% 0.76/0.95             (k4_tarski @ (sk_C @ X0 @ sk_C_1) @ (sk_D_1 @ X0 @ sk_C_1)) @ 
% 0.76/0.95             (k7_relat_1 @ sk_B @ X1))
% 0.76/0.95          | ~ (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X1))),
% 0.76/0.95      inference('sup-', [status(thm)], ['36', '37'])).
% 0.76/0.95  thf('39', plain, ((v1_relat_1 @ sk_B)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('40', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((r1_tarski @ sk_C_1 @ X0)
% 0.76/0.95          | (r2_hidden @ 
% 0.76/0.95             (k4_tarski @ (sk_C @ X0 @ sk_C_1) @ (sk_D_1 @ X0 @ sk_C_1)) @ 
% 0.76/0.95             (k7_relat_1 @ sk_B @ X1))
% 0.76/0.95          | ~ (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X1))),
% 0.76/0.95      inference('demod', [status(thm)], ['38', '39'])).
% 0.76/0.95  thf('41', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((r1_tarski @ sk_C_1 @ X0)
% 0.76/0.95          | (r2_hidden @ 
% 0.76/0.95             (k4_tarski @ (sk_C @ X0 @ sk_C_1) @ (sk_D_1 @ X0 @ sk_C_1)) @ 
% 0.76/0.95             (k7_relat_1 @ sk_B @ sk_A))
% 0.76/0.95          | (r1_tarski @ sk_C_1 @ X0))),
% 0.76/0.95      inference('sup-', [status(thm)], ['16', '40'])).
% 0.76/0.95  thf('42', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((r2_hidden @ 
% 0.76/0.95           (k4_tarski @ (sk_C @ X0 @ sk_C_1) @ (sk_D_1 @ X0 @ sk_C_1)) @ 
% 0.76/0.95           (k7_relat_1 @ sk_B @ sk_A))
% 0.76/0.95          | (r1_tarski @ sk_C_1 @ X0))),
% 0.76/0.95      inference('simplify', [status(thm)], ['41'])).
% 0.76/0.95  thf('43', plain,
% 0.76/0.95      (![X6 : $i, X7 : $i]:
% 0.76/0.95         (~ (r2_hidden @ (k4_tarski @ (sk_C @ X6 @ X7) @ (sk_D_1 @ X6 @ X7)) @ 
% 0.76/0.95             X6)
% 0.76/0.95          | (r1_tarski @ X7 @ X6)
% 0.76/0.95          | ~ (v1_relat_1 @ X7))),
% 0.76/0.95      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.76/0.95  thf('44', plain,
% 0.76/0.95      (((r1_tarski @ sk_C_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.76/0.95        | ~ (v1_relat_1 @ sk_C_1)
% 0.76/0.95        | (r1_tarski @ sk_C_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['42', '43'])).
% 0.76/0.95  thf('45', plain, ((v1_relat_1 @ sk_C_1)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('46', plain,
% 0.76/0.95      (((r1_tarski @ sk_C_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.76/0.95        | (r1_tarski @ sk_C_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.76/0.95      inference('demod', [status(thm)], ['44', '45'])).
% 0.76/0.95  thf('47', plain, ((r1_tarski @ sk_C_1 @ (k7_relat_1 @ sk_B @ sk_A))),
% 0.76/0.95      inference('simplify', [status(thm)], ['46'])).
% 0.76/0.95  thf('48', plain, ($false), inference('demod', [status(thm)], ['0', '47'])).
% 0.76/0.95  
% 0.76/0.95  % SZS output end Refutation
% 0.76/0.95  
% 0.76/0.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
