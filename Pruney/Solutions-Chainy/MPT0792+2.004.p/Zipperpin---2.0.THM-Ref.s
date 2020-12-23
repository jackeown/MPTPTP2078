%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bdoYe3bwxX

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 107 expanded)
%              Number of leaves         :   16 (  38 expanded)
%              Depth                    :   22
%              Number of atoms          :  709 (1822 expanded)
%              Number of equality atoms :   11 (  43 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(t42_wellord1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( v2_wellord1 @ C )
          & ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) )
          & ! [D: $i] :
              ( ( r2_hidden @ D @ ( k1_wellord1 @ C @ A ) )
             => ( ( r2_hidden @ ( k4_tarski @ D @ B ) @ C )
                & ( D != B ) ) ) )
       => ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( ( v2_wellord1 @ C )
            & ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
            & ( r2_hidden @ B @ ( k3_relat_1 @ C ) )
            & ! [D: $i] :
                ( ( r2_hidden @ D @ ( k1_wellord1 @ C @ A ) )
               => ( ( r2_hidden @ ( k4_tarski @ D @ B ) @ C )
                  & ( D != B ) ) ) )
         => ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t42_wellord1])).

thf('0',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    ! [X13: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X13 @ sk_B ) @ sk_C_1 )
      | ~ ( r2_hidden @ X13 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) @ sk_B ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t30_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 )
      | ( r2_hidden @ X4 @ ( k3_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ X0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) @ sk_B ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t37_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( v2_wellord1 @ C )
          & ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) )
       => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
        <=> ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v2_wellord1 @ X7 )
      | ~ ( r2_hidden @ X8 @ ( k3_relat_1 @ X7 ) )
      | ~ ( r2_hidden @ X9 @ ( k3_relat_1 @ X7 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X7 )
      | ( r1_tarski @ ( k1_wellord1 @ X7 @ X8 ) @ ( k1_wellord1 @ X7 @ X9 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t37_wellord1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ X0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) @ ( k1_wellord1 @ sk_C_1 @ X1 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) @ X1 ) @ sk_C_1 )
      | ~ ( r2_hidden @ X1 @ ( k3_relat_1 @ sk_C_1 ) )
      | ~ ( v2_wellord1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v2_wellord1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) @ ( k1_wellord1 @ sk_C_1 @ X1 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) @ X1 ) @ sk_C_1 )
      | ~ ( r2_hidden @ X1 @ ( k3_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_1 ) )
      | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) )
      | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) )
      | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) )
      | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t38_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( v2_wellord1 @ C )
          & ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) )
       => ( ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) )
        <=> ( ( A = B )
            | ( r2_hidden @ A @ ( k1_wellord1 @ C @ B ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v2_wellord1 @ X10 )
      | ~ ( r2_hidden @ X11 @ ( k3_relat_1 @ X10 ) )
      | ~ ( r2_hidden @ X12 @ ( k3_relat_1 @ X10 ) )
      | ~ ( r1_tarski @ ( k1_wellord1 @ X10 @ X11 ) @ ( k1_wellord1 @ X10 @ X12 ) )
      | ( X11 = X12 )
      | ( r2_hidden @ X11 @ ( k1_wellord1 @ X10 @ X12 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t38_wellord1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ X0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) )
      | ( ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
        = sk_B )
      | ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_C_1 ) )
      | ~ ( v2_wellord1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v2_wellord1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) )
      | ( ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
        = sk_B )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ X0 )
      | ( ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
        = sk_B )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) )
      | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) )
      | ( ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
        = sk_B )
      | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) )
    | ( ( sk_C @ ( k1_wellord1 @ sk_C_1 @ sk_B ) @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
      = sk_B )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( sk_C @ ( k1_wellord1 @ sk_C_1 @ sk_B ) @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
      = sk_B )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,
    ( ( r2_hidden @ sk_B @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) )
    | ( r2_hidden @ sk_B @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X13: $i] :
      ( ( X13 != sk_B )
      | ~ ( r2_hidden @ X13 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ~ ( r2_hidden @ sk_B @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) ),
    inference(clc,[status(thm)],['32','34'])).

thf('36',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v2_wellord1 @ X7 )
      | ~ ( r2_hidden @ X8 @ ( k3_relat_1 @ X7 ) )
      | ~ ( r2_hidden @ X9 @ ( k3_relat_1 @ X7 ) )
      | ~ ( r1_tarski @ ( k1_wellord1 @ X7 @ X8 ) @ ( k1_wellord1 @ X7 @ X9 ) )
      | ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t37_wellord1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    | ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) )
    | ~ ( v2_wellord1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_wellord1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ),
    inference(demod,[status(thm)],['37','38','39','40','41'])).

thf('43',plain,(
    $false ),
    inference(demod,[status(thm)],['0','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bdoYe3bwxX
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:02:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 47 iterations in 0.034s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.49  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.20/0.49  thf(t42_wellord1, conjecture,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ C ) =>
% 0.20/0.49       ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.20/0.49           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) & 
% 0.20/0.49           ( ![D:$i]:
% 0.20/0.49             ( ( r2_hidden @ D @ ( k1_wellord1 @ C @ A ) ) =>
% 0.20/0.49               ( ( r2_hidden @ ( k4_tarski @ D @ B ) @ C ) & ( ( D ) != ( B ) ) ) ) ) ) =>
% 0.20/0.49         ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.49        ( ( v1_relat_1 @ C ) =>
% 0.20/0.49          ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.20/0.49              ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) & 
% 0.20/0.49              ( ![D:$i]:
% 0.20/0.49                ( ( r2_hidden @ D @ ( k1_wellord1 @ C @ A ) ) =>
% 0.20/0.49                  ( ( r2_hidden @ ( k4_tarski @ D @ B ) @ C ) & 
% 0.20/0.49                    ( ( D ) != ( B ) ) ) ) ) ) =>
% 0.20/0.49            ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t42_wellord1])).
% 0.20/0.49  thf('0', plain, (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(d3_tarski, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X1 : $i, X3 : $i]:
% 0.20/0.49         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X13 : $i]:
% 0.20/0.49         ((r2_hidden @ (k4_tarski @ X13 @ sk_B) @ sk_C_1)
% 0.20/0.49          | ~ (r2_hidden @ X13 @ (k1_wellord1 @ sk_C_1 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ X0)
% 0.20/0.49          | (r2_hidden @ 
% 0.20/0.49             (k4_tarski @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_1 @ sk_A)) @ sk_B) @ 
% 0.20/0.49             sk_C_1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf(t30_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ C ) =>
% 0.20/0.49       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.20/0.49         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.20/0.49           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ))).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.49         (~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ X6)
% 0.20/0.49          | (r2_hidden @ X4 @ (k3_relat_1 @ X6))
% 0.20/0.49          | ~ (v1_relat_1 @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [t30_relat_1])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ sk_C_1)
% 0.20/0.49          | (r2_hidden @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_1 @ sk_A)) @ 
% 0.20/0.49             (k3_relat_1 @ sk_C_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.49  thf('6', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ X0)
% 0.20/0.49          | (r2_hidden @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_1 @ sk_A)) @ 
% 0.20/0.49             (k3_relat_1 @ sk_C_1)))),
% 0.20/0.49      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ X0)
% 0.20/0.49          | (r2_hidden @ 
% 0.20/0.49             (k4_tarski @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_1 @ sk_A)) @ sk_B) @ 
% 0.20/0.49             sk_C_1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ X0)
% 0.20/0.49          | (r2_hidden @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_1 @ sk_A)) @ 
% 0.20/0.49             (k3_relat_1 @ sk_C_1)))),
% 0.20/0.49      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.49  thf(t37_wellord1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ C ) =>
% 0.20/0.49       ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.20/0.49           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) =>
% 0.20/0.49         ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.20/0.49           ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) ))).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.49         (~ (v2_wellord1 @ X7)
% 0.20/0.49          | ~ (r2_hidden @ X8 @ (k3_relat_1 @ X7))
% 0.20/0.49          | ~ (r2_hidden @ X9 @ (k3_relat_1 @ X7))
% 0.20/0.49          | ~ (r2_hidden @ (k4_tarski @ X8 @ X9) @ X7)
% 0.20/0.49          | (r1_tarski @ (k1_wellord1 @ X7 @ X8) @ (k1_wellord1 @ X7 @ X9))
% 0.20/0.49          | ~ (v1_relat_1 @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [t37_wellord1])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ sk_C_1)
% 0.20/0.49          | (r1_tarski @ 
% 0.20/0.49             (k1_wellord1 @ sk_C_1 @ 
% 0.20/0.49              (sk_C @ X0 @ (k1_wellord1 @ sk_C_1 @ sk_A))) @ 
% 0.20/0.49             (k1_wellord1 @ sk_C_1 @ X1))
% 0.20/0.49          | ~ (r2_hidden @ 
% 0.20/0.49               (k4_tarski @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_1 @ sk_A)) @ X1) @ 
% 0.20/0.49               sk_C_1)
% 0.20/0.49          | ~ (r2_hidden @ X1 @ (k3_relat_1 @ sk_C_1))
% 0.20/0.49          | ~ (v2_wellord1 @ sk_C_1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.49  thf('12', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('13', plain, ((v2_wellord1 @ sk_C_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ X0)
% 0.20/0.49          | (r1_tarski @ 
% 0.20/0.49             (k1_wellord1 @ sk_C_1 @ 
% 0.20/0.49              (sk_C @ X0 @ (k1_wellord1 @ sk_C_1 @ sk_A))) @ 
% 0.20/0.49             (k1_wellord1 @ sk_C_1 @ X1))
% 0.20/0.49          | ~ (r2_hidden @ 
% 0.20/0.49               (k4_tarski @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_1 @ sk_A)) @ X1) @ 
% 0.20/0.49               sk_C_1)
% 0.20/0.49          | ~ (r2_hidden @ X1 @ (k3_relat_1 @ sk_C_1)))),
% 0.20/0.49      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ X0)
% 0.20/0.49          | ~ (r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_1))
% 0.20/0.49          | (r1_tarski @ 
% 0.20/0.49             (k1_wellord1 @ sk_C_1 @ 
% 0.20/0.49              (sk_C @ X0 @ (k1_wellord1 @ sk_C_1 @ sk_A))) @ 
% 0.20/0.49             (k1_wellord1 @ sk_C_1 @ sk_B))
% 0.20/0.49          | (r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['8', '14'])).
% 0.20/0.49  thf('16', plain, ((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_1))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ X0)
% 0.20/0.49          | (r1_tarski @ 
% 0.20/0.49             (k1_wellord1 @ sk_C_1 @ 
% 0.20/0.49              (sk_C @ X0 @ (k1_wellord1 @ sk_C_1 @ sk_A))) @ 
% 0.20/0.49             (k1_wellord1 @ sk_C_1 @ sk_B))
% 0.20/0.49          | (r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r1_tarski @ 
% 0.20/0.49           (k1_wellord1 @ sk_C_1 @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_1 @ sk_A))) @ 
% 0.20/0.49           (k1_wellord1 @ sk_C_1 @ sk_B))
% 0.20/0.49          | (r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.49  thf(t38_wellord1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ C ) =>
% 0.20/0.49       ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.20/0.49           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) =>
% 0.20/0.49         ( ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) <=>
% 0.20/0.49           ( ( ( A ) = ( B ) ) | ( r2_hidden @ A @ ( k1_wellord1 @ C @ B ) ) ) ) ) ))).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.49         (~ (v2_wellord1 @ X10)
% 0.20/0.49          | ~ (r2_hidden @ X11 @ (k3_relat_1 @ X10))
% 0.20/0.49          | ~ (r2_hidden @ X12 @ (k3_relat_1 @ X10))
% 0.20/0.49          | ~ (r1_tarski @ (k1_wellord1 @ X10 @ X11) @ 
% 0.20/0.49               (k1_wellord1 @ X10 @ X12))
% 0.20/0.49          | ((X11) = (X12))
% 0.20/0.49          | (r2_hidden @ X11 @ (k1_wellord1 @ X10 @ X12))
% 0.20/0.49          | ~ (v1_relat_1 @ X10))),
% 0.20/0.49      inference('cnf', [status(esa)], [t38_wellord1])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ sk_C_1)
% 0.20/0.49          | (r2_hidden @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_1 @ sk_A)) @ 
% 0.20/0.49             (k1_wellord1 @ sk_C_1 @ sk_B))
% 0.20/0.49          | ((sk_C @ X0 @ (k1_wellord1 @ sk_C_1 @ sk_A)) = (sk_B))
% 0.20/0.49          | ~ (r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_1))
% 0.20/0.49          | ~ (r2_hidden @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_1 @ sk_A)) @ 
% 0.20/0.49               (k3_relat_1 @ sk_C_1))
% 0.20/0.49          | ~ (v2_wellord1 @ sk_C_1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.49  thf('21', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('22', plain, ((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_1))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('23', plain, ((v2_wellord1 @ sk_C_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ X0)
% 0.20/0.49          | (r2_hidden @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_1 @ sk_A)) @ 
% 0.20/0.49             (k1_wellord1 @ sk_C_1 @ sk_B))
% 0.20/0.49          | ((sk_C @ X0 @ (k1_wellord1 @ sk_C_1 @ sk_A)) = (sk_B))
% 0.20/0.49          | ~ (r2_hidden @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_1 @ sk_A)) @ 
% 0.20/0.49               (k3_relat_1 @ sk_C_1)))),
% 0.20/0.49      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ X0)
% 0.20/0.49          | ((sk_C @ X0 @ (k1_wellord1 @ sk_C_1 @ sk_A)) = (sk_B))
% 0.20/0.49          | (r2_hidden @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_1 @ sk_A)) @ 
% 0.20/0.49             (k1_wellord1 @ sk_C_1 @ sk_B))
% 0.20/0.49          | (r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['7', '24'])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r2_hidden @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_1 @ sk_A)) @ 
% 0.20/0.49           (k1_wellord1 @ sk_C_1 @ sk_B))
% 0.20/0.49          | ((sk_C @ X0 @ (k1_wellord1 @ sk_C_1 @ sk_A)) = (sk_B))
% 0.20/0.49          | (r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X1 : $i, X3 : $i]:
% 0.20/0.49         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.20/0.49         (k1_wellord1 @ sk_C_1 @ sk_B))
% 0.20/0.49        | ((sk_C @ (k1_wellord1 @ sk_C_1 @ sk_B) @ 
% 0.20/0.49            (k1_wellord1 @ sk_C_1 @ sk_A)) = (sk_B))
% 0.20/0.49        | (r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.20/0.49           (k1_wellord1 @ sk_C_1 @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      ((((sk_C @ (k1_wellord1 @ sk_C_1 @ sk_B) @ (k1_wellord1 @ sk_C_1 @ sk_A))
% 0.20/0.49          = (sk_B))
% 0.20/0.49        | (r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.20/0.49           (k1_wellord1 @ sk_C_1 @ sk_B)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (![X1 : $i, X3 : $i]:
% 0.20/0.49         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (((r2_hidden @ sk_B @ (k1_wellord1 @ sk_C_1 @ sk_A))
% 0.20/0.49        | (r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.20/0.49           (k1_wellord1 @ sk_C_1 @ sk_B))
% 0.20/0.49        | (r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.20/0.49           (k1_wellord1 @ sk_C_1 @ sk_B)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['29', '30'])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.20/0.49         (k1_wellord1 @ sk_C_1 @ sk_B))
% 0.20/0.49        | (r2_hidden @ sk_B @ (k1_wellord1 @ sk_C_1 @ sk_A)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (![X13 : $i]:
% 0.20/0.49         (((X13) != (sk_B))
% 0.20/0.49          | ~ (r2_hidden @ X13 @ (k1_wellord1 @ sk_C_1 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('34', plain, (~ (r2_hidden @ sk_B @ (k1_wellord1 @ sk_C_1 @ sk_A))),
% 0.20/0.49      inference('simplify', [status(thm)], ['33'])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      ((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.20/0.49        (k1_wellord1 @ sk_C_1 @ sk_B))),
% 0.20/0.49      inference('clc', [status(thm)], ['32', '34'])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.49         (~ (v2_wellord1 @ X7)
% 0.20/0.49          | ~ (r2_hidden @ X8 @ (k3_relat_1 @ X7))
% 0.20/0.49          | ~ (r2_hidden @ X9 @ (k3_relat_1 @ X7))
% 0.20/0.49          | ~ (r1_tarski @ (k1_wellord1 @ X7 @ X8) @ (k1_wellord1 @ X7 @ X9))
% 0.20/0.49          | (r2_hidden @ (k4_tarski @ X8 @ X9) @ X7)
% 0.20/0.49          | ~ (v1_relat_1 @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [t37_wellord1])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ sk_C_1)
% 0.20/0.49        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.20/0.49        | ~ (r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_1))
% 0.20/0.49        | ~ (r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))
% 0.20/0.49        | ~ (v2_wellord1 @ sk_C_1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.49  thf('38', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('39', plain, ((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_1))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('40', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('41', plain, ((v2_wellord1 @ sk_C_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('42', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1)),
% 0.20/0.49      inference('demod', [status(thm)], ['37', '38', '39', '40', '41'])).
% 0.20/0.49  thf('43', plain, ($false), inference('demod', [status(thm)], ['0', '42'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
