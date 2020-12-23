%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wxexnTjdBZ

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:33 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 180 expanded)
%              Number of leaves         :   15 (  53 expanded)
%              Depth                    :   15
%              Number of atoms          :  658 (2925 expanded)
%              Number of equality atoms :   24 ( 117 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(t38_wellord1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( v2_wellord1 @ C )
          & ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) )
       => ( ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) )
        <=> ( ( A = B )
            | ( r2_hidden @ A @ ( k1_wellord1 @ C @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( ( v2_wellord1 @ C )
            & ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
            & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) )
         => ( ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) )
          <=> ( ( A = B )
              | ( r2_hidden @ A @ ( k1_wellord1 @ C @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_wellord1])).

thf('0',plain,
    ( ( sk_A != sk_B )
    | ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) )
   <= ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_A != sk_B )
    | ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B ) )
    | ( sk_A = sk_B )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) )
   <= ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,
    ( ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
   <= ( ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_A != sk_B )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B ) )
    | ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) )
   <= ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf(t37_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( v2_wellord1 @ C )
          & ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) )
       => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
        <=> ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v2_wellord1 @ X10 )
      | ~ ( r2_hidden @ X11 @ ( k3_relat_1 @ X10 ) )
      | ~ ( r2_hidden @ X12 @ ( k3_relat_1 @ X10 ) )
      | ~ ( r1_tarski @ ( k1_wellord1 @ X10 @ X11 ) @ ( k1_wellord1 @ X10 @ X12 ) )
      | ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t37_wellord1])).

thf('16',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      | ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) )
      | ~ ( v2_wellord1 @ sk_C_1 ) )
   <= ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v2_wellord1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 )
   <= ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf(d1_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k1_wellord1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ( ( D != B )
                & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) )).

thf('22',plain,(
    ! [X5: $i,X6: $i,X7: $i,X9: $i] :
      ( ( X7
       != ( k1_wellord1 @ X6 @ X5 ) )
      | ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X5 ) @ X6 )
      | ( X9 = X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('23',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( X9 = X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X5 ) @ X6 )
      | ( r2_hidden @ X9 @ ( k1_wellord1 @ X6 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B ) )
      | ( sk_A = sk_B )
      | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B ) )
      | ( sk_A = sk_B ) )
   <= ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['12'])).

thf('28',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B ) )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_A != sk_B )
   <= ( sk_A != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('30',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != sk_B )
      & ~ ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B ) )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B ) )
    | ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) )
    | ( sk_A = sk_B ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['2','11','13','31'])).

thf('33',plain,(
    ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['1','32'])).

thf('34',plain,
    ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('35',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X7
       != ( k1_wellord1 @ X6 @ X5 ) )
      | ( r2_hidden @ ( k4_tarski @ X8 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('36',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k1_wellord1 @ X6 @ X5 ) )
      | ( r2_hidden @ ( k4_tarski @ X8 @ X5 ) @ X6 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 )
   <= ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B ) )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) )
    | ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('41',plain,(
    r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','11','13','31','40'])).

thf('42',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ),
    inference(simpl_trail,[status(thm)],['39','41'])).

thf('43',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v2_wellord1 @ X10 )
      | ~ ( r2_hidden @ X11 @ ( k3_relat_1 @ X10 ) )
      | ~ ( r2_hidden @ X12 @ ( k3_relat_1 @ X10 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ X10 )
      | ( r1_tarski @ ( k1_wellord1 @ X10 @ X11 ) @ ( k1_wellord1 @ X10 @ X12 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t37_wellord1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_C_1 ) )
      | ~ ( v2_wellord1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_wellord1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_1 ) )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,(
    r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['33','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wxexnTjdBZ
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:35:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 65 iterations in 0.039s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.49  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.49  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.19/0.49  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.19/0.49  thf(t38_wellord1, conjecture,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ C ) =>
% 0.19/0.49       ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.19/0.49           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) =>
% 0.19/0.49         ( ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) <=>
% 0.19/0.49           ( ( ( A ) = ( B ) ) | ( r2_hidden @ A @ ( k1_wellord1 @ C @ B ) ) ) ) ) ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.49        ( ( v1_relat_1 @ C ) =>
% 0.19/0.49          ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.19/0.49              ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) =>
% 0.19/0.49            ( ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) <=>
% 0.19/0.49              ( ( ( A ) = ( B ) ) | ( r2_hidden @ A @ ( k1_wellord1 @ C @ B ) ) ) ) ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t38_wellord1])).
% 0.19/0.49  thf('0', plain,
% 0.19/0.49      ((((sk_A) != (sk_B))
% 0.19/0.49        | ~ (r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.19/0.49             (k1_wellord1 @ sk_C_1 @ sk_B)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('1', plain,
% 0.19/0.49      ((~ (r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.19/0.49           (k1_wellord1 @ sk_C_1 @ sk_B)))
% 0.19/0.49         <= (~
% 0.19/0.49             ((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.19/0.49               (k1_wellord1 @ sk_C_1 @ sk_B))))),
% 0.19/0.49      inference('split', [status(esa)], ['0'])).
% 0.19/0.49  thf('2', plain,
% 0.19/0.49      (~ (((sk_A) = (sk_B))) | 
% 0.19/0.49       ~
% 0.19/0.49       ((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.19/0.49         (k1_wellord1 @ sk_C_1 @ sk_B)))),
% 0.19/0.49      inference('split', [status(esa)], ['0'])).
% 0.19/0.49  thf(d3_tarski, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( r1_tarski @ A @ B ) <=>
% 0.19/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.19/0.49  thf('3', plain,
% 0.19/0.49      (![X1 : $i, X3 : $i]:
% 0.19/0.49         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.49  thf('4', plain,
% 0.19/0.49      (![X1 : $i, X3 : $i]:
% 0.19/0.49         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.49  thf('5', plain,
% 0.19/0.49      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.49  thf('6', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.19/0.49      inference('simplify', [status(thm)], ['5'])).
% 0.19/0.49  thf('7', plain,
% 0.19/0.49      (((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B))
% 0.19/0.49        | ((sk_A) = (sk_B))
% 0.19/0.49        | (r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.19/0.49           (k1_wellord1 @ sk_C_1 @ sk_B)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('8', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 0.19/0.49      inference('split', [status(esa)], ['7'])).
% 0.19/0.49  thf('9', plain,
% 0.19/0.49      ((~ (r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.19/0.49           (k1_wellord1 @ sk_C_1 @ sk_B)))
% 0.19/0.49         <= (~
% 0.19/0.49             ((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.19/0.49               (k1_wellord1 @ sk_C_1 @ sk_B))))),
% 0.19/0.49      inference('split', [status(esa)], ['0'])).
% 0.19/0.49  thf('10', plain,
% 0.19/0.49      ((~ (r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.19/0.49           (k1_wellord1 @ sk_C_1 @ sk_A)))
% 0.19/0.49         <= (~
% 0.19/0.49             ((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.19/0.49               (k1_wellord1 @ sk_C_1 @ sk_B))) & 
% 0.19/0.49             (((sk_A) = (sk_B))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.49  thf('11', plain,
% 0.19/0.49      (~ (((sk_A) = (sk_B))) | 
% 0.19/0.49       ((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.19/0.49         (k1_wellord1 @ sk_C_1 @ sk_B)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['6', '10'])).
% 0.19/0.49  thf('12', plain,
% 0.19/0.49      ((~ (r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B))
% 0.19/0.49        | ~ (r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.19/0.49             (k1_wellord1 @ sk_C_1 @ sk_B)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('13', plain,
% 0.19/0.49      (~
% 0.19/0.49       ((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.19/0.49         (k1_wellord1 @ sk_C_1 @ sk_B))) | 
% 0.19/0.49       ~ ((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B)))),
% 0.19/0.49      inference('split', [status(esa)], ['12'])).
% 0.19/0.49  thf('14', plain,
% 0.19/0.49      (((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.19/0.49         (k1_wellord1 @ sk_C_1 @ sk_B)))
% 0.19/0.49         <= (((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.19/0.49               (k1_wellord1 @ sk_C_1 @ sk_B))))),
% 0.19/0.49      inference('split', [status(esa)], ['7'])).
% 0.19/0.49  thf(t37_wellord1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ C ) =>
% 0.19/0.49       ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.19/0.49           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) =>
% 0.19/0.49         ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.19/0.49           ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) ))).
% 0.19/0.49  thf('15', plain,
% 0.19/0.49      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.19/0.49         (~ (v2_wellord1 @ X10)
% 0.19/0.49          | ~ (r2_hidden @ X11 @ (k3_relat_1 @ X10))
% 0.19/0.49          | ~ (r2_hidden @ X12 @ (k3_relat_1 @ X10))
% 0.19/0.49          | ~ (r1_tarski @ (k1_wellord1 @ X10 @ X11) @ 
% 0.19/0.49               (k1_wellord1 @ X10 @ X12))
% 0.19/0.49          | (r2_hidden @ (k4_tarski @ X11 @ X12) @ X10)
% 0.19/0.49          | ~ (v1_relat_1 @ X10))),
% 0.19/0.49      inference('cnf', [status(esa)], [t37_wellord1])).
% 0.19/0.49  thf('16', plain,
% 0.19/0.49      (((~ (v1_relat_1 @ sk_C_1)
% 0.19/0.49         | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.19/0.49         | ~ (r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_1))
% 0.19/0.49         | ~ (r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))
% 0.19/0.49         | ~ (v2_wellord1 @ sk_C_1)))
% 0.19/0.49         <= (((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.19/0.49               (k1_wellord1 @ sk_C_1 @ sk_B))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.49  thf('17', plain, ((v1_relat_1 @ sk_C_1)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('18', plain, ((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_1))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('19', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('20', plain, ((v2_wellord1 @ sk_C_1)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('21', plain,
% 0.19/0.49      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1))
% 0.19/0.49         <= (((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.19/0.49               (k1_wellord1 @ sk_C_1 @ sk_B))))),
% 0.19/0.49      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 0.19/0.49  thf(d1_wellord1, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ A ) =>
% 0.19/0.49       ( ![B:$i,C:$i]:
% 0.19/0.49         ( ( ( C ) = ( k1_wellord1 @ A @ B ) ) <=>
% 0.19/0.49           ( ![D:$i]:
% 0.19/0.49             ( ( r2_hidden @ D @ C ) <=>
% 0.19/0.49               ( ( ( D ) != ( B ) ) & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) ) ))).
% 0.19/0.49  thf('22', plain,
% 0.19/0.49      (![X5 : $i, X6 : $i, X7 : $i, X9 : $i]:
% 0.19/0.49         (((X7) != (k1_wellord1 @ X6 @ X5))
% 0.19/0.49          | (r2_hidden @ X9 @ X7)
% 0.19/0.49          | ~ (r2_hidden @ (k4_tarski @ X9 @ X5) @ X6)
% 0.19/0.49          | ((X9) = (X5))
% 0.19/0.49          | ~ (v1_relat_1 @ X6))),
% 0.19/0.49      inference('cnf', [status(esa)], [d1_wellord1])).
% 0.19/0.49  thf('23', plain,
% 0.19/0.49      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.19/0.49         (~ (v1_relat_1 @ X6)
% 0.19/0.49          | ((X9) = (X5))
% 0.19/0.49          | ~ (r2_hidden @ (k4_tarski @ X9 @ X5) @ X6)
% 0.19/0.49          | (r2_hidden @ X9 @ (k1_wellord1 @ X6 @ X5)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['22'])).
% 0.19/0.49  thf('24', plain,
% 0.19/0.49      ((((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B))
% 0.19/0.49         | ((sk_A) = (sk_B))
% 0.19/0.49         | ~ (v1_relat_1 @ sk_C_1)))
% 0.19/0.49         <= (((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.19/0.49               (k1_wellord1 @ sk_C_1 @ sk_B))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['21', '23'])).
% 0.19/0.49  thf('25', plain, ((v1_relat_1 @ sk_C_1)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('26', plain,
% 0.19/0.49      ((((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B)) | ((sk_A) = (sk_B))))
% 0.19/0.49         <= (((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.19/0.49               (k1_wellord1 @ sk_C_1 @ sk_B))))),
% 0.19/0.49      inference('demod', [status(thm)], ['24', '25'])).
% 0.19/0.49  thf('27', plain,
% 0.19/0.49      ((~ (r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B)))
% 0.19/0.49         <= (~ ((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B))))),
% 0.19/0.49      inference('split', [status(esa)], ['12'])).
% 0.19/0.49  thf('28', plain,
% 0.19/0.49      ((((sk_A) = (sk_B)))
% 0.19/0.49         <= (~ ((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B))) & 
% 0.19/0.49             ((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.19/0.49               (k1_wellord1 @ sk_C_1 @ sk_B))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.49  thf('29', plain, ((((sk_A) != (sk_B))) <= (~ (((sk_A) = (sk_B))))),
% 0.19/0.49      inference('split', [status(esa)], ['0'])).
% 0.19/0.49  thf('30', plain,
% 0.19/0.49      ((((sk_A) != (sk_A)))
% 0.19/0.49         <= (~ (((sk_A) = (sk_B))) & 
% 0.19/0.49             ~ ((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B))) & 
% 0.19/0.49             ((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.19/0.49               (k1_wellord1 @ sk_C_1 @ sk_B))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['28', '29'])).
% 0.19/0.49  thf('31', plain,
% 0.19/0.49      (((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B))) | 
% 0.19/0.49       ~
% 0.19/0.49       ((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.19/0.49         (k1_wellord1 @ sk_C_1 @ sk_B))) | 
% 0.19/0.49       (((sk_A) = (sk_B)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['30'])).
% 0.19/0.49  thf('32', plain,
% 0.19/0.49      (~
% 0.19/0.49       ((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.19/0.49         (k1_wellord1 @ sk_C_1 @ sk_B)))),
% 0.19/0.49      inference('sat_resolution*', [status(thm)], ['2', '11', '13', '31'])).
% 0.19/0.49  thf('33', plain,
% 0.19/0.49      (~ (r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.19/0.49          (k1_wellord1 @ sk_C_1 @ sk_B))),
% 0.19/0.49      inference('simpl_trail', [status(thm)], ['1', '32'])).
% 0.19/0.49  thf('34', plain,
% 0.19/0.49      (((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B)))
% 0.19/0.49         <= (((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B))))),
% 0.19/0.49      inference('split', [status(esa)], ['7'])).
% 0.19/0.49  thf('35', plain,
% 0.19/0.49      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.49         (((X7) != (k1_wellord1 @ X6 @ X5))
% 0.19/0.49          | (r2_hidden @ (k4_tarski @ X8 @ X5) @ X6)
% 0.19/0.49          | ~ (r2_hidden @ X8 @ X7)
% 0.19/0.49          | ~ (v1_relat_1 @ X6))),
% 0.19/0.49      inference('cnf', [status(esa)], [d1_wellord1])).
% 0.19/0.49  thf('36', plain,
% 0.19/0.49      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.19/0.49         (~ (v1_relat_1 @ X6)
% 0.19/0.49          | ~ (r2_hidden @ X8 @ (k1_wellord1 @ X6 @ X5))
% 0.19/0.49          | (r2_hidden @ (k4_tarski @ X8 @ X5) @ X6))),
% 0.19/0.49      inference('simplify', [status(thm)], ['35'])).
% 0.19/0.49  thf('37', plain,
% 0.19/0.49      ((((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.19/0.49         | ~ (v1_relat_1 @ sk_C_1)))
% 0.19/0.49         <= (((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['34', '36'])).
% 0.19/0.49  thf('38', plain, ((v1_relat_1 @ sk_C_1)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('39', plain,
% 0.19/0.49      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1))
% 0.19/0.49         <= (((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B))))),
% 0.19/0.49      inference('demod', [status(thm)], ['37', '38'])).
% 0.19/0.49  thf('40', plain,
% 0.19/0.49      (((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B))) | 
% 0.19/0.49       ((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.19/0.49         (k1_wellord1 @ sk_C_1 @ sk_B))) | 
% 0.19/0.49       (((sk_A) = (sk_B)))),
% 0.19/0.49      inference('split', [status(esa)], ['7'])).
% 0.19/0.49  thf('41', plain, (((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B)))),
% 0.19/0.49      inference('sat_resolution*', [status(thm)], ['2', '11', '13', '31', '40'])).
% 0.19/0.49  thf('42', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1)),
% 0.19/0.49      inference('simpl_trail', [status(thm)], ['39', '41'])).
% 0.19/0.49  thf('43', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('44', plain,
% 0.19/0.49      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.19/0.49         (~ (v2_wellord1 @ X10)
% 0.19/0.49          | ~ (r2_hidden @ X11 @ (k3_relat_1 @ X10))
% 0.19/0.49          | ~ (r2_hidden @ X12 @ (k3_relat_1 @ X10))
% 0.19/0.49          | ~ (r2_hidden @ (k4_tarski @ X11 @ X12) @ X10)
% 0.19/0.49          | (r1_tarski @ (k1_wellord1 @ X10 @ X11) @ (k1_wellord1 @ X10 @ X12))
% 0.19/0.49          | ~ (v1_relat_1 @ X10))),
% 0.19/0.49      inference('cnf', [status(esa)], [t37_wellord1])).
% 0.19/0.49  thf('45', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (v1_relat_1 @ sk_C_1)
% 0.19/0.49          | (r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.19/0.49             (k1_wellord1 @ sk_C_1 @ X0))
% 0.19/0.49          | ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_1)
% 0.19/0.49          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C_1))
% 0.19/0.49          | ~ (v2_wellord1 @ sk_C_1))),
% 0.19/0.49      inference('sup-', [status(thm)], ['43', '44'])).
% 0.19/0.49  thf('46', plain, ((v1_relat_1 @ sk_C_1)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('47', plain, ((v2_wellord1 @ sk_C_1)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('48', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.19/0.49           (k1_wellord1 @ sk_C_1 @ X0))
% 0.19/0.49          | ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_1)
% 0.19/0.49          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C_1)))),
% 0.19/0.49      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.19/0.49  thf('49', plain,
% 0.19/0.49      ((~ (r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_1))
% 0.19/0.49        | (r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.19/0.49           (k1_wellord1 @ sk_C_1 @ sk_B)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['42', '48'])).
% 0.19/0.49  thf('50', plain, ((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_1))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('51', plain,
% 0.19/0.49      ((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.19/0.49        (k1_wellord1 @ sk_C_1 @ sk_B))),
% 0.19/0.49      inference('demod', [status(thm)], ['49', '50'])).
% 0.19/0.49  thf('52', plain, ($false), inference('demod', [status(thm)], ['33', '51'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
