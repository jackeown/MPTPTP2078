%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.L5vVOK6La7

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 117 expanded)
%              Number of leaves         :   20 (  44 expanded)
%              Depth                    :   14
%              Number of atoms          :  585 (1956 expanded)
%              Number of equality atoms :   20 (  65 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_wellord1_type,type,(
    v1_wellord1: $i > $o )).

thf(v6_relat_2_type,type,(
    v6_relat_2: $i > $o )).

thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

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
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_B_1 @ ( k3_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l4_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v6_relat_2 @ A )
      <=> ! [B: $i,C: $i] :
            ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
              & ( r2_hidden @ C @ ( k3_relat_1 @ A ) )
              & ( B != C )
              & ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
              & ~ ( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v6_relat_2 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k3_relat_1 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ X1 )
      | ( X2 = X3 )
      | ~ ( r2_hidden @ X3 @ ( k3_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l4_wellord1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_C_1 ) )
      | ( sk_A = X0 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ sk_A ) @ sk_C_1 )
      | ~ ( v6_relat_2 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
      <=> ( ( v1_relat_2 @ A )
          & ( v8_relat_2 @ A )
          & ( v4_relat_2 @ A )
          & ( v6_relat_2 @ A )
          & ( v1_wellord1 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v2_wellord1 @ X0 )
      | ( v6_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('8',plain,
    ( ( v6_relat_2 @ sk_C_1 )
    | ~ ( v2_wellord1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v2_wellord1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v6_relat_2 @ sk_C_1 ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_C_1 ) )
      | ( sk_A = X0 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ sk_A ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['4','5','10'])).

thf('12',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_A ) @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_1 )
    | ( sk_A = sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('13',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( sk_A = sk_B_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_A ) @ sk_C_1 ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    r2_hidden @ sk_B_1 @ ( k3_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t37_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( v2_wellord1 @ C )
          & ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) )
       => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
        <=> ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) ) )).

thf('16',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v2_wellord1 @ X4 )
      | ~ ( r2_hidden @ X5 @ ( k3_relat_1 @ X4 ) )
      | ~ ( r2_hidden @ X6 @ ( k3_relat_1 @ X4 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X6 ) @ X4 )
      | ( r1_tarski @ ( k1_wellord1 @ X4 @ X5 ) @ ( k1_wellord1 @ X4 @ X6 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_wellord1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) @ ( k1_wellord1 @ sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_B_1 @ X0 ) @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_C_1 ) )
      | ~ ( v2_wellord1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v2_wellord1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) @ ( k1_wellord1 @ sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_B_1 @ X0 ) @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ( sk_A = sk_B_1 )
    | ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( sk_A = sk_B_1 )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t38_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( v2_wellord1 @ C )
          & ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) )
       => ( ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) )
        <=> ( ( A = B )
            | ( r2_hidden @ A @ ( k1_wellord1 @ C @ B ) ) ) ) ) ) )).

thf('24',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v2_wellord1 @ X7 )
      | ~ ( r2_hidden @ X8 @ ( k3_relat_1 @ X7 ) )
      | ~ ( r2_hidden @ X9 @ ( k3_relat_1 @ X7 ) )
      | ~ ( r1_tarski @ ( k1_wellord1 @ X7 @ X8 ) @ ( k1_wellord1 @ X7 @ X9 ) )
      | ( X8 = X9 )
      | ( r2_hidden @ X8 @ ( k1_wellord1 @ X7 @ X9 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t38_wellord1])).

thf('25',plain,
    ( ( sk_A = sk_B_1 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( r2_hidden @ sk_B_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ( sk_B_1 = sk_A )
    | ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_B_1 @ ( k3_relat_1 @ sk_C_1 ) )
    | ~ ( v2_wellord1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    r2_hidden @ sk_B_1 @ ( k3_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_wellord1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( sk_A = sk_B_1 )
    | ( r2_hidden @ sk_B_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ( sk_B_1 = sk_A ) ),
    inference(demod,[status(thm)],['25','26','27','28','29'])).

thf('31',plain,
    ( ( r2_hidden @ sk_B_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ( sk_A = sk_B_1 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X10: $i] :
      ( ( X10 != sk_B_1 )
      | ~ ( r2_hidden @ X10 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ~ ( r2_hidden @ sk_B_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    sk_A = sk_B_1 ),
    inference(clc,[status(thm)],['31','33'])).

thf('35',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v2_wellord1 @ X7 )
      | ~ ( r2_hidden @ X8 @ ( k3_relat_1 @ X7 ) )
      | ~ ( r2_hidden @ X9 @ ( k3_relat_1 @ X7 ) )
      | ( X8 != X9 )
      | ( r1_tarski @ ( k1_wellord1 @ X7 @ X8 ) @ ( k1_wellord1 @ X7 @ X9 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t38_wellord1])).

thf('37',plain,(
    ! [X7: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( r1_tarski @ ( k1_wellord1 @ X7 @ X9 ) @ ( k1_wellord1 @ X7 @ X9 ) )
      | ~ ( r2_hidden @ X9 @ ( k3_relat_1 @ X7 ) )
      | ~ ( v2_wellord1 @ X7 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ~ ( v2_wellord1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    v2_wellord1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v2_wellord1 @ X4 )
      | ~ ( r2_hidden @ X5 @ ( k3_relat_1 @ X4 ) )
      | ~ ( r2_hidden @ X6 @ ( k3_relat_1 @ X4 ) )
      | ~ ( r1_tarski @ ( k1_wellord1 @ X4 @ X5 ) @ ( k1_wellord1 @ X4 @ X6 ) )
      | ( r2_hidden @ ( k4_tarski @ X5 @ X6 ) @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_wellord1])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_A ) @ sk_C_1 )
    | ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) )
    | ~ ( v2_wellord1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_wellord1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_A ) @ sk_C_1 ),
    inference(demod,[status(thm)],['43','44','45','46','47'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['0','34','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.L5vVOK6La7
% 0.14/0.36  % Computer   : n011.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 19:11:42 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 42 iterations in 0.028s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(v8_relat_2_type, type, v8_relat_2: $i > $o).
% 0.22/0.50  thf(v1_relat_2_type, type, v1_relat_2: $i > $o).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.50  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.22/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.22/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.50  thf(v1_wellord1_type, type, v1_wellord1: $i > $o).
% 0.22/0.50  thf(v6_relat_2_type, type, v6_relat_2: $i > $o).
% 0.22/0.50  thf(v4_relat_2_type, type, v4_relat_2: $i > $o).
% 0.22/0.50  thf(t42_wellord1, conjecture,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ C ) =>
% 0.22/0.50       ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.22/0.50           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) & 
% 0.22/0.50           ( ![D:$i]:
% 0.22/0.50             ( ( r2_hidden @ D @ ( k1_wellord1 @ C @ A ) ) =>
% 0.22/0.50               ( ( r2_hidden @ ( k4_tarski @ D @ B ) @ C ) & ( ( D ) != ( B ) ) ) ) ) ) =>
% 0.22/0.50         ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.50        ( ( v1_relat_1 @ C ) =>
% 0.22/0.50          ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.22/0.50              ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) & 
% 0.22/0.50              ( ![D:$i]:
% 0.22/0.50                ( ( r2_hidden @ D @ ( k1_wellord1 @ C @ A ) ) =>
% 0.22/0.50                  ( ( r2_hidden @ ( k4_tarski @ D @ B ) @ C ) & 
% 0.22/0.50                    ( ( D ) != ( B ) ) ) ) ) ) =>
% 0.22/0.50            ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t42_wellord1])).
% 0.22/0.50  thf('0', plain, (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('1', plain, ((r2_hidden @ sk_B_1 @ (k3_relat_1 @ sk_C_1))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('2', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(l4_wellord1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ A ) =>
% 0.22/0.50       ( ( v6_relat_2 @ A ) <=>
% 0.22/0.50         ( ![B:$i,C:$i]:
% 0.22/0.50           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 0.22/0.50                ( r2_hidden @ C @ ( k3_relat_1 @ A ) ) & ( ( B ) != ( C ) ) & 
% 0.22/0.50                ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) & 
% 0.22/0.50                ( ~( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) ) ) ) ) ) ))).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.50         (~ (v6_relat_2 @ X1)
% 0.22/0.50          | ~ (r2_hidden @ X2 @ (k3_relat_1 @ X1))
% 0.22/0.50          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ X1)
% 0.22/0.50          | (r2_hidden @ (k4_tarski @ X2 @ X3) @ X1)
% 0.22/0.50          | ((X2) = (X3))
% 0.22/0.50          | ~ (r2_hidden @ X3 @ (k3_relat_1 @ X1))
% 0.22/0.50          | ~ (v1_relat_1 @ X1))),
% 0.22/0.50      inference('cnf', [status(esa)], [l4_wellord1])).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ sk_C_1)
% 0.22/0.50          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C_1))
% 0.22/0.50          | ((sk_A) = (X0))
% 0.22/0.50          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_1)
% 0.22/0.50          | (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ sk_C_1)
% 0.22/0.50          | ~ (v6_relat_2 @ sk_C_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.50  thf('5', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('6', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(d4_wellord1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ A ) =>
% 0.22/0.50       ( ( v2_wellord1 @ A ) <=>
% 0.22/0.50         ( ( v1_relat_2 @ A ) & ( v8_relat_2 @ A ) & ( v4_relat_2 @ A ) & 
% 0.22/0.50           ( v6_relat_2 @ A ) & ( v1_wellord1 @ A ) ) ) ))).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v2_wellord1 @ X0) | (v6_relat_2 @ X0) | ~ (v1_relat_1 @ X0))),
% 0.22/0.50      inference('cnf', [status(esa)], [d4_wellord1])).
% 0.22/0.50  thf('8', plain, (((v6_relat_2 @ sk_C_1) | ~ (v2_wellord1 @ sk_C_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.50  thf('9', plain, ((v2_wellord1 @ sk_C_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('10', plain, ((v6_relat_2 @ sk_C_1)),
% 0.22/0.50      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C_1))
% 0.22/0.50          | ((sk_A) = (X0))
% 0.22/0.50          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_1)
% 0.22/0.50          | (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ sk_C_1))),
% 0.22/0.50      inference('demod', [status(thm)], ['4', '5', '10'])).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (((r2_hidden @ (k4_tarski @ sk_B_1 @ sk_A) @ sk_C_1)
% 0.22/0.50        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_1)
% 0.22/0.50        | ((sk_A) = (sk_B_1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['1', '11'])).
% 0.22/0.50  thf('13', plain, (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      ((((sk_A) = (sk_B_1))
% 0.22/0.50        | (r2_hidden @ (k4_tarski @ sk_B_1 @ sk_A) @ sk_C_1))),
% 0.22/0.50      inference('clc', [status(thm)], ['12', '13'])).
% 0.22/0.50  thf('15', plain, ((r2_hidden @ sk_B_1 @ (k3_relat_1 @ sk_C_1))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t37_wellord1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ C ) =>
% 0.22/0.50       ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.22/0.50           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) =>
% 0.22/0.50         ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.22/0.50           ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) ))).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.50         (~ (v2_wellord1 @ X4)
% 0.22/0.50          | ~ (r2_hidden @ X5 @ (k3_relat_1 @ X4))
% 0.22/0.50          | ~ (r2_hidden @ X6 @ (k3_relat_1 @ X4))
% 0.22/0.50          | ~ (r2_hidden @ (k4_tarski @ X5 @ X6) @ X4)
% 0.22/0.50          | (r1_tarski @ (k1_wellord1 @ X4 @ X5) @ (k1_wellord1 @ X4 @ X6))
% 0.22/0.50          | ~ (v1_relat_1 @ X4))),
% 0.22/0.50      inference('cnf', [status(esa)], [t37_wellord1])).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ sk_C_1)
% 0.22/0.50          | (r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_B_1) @ 
% 0.22/0.50             (k1_wellord1 @ sk_C_1 @ X0))
% 0.22/0.50          | ~ (r2_hidden @ (k4_tarski @ sk_B_1 @ X0) @ sk_C_1)
% 0.22/0.50          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C_1))
% 0.22/0.50          | ~ (v2_wellord1 @ sk_C_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.50  thf('18', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('19', plain, ((v2_wellord1 @ sk_C_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_B_1) @ 
% 0.22/0.50           (k1_wellord1 @ sk_C_1 @ X0))
% 0.22/0.50          | ~ (r2_hidden @ (k4_tarski @ sk_B_1 @ X0) @ sk_C_1)
% 0.22/0.50          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C_1)))),
% 0.22/0.50      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      ((((sk_A) = (sk_B_1))
% 0.22/0.50        | ~ (r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))
% 0.22/0.50        | (r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_B_1) @ 
% 0.22/0.50           (k1_wellord1 @ sk_C_1 @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['14', '20'])).
% 0.22/0.50  thf('22', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      ((((sk_A) = (sk_B_1))
% 0.22/0.50        | (r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_B_1) @ 
% 0.22/0.50           (k1_wellord1 @ sk_C_1 @ sk_A)))),
% 0.22/0.50      inference('demod', [status(thm)], ['21', '22'])).
% 0.22/0.50  thf(t38_wellord1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ C ) =>
% 0.22/0.50       ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.22/0.50           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) =>
% 0.22/0.50         ( ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) <=>
% 0.22/0.50           ( ( ( A ) = ( B ) ) | ( r2_hidden @ A @ ( k1_wellord1 @ C @ B ) ) ) ) ) ))).
% 0.22/0.50  thf('24', plain,
% 0.22/0.50      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.50         (~ (v2_wellord1 @ X7)
% 0.22/0.50          | ~ (r2_hidden @ X8 @ (k3_relat_1 @ X7))
% 0.22/0.50          | ~ (r2_hidden @ X9 @ (k3_relat_1 @ X7))
% 0.22/0.50          | ~ (r1_tarski @ (k1_wellord1 @ X7 @ X8) @ (k1_wellord1 @ X7 @ X9))
% 0.22/0.50          | ((X8) = (X9))
% 0.22/0.50          | (r2_hidden @ X8 @ (k1_wellord1 @ X7 @ X9))
% 0.22/0.50          | ~ (v1_relat_1 @ X7))),
% 0.22/0.50      inference('cnf', [status(esa)], [t38_wellord1])).
% 0.22/0.50  thf('25', plain,
% 0.22/0.50      ((((sk_A) = (sk_B_1))
% 0.22/0.50        | ~ (v1_relat_1 @ sk_C_1)
% 0.22/0.50        | (r2_hidden @ sk_B_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))
% 0.22/0.50        | ((sk_B_1) = (sk_A))
% 0.22/0.50        | ~ (r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))
% 0.22/0.50        | ~ (r2_hidden @ sk_B_1 @ (k3_relat_1 @ sk_C_1))
% 0.22/0.50        | ~ (v2_wellord1 @ sk_C_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.50  thf('26', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('27', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('28', plain, ((r2_hidden @ sk_B_1 @ (k3_relat_1 @ sk_C_1))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('29', plain, ((v2_wellord1 @ sk_C_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('30', plain,
% 0.22/0.50      ((((sk_A) = (sk_B_1))
% 0.22/0.50        | (r2_hidden @ sk_B_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))
% 0.22/0.50        | ((sk_B_1) = (sk_A)))),
% 0.22/0.50      inference('demod', [status(thm)], ['25', '26', '27', '28', '29'])).
% 0.22/0.50  thf('31', plain,
% 0.22/0.50      (((r2_hidden @ sk_B_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))
% 0.22/0.50        | ((sk_A) = (sk_B_1)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['30'])).
% 0.22/0.50  thf('32', plain,
% 0.22/0.50      (![X10 : $i]:
% 0.22/0.50         (((X10) != (sk_B_1))
% 0.22/0.50          | ~ (r2_hidden @ X10 @ (k1_wellord1 @ sk_C_1 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('33', plain, (~ (r2_hidden @ sk_B_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))),
% 0.22/0.50      inference('simplify', [status(thm)], ['32'])).
% 0.22/0.50  thf('34', plain, (((sk_A) = (sk_B_1))),
% 0.22/0.50      inference('clc', [status(thm)], ['31', '33'])).
% 0.22/0.50  thf('35', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('36', plain,
% 0.22/0.50      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.50         (~ (v2_wellord1 @ X7)
% 0.22/0.50          | ~ (r2_hidden @ X8 @ (k3_relat_1 @ X7))
% 0.22/0.50          | ~ (r2_hidden @ X9 @ (k3_relat_1 @ X7))
% 0.22/0.50          | ((X8) != (X9))
% 0.22/0.50          | (r1_tarski @ (k1_wellord1 @ X7 @ X8) @ (k1_wellord1 @ X7 @ X9))
% 0.22/0.50          | ~ (v1_relat_1 @ X7))),
% 0.22/0.50      inference('cnf', [status(esa)], [t38_wellord1])).
% 0.22/0.50  thf('37', plain,
% 0.22/0.50      (![X7 : $i, X9 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ X7)
% 0.22/0.50          | (r1_tarski @ (k1_wellord1 @ X7 @ X9) @ (k1_wellord1 @ X7 @ X9))
% 0.22/0.50          | ~ (r2_hidden @ X9 @ (k3_relat_1 @ X7))
% 0.22/0.50          | ~ (v2_wellord1 @ X7))),
% 0.22/0.50      inference('simplify', [status(thm)], ['36'])).
% 0.22/0.50  thf('38', plain,
% 0.22/0.50      ((~ (v2_wellord1 @ sk_C_1)
% 0.22/0.50        | (r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.22/0.50           (k1_wellord1 @ sk_C_1 @ sk_A))
% 0.22/0.50        | ~ (v1_relat_1 @ sk_C_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['35', '37'])).
% 0.22/0.50  thf('39', plain, ((v2_wellord1 @ sk_C_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('40', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('41', plain,
% 0.22/0.50      ((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.22/0.50        (k1_wellord1 @ sk_C_1 @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.22/0.50  thf('42', plain,
% 0.22/0.50      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.50         (~ (v2_wellord1 @ X4)
% 0.22/0.50          | ~ (r2_hidden @ X5 @ (k3_relat_1 @ X4))
% 0.22/0.50          | ~ (r2_hidden @ X6 @ (k3_relat_1 @ X4))
% 0.22/0.50          | ~ (r1_tarski @ (k1_wellord1 @ X4 @ X5) @ (k1_wellord1 @ X4 @ X6))
% 0.22/0.50          | (r2_hidden @ (k4_tarski @ X5 @ X6) @ X4)
% 0.22/0.50          | ~ (v1_relat_1 @ X4))),
% 0.22/0.50      inference('cnf', [status(esa)], [t37_wellord1])).
% 0.22/0.50  thf('43', plain,
% 0.22/0.50      ((~ (v1_relat_1 @ sk_C_1)
% 0.22/0.50        | (r2_hidden @ (k4_tarski @ sk_A @ sk_A) @ sk_C_1)
% 0.22/0.50        | ~ (r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))
% 0.22/0.50        | ~ (r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))
% 0.22/0.50        | ~ (v2_wellord1 @ sk_C_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.50  thf('44', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('45', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('46', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('47', plain, ((v2_wellord1 @ sk_C_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('48', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_A) @ sk_C_1)),
% 0.22/0.50      inference('demod', [status(thm)], ['43', '44', '45', '46', '47'])).
% 0.22/0.50  thf('49', plain, ($false),
% 0.22/0.50      inference('demod', [status(thm)], ['0', '34', '48'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
