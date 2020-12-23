%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rPE7man3i5

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 115 expanded)
%              Number of leaves         :   14 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :  583 (1427 expanded)
%              Number of equality atoms :    8 (  14 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t40_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ ( k6_relat_1 @ B ) ) ) )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ ( k6_relat_1 @ B ) ) ) )
        <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
            & ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_funct_1])).

thf('0',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t21_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
          <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
              & ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( r2_hidden @ X3 @ ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X2 @ X3 ) @ ( k1_relat_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_1])).

thf('5',plain,
    ( ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_relat_1 @ ( k6_relat_1 @ sk_B ) ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('7',plain,(
    ! [X1: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf(t34_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( B
          = ( k6_relat_1 @ A ) )
      <=> ( ( ( k1_relat_1 @ B )
            = A )
          & ! [C: $i] :
              ( ( r2_hidden @ C @ A )
             => ( ( k1_funct_1 @ B @ C )
                = C ) ) ) ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X6
       != ( k6_relat_1 @ X5 ) )
      | ( ( k1_relat_1 @ X6 )
        = X5 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('9',plain,(
    ! [X5: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X5 ) )
      | ( ( k1_relat_1 @ ( k6_relat_1 @ X5 ) )
        = X5 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('11',plain,(
    ! [X1: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('12',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['5','6','7','12','13','14'])).

thf('16',plain,
    ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B )
   <= ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) )
    | ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['16'])).

thf('20',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('21',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B )
   <= ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('23',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( r2_hidden @ X3 @ ( k1_relat_1 @ X2 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X2 @ X3 ) @ ( k1_relat_1 @ X4 ) )
      | ( r2_hidden @ X3 @ ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k1_funct_1 @ X2 @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('26',plain,(
    ! [X1: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k1_funct_1 @ X2 @ X1 ) @ X0 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) ) )
   <= ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) ) )
   <= ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
      & ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','31'])).

thf('33',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf('34',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('36',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('37',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( r2_hidden @ X3 @ ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ( r2_hidden @ X3 @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_1])).

thf('38',plain,
    ( ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ sk_B ) )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('40',plain,(
    ! [X1: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('41',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['38','39','40','41','42'])).

thf('44',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['16'])).

thf('45',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','18','19','34','35','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rPE7man3i5
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:14:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 38 iterations in 0.032s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.50  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.50  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(t40_funct_1, conjecture,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.50       ( ( r2_hidden @
% 0.21/0.50           A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ ( k6_relat_1 @ B ) ) ) ) <=>
% 0.21/0.50         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.21/0.50           ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.50        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.50          ( ( r2_hidden @
% 0.21/0.50              A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ ( k6_relat_1 @ B ) ) ) ) <=>
% 0.21/0.50            ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.21/0.50              ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t40_funct_1])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      (((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B)
% 0.21/0.50        | (r2_hidden @ sk_A @ 
% 0.21/0.50           (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B)))))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (((r2_hidden @ sk_A @ 
% 0.21/0.50         (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B))))) | 
% 0.21/0.50       ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))
% 0.21/0.50        | (r2_hidden @ sk_A @ 
% 0.21/0.50           (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B)))))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (((r2_hidden @ sk_A @ 
% 0.21/0.50         (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B)))))
% 0.21/0.50         <= (((r2_hidden @ sk_A @ 
% 0.21/0.50               (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B))))))),
% 0.21/0.50      inference('split', [status(esa)], ['2'])).
% 0.21/0.50  thf(t21_funct_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.50       ( ![C:$i]:
% 0.21/0.50         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.50           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) <=>
% 0.21/0.50             ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.21/0.50               ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X2)
% 0.21/0.50          | ~ (v1_funct_1 @ X2)
% 0.21/0.50          | ~ (r2_hidden @ X3 @ (k1_relat_1 @ (k5_relat_1 @ X2 @ X4)))
% 0.21/0.50          | (r2_hidden @ (k1_funct_1 @ X2 @ X3) @ (k1_relat_1 @ X4))
% 0.21/0.50          | ~ (v1_funct_1 @ X4)
% 0.21/0.50          | ~ (v1_relat_1 @ X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [t21_funct_1])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (((~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.21/0.50         | ~ (v1_funct_1 @ (k6_relat_1 @ sk_B))
% 0.21/0.50         | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ 
% 0.21/0.50            (k1_relat_1 @ (k6_relat_1 @ sk_B)))
% 0.21/0.50         | ~ (v1_funct_1 @ sk_C_1)
% 0.21/0.50         | ~ (v1_relat_1 @ sk_C_1)))
% 0.21/0.50         <= (((r2_hidden @ sk_A @ 
% 0.21/0.50               (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B))))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.50  thf(fc3_funct_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.21/0.50       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.50  thf('6', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.50  thf('7', plain, (![X1 : $i]: (v1_funct_1 @ (k6_relat_1 @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.50  thf(t34_funct_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.50       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.21/0.50         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i]:
% 0.21/0.50         (((X6) != (k6_relat_1 @ X5))
% 0.21/0.50          | ((k1_relat_1 @ X6) = (X5))
% 0.21/0.50          | ~ (v1_funct_1 @ X6)
% 0.21/0.50          | ~ (v1_relat_1 @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X5 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ (k6_relat_1 @ X5))
% 0.21/0.50          | ~ (v1_funct_1 @ (k6_relat_1 @ X5))
% 0.21/0.50          | ((k1_relat_1 @ (k6_relat_1 @ X5)) = (X5)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.50  thf('10', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.50  thf('11', plain, (![X1 : $i]: (v1_funct_1 @ (k6_relat_1 @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.50  thf('12', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 0.21/0.50      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.21/0.50  thf('13', plain, ((v1_funct_1 @ sk_C_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('14', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B))
% 0.21/0.50         <= (((r2_hidden @ sk_A @ 
% 0.21/0.50               (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B))))))),
% 0.21/0.50      inference('demod', [status(thm)], ['5', '6', '7', '12', '13', '14'])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      ((~ (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B)
% 0.21/0.50        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))
% 0.21/0.50        | ~ (r2_hidden @ sk_A @ 
% 0.21/0.50             (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B)))))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      ((~ (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B))
% 0.21/0.50         <= (~ ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B)))),
% 0.21/0.50      inference('split', [status(esa)], ['16'])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (~
% 0.21/0.50       ((r2_hidden @ sk_A @ 
% 0.21/0.50         (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B))))) | 
% 0.21/0.50       ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['15', '17'])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))) | 
% 0.21/0.50       ~
% 0.21/0.50       ((r2_hidden @ sk_A @ 
% 0.21/0.50         (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B))))) | 
% 0.21/0.50       ~ ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B))),
% 0.21/0.50      inference('split', [status(esa)], ['16'])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1)))
% 0.21/0.50         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))))),
% 0.21/0.50      inference('split', [status(esa)], ['2'])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B))
% 0.21/0.50         <= (((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B)))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('22', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 0.21/0.50      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X2)
% 0.21/0.50          | ~ (v1_funct_1 @ X2)
% 0.21/0.50          | ~ (r2_hidden @ X3 @ (k1_relat_1 @ X2))
% 0.21/0.50          | ~ (r2_hidden @ (k1_funct_1 @ X2 @ X3) @ (k1_relat_1 @ X4))
% 0.21/0.50          | (r2_hidden @ X3 @ (k1_relat_1 @ (k5_relat_1 @ X2 @ X4)))
% 0.21/0.50          | ~ (v1_funct_1 @ X4)
% 0.21/0.50          | ~ (v1_relat_1 @ X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [t21_funct_1])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (r2_hidden @ (k1_funct_1 @ X2 @ X1) @ X0)
% 0.21/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.50          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.21/0.50          | (r2_hidden @ X1 @ 
% 0.21/0.50             (k1_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X0))))
% 0.21/0.50          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X2))
% 0.21/0.50          | ~ (v1_funct_1 @ X2)
% 0.21/0.50          | ~ (v1_relat_1 @ X2))),
% 0.21/0.50      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.50  thf('25', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.50  thf('26', plain, (![X1 : $i]: (v1_funct_1 @ (k6_relat_1 @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (r2_hidden @ (k1_funct_1 @ X2 @ X1) @ X0)
% 0.21/0.50          | (r2_hidden @ X1 @ 
% 0.21/0.50             (k1_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X0))))
% 0.21/0.50          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X2))
% 0.21/0.50          | ~ (v1_funct_1 @ X2)
% 0.21/0.50          | ~ (v1_relat_1 @ X2))),
% 0.21/0.50      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      (((~ (v1_relat_1 @ sk_C_1)
% 0.21/0.50         | ~ (v1_funct_1 @ sk_C_1)
% 0.21/0.50         | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))
% 0.21/0.50         | (r2_hidden @ sk_A @ 
% 0.21/0.50            (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B))))))
% 0.21/0.50         <= (((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['21', '27'])).
% 0.21/0.50  thf('29', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('30', plain, ((v1_funct_1 @ sk_C_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      (((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))
% 0.21/0.50         | (r2_hidden @ sk_A @ 
% 0.21/0.50            (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B))))))
% 0.21/0.50         <= (((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B)))),
% 0.21/0.50      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (((r2_hidden @ sk_A @ 
% 0.21/0.50         (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B)))))
% 0.21/0.50         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))) & 
% 0.21/0.50             ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['20', '31'])).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      ((~ (r2_hidden @ sk_A @ 
% 0.21/0.50           (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B)))))
% 0.21/0.50         <= (~
% 0.21/0.50             ((r2_hidden @ sk_A @ 
% 0.21/0.50               (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B))))))),
% 0.21/0.50      inference('split', [status(esa)], ['16'])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      (((r2_hidden @ sk_A @ 
% 0.21/0.50         (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B))))) | 
% 0.21/0.50       ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))) | 
% 0.21/0.50       ~ ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      (((r2_hidden @ sk_A @ 
% 0.21/0.50         (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B))))) | 
% 0.21/0.50       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1)))),
% 0.21/0.50      inference('split', [status(esa)], ['2'])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      (((r2_hidden @ sk_A @ 
% 0.21/0.50         (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B)))))
% 0.21/0.50         <= (((r2_hidden @ sk_A @ 
% 0.21/0.50               (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B))))))),
% 0.21/0.50      inference('split', [status(esa)], ['2'])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X2)
% 0.21/0.50          | ~ (v1_funct_1 @ X2)
% 0.21/0.50          | ~ (r2_hidden @ X3 @ (k1_relat_1 @ (k5_relat_1 @ X2 @ X4)))
% 0.21/0.50          | (r2_hidden @ X3 @ (k1_relat_1 @ X2))
% 0.21/0.50          | ~ (v1_funct_1 @ X4)
% 0.21/0.50          | ~ (v1_relat_1 @ X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [t21_funct_1])).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      (((~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.21/0.50         | ~ (v1_funct_1 @ (k6_relat_1 @ sk_B))
% 0.21/0.50         | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))
% 0.21/0.50         | ~ (v1_funct_1 @ sk_C_1)
% 0.21/0.50         | ~ (v1_relat_1 @ sk_C_1)))
% 0.21/0.50         <= (((r2_hidden @ sk_A @ 
% 0.21/0.50               (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B))))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.50  thf('39', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.50  thf('40', plain, (![X1 : $i]: (v1_funct_1 @ (k6_relat_1 @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.50  thf('41', plain, ((v1_funct_1 @ sk_C_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('42', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('43', plain,
% 0.21/0.50      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1)))
% 0.21/0.50         <= (((r2_hidden @ sk_A @ 
% 0.21/0.50               (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B))))))),
% 0.21/0.50      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 0.21/0.50  thf('44', plain,
% 0.21/0.50      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1)))
% 0.21/0.50         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))))),
% 0.21/0.50      inference('split', [status(esa)], ['16'])).
% 0.21/0.50  thf('45', plain,
% 0.21/0.50      (~
% 0.21/0.50       ((r2_hidden @ sk_A @ 
% 0.21/0.50         (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B))))) | 
% 0.21/0.50       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.50  thf('46', plain, ($false),
% 0.21/0.50      inference('sat_resolution*', [status(thm)],
% 0.21/0.50                ['1', '18', '19', '34', '35', '45'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
