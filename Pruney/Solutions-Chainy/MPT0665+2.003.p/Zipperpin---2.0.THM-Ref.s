%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.F1UwC5klxw

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:51 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 121 expanded)
%              Number of leaves         :   18 (  41 expanded)
%              Depth                    :   18
%              Number of atoms          :  568 (1439 expanded)
%              Number of equality atoms :   16 (  21 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(fc8_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t73_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ A @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k2_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
            & ( r2_hidden @ A @ B ) )
         => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k2_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t73_funct_1])).

thf('2',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X24 @ ( k1_relat_1 @ X25 ) )
      | ( X26
       != ( k1_funct_1 @ X25 @ X24 ) )
      | ( r2_hidden @ ( k4_tarski @ X24 @ X26 ) @ X25 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('5',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_funct_1 @ X25 )
      | ( r2_hidden @ ( k4_tarski @ X24 @ ( k1_funct_1 @ X25 @ X24 ) ) @ X25 )
      | ~ ( r2_hidden @ X24 @ ( k1_relat_1 @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C_2 @ sk_A ) ) @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C_2 @ sk_A ) ) @ sk_C_2 ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

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

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
       != ( k7_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d11_relat_1])).

thf('12',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ ( k7_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ X1 )
      | ~ ( r2_hidden @ X3 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_2 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C_2 @ sk_A ) ) @ ( k7_relat_1 @ sk_C_2 @ X0 ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C_2 @ sk_A ) ) @ ( k7_relat_1 @ sk_C_2 @ X0 ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C_2 @ sk_A ) ) @ ( k7_relat_1 @ sk_C_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','17'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('19',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X6 @ X7 ) @ X8 )
      | ( r2_hidden @ X6 @ X9 )
      | ( X9
       != ( k1_relat_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('20',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ ( k1_relat_1 @ X8 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X7 ) @ X8 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X16: $i,X18: $i,X20: $i,X21: $i] :
      ( ( X18
       != ( k2_relat_1 @ X16 ) )
      | ( r2_hidden @ X20 @ X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X16 ) )
      | ( X20
       != ( k1_funct_1 @ X16 @ X21 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('23',plain,(
    ! [X16: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X16 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X16 @ X21 ) @ ( k2_relat_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ ( k7_relat_1 @ sk_C_2 @ sk_B ) @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C_2 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C_2 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('26',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('27',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C_2 @ sk_A ) ) @ ( k7_relat_1 @ sk_C_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','17'])).

thf('28',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X24 @ X26 ) @ X25 )
      | ( X26
        = ( k1_funct_1 @ X25 @ X24 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C_2 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C_2 @ sk_B ) )
    | ( ( k1_funct_1 @ sk_C_2 @ sk_A )
      = ( k1_funct_1 @ ( k7_relat_1 @ sk_C_2 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( ( k1_funct_1 @ sk_C_2 @ sk_A )
      = ( k1_funct_1 @ ( k7_relat_1 @ sk_C_2 @ sk_B ) @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ sk_A )
      = ( k1_funct_1 @ ( k7_relat_1 @ sk_C_2 @ sk_B ) @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( ( k1_funct_1 @ sk_C_2 @ sk_A )
      = ( k1_funct_1 @ ( k7_relat_1 @ sk_C_2 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k1_funct_1 @ sk_C_2 @ sk_A )
    = ( k1_funct_1 @ ( k7_relat_1 @ sk_C_2 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C_2 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C_2 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','36'])).

thf('38',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C_2 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C_2 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C_2 @ sk_B ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['0','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['43','44','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.F1UwC5klxw
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:15:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.46/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.65  % Solved by: fo/fo7.sh
% 0.46/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.65  % done 232 iterations in 0.193s
% 0.46/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.65  % SZS output start Refutation
% 0.46/0.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.65  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.46/0.65  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.46/0.65  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.65  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.46/0.65  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.46/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.65  thf(fc8_funct_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.65       ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) & 
% 0.46/0.65         ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 0.46/0.65  thf('0', plain,
% 0.46/0.65      (![X22 : $i, X23 : $i]:
% 0.46/0.65         (~ (v1_funct_1 @ X22)
% 0.46/0.65          | ~ (v1_relat_1 @ X22)
% 0.46/0.65          | (v1_funct_1 @ (k7_relat_1 @ X22 @ X23)))),
% 0.46/0.65      inference('cnf', [status(esa)], [fc8_funct_1])).
% 0.46/0.65  thf(dt_k7_relat_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.46/0.65  thf('1', plain,
% 0.46/0.65      (![X13 : $i, X14 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X13) | (v1_relat_1 @ (k7_relat_1 @ X13 @ X14)))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.46/0.65  thf(t73_funct_1, conjecture,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.46/0.65       ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & ( r2_hidden @ A @ B ) ) =>
% 0.46/0.65         ( r2_hidden @
% 0.46/0.65           ( k1_funct_1 @ C @ A ) @ ( k2_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) ) ))).
% 0.46/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.65    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.65        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.46/0.65          ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & ( r2_hidden @ A @ B ) ) =>
% 0.46/0.65            ( r2_hidden @
% 0.46/0.65              ( k1_funct_1 @ C @ A ) @ ( k2_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) ) ) )),
% 0.46/0.65    inference('cnf.neg', [status(esa)], [t73_funct_1])).
% 0.46/0.65  thf('2', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('3', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_2))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(t8_funct_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.46/0.65       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.46/0.65         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.46/0.65           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.46/0.65  thf('4', plain,
% 0.46/0.65      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X24 @ (k1_relat_1 @ X25))
% 0.46/0.65          | ((X26) != (k1_funct_1 @ X25 @ X24))
% 0.46/0.65          | (r2_hidden @ (k4_tarski @ X24 @ X26) @ X25)
% 0.46/0.65          | ~ (v1_funct_1 @ X25)
% 0.46/0.65          | ~ (v1_relat_1 @ X25))),
% 0.46/0.65      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.46/0.65  thf('5', plain,
% 0.46/0.65      (![X24 : $i, X25 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X25)
% 0.46/0.65          | ~ (v1_funct_1 @ X25)
% 0.46/0.65          | (r2_hidden @ (k4_tarski @ X24 @ (k1_funct_1 @ X25 @ X24)) @ X25)
% 0.46/0.65          | ~ (r2_hidden @ X24 @ (k1_relat_1 @ X25)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['4'])).
% 0.46/0.65  thf('6', plain,
% 0.46/0.65      (((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C_2 @ sk_A)) @ sk_C_2)
% 0.46/0.65        | ~ (v1_funct_1 @ sk_C_2)
% 0.46/0.65        | ~ (v1_relat_1 @ sk_C_2))),
% 0.46/0.65      inference('sup-', [status(thm)], ['3', '5'])).
% 0.46/0.65  thf('7', plain, ((v1_funct_1 @ sk_C_2)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('8', plain, ((v1_relat_1 @ sk_C_2)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('9', plain,
% 0.46/0.65      ((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C_2 @ sk_A)) @ sk_C_2)),
% 0.46/0.65      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.46/0.65  thf('10', plain,
% 0.46/0.65      (![X13 : $i, X14 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X13) | (v1_relat_1 @ (k7_relat_1 @ X13 @ X14)))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.46/0.65  thf(d11_relat_1, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( v1_relat_1 @ A ) =>
% 0.46/0.65       ( ![B:$i,C:$i]:
% 0.46/0.65         ( ( v1_relat_1 @ C ) =>
% 0.46/0.65           ( ( ( C ) = ( k7_relat_1 @ A @ B ) ) <=>
% 0.46/0.65             ( ![D:$i,E:$i]:
% 0.46/0.65               ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 0.46/0.65                 ( ( r2_hidden @ D @ B ) & 
% 0.46/0.65                   ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) ) ) ))).
% 0.46/0.65  thf('11', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X0)
% 0.46/0.65          | ((X0) != (k7_relat_1 @ X1 @ X2))
% 0.46/0.65          | (r2_hidden @ (k4_tarski @ X3 @ X4) @ X0)
% 0.46/0.65          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X1)
% 0.46/0.65          | ~ (r2_hidden @ X3 @ X2)
% 0.46/0.65          | ~ (v1_relat_1 @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [d11_relat_1])).
% 0.46/0.65  thf('12', plain,
% 0.46/0.65      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X1)
% 0.46/0.65          | ~ (r2_hidden @ X3 @ X2)
% 0.46/0.65          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X1)
% 0.46/0.65          | (r2_hidden @ (k4_tarski @ X3 @ X4) @ (k7_relat_1 @ X1 @ X2))
% 0.46/0.65          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['11'])).
% 0.46/0.65  thf('13', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X1)
% 0.46/0.65          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k7_relat_1 @ X1 @ X0))
% 0.46/0.65          | ~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ X1)
% 0.46/0.65          | ~ (r2_hidden @ X3 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['10', '12'])).
% 0.46/0.65  thf('14', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X3 @ X0)
% 0.46/0.65          | ~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ X1)
% 0.46/0.65          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k7_relat_1 @ X1 @ X0))
% 0.46/0.65          | ~ (v1_relat_1 @ X1))),
% 0.46/0.65      inference('simplify', [status(thm)], ['13'])).
% 0.46/0.65  thf('15', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ sk_C_2)
% 0.46/0.65          | (r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C_2 @ sk_A)) @ 
% 0.46/0.65             (k7_relat_1 @ sk_C_2 @ X0))
% 0.46/0.65          | ~ (r2_hidden @ sk_A @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['9', '14'])).
% 0.46/0.65  thf('16', plain, ((v1_relat_1 @ sk_C_2)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('17', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C_2 @ sk_A)) @ 
% 0.46/0.65           (k7_relat_1 @ sk_C_2 @ X0))
% 0.46/0.65          | ~ (r2_hidden @ sk_A @ X0))),
% 0.46/0.65      inference('demod', [status(thm)], ['15', '16'])).
% 0.46/0.65  thf('18', plain,
% 0.46/0.65      ((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C_2 @ sk_A)) @ 
% 0.46/0.65        (k7_relat_1 @ sk_C_2 @ sk_B))),
% 0.46/0.65      inference('sup-', [status(thm)], ['2', '17'])).
% 0.46/0.65  thf(d4_relat_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.46/0.65       ( ![C:$i]:
% 0.46/0.65         ( ( r2_hidden @ C @ B ) <=>
% 0.46/0.65           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.46/0.65  thf('19', plain,
% 0.46/0.65      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.46/0.65         (~ (r2_hidden @ (k4_tarski @ X6 @ X7) @ X8)
% 0.46/0.65          | (r2_hidden @ X6 @ X9)
% 0.46/0.65          | ((X9) != (k1_relat_1 @ X8)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.46/0.65  thf('20', plain,
% 0.46/0.65      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.65         ((r2_hidden @ X6 @ (k1_relat_1 @ X8))
% 0.46/0.65          | ~ (r2_hidden @ (k4_tarski @ X6 @ X7) @ X8))),
% 0.46/0.65      inference('simplify', [status(thm)], ['19'])).
% 0.46/0.65  thf('21', plain,
% 0.46/0.65      ((r2_hidden @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_C_2 @ sk_B)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['18', '20'])).
% 0.46/0.65  thf(d5_funct_1, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.46/0.65           ( ![C:$i]:
% 0.46/0.65             ( ( r2_hidden @ C @ B ) <=>
% 0.46/0.65               ( ?[D:$i]:
% 0.46/0.65                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.46/0.65                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.46/0.65  thf('22', plain,
% 0.46/0.65      (![X16 : $i, X18 : $i, X20 : $i, X21 : $i]:
% 0.46/0.65         (((X18) != (k2_relat_1 @ X16))
% 0.46/0.65          | (r2_hidden @ X20 @ X18)
% 0.46/0.65          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X16))
% 0.46/0.65          | ((X20) != (k1_funct_1 @ X16 @ X21))
% 0.46/0.65          | ~ (v1_funct_1 @ X16)
% 0.46/0.65          | ~ (v1_relat_1 @ X16))),
% 0.46/0.65      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.46/0.65  thf('23', plain,
% 0.46/0.65      (![X16 : $i, X21 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X16)
% 0.46/0.65          | ~ (v1_funct_1 @ X16)
% 0.46/0.65          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X16))
% 0.46/0.65          | (r2_hidden @ (k1_funct_1 @ X16 @ X21) @ (k2_relat_1 @ X16)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['22'])).
% 0.46/0.65  thf('24', plain,
% 0.46/0.65      (((r2_hidden @ (k1_funct_1 @ (k7_relat_1 @ sk_C_2 @ sk_B) @ sk_A) @ 
% 0.46/0.65         (k2_relat_1 @ (k7_relat_1 @ sk_C_2 @ sk_B)))
% 0.46/0.65        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_C_2 @ sk_B))
% 0.46/0.65        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C_2 @ sk_B)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['21', '23'])).
% 0.46/0.65  thf('25', plain,
% 0.46/0.65      (![X22 : $i, X23 : $i]:
% 0.46/0.65         (~ (v1_funct_1 @ X22)
% 0.46/0.65          | ~ (v1_relat_1 @ X22)
% 0.46/0.65          | (v1_funct_1 @ (k7_relat_1 @ X22 @ X23)))),
% 0.46/0.65      inference('cnf', [status(esa)], [fc8_funct_1])).
% 0.46/0.65  thf('26', plain,
% 0.46/0.65      (![X13 : $i, X14 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X13) | (v1_relat_1 @ (k7_relat_1 @ X13 @ X14)))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.46/0.65  thf('27', plain,
% 0.46/0.65      ((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C_2 @ sk_A)) @ 
% 0.46/0.65        (k7_relat_1 @ sk_C_2 @ sk_B))),
% 0.46/0.65      inference('sup-', [status(thm)], ['2', '17'])).
% 0.46/0.65  thf('28', plain,
% 0.46/0.65      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.46/0.65         (~ (r2_hidden @ (k4_tarski @ X24 @ X26) @ X25)
% 0.46/0.65          | ((X26) = (k1_funct_1 @ X25 @ X24))
% 0.46/0.65          | ~ (v1_funct_1 @ X25)
% 0.46/0.65          | ~ (v1_relat_1 @ X25))),
% 0.46/0.65      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.46/0.65  thf('29', plain,
% 0.46/0.65      ((~ (v1_relat_1 @ (k7_relat_1 @ sk_C_2 @ sk_B))
% 0.46/0.65        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_C_2 @ sk_B))
% 0.46/0.65        | ((k1_funct_1 @ sk_C_2 @ sk_A)
% 0.46/0.65            = (k1_funct_1 @ (k7_relat_1 @ sk_C_2 @ sk_B) @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['27', '28'])).
% 0.46/0.65  thf('30', plain,
% 0.46/0.65      ((~ (v1_relat_1 @ sk_C_2)
% 0.46/0.65        | ((k1_funct_1 @ sk_C_2 @ sk_A)
% 0.46/0.65            = (k1_funct_1 @ (k7_relat_1 @ sk_C_2 @ sk_B) @ sk_A))
% 0.46/0.65        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_C_2 @ sk_B)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['26', '29'])).
% 0.46/0.65  thf('31', plain, ((v1_relat_1 @ sk_C_2)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('32', plain,
% 0.46/0.65      ((((k1_funct_1 @ sk_C_2 @ sk_A)
% 0.46/0.65          = (k1_funct_1 @ (k7_relat_1 @ sk_C_2 @ sk_B) @ sk_A))
% 0.46/0.65        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_C_2 @ sk_B)))),
% 0.46/0.65      inference('demod', [status(thm)], ['30', '31'])).
% 0.46/0.65  thf('33', plain,
% 0.46/0.65      ((~ (v1_relat_1 @ sk_C_2)
% 0.46/0.65        | ~ (v1_funct_1 @ sk_C_2)
% 0.46/0.65        | ((k1_funct_1 @ sk_C_2 @ sk_A)
% 0.46/0.65            = (k1_funct_1 @ (k7_relat_1 @ sk_C_2 @ sk_B) @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['25', '32'])).
% 0.46/0.65  thf('34', plain, ((v1_relat_1 @ sk_C_2)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('35', plain, ((v1_funct_1 @ sk_C_2)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('36', plain,
% 0.46/0.65      (((k1_funct_1 @ sk_C_2 @ sk_A)
% 0.46/0.65         = (k1_funct_1 @ (k7_relat_1 @ sk_C_2 @ sk_B) @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.46/0.65  thf('37', plain,
% 0.46/0.65      (((r2_hidden @ (k1_funct_1 @ sk_C_2 @ sk_A) @ 
% 0.46/0.65         (k2_relat_1 @ (k7_relat_1 @ sk_C_2 @ sk_B)))
% 0.46/0.65        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_C_2 @ sk_B))
% 0.46/0.65        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C_2 @ sk_B)))),
% 0.46/0.65      inference('demod', [status(thm)], ['24', '36'])).
% 0.46/0.65  thf('38', plain,
% 0.46/0.65      (~ (r2_hidden @ (k1_funct_1 @ sk_C_2 @ sk_A) @ 
% 0.46/0.65          (k2_relat_1 @ (k7_relat_1 @ sk_C_2 @ sk_B)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('39', plain,
% 0.46/0.65      ((~ (v1_relat_1 @ (k7_relat_1 @ sk_C_2 @ sk_B))
% 0.46/0.65        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_C_2 @ sk_B)))),
% 0.46/0.65      inference('clc', [status(thm)], ['37', '38'])).
% 0.46/0.65  thf('40', plain,
% 0.46/0.65      ((~ (v1_relat_1 @ sk_C_2) | ~ (v1_funct_1 @ (k7_relat_1 @ sk_C_2 @ sk_B)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['1', '39'])).
% 0.46/0.65  thf('41', plain, ((v1_relat_1 @ sk_C_2)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('42', plain, (~ (v1_funct_1 @ (k7_relat_1 @ sk_C_2 @ sk_B))),
% 0.46/0.65      inference('demod', [status(thm)], ['40', '41'])).
% 0.46/0.65  thf('43', plain, ((~ (v1_relat_1 @ sk_C_2) | ~ (v1_funct_1 @ sk_C_2))),
% 0.46/0.65      inference('sup-', [status(thm)], ['0', '42'])).
% 0.46/0.65  thf('44', plain, ((v1_relat_1 @ sk_C_2)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('45', plain, ((v1_funct_1 @ sk_C_2)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('46', plain, ($false),
% 0.46/0.65      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.46/0.65  
% 0.46/0.65  % SZS output end Refutation
% 0.46/0.65  
% 0.46/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
