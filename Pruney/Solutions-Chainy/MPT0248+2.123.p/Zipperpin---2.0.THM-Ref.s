%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Plxb82s4Yw

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:36 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 236 expanded)
%              Number of leaves         :   23 (  69 expanded)
%              Depth                    :   20
%              Number of atoms          :  581 (2782 expanded)
%              Number of equality atoms :   90 ( 599 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t43_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B = k1_xboole_0 )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B = k1_xboole_0 )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['0','5'])).

thf('7',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['7'])).

thf('10',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('14',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('15',plain,(
    ! [X52: $i,X53: $i] :
      ( ( X53
        = ( k1_tarski @ X52 ) )
      | ( X53 = k1_xboole_0 )
      | ~ ( r1_tarski @ X53 @ ( k1_tarski @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('16',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['7'])).

thf('22',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_B_1
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['9','11','23'])).

thf('25',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['8','24'])).

thf('26',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['6','25'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('27',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('28',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('30',plain,(
    ! [X50: $i,X51: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X50 ) @ X51 )
      | ( r2_hidden @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('31',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('34',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('35',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('36',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r1_xboole_0 @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( r1_xboole_0 @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('39',plain,(
    ! [X47: $i,X49: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X47 ) @ X49 )
      | ~ ( r2_hidden @ X47 @ X49 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_B_1 )
      | ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['29','40'])).

thf('42',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('43',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( r1_xboole_0 @ X13 @ X16 )
      | ~ ( r1_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r1_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 = k1_xboole_0 )
      | ( r1_tarski @ sk_B_1 @ X0 )
      | ( r1_xboole_0 @ X0 @ sk_C_1 )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_C_1 )
      | ( r1_tarski @ sk_B_1 @ X0 )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('49',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X12 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('50',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r1_tarski @ sk_B_1 @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('52',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('54',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['6','25'])).

thf('56',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['17'])).

thf('58',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['56','57'])).

thf('59',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['51','58'])).

thf('60',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r1_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['50','59'])).

thf('61',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('62',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k2_xboole_0 @ sk_B_1 @ sk_C_1 )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','62'])).

thf('64',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['8','24'])).

thf('65',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(demod,[status(thm)],['27','65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['26','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Plxb82s4Yw
% 0.12/0.37  % Computer   : n011.cluster.edu
% 0.12/0.37  % Model      : x86_64 x86_64
% 0.12/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.37  % Memory     : 8042.1875MB
% 0.12/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.37  % CPULimit   : 60
% 0.12/0.37  % DateTime   : Tue Dec  1 19:11:57 EST 2020
% 0.12/0.37  % CPUTime    : 
% 0.12/0.37  % Running portfolio for 600 s
% 0.12/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.37  % Number of cores: 8
% 0.12/0.37  % Python version: Python 3.6.8
% 0.12/0.38  % Running in FO mode
% 0.59/0.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.78  % Solved by: fo/fo7.sh
% 0.59/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.78  % done 706 iterations in 0.302s
% 0.59/0.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.78  % SZS output start Refutation
% 0.59/0.78  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.78  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.59/0.78  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.59/0.78  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.59/0.78  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.59/0.78  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.59/0.78  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.59/0.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.78  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.59/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.78  thf(t43_zfmisc_1, conjecture,
% 0.59/0.78    (![A:$i,B:$i,C:$i]:
% 0.59/0.78     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.59/0.78          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.59/0.78          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.59/0.78          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.59/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.78    (~( ![A:$i,B:$i,C:$i]:
% 0.59/0.78        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.59/0.78             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.59/0.78             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.59/0.78             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.59/0.78    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.59/0.78  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(d3_tarski, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( r1_tarski @ A @ B ) <=>
% 0.59/0.78       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.59/0.78  thf('1', plain,
% 0.59/0.78      (![X4 : $i, X6 : $i]:
% 0.59/0.78         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.59/0.78      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.78  thf(d1_xboole_0, axiom,
% 0.59/0.78    (![A:$i]:
% 0.59/0.78     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.59/0.78  thf('2', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.59/0.78      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.59/0.78  thf('3', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['1', '2'])).
% 0.59/0.78  thf(t12_xboole_1, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.59/0.78  thf('4', plain,
% 0.59/0.78      (![X9 : $i, X10 : $i]:
% 0.59/0.78         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 0.59/0.78      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.59/0.78  thf('5', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]:
% 0.59/0.78         (~ (v1_xboole_0 @ X1) | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['3', '4'])).
% 0.59/0.78  thf('6', plain,
% 0.59/0.78      ((((k1_tarski @ sk_A) = (sk_C_1)) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.59/0.78      inference('sup+', [status(thm)], ['0', '5'])).
% 0.59/0.78  thf('7', plain,
% 0.59/0.78      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('8', plain,
% 0.59/0.78      ((((sk_C_1) != (k1_tarski @ sk_A)))
% 0.59/0.78         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 0.59/0.78      inference('split', [status(esa)], ['7'])).
% 0.59/0.78  thf('9', plain,
% 0.59/0.78      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 0.59/0.78      inference('split', [status(esa)], ['7'])).
% 0.59/0.78  thf('10', plain,
% 0.59/0.78      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('11', plain,
% 0.59/0.78      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | 
% 0.59/0.78       ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.59/0.78      inference('split', [status(esa)], ['10'])).
% 0.59/0.78  thf('12', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(t7_xboole_1, axiom,
% 0.59/0.78    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.59/0.78  thf('13', plain,
% 0.59/0.78      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 0.59/0.78      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.59/0.78  thf('14', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.59/0.78      inference('sup+', [status(thm)], ['12', '13'])).
% 0.59/0.78  thf(l3_zfmisc_1, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.59/0.78       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.59/0.78  thf('15', plain,
% 0.59/0.78      (![X52 : $i, X53 : $i]:
% 0.59/0.78         (((X53) = (k1_tarski @ X52))
% 0.59/0.78          | ((X53) = (k1_xboole_0))
% 0.59/0.78          | ~ (r1_tarski @ X53 @ (k1_tarski @ X52)))),
% 0.59/0.78      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.59/0.78  thf('16', plain,
% 0.59/0.78      ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['14', '15'])).
% 0.59/0.78  thf('17', plain,
% 0.59/0.78      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_xboole_0)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('18', plain,
% 0.59/0.78      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 0.59/0.78         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.59/0.78      inference('split', [status(esa)], ['17'])).
% 0.59/0.78  thf('19', plain,
% 0.59/0.78      (((((sk_B_1) != (sk_B_1)) | ((sk_B_1) = (k1_xboole_0))))
% 0.59/0.78         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['16', '18'])).
% 0.59/0.78  thf('20', plain,
% 0.59/0.78      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.59/0.78      inference('simplify', [status(thm)], ['19'])).
% 0.59/0.78  thf('21', plain,
% 0.59/0.78      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.59/0.78      inference('split', [status(esa)], ['7'])).
% 0.59/0.78  thf('22', plain,
% 0.59/0.78      ((((sk_B_1) != (sk_B_1)))
% 0.59/0.78         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.59/0.78             ~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['20', '21'])).
% 0.59/0.78  thf('23', plain,
% 0.59/0.78      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.59/0.78      inference('simplify', [status(thm)], ['22'])).
% 0.59/0.78  thf('24', plain, (~ (((sk_C_1) = (k1_tarski @ sk_A)))),
% 0.59/0.78      inference('sat_resolution*', [status(thm)], ['9', '11', '23'])).
% 0.59/0.78  thf('25', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 0.59/0.78      inference('simpl_trail', [status(thm)], ['8', '24'])).
% 0.59/0.78  thf('26', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.59/0.78      inference('simplify_reflect-', [status(thm)], ['6', '25'])).
% 0.59/0.78  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.59/0.78  thf('27', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.59/0.78      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.59/0.78  thf('28', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('29', plain,
% 0.59/0.78      ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['14', '15'])).
% 0.59/0.78  thf(l27_zfmisc_1, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.59/0.78  thf('30', plain,
% 0.59/0.78      (![X50 : $i, X51 : $i]:
% 0.59/0.78         ((r1_xboole_0 @ (k1_tarski @ X50) @ X51) | (r2_hidden @ X50 @ X51))),
% 0.59/0.78      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.59/0.78  thf(symmetry_r1_xboole_0, axiom,
% 0.59/0.78    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.59/0.78  thf('31', plain,
% 0.59/0.78      (![X7 : $i, X8 : $i]:
% 0.59/0.78         ((r1_xboole_0 @ X7 @ X8) | ~ (r1_xboole_0 @ X8 @ X7))),
% 0.59/0.78      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.59/0.78  thf('32', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]:
% 0.59/0.78         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['30', '31'])).
% 0.59/0.78  thf('33', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.59/0.78      inference('sup+', [status(thm)], ['12', '13'])).
% 0.59/0.78  thf('34', plain,
% 0.59/0.78      (![X9 : $i, X10 : $i]:
% 0.59/0.78         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 0.59/0.78      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.59/0.78  thf('35', plain,
% 0.59/0.78      (((k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.59/0.78      inference('sup-', [status(thm)], ['33', '34'])).
% 0.59/0.78  thf(t70_xboole_1, axiom,
% 0.59/0.78    (![A:$i,B:$i,C:$i]:
% 0.59/0.78     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.59/0.78            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.59/0.78       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.59/0.78            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.59/0.78  thf('36', plain,
% 0.59/0.78      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.59/0.78         ((r1_xboole_0 @ X13 @ X14)
% 0.59/0.78          | ~ (r1_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X16)))),
% 0.59/0.78      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.59/0.78  thf('37', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (r1_xboole_0 @ X0 @ (k1_tarski @ sk_A))
% 0.59/0.78          | (r1_xboole_0 @ X0 @ sk_B_1))),
% 0.59/0.78      inference('sup-', [status(thm)], ['35', '36'])).
% 0.59/0.78  thf('38', plain,
% 0.59/0.78      (![X0 : $i]: ((r2_hidden @ sk_A @ X0) | (r1_xboole_0 @ X0 @ sk_B_1))),
% 0.59/0.78      inference('sup-', [status(thm)], ['32', '37'])).
% 0.59/0.78  thf(l1_zfmisc_1, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.59/0.78  thf('39', plain,
% 0.59/0.78      (![X47 : $i, X49 : $i]:
% 0.59/0.78         ((r1_tarski @ (k1_tarski @ X47) @ X49) | ~ (r2_hidden @ X47 @ X49))),
% 0.59/0.78      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.59/0.78  thf('40', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((r1_xboole_0 @ X0 @ sk_B_1) | (r1_tarski @ (k1_tarski @ sk_A) @ X0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['38', '39'])).
% 0.59/0.78  thf('41', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((r1_tarski @ sk_B_1 @ X0)
% 0.59/0.78          | ((sk_B_1) = (k1_xboole_0))
% 0.59/0.78          | (r1_xboole_0 @ X0 @ sk_B_1))),
% 0.59/0.78      inference('sup+', [status(thm)], ['29', '40'])).
% 0.59/0.78  thf('42', plain,
% 0.59/0.78      ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['14', '15'])).
% 0.59/0.78  thf('43', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('44', plain,
% 0.59/0.78      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.59/0.78         ((r1_xboole_0 @ X13 @ X16)
% 0.59/0.78          | ~ (r1_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X16)))),
% 0.59/0.78      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.59/0.78  thf('45', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (r1_xboole_0 @ X0 @ (k1_tarski @ sk_A))
% 0.59/0.78          | (r1_xboole_0 @ X0 @ sk_C_1))),
% 0.59/0.78      inference('sup-', [status(thm)], ['43', '44'])).
% 0.59/0.78  thf('46', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (r1_xboole_0 @ X0 @ sk_B_1)
% 0.59/0.78          | ((sk_B_1) = (k1_xboole_0))
% 0.59/0.78          | (r1_xboole_0 @ X0 @ sk_C_1))),
% 0.59/0.78      inference('sup-', [status(thm)], ['42', '45'])).
% 0.59/0.78  thf('47', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (((sk_B_1) = (k1_xboole_0))
% 0.59/0.78          | (r1_tarski @ sk_B_1 @ X0)
% 0.59/0.78          | (r1_xboole_0 @ X0 @ sk_C_1)
% 0.59/0.78          | ((sk_B_1) = (k1_xboole_0)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['41', '46'])).
% 0.59/0.78  thf('48', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((r1_xboole_0 @ X0 @ sk_C_1)
% 0.59/0.78          | (r1_tarski @ sk_B_1 @ X0)
% 0.59/0.78          | ((sk_B_1) = (k1_xboole_0)))),
% 0.59/0.78      inference('simplify', [status(thm)], ['47'])).
% 0.59/0.78  thf(t66_xboole_1, axiom,
% 0.59/0.78    (![A:$i]:
% 0.59/0.78     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.59/0.78       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.59/0.78  thf('49', plain,
% 0.59/0.78      (![X12 : $i]: (((X12) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X12 @ X12))),
% 0.59/0.78      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.59/0.78  thf('50', plain,
% 0.59/0.78      ((((sk_B_1) = (k1_xboole_0))
% 0.59/0.78        | (r1_tarski @ sk_B_1 @ sk_C_1)
% 0.59/0.78        | ((sk_C_1) = (k1_xboole_0)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['48', '49'])).
% 0.59/0.78  thf('51', plain,
% 0.59/0.78      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 0.59/0.78      inference('split', [status(esa)], ['17'])).
% 0.59/0.78  thf('52', plain,
% 0.59/0.78      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.59/0.78      inference('simplify', [status(thm)], ['19'])).
% 0.59/0.78  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.59/0.78      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.59/0.78  thf('54', plain,
% 0.59/0.78      (((v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.59/0.78      inference('sup+', [status(thm)], ['52', '53'])).
% 0.59/0.78  thf('55', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.59/0.78      inference('simplify_reflect-', [status(thm)], ['6', '25'])).
% 0.59/0.78  thf('56', plain, ((((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['54', '55'])).
% 0.59/0.78  thf('57', plain,
% 0.59/0.78      (~ (((sk_C_1) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.59/0.78      inference('split', [status(esa)], ['17'])).
% 0.59/0.78  thf('58', plain, (~ (((sk_C_1) = (k1_xboole_0)))),
% 0.59/0.78      inference('sat_resolution*', [status(thm)], ['56', '57'])).
% 0.59/0.78  thf('59', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.59/0.78      inference('simpl_trail', [status(thm)], ['51', '58'])).
% 0.59/0.78  thf('60', plain,
% 0.59/0.78      ((((sk_B_1) = (k1_xboole_0)) | (r1_tarski @ sk_B_1 @ sk_C_1))),
% 0.59/0.78      inference('simplify_reflect-', [status(thm)], ['50', '59'])).
% 0.59/0.78  thf('61', plain,
% 0.59/0.78      (![X9 : $i, X10 : $i]:
% 0.59/0.78         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 0.59/0.78      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.59/0.78  thf('62', plain,
% 0.59/0.78      ((((sk_B_1) = (k1_xboole_0))
% 0.59/0.78        | ((k2_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_C_1)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['60', '61'])).
% 0.59/0.78  thf('63', plain,
% 0.59/0.78      ((((k1_tarski @ sk_A) = (sk_C_1)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.59/0.78      inference('sup+', [status(thm)], ['28', '62'])).
% 0.59/0.78  thf('64', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 0.59/0.78      inference('simpl_trail', [status(thm)], ['8', '24'])).
% 0.59/0.78  thf('65', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.59/0.78      inference('simplify_reflect-', [status(thm)], ['63', '64'])).
% 0.59/0.78  thf('66', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.59/0.78      inference('demod', [status(thm)], ['27', '65'])).
% 0.59/0.78  thf('67', plain, ($false), inference('demod', [status(thm)], ['26', '66'])).
% 0.59/0.78  
% 0.59/0.78  % SZS output end Refutation
% 0.59/0.78  
% 0.59/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
