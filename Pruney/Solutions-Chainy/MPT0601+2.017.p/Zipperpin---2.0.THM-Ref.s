%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9tTOzkbMVY

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 151 expanded)
%              Number of leaves         :   27 (  52 expanded)
%              Depth                    :   16
%              Number of atoms          :  576 (1196 expanded)
%              Number of equality atoms :   58 ( 115 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(t149_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X40: $i] :
      ( ( ( k9_relat_1 @ X40 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t149_relat_1])).

thf(t205_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
        <=> ( ( k11_relat_1 @ B @ A )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t205_relat_1])).

thf('1',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['1'])).

thf('4',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['1'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('7',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X32 @ X31 )
      | ( r2_hidden @ ( k4_tarski @ X32 @ ( sk_D_1 @ X32 @ X30 ) ) @ X30 )
      | ( X31
       != ( k1_relat_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('8',plain,(
    ! [X30: $i,X32: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X32 @ ( sk_D_1 @ X32 @ X30 ) ) @ X30 )
      | ~ ( r2_hidden @ X32 @ ( k1_relat_1 @ X30 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_1 @ sk_A @ sk_B ) ) @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('10',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X43 @ X41 ) @ X42 )
      | ( r2_hidden @ X41 @ ( k11_relat_1 @ X42 @ X43 ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('11',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k11_relat_1 @ sk_B @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k11_relat_1 @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
      & ( ( k11_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','13'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k6_subset_1 @ X24 @ X25 )
      = ( k4_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('17',plain,(
    ! [X9: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('18',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ( ( k4_xboole_0 @ X20 @ ( k1_tarski @ X19 ) )
       != X20 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('19',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k6_subset_1 @ X24 @ X25 )
      = ( k4_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('20',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ( ( k6_subset_1 @ X20 @ ( k1_tarski @ X19 ) )
       != X20 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','22'])).

thf('24',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['3','23'])).

thf('25',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['2','24'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('26',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k11_relat_1 @ X26 @ X27 )
        = ( k9_relat_1 @ X26 @ ( k1_tarski @ X27 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('27',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ X20 @ ( k1_tarski @ X21 ) )
        = X20 )
      | ( r2_hidden @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('28',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k6_subset_1 @ X24 @ X25 )
      = ( k4_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('29',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k6_subset_1 @ X20 @ ( k1_tarski @ X21 ) )
        = X20 )
      | ( r2_hidden @ X21 @ X20 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf('31',plain,
    ( ( ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) )
      = ( k1_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('33',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k6_subset_1 @ X24 @ X25 )
      = ( k4_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('34',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k6_subset_1 @ X24 @ X25 )
      = ( k4_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('35',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k6_subset_1 @ X7 @ ( k6_subset_1 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ( ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['31','35'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('38',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('39',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k6_subset_1 @ X24 @ X25 )
      = ( k4_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('40',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k6_subset_1 @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['37','40'])).

thf('42',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','41'])).

thf(t145_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k9_relat_1 @ B @ A )
        = ( k9_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('43',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k9_relat_1 @ X38 @ X39 )
        = ( k9_relat_1 @ X38 @ ( k3_xboole_0 @ ( k1_relat_1 @ X38 ) @ X39 ) ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t145_relat_1])).

thf('44',plain,
    ( ( ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = ( k9_relat_1 @ sk_B @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k9_relat_1 @ sk_B @ k1_xboole_0 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('48',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['3','23','47'])).

thf('49',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k9_relat_1 @ sk_B @ k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['46','48'])).

thf('50',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = ( k9_relat_1 @ sk_B @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = ( k9_relat_1 @ sk_B @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ( k9_relat_1 @ sk_B @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['25','52'])).

thf('54',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    $false ),
    inference(simplify,[status(thm)],['56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9tTOzkbMVY
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:50:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 138 iterations in 0.058s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.21/0.52  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.21/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.52  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.52  thf(t149_relat_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ A ) =>
% 0.21/0.52       ( ( k9_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (![X40 : $i]:
% 0.21/0.52         (((k9_relat_1 @ X40 @ k1_xboole_0) = (k1_xboole_0))
% 0.21/0.52          | ~ (v1_relat_1 @ X40))),
% 0.21/0.52      inference('cnf', [status(esa)], [t149_relat_1])).
% 0.21/0.52  thf(t205_relat_1, conjecture,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ B ) =>
% 0.21/0.52       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.21/0.52         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i]:
% 0.21/0.52        ( ( v1_relat_1 @ B ) =>
% 0.21/0.52          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.21/0.52            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      ((((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))
% 0.21/0.52        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      ((((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 0.21/0.52         <= (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.21/0.52      inference('split', [status(esa)], ['1'])).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.21/0.52       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.21/0.52      inference('split', [status(esa)], ['1'])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))
% 0.21/0.52        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.21/0.52         <= ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.21/0.52      inference('split', [status(esa)], ['4'])).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.21/0.52         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.21/0.52      inference('split', [status(esa)], ['1'])).
% 0.21/0.52  thf(d4_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.21/0.52       ( ![C:$i]:
% 0.21/0.52         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.52           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X32 @ X31)
% 0.21/0.52          | (r2_hidden @ (k4_tarski @ X32 @ (sk_D_1 @ X32 @ X30)) @ X30)
% 0.21/0.52          | ((X31) != (k1_relat_1 @ X30)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X30 : $i, X32 : $i]:
% 0.21/0.52         ((r2_hidden @ (k4_tarski @ X32 @ (sk_D_1 @ X32 @ X30)) @ X30)
% 0.21/0.52          | ~ (r2_hidden @ X32 @ (k1_relat_1 @ X30)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_D_1 @ sk_A @ sk_B)) @ sk_B))
% 0.21/0.52         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['6', '8'])).
% 0.21/0.52  thf(t204_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ C ) =>
% 0.21/0.52       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.21/0.52         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.21/0.52         (~ (r2_hidden @ (k4_tarski @ X43 @ X41) @ X42)
% 0.21/0.52          | (r2_hidden @ X41 @ (k11_relat_1 @ X42 @ X43))
% 0.21/0.52          | ~ (v1_relat_1 @ X42))),
% 0.21/0.52      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (((~ (v1_relat_1 @ sk_B)
% 0.21/0.52         | (r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k11_relat_1 @ sk_B @ sk_A))))
% 0.21/0.52         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k11_relat_1 @ sk_B @ sk_A)))
% 0.21/0.52         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.21/0.52      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ k1_xboole_0))
% 0.21/0.52         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) & 
% 0.21/0.52             (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.21/0.52      inference('sup+', [status(thm)], ['5', '13'])).
% 0.21/0.52  thf(t4_boole, axiom,
% 0.21/0.52    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X9 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [t4_boole])).
% 0.21/0.52  thf(redefinition_k6_subset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (![X24 : $i, X25 : $i]:
% 0.21/0.52         ((k6_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (![X9 : $i]: ((k6_subset_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 0.21/0.52      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.52  thf(t65_zfmisc_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.21/0.52       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (![X19 : $i, X20 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X19 @ X20)
% 0.21/0.52          | ((k4_xboole_0 @ X20 @ (k1_tarski @ X19)) != (X20)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X24 : $i, X25 : $i]:
% 0.21/0.52         ((k6_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X19 : $i, X20 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X19 @ X20)
% 0.21/0.52          | ((k6_subset_1 @ X20 @ (k1_tarski @ X19)) != (X20)))),
% 0.21/0.52      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['17', '20'])).
% 0.21/0.52  thf('22', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.52      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) | 
% 0.21/0.52       ~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['14', '22'])).
% 0.21/0.52  thf('24', plain, (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.21/0.52      inference('sat_resolution*', [status(thm)], ['3', '23'])).
% 0.21/0.52  thf('25', plain, (((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))),
% 0.21/0.52      inference('simpl_trail', [status(thm)], ['2', '24'])).
% 0.21/0.52  thf(d16_relat_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      (![X26 : $i, X27 : $i]:
% 0.21/0.52         (((k11_relat_1 @ X26 @ X27) = (k9_relat_1 @ X26 @ (k1_tarski @ X27)))
% 0.21/0.52          | ~ (v1_relat_1 @ X26))),
% 0.21/0.52      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (![X20 : $i, X21 : $i]:
% 0.21/0.52         (((k4_xboole_0 @ X20 @ (k1_tarski @ X21)) = (X20))
% 0.21/0.52          | (r2_hidden @ X21 @ X20))),
% 0.21/0.52      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      (![X24 : $i, X25 : $i]:
% 0.21/0.52         ((k6_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      (![X20 : $i, X21 : $i]:
% 0.21/0.52         (((k6_subset_1 @ X20 @ (k1_tarski @ X21)) = (X20))
% 0.21/0.52          | (r2_hidden @ X21 @ X20))),
% 0.21/0.52      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.21/0.52         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.21/0.52      inference('split', [status(esa)], ['4'])).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      ((((k6_subset_1 @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A))
% 0.21/0.52          = (k1_relat_1 @ sk_B)))
% 0.21/0.52         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.52  thf(t48_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      (![X7 : $i, X8 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.21/0.52           = (k3_xboole_0 @ X7 @ X8))),
% 0.21/0.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      (![X24 : $i, X25 : $i]:
% 0.21/0.52         ((k6_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.52  thf('34', plain,
% 0.21/0.52      (![X24 : $i, X25 : $i]:
% 0.21/0.52         ((k6_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      (![X7 : $i, X8 : $i]:
% 0.21/0.52         ((k6_subset_1 @ X7 @ (k6_subset_1 @ X7 @ X8))
% 0.21/0.52           = (k3_xboole_0 @ X7 @ X8))),
% 0.21/0.52      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      ((((k6_subset_1 @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B))
% 0.21/0.52          = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A))))
% 0.21/0.52         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.21/0.52      inference('sup+', [status(thm)], ['31', '35'])).
% 0.21/0.52  thf(idempotence_k2_xboole_0, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.21/0.52  thf('37', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.21/0.52      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.21/0.52  thf(t46_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      (![X5 : $i, X6 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ X5 @ (k2_xboole_0 @ X5 @ X6)) = (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      (![X24 : $i, X25 : $i]:
% 0.21/0.52         ((k6_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.52  thf('40', plain,
% 0.21/0.52      (![X5 : $i, X6 : $i]:
% 0.21/0.52         ((k6_subset_1 @ X5 @ (k2_xboole_0 @ X5 @ X6)) = (k1_xboole_0))),
% 0.21/0.52      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.52  thf('41', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['37', '40'])).
% 0.21/0.52  thf('42', plain,
% 0.21/0.52      ((((k1_xboole_0)
% 0.21/0.52          = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A))))
% 0.21/0.52         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.21/0.52      inference('demod', [status(thm)], ['36', '41'])).
% 0.21/0.52  thf(t145_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ B ) =>
% 0.21/0.52       ( ( k9_relat_1 @ B @ A ) =
% 0.21/0.52         ( k9_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.21/0.52  thf('43', plain,
% 0.21/0.52      (![X38 : $i, X39 : $i]:
% 0.21/0.52         (((k9_relat_1 @ X38 @ X39)
% 0.21/0.52            = (k9_relat_1 @ X38 @ (k3_xboole_0 @ (k1_relat_1 @ X38) @ X39)))
% 0.21/0.52          | ~ (v1_relat_1 @ X38))),
% 0.21/0.52      inference('cnf', [status(esa)], [t145_relat_1])).
% 0.21/0.52  thf('44', plain,
% 0.21/0.52      (((((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.21/0.52           = (k9_relat_1 @ sk_B @ k1_xboole_0))
% 0.21/0.52         | ~ (v1_relat_1 @ sk_B)))
% 0.21/0.52         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.21/0.52      inference('sup+', [status(thm)], ['42', '43'])).
% 0.21/0.52  thf('45', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('46', plain,
% 0.21/0.52      ((((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.21/0.52          = (k9_relat_1 @ sk_B @ k1_xboole_0)))
% 0.21/0.52         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.21/0.52      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.52  thf('47', plain,
% 0.21/0.52      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) | 
% 0.21/0.52       (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.21/0.52      inference('split', [status(esa)], ['4'])).
% 0.21/0.52  thf('48', plain, (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.21/0.52      inference('sat_resolution*', [status(thm)], ['3', '23', '47'])).
% 0.21/0.52  thf('49', plain,
% 0.21/0.52      (((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.21/0.52         = (k9_relat_1 @ sk_B @ k1_xboole_0))),
% 0.21/0.52      inference('simpl_trail', [status(thm)], ['46', '48'])).
% 0.21/0.52  thf('50', plain,
% 0.21/0.52      ((((k11_relat_1 @ sk_B @ sk_A) = (k9_relat_1 @ sk_B @ k1_xboole_0))
% 0.21/0.52        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.52      inference('sup+', [status(thm)], ['26', '49'])).
% 0.21/0.52  thf('51', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('52', plain,
% 0.21/0.52      (((k11_relat_1 @ sk_B @ sk_A) = (k9_relat_1 @ sk_B @ k1_xboole_0))),
% 0.21/0.52      inference('demod', [status(thm)], ['50', '51'])).
% 0.21/0.52  thf('53', plain, (((k9_relat_1 @ sk_B @ k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.52      inference('demod', [status(thm)], ['25', '52'])).
% 0.21/0.52  thf('54', plain,
% 0.21/0.52      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['0', '53'])).
% 0.21/0.52  thf('55', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('56', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.52      inference('demod', [status(thm)], ['54', '55'])).
% 0.21/0.52  thf('57', plain, ($false), inference('simplify', [status(thm)], ['56'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
