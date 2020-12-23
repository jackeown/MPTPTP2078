%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oUf3htVbZR

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:51 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 120 expanded)
%              Number of leaves         :   27 (  45 expanded)
%              Depth                    :   16
%              Number of atoms          :  535 ( 929 expanded)
%              Number of equality atoms :   27 (  44 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(t30_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
         => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
            & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t30_relat_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_2 ) )
    | ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_2 ) )
   <= ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('3',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X24 @ X25 ) @ X26 )
      | ( r2_hidden @ X24 @ X27 )
      | ( X27
       != ( k1_relat_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('4',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r2_hidden @ X24 @ ( k1_relat_1 @ X26 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X24 @ X25 ) @ X26 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('6',plain,(
    ! [X38: $i] :
      ( ( ( k3_relat_1 @ X38 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X38 ) @ ( k2_relat_1 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X9 != X11 )
      | ( r2_hidden @ X9 @ X10 )
      | ( X10
       != ( k2_tarski @ X11 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('8',plain,(
    ! [X8: $i,X11: $i] :
      ( r2_hidden @ X11 @ ( k2_tarski @ X11 @ X8 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X16 @ X17 ) )
      = ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf(t100_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ) )).

thf('10',plain,(
    ! [X18: $i] :
      ( r1_tarski @ X18 @ ( k1_zfmisc_1 @ ( k3_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('14',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('15',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','16'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('18',plain,(
    ! [X19: $i,X20: $i] :
      ( ( m1_subset_1 @ X19 @ X20 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','23'])).

thf('25',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_2 ) )
    | ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['5','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_2 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_2 ) )
    | ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,(
    ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_2 ) ) ),
    inference('sat_resolution*',[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_2 ) ) ),
    inference(simpl_trail,[status(thm)],['1','33'])).

thf('35',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('36',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X31 @ X32 ) @ X33 )
      | ( r2_hidden @ X32 @ X34 )
      | ( X34
       != ( k2_relat_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('37',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( r2_hidden @ X32 @ ( k2_relat_1 @ X33 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X31 @ X32 ) @ X33 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    r2_hidden @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X38: $i] :
      ( ( ( k3_relat_1 @ X38 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X38 ) @ ( k2_relat_1 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('40',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X9 != X8 )
      | ( r2_hidden @ X9 @ X10 )
      | ( X10
       != ( k2_tarski @ X11 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('41',plain,(
    ! [X8: $i,X11: $i] :
      ( r2_hidden @ X8 @ ( k2_tarski @ X11 @ X8 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X19: $i,X20: $i] :
      ( ( m1_subset_1 @ X19 @ X20 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','49'])).

thf('51',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_2 ) )
    | ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['38','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['34','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oUf3htVbZR
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:41:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.43/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.43/0.62  % Solved by: fo/fo7.sh
% 0.43/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.62  % done 285 iterations in 0.175s
% 0.43/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.43/0.62  % SZS output start Refutation
% 0.43/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.43/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.43/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.43/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.43/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.43/0.62  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.43/0.62  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.43/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.43/0.62  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.43/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.43/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.43/0.62  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.43/0.62  thf(t30_relat_1, conjecture,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( v1_relat_1 @ C ) =>
% 0.43/0.62       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.43/0.62         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.43/0.62           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ))).
% 0.43/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.62    (~( ![A:$i,B:$i,C:$i]:
% 0.43/0.62        ( ( v1_relat_1 @ C ) =>
% 0.43/0.62          ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.43/0.62            ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.43/0.62              ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )),
% 0.43/0.62    inference('cnf.neg', [status(esa)], [t30_relat_1])).
% 0.43/0.62  thf('0', plain,
% 0.43/0.62      ((~ (r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_2))
% 0.43/0.62        | ~ (r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_2)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('1', plain,
% 0.43/0.62      ((~ (r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_2)))
% 0.43/0.62         <= (~ ((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_2))))),
% 0.43/0.62      inference('split', [status(esa)], ['0'])).
% 0.43/0.62  thf('2', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_2)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(d4_relat_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.43/0.62       ( ![C:$i]:
% 0.43/0.62         ( ( r2_hidden @ C @ B ) <=>
% 0.43/0.62           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.43/0.62  thf('3', plain,
% 0.43/0.62      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.43/0.62         (~ (r2_hidden @ (k4_tarski @ X24 @ X25) @ X26)
% 0.43/0.62          | (r2_hidden @ X24 @ X27)
% 0.43/0.62          | ((X27) != (k1_relat_1 @ X26)))),
% 0.43/0.62      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.43/0.62  thf('4', plain,
% 0.43/0.62      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.43/0.62         ((r2_hidden @ X24 @ (k1_relat_1 @ X26))
% 0.43/0.62          | ~ (r2_hidden @ (k4_tarski @ X24 @ X25) @ X26))),
% 0.43/0.62      inference('simplify', [status(thm)], ['3'])).
% 0.43/0.62  thf('5', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_2))),
% 0.43/0.62      inference('sup-', [status(thm)], ['2', '4'])).
% 0.43/0.62  thf(d6_relat_1, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( v1_relat_1 @ A ) =>
% 0.43/0.62       ( ( k3_relat_1 @ A ) =
% 0.43/0.62         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.43/0.62  thf('6', plain,
% 0.43/0.62      (![X38 : $i]:
% 0.43/0.62         (((k3_relat_1 @ X38)
% 0.43/0.62            = (k2_xboole_0 @ (k1_relat_1 @ X38) @ (k2_relat_1 @ X38)))
% 0.43/0.62          | ~ (v1_relat_1 @ X38))),
% 0.43/0.62      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.43/0.62  thf(d2_tarski, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.43/0.62       ( ![D:$i]:
% 0.43/0.62         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.43/0.62  thf('7', plain,
% 0.43/0.62      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.43/0.62         (((X9) != (X11))
% 0.43/0.62          | (r2_hidden @ X9 @ X10)
% 0.43/0.62          | ((X10) != (k2_tarski @ X11 @ X8)))),
% 0.43/0.62      inference('cnf', [status(esa)], [d2_tarski])).
% 0.43/0.62  thf('8', plain,
% 0.43/0.62      (![X8 : $i, X11 : $i]: (r2_hidden @ X11 @ (k2_tarski @ X11 @ X8))),
% 0.43/0.62      inference('simplify', [status(thm)], ['7'])).
% 0.43/0.62  thf(l51_zfmisc_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.43/0.62  thf('9', plain,
% 0.43/0.62      (![X16 : $i, X17 : $i]:
% 0.43/0.62         ((k3_tarski @ (k2_tarski @ X16 @ X17)) = (k2_xboole_0 @ X16 @ X17))),
% 0.43/0.62      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.43/0.62  thf(t100_zfmisc_1, axiom,
% 0.43/0.62    (![A:$i]: ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ))).
% 0.43/0.62  thf('10', plain,
% 0.43/0.62      (![X18 : $i]: (r1_tarski @ X18 @ (k1_zfmisc_1 @ (k3_tarski @ X18)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t100_zfmisc_1])).
% 0.43/0.62  thf('11', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (r1_tarski @ (k2_tarski @ X1 @ X0) @ 
% 0.43/0.62          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['9', '10'])).
% 0.43/0.62  thf(t28_xboole_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.43/0.62  thf('12', plain,
% 0.43/0.62      (![X6 : $i, X7 : $i]:
% 0.43/0.62         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.43/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.43/0.62  thf('13', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((k3_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 0.43/0.62           (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0))) = (k2_tarski @ X1 @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['11', '12'])).
% 0.43/0.62  thf(d4_xboole_0, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.43/0.62       ( ![D:$i]:
% 0.43/0.62         ( ( r2_hidden @ D @ C ) <=>
% 0.43/0.62           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.43/0.62  thf('14', plain,
% 0.43/0.62      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X4 @ X3)
% 0.43/0.62          | (r2_hidden @ X4 @ X2)
% 0.43/0.62          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.43/0.62      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.43/0.62  thf('15', plain,
% 0.43/0.62      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.43/0.62         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.43/0.62      inference('simplify', [status(thm)], ['14'])).
% 0.43/0.62  thf('16', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.43/0.62          | (r2_hidden @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['13', '15'])).
% 0.43/0.62  thf('17', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (r2_hidden @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['8', '16'])).
% 0.43/0.62  thf(t1_subset, axiom,
% 0.43/0.62    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.43/0.62  thf('18', plain,
% 0.43/0.62      (![X19 : $i, X20 : $i]:
% 0.43/0.62         ((m1_subset_1 @ X19 @ X20) | ~ (r2_hidden @ X19 @ X20))),
% 0.43/0.62      inference('cnf', [status(esa)], [t1_subset])).
% 0.43/0.62  thf('19', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['17', '18'])).
% 0.43/0.62  thf(t3_subset, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.43/0.62  thf('20', plain,
% 0.43/0.62      (![X21 : $i, X22 : $i]:
% 0.43/0.62         ((r1_tarski @ X21 @ X22) | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.43/0.62  thf('21', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['19', '20'])).
% 0.43/0.62  thf('22', plain,
% 0.43/0.62      (![X6 : $i, X7 : $i]:
% 0.43/0.62         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.43/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.43/0.62  thf('23', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['21', '22'])).
% 0.43/0.62  thf('24', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (((k3_xboole_0 @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.43/0.62            = (k1_relat_1 @ X0))
% 0.43/0.62          | ~ (v1_relat_1 @ X0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['6', '23'])).
% 0.43/0.62  thf('25', plain,
% 0.43/0.62      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.43/0.62         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.43/0.62      inference('simplify', [status(thm)], ['14'])).
% 0.43/0.62  thf('26', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.43/0.62          | ~ (v1_relat_1 @ X0)
% 0.43/0.62          | (r2_hidden @ X1 @ (k3_relat_1 @ X0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['24', '25'])).
% 0.43/0.62  thf('27', plain,
% 0.43/0.62      (((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_2)) | ~ (v1_relat_1 @ sk_C_2))),
% 0.43/0.62      inference('sup-', [status(thm)], ['5', '26'])).
% 0.43/0.62  thf('28', plain, ((v1_relat_1 @ sk_C_2)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('29', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_2))),
% 0.43/0.62      inference('demod', [status(thm)], ['27', '28'])).
% 0.43/0.62  thf('30', plain,
% 0.43/0.62      ((~ (r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_2)))
% 0.43/0.62         <= (~ ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_2))))),
% 0.43/0.62      inference('split', [status(esa)], ['0'])).
% 0.43/0.62  thf('31', plain, (((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_2)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['29', '30'])).
% 0.43/0.62  thf('32', plain,
% 0.43/0.62      (~ ((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_2))) | 
% 0.43/0.62       ~ ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_2)))),
% 0.43/0.62      inference('split', [status(esa)], ['0'])).
% 0.43/0.62  thf('33', plain, (~ ((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_2)))),
% 0.43/0.62      inference('sat_resolution*', [status(thm)], ['31', '32'])).
% 0.43/0.62  thf('34', plain, (~ (r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_2))),
% 0.43/0.62      inference('simpl_trail', [status(thm)], ['1', '33'])).
% 0.43/0.62  thf('35', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_2)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(d5_relat_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.43/0.62       ( ![C:$i]:
% 0.43/0.62         ( ( r2_hidden @ C @ B ) <=>
% 0.43/0.62           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.43/0.62  thf('36', plain,
% 0.43/0.62      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.43/0.62         (~ (r2_hidden @ (k4_tarski @ X31 @ X32) @ X33)
% 0.43/0.62          | (r2_hidden @ X32 @ X34)
% 0.43/0.62          | ((X34) != (k2_relat_1 @ X33)))),
% 0.43/0.62      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.43/0.62  thf('37', plain,
% 0.43/0.62      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.43/0.62         ((r2_hidden @ X32 @ (k2_relat_1 @ X33))
% 0.43/0.62          | ~ (r2_hidden @ (k4_tarski @ X31 @ X32) @ X33))),
% 0.43/0.62      inference('simplify', [status(thm)], ['36'])).
% 0.43/0.62  thf('38', plain, ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_C_2))),
% 0.43/0.62      inference('sup-', [status(thm)], ['35', '37'])).
% 0.43/0.62  thf('39', plain,
% 0.43/0.62      (![X38 : $i]:
% 0.43/0.62         (((k3_relat_1 @ X38)
% 0.43/0.62            = (k2_xboole_0 @ (k1_relat_1 @ X38) @ (k2_relat_1 @ X38)))
% 0.43/0.62          | ~ (v1_relat_1 @ X38))),
% 0.43/0.62      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.43/0.62  thf('40', plain,
% 0.43/0.62      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.43/0.62         (((X9) != (X8))
% 0.43/0.62          | (r2_hidden @ X9 @ X10)
% 0.43/0.62          | ((X10) != (k2_tarski @ X11 @ X8)))),
% 0.43/0.62      inference('cnf', [status(esa)], [d2_tarski])).
% 0.43/0.62  thf('41', plain,
% 0.43/0.62      (![X8 : $i, X11 : $i]: (r2_hidden @ X8 @ (k2_tarski @ X11 @ X8))),
% 0.43/0.62      inference('simplify', [status(thm)], ['40'])).
% 0.43/0.62  thf('42', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.43/0.62          | (r2_hidden @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['13', '15'])).
% 0.43/0.62  thf('43', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (r2_hidden @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['41', '42'])).
% 0.43/0.62  thf('44', plain,
% 0.43/0.62      (![X19 : $i, X20 : $i]:
% 0.43/0.62         ((m1_subset_1 @ X19 @ X20) | ~ (r2_hidden @ X19 @ X20))),
% 0.43/0.62      inference('cnf', [status(esa)], [t1_subset])).
% 0.43/0.62  thf('45', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['43', '44'])).
% 0.43/0.62  thf('46', plain,
% 0.43/0.62      (![X21 : $i, X22 : $i]:
% 0.43/0.62         ((r1_tarski @ X21 @ X22) | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.43/0.62  thf('47', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['45', '46'])).
% 0.43/0.62  thf('48', plain,
% 0.43/0.62      (![X6 : $i, X7 : $i]:
% 0.43/0.62         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.43/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.43/0.62  thf('49', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['47', '48'])).
% 0.43/0.62  thf('50', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (((k3_xboole_0 @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.43/0.62            = (k2_relat_1 @ X0))
% 0.43/0.62          | ~ (v1_relat_1 @ X0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['39', '49'])).
% 0.43/0.62  thf('51', plain,
% 0.43/0.62      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.43/0.62         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.43/0.62      inference('simplify', [status(thm)], ['14'])).
% 0.43/0.62  thf('52', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.43/0.62          | ~ (v1_relat_1 @ X0)
% 0.43/0.62          | (r2_hidden @ X1 @ (k3_relat_1 @ X0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['50', '51'])).
% 0.43/0.62  thf('53', plain,
% 0.43/0.62      (((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_2)) | ~ (v1_relat_1 @ sk_C_2))),
% 0.43/0.62      inference('sup-', [status(thm)], ['38', '52'])).
% 0.43/0.62  thf('54', plain, ((v1_relat_1 @ sk_C_2)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('55', plain, ((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_2))),
% 0.43/0.62      inference('demod', [status(thm)], ['53', '54'])).
% 0.43/0.62  thf('56', plain, ($false), inference('demod', [status(thm)], ['34', '55'])).
% 0.43/0.62  
% 0.43/0.62  % SZS output end Refutation
% 0.43/0.62  
% 0.48/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
