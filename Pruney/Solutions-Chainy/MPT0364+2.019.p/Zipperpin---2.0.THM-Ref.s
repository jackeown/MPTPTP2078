%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m3zn6qaM00

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 124 expanded)
%              Number of leaves         :   18 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :  569 (1240 expanded)
%              Number of equality atoms :    9 (  18 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t44_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) )
          <=> ( r1_tarski @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) )
            <=> ( r1_tarski @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_subset_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
    | ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
    | ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X6 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k4_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('10',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
    | ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
   <= ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['11'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('14',plain,
    ( ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ sk_B )
   <= ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B )
   <= ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['10','14'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X9 @ X11 )
      | ( r1_tarski @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ X0 @ sk_B ) )
        | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ X0 ) )
   <= ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['7','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k4_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('21',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('23',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X15 @ X14 ) @ ( k3_subset_1 @ X15 @ X16 ) )
      | ( r1_tarski @ X16 @ X14 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ X0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['18','29'])).

thf('31',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
    | ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
    | ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['11'])).

thf('34',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['11'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X16 @ X14 )
      | ( r1_tarski @ ( k3_subset_1 @ X15 @ X14 ) @ ( k3_subset_1 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
    | ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('43',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
    | ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['34','43'])).

thf('45',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X6 @ X8 )
      | ~ ( r1_tarski @ X6 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('46',plain,
    ( ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('48',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('50',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
   <= ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('51',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) )
   <= ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
    | ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','32','33','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m3zn6qaM00
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:12:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 124 iterations in 0.058s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.52  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.22/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.52  thf(t44_subset_1, conjecture,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.52       ( ![C:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.52           ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) ) <=>
% 0.22/0.52             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i,B:$i]:
% 0.22/0.52        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.52          ( ![C:$i]:
% 0.22/0.52            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.52              ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) ) <=>
% 0.22/0.52                ( r1_tarski @ B @ C ) ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t44_subset_1])).
% 0.22/0.52  thf('0', plain,
% 0.22/0.52      ((~ (r1_tarski @ sk_B @ sk_C_1)
% 0.22/0.52        | ~ (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      (~ ((r1_tarski @ sk_B @ sk_C_1)) | 
% 0.22/0.52       ~ ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.22/0.52      inference('split', [status(esa)], ['0'])).
% 0.22/0.52  thf(d3_tarski, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      (![X1 : $i, X3 : $i]:
% 0.22/0.52         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      (![X1 : $i, X3 : $i]:
% 0.22/0.52         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.22/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.52  thf('5', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.22/0.52      inference('simplify', [status(thm)], ['4'])).
% 0.22/0.52  thf(t106_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.22/0.52       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.22/0.52  thf('6', plain,
% 0.22/0.52      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.52         ((r1_tarski @ X6 @ X7) | ~ (r1_tarski @ X6 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X1)),
% 0.22/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.52  thf('8', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(d5_subset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.52       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.22/0.52  thf('9', plain,
% 0.22/0.52      (![X12 : $i, X13 : $i]:
% 0.22/0.52         (((k3_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))
% 0.22/0.52          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.22/0.52      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      (((r1_tarski @ sk_B @ sk_C_1)
% 0.22/0.52        | (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 0.22/0.52         <= (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.22/0.52      inference('split', [status(esa)], ['11'])).
% 0.22/0.52  thf(symmetry_r1_xboole_0, axiom,
% 0.22/0.52    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (![X4 : $i, X5 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ X4 @ X5) | ~ (r1_xboole_0 @ X5 @ X4))),
% 0.22/0.52      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      (((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_B))
% 0.22/0.52         <= (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      (((r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C_1) @ sk_B))
% 0.22/0.52         <= (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.22/0.52      inference('sup+', [status(thm)], ['10', '14'])).
% 0.22/0.52  thf(t86_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.22/0.52       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.52         (~ (r1_tarski @ X9 @ X10)
% 0.22/0.52          | ~ (r1_xboole_0 @ X9 @ X11)
% 0.22/0.52          | (r1_tarski @ X9 @ (k4_xboole_0 @ X10 @ X11)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t86_xboole_1])).
% 0.22/0.52  thf('17', plain,
% 0.22/0.52      ((![X0 : $i]:
% 0.22/0.52          ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.22/0.52            (k4_xboole_0 @ X0 @ sk_B))
% 0.22/0.52           | ~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C_1) @ X0)))
% 0.22/0.52         <= (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.22/0.52         (k4_xboole_0 @ sk_A @ sk_B)))
% 0.22/0.52         <= (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['7', '17'])).
% 0.22/0.52  thf('19', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      (![X12 : $i, X13 : $i]:
% 0.22/0.52         (((k3_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))
% 0.22/0.52          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.22/0.52      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.52  thf('22', plain,
% 0.22/0.52      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.52  thf(t31_subset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.52       ( ![C:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.52           ( ( r1_tarski @ B @ C ) <=>
% 0.22/0.52             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.22/0.52          | ~ (r1_tarski @ (k3_subset_1 @ X15 @ X14) @ 
% 0.22/0.52               (k3_subset_1 @ X15 @ X16))
% 0.22/0.52          | (r1_tarski @ X16 @ X14)
% 0.22/0.52          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.22/0.52             (k3_subset_1 @ sk_A @ X0))
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.52          | (r1_tarski @ X0 @ sk_C_1)
% 0.22/0.52          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.52  thf('25', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.22/0.52             (k3_subset_1 @ sk_A @ X0))
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.52          | (r1_tarski @ X0 @ sk_C_1))),
% 0.22/0.52      inference('demod', [status(thm)], ['24', '25'])).
% 0.22/0.52  thf('27', plain,
% 0.22/0.52      ((~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.22/0.52           (k4_xboole_0 @ sk_A @ sk_B))
% 0.22/0.52        | (r1_tarski @ sk_B @ sk_C_1)
% 0.22/0.52        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['21', '26'])).
% 0.22/0.52  thf('28', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      ((~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.22/0.52           (k4_xboole_0 @ sk_A @ sk_B))
% 0.22/0.52        | (r1_tarski @ sk_B @ sk_C_1))),
% 0.22/0.52      inference('demod', [status(thm)], ['27', '28'])).
% 0.22/0.52  thf('30', plain,
% 0.22/0.52      (((r1_tarski @ sk_B @ sk_C_1))
% 0.22/0.52         <= (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['18', '29'])).
% 0.22/0.52  thf('31', plain,
% 0.22/0.52      ((~ (r1_tarski @ sk_B @ sk_C_1)) <= (~ ((r1_tarski @ sk_B @ sk_C_1)))),
% 0.22/0.52      inference('split', [status(esa)], ['0'])).
% 0.22/0.52  thf('32', plain,
% 0.22/0.52      (((r1_tarski @ sk_B @ sk_C_1)) | 
% 0.22/0.52       ~ ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.52  thf('33', plain,
% 0.22/0.52      (((r1_tarski @ sk_B @ sk_C_1)) | 
% 0.22/0.52       ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.22/0.52      inference('split', [status(esa)], ['11'])).
% 0.22/0.52  thf('34', plain,
% 0.22/0.52      (((r1_tarski @ sk_B @ sk_C_1)) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.22/0.52      inference('split', [status(esa)], ['11'])).
% 0.22/0.52  thf('35', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('36', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('37', plain,
% 0.22/0.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.22/0.52          | ~ (r1_tarski @ X16 @ X14)
% 0.22/0.52          | (r1_tarski @ (k3_subset_1 @ X15 @ X14) @ (k3_subset_1 @ X15 @ X16))
% 0.22/0.52          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.22/0.52  thf('38', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.52          | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.22/0.52             (k3_subset_1 @ sk_A @ X0))
% 0.22/0.52          | ~ (r1_tarski @ X0 @ sk_C_1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['36', '37'])).
% 0.22/0.52  thf('39', plain,
% 0.22/0.52      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.52  thf('40', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.52          | (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.22/0.52             (k3_subset_1 @ sk_A @ X0))
% 0.22/0.52          | ~ (r1_tarski @ X0 @ sk_C_1))),
% 0.22/0.52      inference('demod', [status(thm)], ['38', '39'])).
% 0.22/0.52  thf('41', plain,
% 0.22/0.52      ((~ (r1_tarski @ sk_B @ sk_C_1)
% 0.22/0.52        | (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.22/0.52           (k3_subset_1 @ sk_A @ sk_B)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['35', '40'])).
% 0.22/0.52  thf('42', plain,
% 0.22/0.52      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.52  thf('43', plain,
% 0.22/0.52      ((~ (r1_tarski @ sk_B @ sk_C_1)
% 0.22/0.52        | (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.22/0.52           (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.52      inference('demod', [status(thm)], ['41', '42'])).
% 0.22/0.52  thf('44', plain,
% 0.22/0.52      (((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.22/0.52         (k4_xboole_0 @ sk_A @ sk_B))) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['34', '43'])).
% 0.22/0.52  thf('45', plain,
% 0.22/0.52      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ X6 @ X8)
% 0.22/0.52          | ~ (r1_tarski @ X6 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.22/0.52  thf('46', plain,
% 0.22/0.52      (((r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C_1) @ sk_B))
% 0.22/0.52         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['44', '45'])).
% 0.22/0.52  thf('47', plain,
% 0.22/0.52      (![X4 : $i, X5 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ X4 @ X5) | ~ (r1_xboole_0 @ X5 @ X4))),
% 0.22/0.52      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.22/0.52  thf('48', plain,
% 0.22/0.52      (((r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C_1)))
% 0.22/0.52         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.52  thf('49', plain,
% 0.22/0.52      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.52  thf('50', plain,
% 0.22/0.52      ((~ (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 0.22/0.52         <= (~ ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.22/0.52      inference('split', [status(esa)], ['0'])).
% 0.22/0.52  thf('51', plain,
% 0.22/0.52      ((~ (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C_1)))
% 0.22/0.52         <= (~ ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['49', '50'])).
% 0.22/0.52  thf('52', plain,
% 0.22/0.52      (~ ((r1_tarski @ sk_B @ sk_C_1)) | 
% 0.22/0.52       ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['48', '51'])).
% 0.22/0.52  thf('53', plain, ($false),
% 0.22/0.52      inference('sat_resolution*', [status(thm)], ['1', '32', '33', '52'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
