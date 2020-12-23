%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7T83VOPxvD

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:00 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 147 expanded)
%              Number of leaves         :   22 (  48 expanded)
%              Depth                    :   15
%              Number of atoms          :  510 (1420 expanded)
%              Number of equality atoms :    8 (  15 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t43_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ C )
          <=> ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_xboole_0 @ B @ C )
            <=> ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_subset_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_3 ) )
    | ~ ( r1_xboole_0 @ sk_B @ sk_C_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_3 ) )
   <= ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_3 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_3 ) )
    | ~ ( r1_xboole_0 @ sk_B @ sk_C_3 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_subset_1 @ X29 @ X30 )
        = ( k4_xboole_0 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_3 )
    = ( k4_xboole_0 @ sk_A @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C_1 @ X13 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C_1 @ X13 @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('9',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_xboole_0 @ sk_C_3 @ ( k3_subset_1 @ sk_A @ sk_C_3 ) ),
    inference('sup+',[status(thm)],['5','14'])).

thf('16',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C_1 @ X13 @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('17',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_3 ) )
    | ( r1_xboole_0 @ sk_B @ sk_C_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_3 ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_3 ) ) ),
    inference(split,[status(esa)],['17'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_3 ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ( r1_xboole_0 @ sk_B @ X0 )
        | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ ( k3_subset_1 @ sk_A @ sk_C_3 ) ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C_1 @ X13 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('23',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ! [X0: $i] :
        ( ( r1_xboole_0 @ sk_B @ X0 )
        | ~ ( r1_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_3 ) )
        | ( r1_xboole_0 @ sk_B @ X0 ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_3 ) )
        | ( r1_xboole_0 @ sk_B @ X0 ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_3 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C_3 )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['15','26'])).

thf('28',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ sk_C_3 )
   <= ~ ( r1_xboole_0 @ sk_B @ sk_C_3 ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C_3 )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_3 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','29'])).

thf('31',plain,(
    ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_3 ) ) ),
    inference(simpl_trail,[status(thm)],['1','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('33',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ X27 )
      | ( r2_hidden @ X26 @ X27 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('35',plain,(
    ! [X31: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('36',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['34','35'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('37',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X24 @ X23 )
      | ( r1_tarski @ X24 @ X22 )
      | ( X23
       != ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('38',plain,(
    ! [X22: $i,X24: $i] :
      ( ( r1_tarski @ X24 @ X22 )
      | ~ ( r2_hidden @ X24 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C_3 )
   <= ( r1_xboole_0 @ sk_B @ sk_C_3 ) ),
    inference(split,[status(esa)],['17'])).

thf('41',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C_3 )
    | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_3 ) ) ),
    inference(split,[status(esa)],['17'])).

thf('42',plain,(
    r1_xboole_0 @ sk_B @ sk_C_3 ),
    inference('sat_resolution*',[status(thm)],['2','29','41'])).

thf('43',plain,(
    r1_xboole_0 @ sk_B @ sk_C_3 ),
    inference(simpl_trail,[status(thm)],['40','42'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('44',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X18 @ X20 )
      | ( r1_tarski @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C_3 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_3 )
    = ( k4_xboole_0 @ sk_A @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('48',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_3 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['31','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7T83VOPxvD
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:56:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.39/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.57  % Solved by: fo/fo7.sh
% 0.39/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.57  % done 194 iterations in 0.086s
% 0.39/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.57  % SZS output start Refutation
% 0.39/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.57  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.39/0.57  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.39/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.57  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.39/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.39/0.57  thf(t43_subset_1, conjecture,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.57       ( ![C:$i]:
% 0.39/0.57         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.57           ( ( r1_xboole_0 @ B @ C ) <=>
% 0.39/0.57             ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.39/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.57    (~( ![A:$i,B:$i]:
% 0.39/0.57        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.57          ( ![C:$i]:
% 0.39/0.57            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.57              ( ( r1_xboole_0 @ B @ C ) <=>
% 0.39/0.57                ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ) )),
% 0.39/0.57    inference('cnf.neg', [status(esa)], [t43_subset_1])).
% 0.39/0.57  thf('0', plain,
% 0.39/0.57      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_3))
% 0.39/0.57        | ~ (r1_xboole_0 @ sk_B @ sk_C_3))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('1', plain,
% 0.39/0.57      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_3)))
% 0.39/0.57         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_3))))),
% 0.39/0.57      inference('split', [status(esa)], ['0'])).
% 0.39/0.57  thf('2', plain,
% 0.39/0.57      (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_3))) | 
% 0.39/0.57       ~ ((r1_xboole_0 @ sk_B @ sk_C_3))),
% 0.39/0.57      inference('split', [status(esa)], ['0'])).
% 0.39/0.57  thf('3', plain, ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(d5_subset_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.57       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.39/0.57  thf('4', plain,
% 0.39/0.57      (![X29 : $i, X30 : $i]:
% 0.39/0.57         (((k3_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))
% 0.39/0.57          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.39/0.57  thf('5', plain,
% 0.39/0.57      (((k3_subset_1 @ sk_A @ sk_C_3) = (k4_xboole_0 @ sk_A @ sk_C_3))),
% 0.39/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.39/0.57  thf(t3_xboole_0, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.39/0.57            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.39/0.57       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.39/0.57            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.39/0.57  thf('6', plain,
% 0.39/0.57      (![X12 : $i, X13 : $i]:
% 0.39/0.57         ((r1_xboole_0 @ X12 @ X13) | (r2_hidden @ (sk_C_1 @ X13 @ X12) @ X13))),
% 0.39/0.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.39/0.57  thf('7', plain,
% 0.39/0.57      (![X12 : $i, X13 : $i]:
% 0.39/0.57         ((r1_xboole_0 @ X12 @ X13) | (r2_hidden @ (sk_C_1 @ X13 @ X12) @ X12))),
% 0.39/0.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.39/0.57  thf(d5_xboole_0, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.39/0.57       ( ![D:$i]:
% 0.39/0.57         ( ( r2_hidden @ D @ C ) <=>
% 0.39/0.57           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.39/0.57  thf('8', plain,
% 0.39/0.57      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X8 @ X7)
% 0.39/0.57          | ~ (r2_hidden @ X8 @ X6)
% 0.39/0.57          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.39/0.57  thf('9', plain,
% 0.39/0.57      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X8 @ X6)
% 0.39/0.57          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.39/0.57      inference('simplify', [status(thm)], ['8'])).
% 0.39/0.57  thf('10', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.39/0.57          | ~ (r2_hidden @ (sk_C_1 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['7', '9'])).
% 0.39/0.57  thf('11', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.39/0.57          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['6', '10'])).
% 0.39/0.57  thf('12', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.39/0.57      inference('simplify', [status(thm)], ['11'])).
% 0.39/0.57  thf(symmetry_r1_xboole_0, axiom,
% 0.39/0.57    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.39/0.57  thf('13', plain,
% 0.39/0.57      (![X10 : $i, X11 : $i]:
% 0.39/0.57         ((r1_xboole_0 @ X10 @ X11) | ~ (r1_xboole_0 @ X11 @ X10))),
% 0.39/0.57      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.39/0.57  thf('14', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['12', '13'])).
% 0.39/0.57  thf('15', plain, ((r1_xboole_0 @ sk_C_3 @ (k3_subset_1 @ sk_A @ sk_C_3))),
% 0.39/0.57      inference('sup+', [status(thm)], ['5', '14'])).
% 0.39/0.57  thf('16', plain,
% 0.39/0.57      (![X12 : $i, X13 : $i]:
% 0.39/0.57         ((r1_xboole_0 @ X12 @ X13) | (r2_hidden @ (sk_C_1 @ X13 @ X12) @ X12))),
% 0.39/0.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.39/0.57  thf('17', plain,
% 0.39/0.57      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_3))
% 0.39/0.57        | (r1_xboole_0 @ sk_B @ sk_C_3))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('18', plain,
% 0.39/0.57      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_3)))
% 0.39/0.57         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_3))))),
% 0.39/0.57      inference('split', [status(esa)], ['17'])).
% 0.39/0.57  thf(d3_tarski, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.39/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.39/0.57  thf('19', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X0 @ X1)
% 0.39/0.57          | (r2_hidden @ X0 @ X2)
% 0.39/0.57          | ~ (r1_tarski @ X1 @ X2))),
% 0.39/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.57  thf('20', plain,
% 0.39/0.57      ((![X0 : $i]:
% 0.39/0.57          ((r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_C_3))
% 0.39/0.57           | ~ (r2_hidden @ X0 @ sk_B)))
% 0.39/0.57         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_3))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['18', '19'])).
% 0.39/0.57  thf('21', plain,
% 0.39/0.57      ((![X0 : $i]:
% 0.39/0.57          ((r1_xboole_0 @ sk_B @ X0)
% 0.39/0.57           | (r2_hidden @ (sk_C_1 @ X0 @ sk_B) @ (k3_subset_1 @ sk_A @ sk_C_3))))
% 0.39/0.57         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_3))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['16', '20'])).
% 0.39/0.57  thf('22', plain,
% 0.39/0.57      (![X12 : $i, X13 : $i]:
% 0.39/0.57         ((r1_xboole_0 @ X12 @ X13) | (r2_hidden @ (sk_C_1 @ X13 @ X12) @ X13))),
% 0.39/0.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.39/0.57  thf('23', plain,
% 0.39/0.57      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X14 @ X12)
% 0.39/0.57          | ~ (r2_hidden @ X14 @ X15)
% 0.39/0.57          | ~ (r1_xboole_0 @ X12 @ X15))),
% 0.39/0.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.39/0.57  thf('24', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         ((r1_xboole_0 @ X1 @ X0)
% 0.39/0.57          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.39/0.57          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 0.39/0.57      inference('sup-', [status(thm)], ['22', '23'])).
% 0.39/0.57  thf('25', plain,
% 0.39/0.57      ((![X0 : $i]:
% 0.39/0.57          ((r1_xboole_0 @ sk_B @ X0)
% 0.39/0.57           | ~ (r1_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_3))
% 0.39/0.57           | (r1_xboole_0 @ sk_B @ X0)))
% 0.39/0.57         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_3))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['21', '24'])).
% 0.39/0.57  thf('26', plain,
% 0.39/0.57      ((![X0 : $i]:
% 0.39/0.57          (~ (r1_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_3))
% 0.39/0.57           | (r1_xboole_0 @ sk_B @ X0)))
% 0.39/0.57         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_3))))),
% 0.39/0.57      inference('simplify', [status(thm)], ['25'])).
% 0.39/0.57  thf('27', plain,
% 0.39/0.57      (((r1_xboole_0 @ sk_B @ sk_C_3))
% 0.39/0.57         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_3))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['15', '26'])).
% 0.39/0.57  thf('28', plain,
% 0.39/0.57      ((~ (r1_xboole_0 @ sk_B @ sk_C_3)) <= (~ ((r1_xboole_0 @ sk_B @ sk_C_3)))),
% 0.39/0.57      inference('split', [status(esa)], ['0'])).
% 0.39/0.57  thf('29', plain,
% 0.39/0.57      (((r1_xboole_0 @ sk_B @ sk_C_3)) | 
% 0.39/0.57       ~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_3)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['27', '28'])).
% 0.39/0.57  thf('30', plain, (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_3)))),
% 0.39/0.57      inference('sat_resolution*', [status(thm)], ['2', '29'])).
% 0.39/0.57  thf('31', plain, (~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_3))),
% 0.39/0.57      inference('simpl_trail', [status(thm)], ['1', '30'])).
% 0.39/0.57  thf('32', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(d2_subset_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ( v1_xboole_0 @ A ) =>
% 0.39/0.57         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.39/0.57       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.39/0.57         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.39/0.57  thf('33', plain,
% 0.39/0.57      (![X26 : $i, X27 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X26 @ X27)
% 0.39/0.57          | (r2_hidden @ X26 @ X27)
% 0.39/0.57          | (v1_xboole_0 @ X27))),
% 0.39/0.57      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.39/0.57  thf('34', plain,
% 0.39/0.57      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.39/0.57        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['32', '33'])).
% 0.39/0.57  thf(fc1_subset_1, axiom,
% 0.39/0.57    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.39/0.57  thf('35', plain, (![X31 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X31))),
% 0.39/0.57      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.39/0.57  thf('36', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.57      inference('clc', [status(thm)], ['34', '35'])).
% 0.39/0.57  thf(d1_zfmisc_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.39/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.39/0.57  thf('37', plain,
% 0.39/0.57      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X24 @ X23)
% 0.39/0.57          | (r1_tarski @ X24 @ X22)
% 0.39/0.57          | ((X23) != (k1_zfmisc_1 @ X22)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.39/0.57  thf('38', plain,
% 0.39/0.57      (![X22 : $i, X24 : $i]:
% 0.39/0.57         ((r1_tarski @ X24 @ X22) | ~ (r2_hidden @ X24 @ (k1_zfmisc_1 @ X22)))),
% 0.39/0.57      inference('simplify', [status(thm)], ['37'])).
% 0.39/0.57  thf('39', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.39/0.57      inference('sup-', [status(thm)], ['36', '38'])).
% 0.39/0.57  thf('40', plain,
% 0.39/0.57      (((r1_xboole_0 @ sk_B @ sk_C_3)) <= (((r1_xboole_0 @ sk_B @ sk_C_3)))),
% 0.39/0.57      inference('split', [status(esa)], ['17'])).
% 0.39/0.57  thf('41', plain,
% 0.39/0.57      (((r1_xboole_0 @ sk_B @ sk_C_3)) | 
% 0.39/0.57       ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_3)))),
% 0.39/0.57      inference('split', [status(esa)], ['17'])).
% 0.39/0.57  thf('42', plain, (((r1_xboole_0 @ sk_B @ sk_C_3))),
% 0.39/0.57      inference('sat_resolution*', [status(thm)], ['2', '29', '41'])).
% 0.39/0.57  thf('43', plain, ((r1_xboole_0 @ sk_B @ sk_C_3)),
% 0.39/0.57      inference('simpl_trail', [status(thm)], ['40', '42'])).
% 0.39/0.57  thf(t86_xboole_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.39/0.57       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.39/0.57  thf('44', plain,
% 0.39/0.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.39/0.57         (~ (r1_tarski @ X18 @ X19)
% 0.39/0.57          | ~ (r1_xboole_0 @ X18 @ X20)
% 0.39/0.57          | (r1_tarski @ X18 @ (k4_xboole_0 @ X19 @ X20)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t86_xboole_1])).
% 0.39/0.57  thf('45', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((r1_tarski @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_3))
% 0.39/0.57          | ~ (r1_tarski @ sk_B @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['43', '44'])).
% 0.39/0.57  thf('46', plain, ((r1_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C_3))),
% 0.39/0.57      inference('sup-', [status(thm)], ['39', '45'])).
% 0.39/0.57  thf('47', plain,
% 0.39/0.57      (((k3_subset_1 @ sk_A @ sk_C_3) = (k4_xboole_0 @ sk_A @ sk_C_3))),
% 0.39/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.39/0.57  thf('48', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_3))),
% 0.39/0.57      inference('demod', [status(thm)], ['46', '47'])).
% 0.39/0.57  thf('49', plain, ($false), inference('demod', [status(thm)], ['31', '48'])).
% 0.39/0.57  
% 0.39/0.57  % SZS output end Refutation
% 0.39/0.57  
% 0.39/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
