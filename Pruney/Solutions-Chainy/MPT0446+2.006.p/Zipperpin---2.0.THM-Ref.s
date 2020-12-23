%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AdGj81dtfy

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:51 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 103 expanded)
%              Number of leaves         :   25 (  40 expanded)
%              Depth                    :   14
%              Number of atoms          :  458 ( 761 expanded)
%              Number of equality atoms :   16 (  22 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ( ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_3 ) )
    | ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_3 ) )
   <= ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_3 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_3 ),
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
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ X20 )
      | ( r2_hidden @ X18 @ X21 )
      | ( X21
       != ( k1_relat_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('4',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X18 @ ( k1_relat_1 @ X20 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ X20 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('6',plain,(
    ! [X32: $i] :
      ( ( ( k3_relat_1 @ X32 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
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
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X7 )
      | ( r2_hidden @ X5 @ X6 )
      | ( X6
       != ( k2_tarski @ X7 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('8',plain,(
    ! [X4: $i,X7: $i] :
      ( r2_hidden @ X7 @ ( k2_tarski @ X7 @ X4 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X10 @ X11 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf(t100_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ) )).

thf('10',plain,(
    ! [X12: $i] :
      ( r1_tarski @ X12 @ ( k1_zfmisc_1 @ ( k3_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ X13 @ X14 )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_3 ) )
    | ~ ( v1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['5','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_3 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_3 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_3 ) )
    | ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_3 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('28',plain,(
    ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_3 ) ) ),
    inference('sat_resolution*',[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_3 ) ) ),
    inference(simpl_trail,[status(thm)],['1','28'])).

thf('30',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('31',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X25 @ X26 ) @ X27 )
      | ( r2_hidden @ X26 @ X28 )
      | ( X28
       != ( k2_relat_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('32',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_hidden @ X26 @ ( k2_relat_1 @ X27 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X25 @ X26 ) @ X27 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    r2_hidden @ sk_B @ ( k2_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X32: $i] :
      ( ( ( k3_relat_1 @ X32 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('35',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X4 )
      | ( r2_hidden @ X5 @ X6 )
      | ( X6
       != ( k2_tarski @ X7 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('36',plain,(
    ! [X4: $i,X7: $i] :
      ( r2_hidden @ X4 @ ( k2_tarski @ X7 @ X4 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ X13 @ X14 )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_3 ) )
    | ~ ( v1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['33','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['29','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AdGj81dtfy
% 0.14/0.38  % Computer   : n013.cluster.edu
% 0.14/0.38  % Model      : x86_64 x86_64
% 0.14/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.38  % Memory     : 8042.1875MB
% 0.14/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.38  % CPULimit   : 60
% 0.14/0.38  % DateTime   : Tue Dec  1 11:43:10 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.45/0.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.64  % Solved by: fo/fo7.sh
% 0.45/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.64  % done 209 iterations in 0.149s
% 0.45/0.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.64  % SZS output start Refutation
% 0.45/0.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.64  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.64  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.45/0.64  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.45/0.64  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.45/0.64  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.45/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.64  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.64  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.64  thf(t30_relat_1, conjecture,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( v1_relat_1 @ C ) =>
% 0.45/0.64       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.45/0.64         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.45/0.64           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ))).
% 0.45/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.64    (~( ![A:$i,B:$i,C:$i]:
% 0.45/0.64        ( ( v1_relat_1 @ C ) =>
% 0.45/0.64          ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.45/0.64            ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.45/0.64              ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )),
% 0.45/0.64    inference('cnf.neg', [status(esa)], [t30_relat_1])).
% 0.45/0.64  thf('0', plain,
% 0.45/0.64      ((~ (r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_3))
% 0.45/0.64        | ~ (r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_3)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('1', plain,
% 0.45/0.64      ((~ (r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_3)))
% 0.45/0.64         <= (~ ((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_3))))),
% 0.45/0.64      inference('split', [status(esa)], ['0'])).
% 0.45/0.64  thf('2', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_3)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(d4_relat_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.45/0.64       ( ![C:$i]:
% 0.45/0.64         ( ( r2_hidden @ C @ B ) <=>
% 0.45/0.64           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.45/0.64  thf('3', plain,
% 0.45/0.64      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.45/0.64         (~ (r2_hidden @ (k4_tarski @ X18 @ X19) @ X20)
% 0.45/0.64          | (r2_hidden @ X18 @ X21)
% 0.45/0.64          | ((X21) != (k1_relat_1 @ X20)))),
% 0.45/0.64      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.45/0.64  thf('4', plain,
% 0.45/0.64      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.64         ((r2_hidden @ X18 @ (k1_relat_1 @ X20))
% 0.45/0.64          | ~ (r2_hidden @ (k4_tarski @ X18 @ X19) @ X20))),
% 0.45/0.64      inference('simplify', [status(thm)], ['3'])).
% 0.45/0.64  thf('5', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_3))),
% 0.45/0.64      inference('sup-', [status(thm)], ['2', '4'])).
% 0.45/0.64  thf(d6_relat_1, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( v1_relat_1 @ A ) =>
% 0.45/0.64       ( ( k3_relat_1 @ A ) =
% 0.45/0.64         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.45/0.64  thf('6', plain,
% 0.45/0.64      (![X32 : $i]:
% 0.45/0.64         (((k3_relat_1 @ X32)
% 0.45/0.64            = (k2_xboole_0 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32)))
% 0.45/0.64          | ~ (v1_relat_1 @ X32))),
% 0.45/0.64      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.45/0.64  thf(d2_tarski, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.45/0.64       ( ![D:$i]:
% 0.45/0.64         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.45/0.64  thf('7', plain,
% 0.45/0.64      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.64         (((X5) != (X7))
% 0.45/0.64          | (r2_hidden @ X5 @ X6)
% 0.45/0.64          | ((X6) != (k2_tarski @ X7 @ X4)))),
% 0.45/0.64      inference('cnf', [status(esa)], [d2_tarski])).
% 0.45/0.64  thf('8', plain,
% 0.45/0.64      (![X4 : $i, X7 : $i]: (r2_hidden @ X7 @ (k2_tarski @ X7 @ X4))),
% 0.45/0.64      inference('simplify', [status(thm)], ['7'])).
% 0.45/0.64  thf(l51_zfmisc_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.45/0.64  thf('9', plain,
% 0.45/0.64      (![X10 : $i, X11 : $i]:
% 0.45/0.64         ((k3_tarski @ (k2_tarski @ X10 @ X11)) = (k2_xboole_0 @ X10 @ X11))),
% 0.45/0.64      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.45/0.64  thf(t100_zfmisc_1, axiom,
% 0.45/0.64    (![A:$i]: ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ))).
% 0.45/0.64  thf('10', plain,
% 0.45/0.64      (![X12 : $i]: (r1_tarski @ X12 @ (k1_zfmisc_1 @ (k3_tarski @ X12)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t100_zfmisc_1])).
% 0.45/0.64  thf('11', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         (r1_tarski @ (k2_tarski @ X1 @ X0) @ 
% 0.45/0.64          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.45/0.64      inference('sup+', [status(thm)], ['9', '10'])).
% 0.45/0.64  thf(d3_tarski, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( r1_tarski @ A @ B ) <=>
% 0.45/0.64       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.45/0.64  thf('12', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.64         (~ (r2_hidden @ X0 @ X1)
% 0.45/0.64          | (r2_hidden @ X0 @ X2)
% 0.45/0.64          | ~ (r1_tarski @ X1 @ X2))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.64  thf('13', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.64         ((r2_hidden @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 0.45/0.64          | ~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.64  thf('14', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         (r2_hidden @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['8', '13'])).
% 0.45/0.64  thf(t1_subset, axiom,
% 0.45/0.64    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.45/0.64  thf('15', plain,
% 0.45/0.64      (![X13 : $i, X14 : $i]:
% 0.45/0.64         ((m1_subset_1 @ X13 @ X14) | ~ (r2_hidden @ X13 @ X14))),
% 0.45/0.64      inference('cnf', [status(esa)], [t1_subset])).
% 0.45/0.64  thf('16', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['14', '15'])).
% 0.45/0.64  thf(t3_subset, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.64  thf('17', plain,
% 0.45/0.64      (![X15 : $i, X16 : $i]:
% 0.45/0.64         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.64  thf('18', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.64  thf('19', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.45/0.64          | ~ (v1_relat_1 @ X0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['6', '18'])).
% 0.45/0.64  thf('20', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.64         (~ (r2_hidden @ X0 @ X1)
% 0.45/0.64          | (r2_hidden @ X0 @ X2)
% 0.45/0.64          | ~ (r1_tarski @ X1 @ X2))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.64  thf('21', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         (~ (v1_relat_1 @ X0)
% 0.45/0.64          | (r2_hidden @ X1 @ (k3_relat_1 @ X0))
% 0.45/0.64          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['19', '20'])).
% 0.45/0.64  thf('22', plain,
% 0.45/0.64      (((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_3)) | ~ (v1_relat_1 @ sk_C_3))),
% 0.45/0.64      inference('sup-', [status(thm)], ['5', '21'])).
% 0.45/0.64  thf('23', plain, ((v1_relat_1 @ sk_C_3)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('24', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_3))),
% 0.45/0.64      inference('demod', [status(thm)], ['22', '23'])).
% 0.45/0.64  thf('25', plain,
% 0.45/0.64      ((~ (r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_3)))
% 0.45/0.64         <= (~ ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_3))))),
% 0.45/0.64      inference('split', [status(esa)], ['0'])).
% 0.45/0.64  thf('26', plain, (((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_3)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['24', '25'])).
% 0.45/0.64  thf('27', plain,
% 0.45/0.64      (~ ((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_3))) | 
% 0.45/0.64       ~ ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_3)))),
% 0.45/0.64      inference('split', [status(esa)], ['0'])).
% 0.45/0.64  thf('28', plain, (~ ((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_3)))),
% 0.45/0.64      inference('sat_resolution*', [status(thm)], ['26', '27'])).
% 0.45/0.64  thf('29', plain, (~ (r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_3))),
% 0.45/0.64      inference('simpl_trail', [status(thm)], ['1', '28'])).
% 0.45/0.64  thf('30', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_3)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(d5_relat_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.45/0.64       ( ![C:$i]:
% 0.45/0.64         ( ( r2_hidden @ C @ B ) <=>
% 0.45/0.64           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.45/0.64  thf('31', plain,
% 0.45/0.64      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.45/0.64         (~ (r2_hidden @ (k4_tarski @ X25 @ X26) @ X27)
% 0.45/0.64          | (r2_hidden @ X26 @ X28)
% 0.45/0.64          | ((X28) != (k2_relat_1 @ X27)))),
% 0.45/0.64      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.45/0.64  thf('32', plain,
% 0.45/0.64      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.45/0.64         ((r2_hidden @ X26 @ (k2_relat_1 @ X27))
% 0.45/0.64          | ~ (r2_hidden @ (k4_tarski @ X25 @ X26) @ X27))),
% 0.45/0.64      inference('simplify', [status(thm)], ['31'])).
% 0.45/0.64  thf('33', plain, ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_C_3))),
% 0.45/0.64      inference('sup-', [status(thm)], ['30', '32'])).
% 0.45/0.64  thf('34', plain,
% 0.45/0.64      (![X32 : $i]:
% 0.45/0.64         (((k3_relat_1 @ X32)
% 0.45/0.64            = (k2_xboole_0 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32)))
% 0.45/0.64          | ~ (v1_relat_1 @ X32))),
% 0.45/0.64      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.45/0.64  thf('35', plain,
% 0.45/0.64      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.64         (((X5) != (X4))
% 0.45/0.64          | (r2_hidden @ X5 @ X6)
% 0.45/0.64          | ((X6) != (k2_tarski @ X7 @ X4)))),
% 0.45/0.64      inference('cnf', [status(esa)], [d2_tarski])).
% 0.45/0.64  thf('36', plain,
% 0.45/0.64      (![X4 : $i, X7 : $i]: (r2_hidden @ X4 @ (k2_tarski @ X7 @ X4))),
% 0.45/0.64      inference('simplify', [status(thm)], ['35'])).
% 0.45/0.64  thf('37', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.64         ((r2_hidden @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 0.45/0.64          | ~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.64  thf('38', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         (r2_hidden @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['36', '37'])).
% 0.45/0.64  thf('39', plain,
% 0.45/0.64      (![X13 : $i, X14 : $i]:
% 0.45/0.64         ((m1_subset_1 @ X13 @ X14) | ~ (r2_hidden @ X13 @ X14))),
% 0.45/0.64      inference('cnf', [status(esa)], [t1_subset])).
% 0.45/0.64  thf('40', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['38', '39'])).
% 0.45/0.64  thf('41', plain,
% 0.45/0.64      (![X15 : $i, X16 : $i]:
% 0.45/0.64         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.64  thf('42', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['40', '41'])).
% 0.45/0.64  thf('43', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((r1_tarski @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.45/0.64          | ~ (v1_relat_1 @ X0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['34', '42'])).
% 0.45/0.64  thf('44', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.64         (~ (r2_hidden @ X0 @ X1)
% 0.45/0.64          | (r2_hidden @ X0 @ X2)
% 0.45/0.64          | ~ (r1_tarski @ X1 @ X2))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.64  thf('45', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         (~ (v1_relat_1 @ X0)
% 0.45/0.64          | (r2_hidden @ X1 @ (k3_relat_1 @ X0))
% 0.45/0.64          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['43', '44'])).
% 0.45/0.64  thf('46', plain,
% 0.45/0.64      (((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_3)) | ~ (v1_relat_1 @ sk_C_3))),
% 0.45/0.64      inference('sup-', [status(thm)], ['33', '45'])).
% 0.45/0.64  thf('47', plain, ((v1_relat_1 @ sk_C_3)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('48', plain, ((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_3))),
% 0.45/0.64      inference('demod', [status(thm)], ['46', '47'])).
% 0.45/0.64  thf('49', plain, ($false), inference('demod', [status(thm)], ['29', '48'])).
% 0.45/0.64  
% 0.45/0.64  % SZS output end Refutation
% 0.45/0.64  
% 0.45/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
