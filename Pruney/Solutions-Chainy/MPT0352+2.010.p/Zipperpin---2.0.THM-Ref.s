%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oZ7FOZ8N0l

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:08 EST 2020

% Result     : Theorem 0.79s
% Output     : Refutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :  139 (1285 expanded)
%              Number of leaves         :   29 ( 422 expanded)
%              Depth                    :   22
%              Number of atoms          :  950 (9511 expanded)
%              Number of equality atoms :   60 ( 616 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(t31_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_tarski @ B @ C )
            <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_subset_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_tarski @ X27 @ ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('4',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ X35 )
      | ( r2_hidden @ X34 @ X35 )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('6',plain,(
    ! [X39: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('7',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('8',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X32 @ X31 )
      | ( r1_tarski @ X32 @ X30 )
      | ( X31
       != ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('9',plain,(
    ! [X30: $i,X32: $i] :
      ( ( r1_tarski @ X32 @ X30 )
      | ~ ( r2_hidden @ X32 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['7','9'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C_1 @ ( k2_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','12'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('14',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 )
      | ~ ( r1_tarski @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_C_1 @ sk_A ) @ X0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_tarski @ X27 @ ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('17',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 )
      | ~ ( r1_tarski @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('19',plain,(
    ! [X12: $i] :
      ( r1_tarski @ k1_xboole_0 @ X12 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('28',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('29',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('30',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','31'])).

thf('33',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','32'])).

thf('34',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('35',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('37',plain,
    ( sk_C_1
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('39',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['37','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('43',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_subset_1 @ X37 @ X38 )
        = ( k4_xboole_0 @ X37 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('44',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_tarski @ X27 @ ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ X35 )
      | ( r2_hidden @ X34 @ X35 )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('49',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X39: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('51',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X30: $i,X32: $i] :
      ( ( r1_tarski @ X32 @ X30 )
      | ~ ( r2_hidden @ X32 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('53',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','55'])).

thf('57',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 )
      | ~ ( r1_tarski @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ sk_A ) @ X0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','31'])).

thf('60',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('62',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('64',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('66',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_subset_1 @ X37 @ X38 )
        = ( k4_xboole_0 @ X37 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('69',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['66','69'])).

thf('71',plain,
    ( ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k5_xboole_0 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['1','45','70'])).

thf('72',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('73',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['37','40'])).

thf('74',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('75',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) )
    = ( k3_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('77',plain,
    ( sk_C_1
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('78',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) )
    = sk_C_1 ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['79'])).

thf(t34_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ) )).

thf('81',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ ( k4_xboole_0 @ X15 @ X14 ) @ ( k4_xboole_0 @ X15 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('82',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['66','69'])).

thf('84',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['41','44'])).

thf('85',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_A @ sk_B ) ) @ ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_B ) ) @ sk_C_1 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['78','85'])).

thf('87',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('88',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('89',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('91',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('92',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['86','92'])).

thf('94',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('95',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['72','95'])).

thf('97',plain,(
    ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['71','96'])).

thf('98',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['37','40'])).

thf('99',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['79'])).

thf('100',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ ( k4_xboole_0 @ X15 @ X14 ) @ ( k4_xboole_0 @ X15 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('101',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ ( k4_xboole_0 @ X0 @ sk_B ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['79'])).

thf('103',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['72','95','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['101','103'])).

thf('105',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['98','104'])).

thf('106',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('107',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    $false ),
    inference(demod,[status(thm)],['97','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oZ7FOZ8N0l
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:47:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.79/0.98  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.79/0.98  % Solved by: fo/fo7.sh
% 0.79/0.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.79/0.98  % done 1526 iterations in 0.530s
% 0.79/0.98  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.79/0.98  % SZS output start Refutation
% 0.79/0.98  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.79/0.98  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.79/0.98  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.79/0.98  thf(sk_A_type, type, sk_A: $i).
% 0.79/0.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.79/0.98  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.79/0.98  thf(sk_B_type, type, sk_B: $i).
% 0.79/0.98  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.79/0.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.79/0.98  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.79/0.98  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.79/0.98  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.79/0.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.79/0.98  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.79/0.98  thf(t31_subset_1, conjecture,
% 0.79/0.98    (![A:$i,B:$i]:
% 0.79/0.98     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.79/0.98       ( ![C:$i]:
% 0.79/0.98         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.79/0.98           ( ( r1_tarski @ B @ C ) <=>
% 0.79/0.98             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.79/0.98  thf(zf_stmt_0, negated_conjecture,
% 0.79/0.98    (~( ![A:$i,B:$i]:
% 0.79/0.98        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.79/0.98          ( ![C:$i]:
% 0.79/0.98            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.79/0.98              ( ( r1_tarski @ B @ C ) <=>
% 0.79/0.98                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 0.79/0.98    inference('cnf.neg', [status(esa)], [t31_subset_1])).
% 0.79/0.98  thf('0', plain,
% 0.79/0.98      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.79/0.98           (k3_subset_1 @ sk_A @ sk_B))
% 0.79/0.98        | ~ (r1_tarski @ sk_B @ sk_C_1))),
% 0.79/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.98  thf('1', plain,
% 0.79/0.98      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.79/0.98           (k3_subset_1 @ sk_A @ sk_B)))
% 0.79/0.98         <= (~
% 0.79/0.98             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.79/0.98               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.79/0.98      inference('split', [status(esa)], ['0'])).
% 0.79/0.98  thf(t7_xboole_1, axiom,
% 0.79/0.98    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.79/0.98  thf('2', plain,
% 0.79/0.98      (![X27 : $i, X28 : $i]: (r1_tarski @ X27 @ (k2_xboole_0 @ X27 @ X28))),
% 0.79/0.98      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.79/0.98  thf('3', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.79/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.98  thf(d2_subset_1, axiom,
% 0.79/0.98    (![A:$i,B:$i]:
% 0.79/0.98     ( ( ( v1_xboole_0 @ A ) =>
% 0.79/0.98         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.79/0.98       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.79/0.98         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.79/0.98  thf('4', plain,
% 0.79/0.98      (![X34 : $i, X35 : $i]:
% 0.79/0.98         (~ (m1_subset_1 @ X34 @ X35)
% 0.79/0.98          | (r2_hidden @ X34 @ X35)
% 0.79/0.98          | (v1_xboole_0 @ X35))),
% 0.79/0.98      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.79/0.98  thf('5', plain,
% 0.79/0.98      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.79/0.98        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.79/0.98      inference('sup-', [status(thm)], ['3', '4'])).
% 0.79/0.98  thf(fc1_subset_1, axiom,
% 0.79/0.98    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.79/0.98  thf('6', plain, (![X39 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X39))),
% 0.79/0.98      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.79/0.98  thf('7', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.79/0.98      inference('clc', [status(thm)], ['5', '6'])).
% 0.79/0.98  thf(d1_zfmisc_1, axiom,
% 0.79/0.98    (![A:$i,B:$i]:
% 0.79/0.98     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.79/0.98       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.79/0.98  thf('8', plain,
% 0.79/0.98      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.79/0.98         (~ (r2_hidden @ X32 @ X31)
% 0.79/0.98          | (r1_tarski @ X32 @ X30)
% 0.79/0.98          | ((X31) != (k1_zfmisc_1 @ X30)))),
% 0.79/0.98      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.79/0.98  thf('9', plain,
% 0.79/0.98      (![X30 : $i, X32 : $i]:
% 0.79/0.98         ((r1_tarski @ X32 @ X30) | ~ (r2_hidden @ X32 @ (k1_zfmisc_1 @ X30)))),
% 0.79/0.98      inference('simplify', [status(thm)], ['8'])).
% 0.79/0.98  thf('10', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 0.79/0.98      inference('sup-', [status(thm)], ['7', '9'])).
% 0.79/0.98  thf(t1_xboole_1, axiom,
% 0.79/0.98    (![A:$i,B:$i,C:$i]:
% 0.79/0.98     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.79/0.98       ( r1_tarski @ A @ C ) ))).
% 0.79/0.98  thf('11', plain,
% 0.79/0.98      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.79/0.98         (~ (r1_tarski @ X9 @ X10)
% 0.79/0.98          | ~ (r1_tarski @ X10 @ X11)
% 0.79/0.98          | (r1_tarski @ X9 @ X11))),
% 0.79/0.98      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.79/0.98  thf('12', plain,
% 0.79/0.98      (![X0 : $i]: ((r1_tarski @ sk_C_1 @ X0) | ~ (r1_tarski @ sk_A @ X0))),
% 0.79/0.98      inference('sup-', [status(thm)], ['10', '11'])).
% 0.79/0.98  thf('13', plain,
% 0.79/0.98      (![X0 : $i]: (r1_tarski @ sk_C_1 @ (k2_xboole_0 @ sk_A @ X0))),
% 0.79/0.98      inference('sup-', [status(thm)], ['2', '12'])).
% 0.79/0.98  thf(t43_xboole_1, axiom,
% 0.79/0.98    (![A:$i,B:$i,C:$i]:
% 0.79/0.98     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.79/0.98       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.79/0.98  thf('14', plain,
% 0.79/0.98      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.79/0.98         ((r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X21)
% 0.79/0.98          | ~ (r1_tarski @ X19 @ (k2_xboole_0 @ X20 @ X21)))),
% 0.79/0.98      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.79/0.98  thf('15', plain,
% 0.79/0.98      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_C_1 @ sk_A) @ X0)),
% 0.79/0.98      inference('sup-', [status(thm)], ['13', '14'])).
% 0.79/0.98  thf('16', plain,
% 0.79/0.98      (![X27 : $i, X28 : $i]: (r1_tarski @ X27 @ (k2_xboole_0 @ X27 @ X28))),
% 0.79/0.98      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.79/0.98  thf('17', plain,
% 0.79/0.98      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.79/0.98         ((r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X21)
% 0.79/0.98          | ~ (r1_tarski @ X19 @ (k2_xboole_0 @ X20 @ X21)))),
% 0.79/0.98      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.79/0.98  thf('18', plain,
% 0.79/0.98      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 0.79/0.98      inference('sup-', [status(thm)], ['16', '17'])).
% 0.79/0.98  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.79/0.98  thf('19', plain, (![X12 : $i]: (r1_tarski @ k1_xboole_0 @ X12)),
% 0.79/0.98      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.79/0.98  thf(d10_xboole_0, axiom,
% 0.79/0.98    (![A:$i,B:$i]:
% 0.79/0.98     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.79/0.98  thf('20', plain,
% 0.79/0.98      (![X4 : $i, X6 : $i]:
% 0.79/0.98         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.79/0.98      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.79/0.98  thf('21', plain,
% 0.79/0.98      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.79/0.98      inference('sup-', [status(thm)], ['19', '20'])).
% 0.79/0.98  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.79/0.98      inference('sup-', [status(thm)], ['18', '21'])).
% 0.79/0.98  thf('23', plain,
% 0.79/0.98      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.79/0.98      inference('sup-', [status(thm)], ['19', '20'])).
% 0.79/0.98  thf('24', plain,
% 0.79/0.98      (![X0 : $i, X1 : $i]:
% 0.79/0.98         (~ (r1_tarski @ X1 @ (k4_xboole_0 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 0.79/0.98      inference('sup-', [status(thm)], ['22', '23'])).
% 0.79/0.98  thf('25', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.79/0.98      inference('sup-', [status(thm)], ['18', '21'])).
% 0.79/0.98  thf(t48_xboole_1, axiom,
% 0.79/0.98    (![A:$i,B:$i]:
% 0.79/0.98     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.79/0.98  thf('26', plain,
% 0.79/0.98      (![X25 : $i, X26 : $i]:
% 0.79/0.98         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 0.79/0.98           = (k3_xboole_0 @ X25 @ X26))),
% 0.79/0.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.79/0.98  thf('27', plain,
% 0.79/0.98      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.79/0.98      inference('sup+', [status(thm)], ['25', '26'])).
% 0.79/0.98  thf(t3_boole, axiom,
% 0.79/0.98    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.79/0.98  thf('28', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.79/0.98      inference('cnf', [status(esa)], [t3_boole])).
% 0.79/0.98  thf('29', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.79/0.98      inference('demod', [status(thm)], ['27', '28'])).
% 0.79/0.98  thf(t100_xboole_1, axiom,
% 0.79/0.98    (![A:$i,B:$i]:
% 0.79/0.98     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.79/0.98  thf('30', plain,
% 0.79/0.98      (![X7 : $i, X8 : $i]:
% 0.79/0.98         ((k4_xboole_0 @ X7 @ X8)
% 0.79/0.98           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.79/0.98      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.79/0.98  thf('31', plain,
% 0.79/0.98      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.79/0.98      inference('sup+', [status(thm)], ['29', '30'])).
% 0.79/0.98  thf('32', plain,
% 0.79/0.98      (![X0 : $i, X1 : $i]:
% 0.79/0.98         (~ (r1_tarski @ X1 @ (k5_xboole_0 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 0.79/0.98      inference('demod', [status(thm)], ['24', '31'])).
% 0.79/0.98  thf('33', plain, (((k4_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 0.79/0.98      inference('sup-', [status(thm)], ['15', '32'])).
% 0.79/0.98  thf('34', plain,
% 0.79/0.98      (![X25 : $i, X26 : $i]:
% 0.79/0.98         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 0.79/0.98           = (k3_xboole_0 @ X25 @ X26))),
% 0.79/0.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.79/0.98  thf('35', plain,
% 0.79/0.98      (((k4_xboole_0 @ sk_C_1 @ k1_xboole_0) = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 0.79/0.98      inference('sup+', [status(thm)], ['33', '34'])).
% 0.79/0.98  thf('36', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.79/0.98      inference('cnf', [status(esa)], [t3_boole])).
% 0.79/0.98  thf('37', plain, (((sk_C_1) = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 0.79/0.98      inference('demod', [status(thm)], ['35', '36'])).
% 0.79/0.98  thf(commutativity_k3_xboole_0, axiom,
% 0.79/0.98    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.79/0.98  thf('38', plain,
% 0.79/0.98      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.79/0.98      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.79/0.98  thf('39', plain,
% 0.79/0.98      (![X7 : $i, X8 : $i]:
% 0.79/0.98         ((k4_xboole_0 @ X7 @ X8)
% 0.79/0.98           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.79/0.98      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.79/0.98  thf('40', plain,
% 0.79/0.98      (![X0 : $i, X1 : $i]:
% 0.79/0.98         ((k4_xboole_0 @ X0 @ X1)
% 0.79/0.98           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.79/0.98      inference('sup+', [status(thm)], ['38', '39'])).
% 0.79/0.98  thf('41', plain,
% 0.79/0.98      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 0.79/0.98      inference('sup+', [status(thm)], ['37', '40'])).
% 0.79/0.98  thf('42', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.79/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.98  thf(d5_subset_1, axiom,
% 0.79/0.98    (![A:$i,B:$i]:
% 0.79/0.98     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.79/0.98       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.79/0.98  thf('43', plain,
% 0.79/0.98      (![X37 : $i, X38 : $i]:
% 0.79/0.98         (((k3_subset_1 @ X37 @ X38) = (k4_xboole_0 @ X37 @ X38))
% 0.79/0.98          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X37)))),
% 0.79/0.98      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.79/0.98  thf('44', plain,
% 0.79/0.98      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.79/0.98      inference('sup-', [status(thm)], ['42', '43'])).
% 0.79/0.98  thf('45', plain,
% 0.79/0.98      (((k3_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 0.79/0.98      inference('sup+', [status(thm)], ['41', '44'])).
% 0.79/0.98  thf('46', plain,
% 0.79/0.98      (![X27 : $i, X28 : $i]: (r1_tarski @ X27 @ (k2_xboole_0 @ X27 @ X28))),
% 0.79/0.98      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.79/0.98  thf('47', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.79/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.98  thf('48', plain,
% 0.79/0.98      (![X34 : $i, X35 : $i]:
% 0.79/0.98         (~ (m1_subset_1 @ X34 @ X35)
% 0.79/0.98          | (r2_hidden @ X34 @ X35)
% 0.79/0.98          | (v1_xboole_0 @ X35))),
% 0.79/0.98      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.79/0.98  thf('49', plain,
% 0.79/0.98      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.79/0.98        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.79/0.98      inference('sup-', [status(thm)], ['47', '48'])).
% 0.79/0.98  thf('50', plain, (![X39 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X39))),
% 0.79/0.98      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.79/0.98  thf('51', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.79/0.98      inference('clc', [status(thm)], ['49', '50'])).
% 0.79/0.98  thf('52', plain,
% 0.79/0.98      (![X30 : $i, X32 : $i]:
% 0.79/0.98         ((r1_tarski @ X32 @ X30) | ~ (r2_hidden @ X32 @ (k1_zfmisc_1 @ X30)))),
% 0.79/0.98      inference('simplify', [status(thm)], ['8'])).
% 0.79/0.98  thf('53', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.79/0.98      inference('sup-', [status(thm)], ['51', '52'])).
% 0.79/0.98  thf('54', plain,
% 0.79/0.98      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.79/0.98         (~ (r1_tarski @ X9 @ X10)
% 0.79/0.98          | ~ (r1_tarski @ X10 @ X11)
% 0.79/0.98          | (r1_tarski @ X9 @ X11))),
% 0.79/0.98      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.79/0.98  thf('55', plain,
% 0.79/0.98      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ~ (r1_tarski @ sk_A @ X0))),
% 0.79/0.98      inference('sup-', [status(thm)], ['53', '54'])).
% 0.79/0.98  thf('56', plain,
% 0.79/0.98      (![X0 : $i]: (r1_tarski @ sk_B @ (k2_xboole_0 @ sk_A @ X0))),
% 0.79/0.98      inference('sup-', [status(thm)], ['46', '55'])).
% 0.79/0.98  thf('57', plain,
% 0.79/0.98      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.79/0.98         ((r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X21)
% 0.79/0.98          | ~ (r1_tarski @ X19 @ (k2_xboole_0 @ X20 @ X21)))),
% 0.79/0.98      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.79/0.98  thf('58', plain,
% 0.79/0.98      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_B @ sk_A) @ X0)),
% 0.79/0.98      inference('sup-', [status(thm)], ['56', '57'])).
% 0.79/0.98  thf('59', plain,
% 0.79/0.98      (![X0 : $i, X1 : $i]:
% 0.79/0.98         (~ (r1_tarski @ X1 @ (k5_xboole_0 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 0.79/0.98      inference('demod', [status(thm)], ['24', '31'])).
% 0.79/0.98  thf('60', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.79/0.98      inference('sup-', [status(thm)], ['58', '59'])).
% 0.79/0.98  thf('61', plain,
% 0.79/0.98      (![X25 : $i, X26 : $i]:
% 0.79/0.98         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 0.79/0.98           = (k3_xboole_0 @ X25 @ X26))),
% 0.79/0.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.79/0.98  thf('62', plain,
% 0.79/0.98      (((k4_xboole_0 @ sk_B @ k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.79/0.98      inference('sup+', [status(thm)], ['60', '61'])).
% 0.79/0.98  thf('63', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.79/0.98      inference('cnf', [status(esa)], [t3_boole])).
% 0.79/0.98  thf('64', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.79/0.98      inference('demod', [status(thm)], ['62', '63'])).
% 0.79/0.98  thf('65', plain,
% 0.79/0.98      (![X0 : $i, X1 : $i]:
% 0.79/0.98         ((k4_xboole_0 @ X0 @ X1)
% 0.79/0.98           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.79/0.98      inference('sup+', [status(thm)], ['38', '39'])).
% 0.79/0.98  thf('66', plain,
% 0.79/0.98      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.79/0.98      inference('sup+', [status(thm)], ['64', '65'])).
% 0.79/0.98  thf('67', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.79/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.98  thf('68', plain,
% 0.79/0.98      (![X37 : $i, X38 : $i]:
% 0.79/0.98         (((k3_subset_1 @ X37 @ X38) = (k4_xboole_0 @ X37 @ X38))
% 0.79/0.98          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X37)))),
% 0.79/0.98      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.79/0.98  thf('69', plain,
% 0.79/0.98      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.79/0.98      inference('sup-', [status(thm)], ['67', '68'])).
% 0.79/0.98  thf('70', plain,
% 0.79/0.98      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.79/0.98      inference('sup+', [status(thm)], ['66', '69'])).
% 0.79/0.98  thf('71', plain,
% 0.79/0.98      ((~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.79/0.98           (k5_xboole_0 @ sk_A @ sk_B)))
% 0.79/0.98         <= (~
% 0.79/0.98             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.79/0.98               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.79/0.98      inference('demod', [status(thm)], ['1', '45', '70'])).
% 0.79/0.98  thf('72', plain,
% 0.79/0.98      (~
% 0.79/0.98       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.79/0.98         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.79/0.98       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 0.79/0.98      inference('split', [status(esa)], ['0'])).
% 0.79/0.98  thf('73', plain,
% 0.79/0.98      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 0.79/0.98      inference('sup+', [status(thm)], ['37', '40'])).
% 0.79/0.98  thf('74', plain,
% 0.79/0.98      (![X25 : $i, X26 : $i]:
% 0.79/0.98         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 0.79/0.98           = (k3_xboole_0 @ X25 @ X26))),
% 0.79/0.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.79/0.98  thf('75', plain,
% 0.79/0.98      (((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C_1))
% 0.79/0.98         = (k3_xboole_0 @ sk_A @ sk_C_1))),
% 0.79/0.98      inference('sup+', [status(thm)], ['73', '74'])).
% 0.79/0.98  thf('76', plain,
% 0.79/0.98      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.79/0.98      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.79/0.98  thf('77', plain, (((sk_C_1) = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 0.79/0.98      inference('demod', [status(thm)], ['35', '36'])).
% 0.79/0.98  thf('78', plain,
% 0.79/0.98      (((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C_1)) = (sk_C_1))),
% 0.79/0.98      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.79/0.98  thf('79', plain,
% 0.79/0.98      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.79/0.98         (k3_subset_1 @ sk_A @ sk_B))
% 0.79/0.98        | (r1_tarski @ sk_B @ sk_C_1))),
% 0.79/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.98  thf('80', plain,
% 0.79/0.98      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.79/0.98         (k3_subset_1 @ sk_A @ sk_B)))
% 0.79/0.98         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.79/0.98               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.79/0.98      inference('split', [status(esa)], ['79'])).
% 0.79/0.98  thf(t34_xboole_1, axiom,
% 0.79/0.98    (![A:$i,B:$i,C:$i]:
% 0.79/0.98     ( ( r1_tarski @ A @ B ) =>
% 0.79/0.98       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 0.79/0.98  thf('81', plain,
% 0.79/0.98      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.79/0.98         (~ (r1_tarski @ X13 @ X14)
% 0.79/0.98          | (r1_tarski @ (k4_xboole_0 @ X15 @ X14) @ (k4_xboole_0 @ X15 @ X13)))),
% 0.79/0.98      inference('cnf', [status(esa)], [t34_xboole_1])).
% 0.79/0.98  thf('82', plain,
% 0.79/0.98      ((![X0 : $i]:
% 0.79/0.98          (r1_tarski @ (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_B)) @ 
% 0.79/0.98           (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))))
% 0.79/0.98         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.79/0.98               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.79/0.98      inference('sup-', [status(thm)], ['80', '81'])).
% 0.79/0.98  thf('83', plain,
% 0.79/0.98      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.79/0.98      inference('sup+', [status(thm)], ['66', '69'])).
% 0.79/0.98  thf('84', plain,
% 0.79/0.98      (((k3_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 0.79/0.98      inference('sup+', [status(thm)], ['41', '44'])).
% 0.79/0.98  thf('85', plain,
% 0.79/0.98      ((![X0 : $i]:
% 0.79/0.98          (r1_tarski @ (k4_xboole_0 @ X0 @ (k5_xboole_0 @ sk_A @ sk_B)) @ 
% 0.79/0.98           (k4_xboole_0 @ X0 @ (k5_xboole_0 @ sk_A @ sk_C_1))))
% 0.79/0.98         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.79/0.98               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.79/0.98      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.79/0.98  thf('86', plain,
% 0.79/0.98      (((r1_tarski @ (k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_B)) @ 
% 0.79/0.98         sk_C_1))
% 0.79/0.98         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.79/0.98               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.79/0.98      inference('sup+', [status(thm)], ['78', '85'])).
% 0.79/0.98  thf('87', plain,
% 0.79/0.98      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.79/0.98      inference('sup+', [status(thm)], ['64', '65'])).
% 0.79/0.98  thf('88', plain,
% 0.79/0.98      (![X25 : $i, X26 : $i]:
% 0.79/0.98         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 0.79/0.98           = (k3_xboole_0 @ X25 @ X26))),
% 0.79/0.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.79/0.98  thf('89', plain,
% 0.79/0.98      (((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_B))
% 0.79/0.98         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.79/0.98      inference('sup+', [status(thm)], ['87', '88'])).
% 0.79/0.98  thf('90', plain,
% 0.79/0.98      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.79/0.98      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.79/0.98  thf('91', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.79/0.98      inference('demod', [status(thm)], ['62', '63'])).
% 0.79/0.98  thf('92', plain,
% 0.79/0.98      (((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.79/0.98      inference('demod', [status(thm)], ['89', '90', '91'])).
% 0.79/0.98  thf('93', plain,
% 0.79/0.98      (((r1_tarski @ sk_B @ sk_C_1))
% 0.79/0.98         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.79/0.98               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.79/0.98      inference('demod', [status(thm)], ['86', '92'])).
% 0.79/0.98  thf('94', plain,
% 0.79/0.98      ((~ (r1_tarski @ sk_B @ sk_C_1)) <= (~ ((r1_tarski @ sk_B @ sk_C_1)))),
% 0.79/0.98      inference('split', [status(esa)], ['0'])).
% 0.79/0.98  thf('95', plain,
% 0.79/0.98      (((r1_tarski @ sk_B @ sk_C_1)) | 
% 0.79/0.98       ~
% 0.79/0.98       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.79/0.98         (k3_subset_1 @ sk_A @ sk_B)))),
% 0.79/0.98      inference('sup-', [status(thm)], ['93', '94'])).
% 0.79/0.98  thf('96', plain,
% 0.79/0.98      (~
% 0.79/0.98       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.79/0.98         (k3_subset_1 @ sk_A @ sk_B)))),
% 0.79/0.98      inference('sat_resolution*', [status(thm)], ['72', '95'])).
% 0.79/0.98  thf('97', plain,
% 0.79/0.98      (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.79/0.98          (k5_xboole_0 @ sk_A @ sk_B))),
% 0.79/0.98      inference('simpl_trail', [status(thm)], ['71', '96'])).
% 0.79/0.98  thf('98', plain,
% 0.79/0.98      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 0.79/0.98      inference('sup+', [status(thm)], ['37', '40'])).
% 0.79/0.98  thf('99', plain,
% 0.79/0.98      (((r1_tarski @ sk_B @ sk_C_1)) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.79/0.98      inference('split', [status(esa)], ['79'])).
% 0.79/0.98  thf('100', plain,
% 0.79/0.98      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.79/0.98         (~ (r1_tarski @ X13 @ X14)
% 0.79/0.98          | (r1_tarski @ (k4_xboole_0 @ X15 @ X14) @ (k4_xboole_0 @ X15 @ X13)))),
% 0.79/0.98      inference('cnf', [status(esa)], [t34_xboole_1])).
% 0.79/0.98  thf('101', plain,
% 0.79/0.98      ((![X0 : $i]:
% 0.79/0.98          (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C_1) @ (k4_xboole_0 @ X0 @ sk_B)))
% 0.79/0.98         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.79/0.98      inference('sup-', [status(thm)], ['99', '100'])).
% 0.79/0.98  thf('102', plain,
% 0.79/0.98      (((r1_tarski @ sk_B @ sk_C_1)) | 
% 0.79/0.99       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.79/0.99         (k3_subset_1 @ sk_A @ sk_B)))),
% 0.79/0.99      inference('split', [status(esa)], ['79'])).
% 0.79/0.99  thf('103', plain, (((r1_tarski @ sk_B @ sk_C_1))),
% 0.79/0.99      inference('sat_resolution*', [status(thm)], ['72', '95', '102'])).
% 0.79/0.99  thf('104', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C_1) @ (k4_xboole_0 @ X0 @ sk_B))),
% 0.79/0.99      inference('simpl_trail', [status(thm)], ['101', '103'])).
% 0.79/0.99  thf('105', plain,
% 0.79/0.99      ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.79/0.99      inference('sup+', [status(thm)], ['98', '104'])).
% 0.79/0.99  thf('106', plain,
% 0.79/0.99      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.79/0.99      inference('sup+', [status(thm)], ['64', '65'])).
% 0.79/0.99  thf('107', plain,
% 0.79/0.99      ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ (k5_xboole_0 @ sk_A @ sk_B))),
% 0.79/0.99      inference('demod', [status(thm)], ['105', '106'])).
% 0.79/0.99  thf('108', plain, ($false), inference('demod', [status(thm)], ['97', '107'])).
% 0.79/0.99  
% 0.79/0.99  % SZS output end Refutation
% 0.79/0.99  
% 0.79/0.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
