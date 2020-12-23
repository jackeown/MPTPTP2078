%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LKnvKl0l0Y

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:46 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 193 expanded)
%              Number of leaves         :   34 (  72 expanded)
%              Depth                    :   12
%              Number of atoms          :  604 (1383 expanded)
%              Number of equality atoms :   60 ( 125 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','13'])).

thf(t25_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
          = ( k2_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_subset_1])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ X29 )
      | ( r2_hidden @ X28 @ X29 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('18',plain,(
    ! [X36: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('19',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['17','18'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('20',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X24 @ X23 )
      | ( r1_tarski @ X24 @ X22 )
      | ( X23
       != ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('21',plain,(
    ! [X22: $i,X24: $i] :
      ( ( r1_tarski @ X24 @ X22 )
      | ~ ( r2_hidden @ X24 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('24',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('26',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ ( k3_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('29',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X15 @ X14 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X26 @ X27 ) )
      = ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X26 @ X27 ) )
      = ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','33'])).

thf('35',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['14','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('37',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['22','23'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('39',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','36','39'])).

thf('41',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('42',plain,(
    ! [X31: $i] :
      ( ( k2_subset_1 @ X31 )
      = X31 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('43',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('46',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k3_subset_1 @ X32 @ X33 )
        = ( k4_xboole_0 @ X32 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('47',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['43','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('51',plain,(
    ! [X34: $i,X35: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X34 @ X35 ) @ ( k1_zfmisc_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('52',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('54',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('56',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) )
      | ( ( k4_subset_1 @ X38 @ X37 @ X39 )
        = ( k2_xboole_0 @ X37 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ( k2_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['49','58'])).

thf('60',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['40','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LKnvKl0l0Y
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:57:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.63  % Solved by: fo/fo7.sh
% 0.35/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.63  % done 466 iterations in 0.166s
% 0.35/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.63  % SZS output start Refutation
% 0.35/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.35/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.63  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.35/0.63  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.35/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.63  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.35/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.35/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.63  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.35/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.35/0.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.35/0.63  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.35/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.63  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.35/0.63  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.35/0.63  thf('0', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.35/0.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.35/0.63  thf(t28_xboole_1, axiom,
% 0.35/0.63    (![A:$i,B:$i]:
% 0.35/0.63     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.35/0.63  thf('1', plain,
% 0.35/0.63      (![X4 : $i, X5 : $i]:
% 0.35/0.63         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.35/0.63      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.35/0.63  thf('2', plain,
% 0.35/0.63      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.35/0.63      inference('sup-', [status(thm)], ['0', '1'])).
% 0.35/0.63  thf(commutativity_k3_xboole_0, axiom,
% 0.35/0.63    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.35/0.63  thf('3', plain,
% 0.35/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.35/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.35/0.63  thf(t100_xboole_1, axiom,
% 0.35/0.63    (![A:$i,B:$i]:
% 0.35/0.63     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.35/0.63  thf('4', plain,
% 0.35/0.63      (![X2 : $i, X3 : $i]:
% 0.35/0.63         ((k4_xboole_0 @ X2 @ X3)
% 0.35/0.63           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.35/0.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.35/0.63  thf('5', plain,
% 0.35/0.63      (![X0 : $i, X1 : $i]:
% 0.35/0.63         ((k4_xboole_0 @ X0 @ X1)
% 0.35/0.63           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.35/0.63      inference('sup+', [status(thm)], ['3', '4'])).
% 0.35/0.63  thf('6', plain,
% 0.35/0.63      (![X0 : $i]:
% 0.35/0.63         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.35/0.63      inference('sup+', [status(thm)], ['2', '5'])).
% 0.35/0.63  thf(t5_boole, axiom,
% 0.35/0.63    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.35/0.63  thf('7', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.35/0.63      inference('cnf', [status(esa)], [t5_boole])).
% 0.35/0.63  thf('8', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.35/0.63      inference('demod', [status(thm)], ['6', '7'])).
% 0.35/0.63  thf(t48_xboole_1, axiom,
% 0.35/0.63    (![A:$i,B:$i]:
% 0.35/0.63     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.35/0.63  thf('9', plain,
% 0.35/0.63      (![X7 : $i, X8 : $i]:
% 0.35/0.63         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.35/0.63           = (k3_xboole_0 @ X7 @ X8))),
% 0.35/0.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.35/0.63  thf('10', plain,
% 0.35/0.63      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.35/0.63      inference('sup+', [status(thm)], ['8', '9'])).
% 0.35/0.63  thf('11', plain,
% 0.35/0.63      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.35/0.63      inference('sup-', [status(thm)], ['0', '1'])).
% 0.35/0.63  thf('12', plain,
% 0.35/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.35/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.35/0.63  thf('13', plain,
% 0.35/0.63      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.63      inference('sup+', [status(thm)], ['11', '12'])).
% 0.35/0.63  thf('14', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.35/0.63      inference('demod', [status(thm)], ['10', '13'])).
% 0.35/0.63  thf(t25_subset_1, conjecture,
% 0.35/0.63    (![A:$i,B:$i]:
% 0.35/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.63       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.35/0.63         ( k2_subset_1 @ A ) ) ))).
% 0.35/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.63    (~( ![A:$i,B:$i]:
% 0.35/0.63        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.63          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.35/0.63            ( k2_subset_1 @ A ) ) ) )),
% 0.35/0.63    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 0.35/0.63  thf('15', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.35/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.63  thf(d2_subset_1, axiom,
% 0.35/0.63    (![A:$i,B:$i]:
% 0.35/0.63     ( ( ( v1_xboole_0 @ A ) =>
% 0.35/0.63         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.35/0.63       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.35/0.63         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.35/0.63  thf('16', plain,
% 0.35/0.63      (![X28 : $i, X29 : $i]:
% 0.35/0.63         (~ (m1_subset_1 @ X28 @ X29)
% 0.35/0.63          | (r2_hidden @ X28 @ X29)
% 0.35/0.63          | (v1_xboole_0 @ X29))),
% 0.35/0.63      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.35/0.63  thf('17', plain,
% 0.35/0.63      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.35/0.63        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.35/0.63      inference('sup-', [status(thm)], ['15', '16'])).
% 0.35/0.63  thf(fc1_subset_1, axiom,
% 0.35/0.63    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.35/0.63  thf('18', plain, (![X36 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X36))),
% 0.35/0.63      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.35/0.63  thf('19', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.35/0.63      inference('clc', [status(thm)], ['17', '18'])).
% 0.35/0.63  thf(d1_zfmisc_1, axiom,
% 0.35/0.63    (![A:$i,B:$i]:
% 0.35/0.63     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.35/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.35/0.63  thf('20', plain,
% 0.35/0.63      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.35/0.63         (~ (r2_hidden @ X24 @ X23)
% 0.35/0.63          | (r1_tarski @ X24 @ X22)
% 0.35/0.63          | ((X23) != (k1_zfmisc_1 @ X22)))),
% 0.35/0.63      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.35/0.63  thf('21', plain,
% 0.35/0.63      (![X22 : $i, X24 : $i]:
% 0.35/0.63         ((r1_tarski @ X24 @ X22) | ~ (r2_hidden @ X24 @ (k1_zfmisc_1 @ X22)))),
% 0.35/0.63      inference('simplify', [status(thm)], ['20'])).
% 0.35/0.63  thf('22', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.35/0.63      inference('sup-', [status(thm)], ['19', '21'])).
% 0.35/0.63  thf('23', plain,
% 0.35/0.63      (![X4 : $i, X5 : $i]:
% 0.35/0.63         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.35/0.63      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.35/0.63  thf('24', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.35/0.63      inference('sup-', [status(thm)], ['22', '23'])).
% 0.35/0.63  thf('25', plain,
% 0.35/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.35/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.35/0.63  thf(t52_xboole_1, axiom,
% 0.35/0.63    (![A:$i,B:$i,C:$i]:
% 0.35/0.63     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.35/0.63       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.35/0.63  thf('26', plain,
% 0.35/0.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.35/0.63         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X11))
% 0.35/0.63           = (k2_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ (k3_xboole_0 @ X9 @ X11)))),
% 0.35/0.63      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.35/0.63  thf('27', plain,
% 0.35/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.63         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))
% 0.35/0.63           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.35/0.63      inference('sup+', [status(thm)], ['25', '26'])).
% 0.35/0.63  thf('28', plain,
% 0.35/0.63      (![X0 : $i]:
% 0.35/0.63         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B))
% 0.35/0.63           = (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ sk_B))),
% 0.35/0.63      inference('sup+', [status(thm)], ['24', '27'])).
% 0.35/0.63  thf(commutativity_k2_tarski, axiom,
% 0.35/0.63    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.35/0.63  thf('29', plain,
% 0.35/0.63      (![X14 : $i, X15 : $i]:
% 0.35/0.63         ((k2_tarski @ X15 @ X14) = (k2_tarski @ X14 @ X15))),
% 0.35/0.63      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.35/0.63  thf(l51_zfmisc_1, axiom,
% 0.35/0.63    (![A:$i,B:$i]:
% 0.35/0.63     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.35/0.63  thf('30', plain,
% 0.35/0.63      (![X26 : $i, X27 : $i]:
% 0.35/0.63         ((k3_tarski @ (k2_tarski @ X26 @ X27)) = (k2_xboole_0 @ X26 @ X27))),
% 0.35/0.63      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.35/0.63  thf('31', plain,
% 0.35/0.63      (![X0 : $i, X1 : $i]:
% 0.35/0.63         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.35/0.63      inference('sup+', [status(thm)], ['29', '30'])).
% 0.35/0.63  thf('32', plain,
% 0.35/0.63      (![X26 : $i, X27 : $i]:
% 0.35/0.63         ((k3_tarski @ (k2_tarski @ X26 @ X27)) = (k2_xboole_0 @ X26 @ X27))),
% 0.35/0.63      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.35/0.63  thf('33', plain,
% 0.35/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.35/0.63      inference('sup+', [status(thm)], ['31', '32'])).
% 0.35/0.63  thf('34', plain,
% 0.35/0.63      (![X0 : $i]:
% 0.35/0.63         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B))
% 0.35/0.63           = (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ X0)))),
% 0.35/0.63      inference('demod', [status(thm)], ['28', '33'])).
% 0.35/0.63  thf('35', plain,
% 0.35/0.63      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.35/0.63         = (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.35/0.63      inference('sup+', [status(thm)], ['14', '34'])).
% 0.35/0.63  thf('36', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.35/0.63      inference('demod', [status(thm)], ['6', '7'])).
% 0.35/0.63  thf('37', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.35/0.63      inference('sup-', [status(thm)], ['22', '23'])).
% 0.35/0.63  thf('38', plain,
% 0.35/0.63      (![X0 : $i, X1 : $i]:
% 0.35/0.63         ((k4_xboole_0 @ X0 @ X1)
% 0.35/0.63           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.35/0.63      inference('sup+', [status(thm)], ['3', '4'])).
% 0.35/0.63  thf('39', plain,
% 0.35/0.63      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.35/0.63      inference('sup+', [status(thm)], ['37', '38'])).
% 0.35/0.63  thf('40', plain,
% 0.35/0.63      (((sk_A) = (k2_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 0.35/0.63      inference('demod', [status(thm)], ['35', '36', '39'])).
% 0.35/0.63  thf('41', plain,
% 0.35/0.63      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.35/0.63         != (k2_subset_1 @ sk_A))),
% 0.35/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.63  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.35/0.63  thf('42', plain, (![X31 : $i]: ((k2_subset_1 @ X31) = (X31))),
% 0.35/0.63      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.35/0.63  thf('43', plain,
% 0.35/0.63      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.35/0.63      inference('demod', [status(thm)], ['41', '42'])).
% 0.35/0.63  thf('44', plain,
% 0.35/0.63      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.35/0.63      inference('sup+', [status(thm)], ['37', '38'])).
% 0.35/0.63  thf('45', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.35/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.63  thf(d5_subset_1, axiom,
% 0.35/0.63    (![A:$i,B:$i]:
% 0.35/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.63       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.35/0.63  thf('46', plain,
% 0.35/0.63      (![X32 : $i, X33 : $i]:
% 0.35/0.63         (((k3_subset_1 @ X32 @ X33) = (k4_xboole_0 @ X32 @ X33))
% 0.35/0.63          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32)))),
% 0.35/0.63      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.35/0.63  thf('47', plain,
% 0.35/0.63      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.35/0.63      inference('sup-', [status(thm)], ['45', '46'])).
% 0.35/0.63  thf('48', plain,
% 0.35/0.63      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.35/0.63      inference('sup+', [status(thm)], ['44', '47'])).
% 0.35/0.63  thf('49', plain,
% 0.35/0.63      (((k4_subset_1 @ sk_A @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)) != (sk_A))),
% 0.35/0.63      inference('demod', [status(thm)], ['43', '48'])).
% 0.35/0.63  thf('50', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.35/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.63  thf(dt_k3_subset_1, axiom,
% 0.35/0.63    (![A:$i,B:$i]:
% 0.35/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.63       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.35/0.63  thf('51', plain,
% 0.35/0.63      (![X34 : $i, X35 : $i]:
% 0.35/0.63         ((m1_subset_1 @ (k3_subset_1 @ X34 @ X35) @ (k1_zfmisc_1 @ X34))
% 0.35/0.63          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 0.35/0.63      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.35/0.63  thf('52', plain,
% 0.35/0.63      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.35/0.63      inference('sup-', [status(thm)], ['50', '51'])).
% 0.35/0.63  thf('53', plain,
% 0.35/0.63      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.35/0.63      inference('sup+', [status(thm)], ['44', '47'])).
% 0.35/0.63  thf('54', plain,
% 0.35/0.63      ((m1_subset_1 @ (k5_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.35/0.63      inference('demod', [status(thm)], ['52', '53'])).
% 0.35/0.63  thf('55', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.35/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.63  thf(redefinition_k4_subset_1, axiom,
% 0.35/0.63    (![A:$i,B:$i,C:$i]:
% 0.35/0.63     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.35/0.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.35/0.63       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.35/0.63  thf('56', plain,
% 0.35/0.63      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.35/0.63         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38))
% 0.35/0.63          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38))
% 0.35/0.63          | ((k4_subset_1 @ X38 @ X37 @ X39) = (k2_xboole_0 @ X37 @ X39)))),
% 0.35/0.63      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.35/0.63  thf('57', plain,
% 0.35/0.63      (![X0 : $i]:
% 0.35/0.63         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.35/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.35/0.63      inference('sup-', [status(thm)], ['55', '56'])).
% 0.35/0.63  thf('58', plain,
% 0.35/0.63      (((k4_subset_1 @ sk_A @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B))
% 0.35/0.63         = (k2_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 0.35/0.63      inference('sup-', [status(thm)], ['54', '57'])).
% 0.35/0.63  thf('59', plain,
% 0.35/0.63      (((k2_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)) != (sk_A))),
% 0.35/0.63      inference('demod', [status(thm)], ['49', '58'])).
% 0.35/0.63  thf('60', plain, ($false),
% 0.35/0.63      inference('simplify_reflect-', [status(thm)], ['40', '59'])).
% 0.35/0.63  
% 0.35/0.63  % SZS output end Refutation
% 0.35/0.63  
% 0.46/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
