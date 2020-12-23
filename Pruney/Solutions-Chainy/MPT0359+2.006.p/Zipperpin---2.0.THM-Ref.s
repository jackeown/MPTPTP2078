%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xfGjWhCWfm

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:31 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 524 expanded)
%              Number of leaves         :   29 ( 169 expanded)
%              Depth                    :   16
%              Number of atoms          :  969 (4085 expanded)
%              Number of equality atoms :  111 ( 428 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t39_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
      <=> ( B
          = ( k2_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
        <=> ( B
            = ( k2_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_subset_1])).

thf('0',plain,(
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

thf('1',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ X26 )
      | ( r2_hidden @ X25 @ X26 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X31: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('4',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['2','3'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('5',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X23 @ X22 )
      | ( r1_tarski @ X23 @ X21 )
      | ( X22
       != ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('6',plain,(
    ! [X21: $i,X23: $i] :
      ( ( r1_tarski @ X23 @ X21 )
      | ~ ( r2_hidden @ X23 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['4','6'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('15',plain,
    ( ( ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      = ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('21',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
      = ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      = ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('23',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
      = ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('25',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('27',plain,
    ( ( ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('29',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_subset_1 @ X29 @ X30 )
        = ( k4_xboole_0 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('30',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf('32',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('33',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('36',plain,
    ( ( ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['27','34','35'])).

thf('37',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['37'])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('39',plain,(
    ! [X28: $i] :
      ( ( k2_subset_1 @ X28 )
      = X28 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('40',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['12'])).

thf('41',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_subset_1 @ X29 @ X30 )
        = ( k4_xboole_0 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('45',plain,
    ( ( ( k3_subset_1 @ sk_A @ sk_A )
      = ( k4_xboole_0 @ sk_A @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('46',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('47',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('52',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('53',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('56',plain,(
    ! [X12: $i] :
      ( r1_tarski @ k1_xboole_0 @ X12 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('57',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55','60'])).

thf('62',plain,
    ( ( ( k3_subset_1 @ sk_A @ sk_A )
      = k1_xboole_0 )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','51','61'])).

thf('63',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('64',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['37'])).

thf('65',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('67',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_A ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['62','67'])).

thf('69',plain,(
    ! [X12: $i] :
      ( r1_tarski @ k1_xboole_0 @ X12 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('70',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['12'])).

thf('72',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sat_resolution*',[status(thm)],['38','70','71'])).

thf('73',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['36','72'])).

thf('74',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('75',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('76',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('78',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf('79',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('80',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55','60'])).

thf('84',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('86',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('88',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['86','91'])).

thf('93',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['76','77','92'])).

thf('94',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('95',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('97',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('98',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['73','95','96','97'])).

thf('99',plain,(
    sk_A = sk_B ),
    inference('sup+',[status(thm)],['11','98'])).

thf('100',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['37'])).

thf('101',plain,(
    ! [X28: $i] :
      ( ( k2_subset_1 @ X28 )
      = X28 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('102',plain,
    ( ( sk_B != sk_A )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    sk_B
 != ( k2_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['38','70'])).

thf('104',plain,(
    sk_B != sk_A ),
    inference(simpl_trail,[status(thm)],['102','103'])).

thf('105',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['99','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xfGjWhCWfm
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:42:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 308 iterations in 0.104s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.55  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.55  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.55  thf(t39_subset_1, conjecture,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.55       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.20/0.55         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i,B:$i]:
% 0.20/0.55        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.55          ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.20/0.55            ( ( B ) = ( k2_subset_1 @ A ) ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t39_subset_1])).
% 0.20/0.55  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(d2_subset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( v1_xboole_0 @ A ) =>
% 0.20/0.55         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.20/0.55       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.55         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      (![X25 : $i, X26 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X25 @ X26)
% 0.20/0.55          | (r2_hidden @ X25 @ X26)
% 0.20/0.55          | (v1_xboole_0 @ X26))),
% 0.20/0.55      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.55        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.55  thf(fc1_subset_1, axiom,
% 0.20/0.55    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.55  thf('3', plain, (![X31 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X31))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.55  thf('4', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.55      inference('clc', [status(thm)], ['2', '3'])).
% 0.20/0.55  thf(d1_zfmisc_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.20/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.20/0.55  thf('5', plain,
% 0.20/0.55      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X23 @ X22)
% 0.20/0.55          | (r1_tarski @ X23 @ X21)
% 0.20/0.55          | ((X22) != (k1_zfmisc_1 @ X21)))),
% 0.20/0.55      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.55  thf('6', plain,
% 0.20/0.55      (![X21 : $i, X23 : $i]:
% 0.20/0.55         ((r1_tarski @ X23 @ X21) | ~ (r2_hidden @ X23 @ (k1_zfmisc_1 @ X21)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.55  thf('7', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.20/0.55      inference('sup-', [status(thm)], ['4', '6'])).
% 0.20/0.55  thf(t28_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.55  thf('8', plain,
% 0.20/0.55      (![X10 : $i, X11 : $i]:
% 0.20/0.55         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.20/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.55  thf('9', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.55  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.55    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.55  thf('10', plain,
% 0.20/0.55      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.20/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.55  thf('11', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.20/0.55      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.55  thf('12', plain,
% 0.20/0.55      ((((sk_B) = (k2_subset_1 @ sk_A))
% 0.20/0.55        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('13', plain,
% 0.20/0.55      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.20/0.55         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.55      inference('split', [status(esa)], ['12'])).
% 0.20/0.55  thf('14', plain,
% 0.20/0.55      (![X10 : $i, X11 : $i]:
% 0.20/0.55         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.20/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.55  thf('15', plain,
% 0.20/0.55      ((((k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)
% 0.20/0.55          = (k3_subset_1 @ sk_A @ sk_B)))
% 0.20/0.55         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.20/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.55  thf('17', plain,
% 0.20/0.55      ((((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.20/0.55          = (k3_subset_1 @ sk_A @ sk_B)))
% 0.20/0.55         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.55      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.55  thf(t100_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.55  thf('18', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ X7 @ X8)
% 0.20/0.55           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.55  thf('19', plain,
% 0.20/0.55      ((((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.20/0.55          = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))
% 0.20/0.55         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.55  thf(t48_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.55  thf('20', plain,
% 0.20/0.55      (![X16 : $i, X17 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.20/0.55           = (k3_xboole_0 @ X16 @ X17))),
% 0.20/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.55  thf('21', plain,
% 0.20/0.55      ((((k4_xboole_0 @ sk_B @ 
% 0.20/0.55          (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.20/0.55          = (k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))
% 0.20/0.55         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['19', '20'])).
% 0.20/0.55  thf('22', plain,
% 0.20/0.55      ((((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.20/0.55          = (k3_subset_1 @ sk_A @ sk_B)))
% 0.20/0.55         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.55      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.55  thf('23', plain,
% 0.20/0.55      ((((k4_xboole_0 @ sk_B @ 
% 0.20/0.55          (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.20/0.55          = (k3_subset_1 @ sk_A @ sk_B)))
% 0.20/0.55         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.55      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.55  thf('24', plain,
% 0.20/0.55      (![X16 : $i, X17 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.20/0.55           = (k3_xboole_0 @ X16 @ X17))),
% 0.20/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.55  thf('25', plain,
% 0.20/0.55      ((((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.20/0.55          = (k3_xboole_0 @ sk_B @ 
% 0.20/0.55             (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))))
% 0.20/0.55         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['23', '24'])).
% 0.20/0.55  thf('26', plain,
% 0.20/0.55      ((((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.20/0.55          = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))
% 0.20/0.55         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.55  thf('27', plain,
% 0.20/0.55      ((((k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.20/0.55          = (k3_xboole_0 @ sk_B @ 
% 0.20/0.55             (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))))
% 0.20/0.55         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.55      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.55  thf('28', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(d5_subset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.55       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.55  thf('29', plain,
% 0.20/0.55      (![X29 : $i, X30 : $i]:
% 0.20/0.55         (((k3_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))
% 0.20/0.55          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 0.20/0.55      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.55  thf('30', plain,
% 0.20/0.55      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.55  thf('31', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.20/0.55      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.55  thf('32', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ X7 @ X8)
% 0.20/0.55           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.55  thf('33', plain,
% 0.20/0.55      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.55      inference('sup+', [status(thm)], ['31', '32'])).
% 0.20/0.55  thf('34', plain,
% 0.20/0.55      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.55      inference('sup+', [status(thm)], ['30', '33'])).
% 0.20/0.55  thf('35', plain,
% 0.20/0.55      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.55      inference('sup+', [status(thm)], ['30', '33'])).
% 0.20/0.55  thf('36', plain,
% 0.20/0.55      ((((k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B))
% 0.20/0.55          = (k3_xboole_0 @ sk_B @ 
% 0.20/0.55             (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)))))
% 0.20/0.55         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.55      inference('demod', [status(thm)], ['27', '34', '35'])).
% 0.20/0.55  thf('37', plain,
% 0.20/0.55      ((((sk_B) != (k2_subset_1 @ sk_A))
% 0.20/0.55        | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('38', plain,
% 0.20/0.55      (~ (((sk_B) = (k2_subset_1 @ sk_A))) | 
% 0.20/0.55       ~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.55      inference('split', [status(esa)], ['37'])).
% 0.20/0.55  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.55  thf('39', plain, (![X28 : $i]: ((k2_subset_1 @ X28) = (X28))),
% 0.20/0.55      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.55  thf('40', plain,
% 0.20/0.55      ((((sk_B) = (k2_subset_1 @ sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.55      inference('split', [status(esa)], ['12'])).
% 0.20/0.55  thf('41', plain,
% 0.20/0.55      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.55      inference('sup+', [status(thm)], ['39', '40'])).
% 0.20/0.55  thf('42', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('43', plain,
% 0.20/0.55      (((m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ sk_A)))
% 0.20/0.55         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.55      inference('sup+', [status(thm)], ['41', '42'])).
% 0.20/0.55  thf('44', plain,
% 0.20/0.55      (![X29 : $i, X30 : $i]:
% 0.20/0.55         (((k3_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))
% 0.20/0.55          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 0.20/0.55      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.55  thf('45', plain,
% 0.20/0.55      ((((k3_subset_1 @ sk_A @ sk_A) = (k4_xboole_0 @ sk_A @ sk_A)))
% 0.20/0.55         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.55  thf(d10_xboole_0, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.55  thf('46', plain,
% 0.20/0.55      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.20/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.55  thf('47', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.20/0.55      inference('simplify', [status(thm)], ['46'])).
% 0.20/0.55  thf('48', plain,
% 0.20/0.55      (![X10 : $i, X11 : $i]:
% 0.20/0.55         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.20/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.55  thf('49', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.55  thf('50', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ X7 @ X8)
% 0.20/0.55           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.55  thf('51', plain,
% 0.20/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['49', '50'])).
% 0.20/0.55  thf(t3_boole, axiom,
% 0.20/0.55    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.55  thf('52', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.20/0.55      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.55  thf('53', plain,
% 0.20/0.55      (![X16 : $i, X17 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.20/0.55           = (k3_xboole_0 @ X16 @ X17))),
% 0.20/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.55  thf('54', plain,
% 0.20/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['52', '53'])).
% 0.20/0.55  thf('55', plain,
% 0.20/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['49', '50'])).
% 0.20/0.55  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.55  thf('56', plain, (![X12 : $i]: (r1_tarski @ k1_xboole_0 @ X12)),
% 0.20/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.55  thf('57', plain,
% 0.20/0.55      (![X10 : $i, X11 : $i]:
% 0.20/0.55         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.20/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.55  thf('58', plain,
% 0.20/0.55      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['56', '57'])).
% 0.20/0.55  thf('59', plain,
% 0.20/0.55      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.20/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.55  thf('60', plain,
% 0.20/0.55      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['58', '59'])).
% 0.20/0.55  thf('61', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.55      inference('demod', [status(thm)], ['54', '55', '60'])).
% 0.20/0.55  thf('62', plain,
% 0.20/0.55      ((((k3_subset_1 @ sk_A @ sk_A) = (k1_xboole_0)))
% 0.20/0.55         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.55      inference('demod', [status(thm)], ['45', '51', '61'])).
% 0.20/0.55  thf('63', plain,
% 0.20/0.55      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.55      inference('sup+', [status(thm)], ['39', '40'])).
% 0.20/0.55  thf('64', plain,
% 0.20/0.55      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.20/0.55         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.55      inference('split', [status(esa)], ['37'])).
% 0.20/0.55  thf('65', plain,
% 0.20/0.55      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A))
% 0.20/0.55         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.20/0.55             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.55  thf('66', plain,
% 0.20/0.55      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.55      inference('sup+', [status(thm)], ['39', '40'])).
% 0.20/0.55  thf('67', plain,
% 0.20/0.55      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_A) @ sk_A))
% 0.20/0.55         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.20/0.55             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.55      inference('demod', [status(thm)], ['65', '66'])).
% 0.20/0.55  thf('68', plain,
% 0.20/0.55      ((~ (r1_tarski @ k1_xboole_0 @ sk_A))
% 0.20/0.55         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.20/0.55             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['62', '67'])).
% 0.20/0.55  thf('69', plain, (![X12 : $i]: (r1_tarski @ k1_xboole_0 @ X12)),
% 0.20/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.55  thf('70', plain,
% 0.20/0.55      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.20/0.55       ~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.20/0.55      inference('demod', [status(thm)], ['68', '69'])).
% 0.20/0.55  thf('71', plain,
% 0.20/0.55      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.20/0.55       (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.20/0.55      inference('split', [status(esa)], ['12'])).
% 0.20/0.55  thf('72', plain, (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.55      inference('sat_resolution*', [status(thm)], ['38', '70', '71'])).
% 0.20/0.55  thf('73', plain,
% 0.20/0.55      (((k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B))
% 0.20/0.55         = (k3_xboole_0 @ sk_B @ 
% 0.20/0.55            (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B))))),
% 0.20/0.55      inference('simpl_trail', [status(thm)], ['36', '72'])).
% 0.20/0.55  thf('74', plain,
% 0.20/0.55      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.55  thf(t98_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.20/0.55  thf('75', plain,
% 0.20/0.55      (![X18 : $i, X19 : $i]:
% 0.20/0.55         ((k2_xboole_0 @ X18 @ X19)
% 0.20/0.55           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.20/0.55  thf('76', plain,
% 0.20/0.55      (((k2_xboole_0 @ sk_B @ sk_A)
% 0.20/0.55         = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['74', '75'])).
% 0.20/0.55  thf(commutativity_k2_xboole_0, axiom,
% 0.20/0.55    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.20/0.55  thf('77', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.55      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.55  thf('78', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.20/0.55      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.55  thf('79', plain,
% 0.20/0.55      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.20/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.55  thf('80', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ X7 @ X8)
% 0.20/0.55           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.55  thf('81', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ X0 @ X1)
% 0.20/0.55           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['79', '80'])).
% 0.20/0.55  thf('82', plain,
% 0.20/0.55      (((k4_xboole_0 @ sk_B @ sk_A) = (k5_xboole_0 @ sk_B @ sk_B))),
% 0.20/0.55      inference('sup+', [status(thm)], ['78', '81'])).
% 0.20/0.55  thf('83', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.55      inference('demod', [status(thm)], ['54', '55', '60'])).
% 0.20/0.55  thf('84', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.20/0.55      inference('demod', [status(thm)], ['82', '83'])).
% 0.20/0.55  thf('85', plain,
% 0.20/0.55      (![X18 : $i, X19 : $i]:
% 0.20/0.55         ((k2_xboole_0 @ X18 @ X19)
% 0.20/0.55           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.20/0.55  thf('86', plain,
% 0.20/0.55      (((k2_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['84', '85'])).
% 0.20/0.55  thf('87', plain,
% 0.20/0.55      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['58', '59'])).
% 0.20/0.55  thf('88', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ X7 @ X8)
% 0.20/0.55           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.55  thf('89', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['87', '88'])).
% 0.20/0.55  thf('90', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.20/0.55      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.55  thf('91', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['89', '90'])).
% 0.20/0.55  thf('92', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['86', '91'])).
% 0.20/0.55  thf('93', plain,
% 0.20/0.55      (((sk_A) = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.20/0.55      inference('demod', [status(thm)], ['76', '77', '92'])).
% 0.20/0.55  thf('94', plain,
% 0.20/0.55      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.55      inference('sup+', [status(thm)], ['30', '33'])).
% 0.20/0.55  thf('95', plain,
% 0.20/0.55      (((sk_A) = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.55      inference('demod', [status(thm)], ['93', '94'])).
% 0.20/0.55  thf('96', plain,
% 0.20/0.55      (((sk_A) = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.55      inference('demod', [status(thm)], ['93', '94'])).
% 0.20/0.55  thf('97', plain,
% 0.20/0.55      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.20/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.55  thf('98', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.55      inference('demod', [status(thm)], ['73', '95', '96', '97'])).
% 0.20/0.55  thf('99', plain, (((sk_A) = (sk_B))),
% 0.20/0.55      inference('sup+', [status(thm)], ['11', '98'])).
% 0.20/0.55  thf('100', plain,
% 0.20/0.55      ((((sk_B) != (k2_subset_1 @ sk_A)))
% 0.20/0.55         <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.55      inference('split', [status(esa)], ['37'])).
% 0.20/0.55  thf('101', plain, (![X28 : $i]: ((k2_subset_1 @ X28) = (X28))),
% 0.20/0.55      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.55  thf('102', plain,
% 0.20/0.55      ((((sk_B) != (sk_A))) <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.55      inference('demod', [status(thm)], ['100', '101'])).
% 0.20/0.55  thf('103', plain, (~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.20/0.55      inference('sat_resolution*', [status(thm)], ['38', '70'])).
% 0.20/0.55  thf('104', plain, (((sk_B) != (sk_A))),
% 0.20/0.55      inference('simpl_trail', [status(thm)], ['102', '103'])).
% 0.20/0.55  thf('105', plain, ($false),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)], ['99', '104'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
