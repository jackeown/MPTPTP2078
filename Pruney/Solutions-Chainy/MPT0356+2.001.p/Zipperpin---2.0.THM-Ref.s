%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7Y2NmClewj

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:17 EST 2020

% Result     : Theorem 0.78s
% Output     : Refutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 814 expanded)
%              Number of leaves         :   33 ( 264 expanded)
%              Depth                    :   27
%              Number of atoms          : 1063 (5805 expanded)
%              Number of equality atoms :   81 ( 384 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(t35_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
           => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
             => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_subset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X25: $i,X26: $i] :
      ( r1_tarski @ X25 @ ( k2_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ X36 )
      | ( r2_hidden @ X35 @ X36 )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X40: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('6',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['4','5'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('7',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X33 @ X32 )
      | ( r1_tarski @ X33 @ X31 )
      | ( X32
       != ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('8',plain,(
    ! [X31: $i,X33: $i] :
      ( ( r1_tarski @ X33 @ X31 )
      | ~ ( r2_hidden @ X33 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['6','8'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('13',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X22 )
      | ~ ( r1_tarski @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ sk_A ) @ X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('15',plain,(
    ! [X17: $i] :
      ( r1_tarski @ k1_xboole_0 @ X17 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['14','17'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('21',plain,(
    ! [X43: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k3_subset_1 @ X38 @ X39 )
        = ( k4_xboole_0 @ X38 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X25: $i,X26: $i] :
      ( r1_tarski @ X25 @ ( k2_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('25',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X22 )
      | ~ ( r1_tarski @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ X30 @ X31 )
      | ( r2_hidden @ X30 @ X32 )
      | ( X32
       != ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('32',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r2_hidden @ X30 @ ( k1_zfmisc_1 @ X31 ) )
      | ~ ( r1_tarski @ X30 @ X31 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X35 @ X36 )
      | ( m1_subset_1 @ X35 @ X36 )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X40: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k3_subset_1 @ X38 @ X39 )
        = ( k4_xboole_0 @ X38 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('42',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k3_subset_1 @ X42 @ ( k3_subset_1 @ X42 @ X41 ) )
        = X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','44'])).

thf('46',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['20','45'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('47',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('48',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k3_subset_1 @ X38 @ X39 )
        = ( k4_xboole_0 @ X38 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('53',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['50','53'])).

thf('55',plain,(
    ~ ( r1_tarski @ sk_C_1 @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ X36 )
      | ( r2_hidden @ X35 @ X36 )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('58',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X40: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('60',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X31: $i,X33: $i] :
      ( ( r1_tarski @ X33 @ X31 )
      | ~ ( r2_hidden @ X33 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('62',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('64',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X25: $i,X26: $i] :
      ( r1_tarski @ X25 @ ( k2_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('66',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['60','61'])).

thf('67',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C_1 @ ( k2_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X22 )
      | ~ ( r1_tarski @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_C_1 @ sk_A ) @ X0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('73',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('75',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','44'])).

thf('77',plain,
    ( sk_C_1
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('79',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k3_subset_1 @ X38 @ X39 )
        = ( k4_xboole_0 @ X38 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('82',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['79','82'])).

thf('84',plain,(
    r1_tarski @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['64','83'])).

thf('85',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('86',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X9 @ X11 )
      | ~ ( r1_tarski @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) )
      | ( r1_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['84','87'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('89',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X27 @ X28 )
      | ~ ( r1_xboole_0 @ X27 @ X29 )
      | ( r1_tarski @ X27 @ ( k4_xboole_0 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C_1 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['63','90'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('92',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('93',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('96',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('97',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k3_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('99',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['98','101'])).

thf('103',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('106',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['104','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','44'])).

thf('110',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','44'])).

thf('111',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','39'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['114','117'])).

thf('119',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['97','113','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('121',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_B )
    = ( k5_xboole_0 @ sk_C_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','44'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('124',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['122','125'])).

thf('127',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_B )
    = sk_C_1 ),
    inference(demod,[status(thm)],['121','126'])).

thf('128',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('129',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X9 @ X11 )
      | ~ ( r1_tarski @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference('sup+',[status(thm)],['127','130'])).

thf('132',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X27 @ X28 )
      | ~ ( r1_xboole_0 @ X27 @ X29 )
      | ( r1_tarski @ X27 @ ( k4_xboole_0 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ ( k4_xboole_0 @ X0 @ sk_B ) )
      | ~ ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    r1_tarski @ sk_C_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['62','133'])).

thf('135',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('136',plain,(
    r1_tarski @ sk_C_1 @ ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    $false ),
    inference(demod,[status(thm)],['55','136'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7Y2NmClewj
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:14:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.78/0.97  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.78/0.97  % Solved by: fo/fo7.sh
% 0.78/0.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.78/0.97  % done 1943 iterations in 0.519s
% 0.78/0.97  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.78/0.97  % SZS output start Refutation
% 0.78/0.97  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.78/0.97  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.78/0.97  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.78/0.97  thf(sk_A_type, type, sk_A: $i).
% 0.78/0.97  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.78/0.97  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.78/0.97  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.78/0.97  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.78/0.97  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.78/0.97  thf(sk_B_type, type, sk_B: $i).
% 0.78/0.97  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.78/0.97  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.78/0.97  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.78/0.97  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.78/0.97  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.78/0.97  thf(t35_subset_1, conjecture,
% 0.78/0.97    (![A:$i,B:$i]:
% 0.78/0.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.78/0.97       ( ![C:$i]:
% 0.78/0.97         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.78/0.97           ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 0.78/0.97             ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.78/0.97  thf(zf_stmt_0, negated_conjecture,
% 0.78/0.97    (~( ![A:$i,B:$i]:
% 0.78/0.97        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.78/0.97          ( ![C:$i]:
% 0.78/0.97            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.78/0.97              ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 0.78/0.97                ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 0.78/0.97    inference('cnf.neg', [status(esa)], [t35_subset_1])).
% 0.78/0.97  thf('0', plain, (~ (r1_tarski @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_B))),
% 0.78/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.97  thf(t7_xboole_1, axiom,
% 0.78/0.97    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.78/0.97  thf('1', plain,
% 0.78/0.97      (![X25 : $i, X26 : $i]: (r1_tarski @ X25 @ (k2_xboole_0 @ X25 @ X26))),
% 0.78/0.97      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.78/0.97  thf('2', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.78/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.97  thf(d2_subset_1, axiom,
% 0.78/0.97    (![A:$i,B:$i]:
% 0.78/0.97     ( ( ( v1_xboole_0 @ A ) =>
% 0.78/0.97         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.78/0.97       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.78/0.97         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.78/0.97  thf('3', plain,
% 0.78/0.97      (![X35 : $i, X36 : $i]:
% 0.78/0.97         (~ (m1_subset_1 @ X35 @ X36)
% 0.78/0.97          | (r2_hidden @ X35 @ X36)
% 0.78/0.97          | (v1_xboole_0 @ X36))),
% 0.78/0.97      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.78/0.97  thf('4', plain,
% 0.78/0.97      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.78/0.97        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.78/0.97      inference('sup-', [status(thm)], ['2', '3'])).
% 0.78/0.97  thf(fc1_subset_1, axiom,
% 0.78/0.97    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.78/0.97  thf('5', plain, (![X40 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X40))),
% 0.78/0.97      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.78/0.97  thf('6', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.78/0.97      inference('clc', [status(thm)], ['4', '5'])).
% 0.78/0.97  thf(d1_zfmisc_1, axiom,
% 0.78/0.97    (![A:$i,B:$i]:
% 0.78/0.97     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.78/0.97       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.78/0.97  thf('7', plain,
% 0.78/0.97      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.78/0.97         (~ (r2_hidden @ X33 @ X32)
% 0.78/0.97          | (r1_tarski @ X33 @ X31)
% 0.78/0.97          | ((X32) != (k1_zfmisc_1 @ X31)))),
% 0.78/0.97      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.78/0.97  thf('8', plain,
% 0.78/0.97      (![X31 : $i, X33 : $i]:
% 0.78/0.97         ((r1_tarski @ X33 @ X31) | ~ (r2_hidden @ X33 @ (k1_zfmisc_1 @ X31)))),
% 0.78/0.97      inference('simplify', [status(thm)], ['7'])).
% 0.78/0.97  thf('9', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.78/0.97      inference('sup-', [status(thm)], ['6', '8'])).
% 0.78/0.97  thf(t1_xboole_1, axiom,
% 0.78/0.97    (![A:$i,B:$i,C:$i]:
% 0.78/0.97     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.78/0.97       ( r1_tarski @ A @ C ) ))).
% 0.78/0.97  thf('10', plain,
% 0.78/0.97      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.78/0.97         (~ (r1_tarski @ X14 @ X15)
% 0.78/0.97          | ~ (r1_tarski @ X15 @ X16)
% 0.78/0.97          | (r1_tarski @ X14 @ X16))),
% 0.78/0.97      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.78/0.97  thf('11', plain,
% 0.78/0.97      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ~ (r1_tarski @ sk_A @ X0))),
% 0.78/0.97      inference('sup-', [status(thm)], ['9', '10'])).
% 0.78/0.97  thf('12', plain,
% 0.78/0.97      (![X0 : $i]: (r1_tarski @ sk_B @ (k2_xboole_0 @ sk_A @ X0))),
% 0.78/0.97      inference('sup-', [status(thm)], ['1', '11'])).
% 0.78/0.97  thf(t43_xboole_1, axiom,
% 0.78/0.97    (![A:$i,B:$i,C:$i]:
% 0.78/0.97     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.78/0.97       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.78/0.97  thf('13', plain,
% 0.78/0.97      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.78/0.97         ((r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X22)
% 0.78/0.97          | ~ (r1_tarski @ X20 @ (k2_xboole_0 @ X21 @ X22)))),
% 0.78/0.97      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.78/0.97  thf('14', plain,
% 0.78/0.97      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_B @ sk_A) @ X0)),
% 0.78/0.97      inference('sup-', [status(thm)], ['12', '13'])).
% 0.78/0.97  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.78/0.97  thf('15', plain, (![X17 : $i]: (r1_tarski @ k1_xboole_0 @ X17)),
% 0.78/0.97      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.78/0.97  thf(d10_xboole_0, axiom,
% 0.78/0.97    (![A:$i,B:$i]:
% 0.78/0.97     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.78/0.97  thf('16', plain,
% 0.78/0.97      (![X4 : $i, X6 : $i]:
% 0.78/0.97         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.78/0.97      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.78/0.97  thf('17', plain,
% 0.78/0.97      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.78/0.97      inference('sup-', [status(thm)], ['15', '16'])).
% 0.78/0.97  thf('18', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.78/0.97      inference('sup-', [status(thm)], ['14', '17'])).
% 0.78/0.97  thf(t48_xboole_1, axiom,
% 0.78/0.97    (![A:$i,B:$i]:
% 0.78/0.97     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.78/0.97  thf('19', plain,
% 0.78/0.97      (![X23 : $i, X24 : $i]:
% 0.78/0.97         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 0.78/0.97           = (k3_xboole_0 @ X23 @ X24))),
% 0.78/0.97      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.78/0.97  thf('20', plain,
% 0.78/0.97      (((k4_xboole_0 @ sk_B @ k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.78/0.97      inference('sup+', [status(thm)], ['18', '19'])).
% 0.78/0.97  thf(t4_subset_1, axiom,
% 0.78/0.97    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.78/0.97  thf('21', plain,
% 0.78/0.97      (![X43 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X43))),
% 0.78/0.97      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.78/0.97  thf(d5_subset_1, axiom,
% 0.78/0.97    (![A:$i,B:$i]:
% 0.78/0.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.78/0.97       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.78/0.97  thf('22', plain,
% 0.78/0.97      (![X38 : $i, X39 : $i]:
% 0.78/0.97         (((k3_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))
% 0.78/0.97          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38)))),
% 0.78/0.97      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.78/0.97  thf('23', plain,
% 0.78/0.97      (![X0 : $i]:
% 0.78/0.97         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.78/0.97      inference('sup-', [status(thm)], ['21', '22'])).
% 0.78/0.97  thf('24', plain,
% 0.78/0.97      (![X25 : $i, X26 : $i]: (r1_tarski @ X25 @ (k2_xboole_0 @ X25 @ X26))),
% 0.78/0.97      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.78/0.97  thf('25', plain,
% 0.78/0.97      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.78/0.97         ((r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X22)
% 0.78/0.97          | ~ (r1_tarski @ X20 @ (k2_xboole_0 @ X21 @ X22)))),
% 0.78/0.97      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.78/0.97  thf('26', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 0.78/0.97      inference('sup-', [status(thm)], ['24', '25'])).
% 0.78/0.97  thf('27', plain,
% 0.78/0.97      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.78/0.97      inference('sup-', [status(thm)], ['15', '16'])).
% 0.78/0.97  thf('28', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.78/0.97      inference('sup-', [status(thm)], ['26', '27'])).
% 0.78/0.97  thf('29', plain,
% 0.78/0.97      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.78/0.97      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.78/0.97  thf('30', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.78/0.97      inference('simplify', [status(thm)], ['29'])).
% 0.78/0.97  thf('31', plain,
% 0.78/0.97      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.78/0.97         (~ (r1_tarski @ X30 @ X31)
% 0.78/0.97          | (r2_hidden @ X30 @ X32)
% 0.78/0.97          | ((X32) != (k1_zfmisc_1 @ X31)))),
% 0.78/0.97      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.78/0.97  thf('32', plain,
% 0.78/0.97      (![X30 : $i, X31 : $i]:
% 0.78/0.97         ((r2_hidden @ X30 @ (k1_zfmisc_1 @ X31)) | ~ (r1_tarski @ X30 @ X31))),
% 0.78/0.97      inference('simplify', [status(thm)], ['31'])).
% 0.78/0.97  thf('33', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.78/0.97      inference('sup-', [status(thm)], ['30', '32'])).
% 0.78/0.97  thf('34', plain,
% 0.78/0.97      (![X35 : $i, X36 : $i]:
% 0.78/0.97         (~ (r2_hidden @ X35 @ X36)
% 0.78/0.97          | (m1_subset_1 @ X35 @ X36)
% 0.78/0.97          | (v1_xboole_0 @ X36))),
% 0.78/0.97      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.78/0.97  thf('35', plain,
% 0.78/0.97      (![X0 : $i]:
% 0.78/0.97         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.78/0.97          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 0.78/0.97      inference('sup-', [status(thm)], ['33', '34'])).
% 0.78/0.97  thf('36', plain, (![X40 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X40))),
% 0.78/0.97      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.78/0.97  thf('37', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.78/0.97      inference('clc', [status(thm)], ['35', '36'])).
% 0.78/0.97  thf('38', plain,
% 0.78/0.97      (![X38 : $i, X39 : $i]:
% 0.78/0.97         (((k3_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))
% 0.78/0.97          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38)))),
% 0.78/0.97      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.78/0.97  thf('39', plain,
% 0.78/0.97      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.78/0.97      inference('sup-', [status(thm)], ['37', '38'])).
% 0.78/0.97  thf('40', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.78/0.97      inference('demod', [status(thm)], ['28', '39'])).
% 0.78/0.97  thf('41', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.78/0.97      inference('clc', [status(thm)], ['35', '36'])).
% 0.78/0.97  thf(involutiveness_k3_subset_1, axiom,
% 0.78/0.97    (![A:$i,B:$i]:
% 0.78/0.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.78/0.97       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.78/0.97  thf('42', plain,
% 0.78/0.97      (![X41 : $i, X42 : $i]:
% 0.78/0.97         (((k3_subset_1 @ X42 @ (k3_subset_1 @ X42 @ X41)) = (X41))
% 0.78/0.97          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42)))),
% 0.78/0.97      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.78/0.97  thf('43', plain,
% 0.78/0.97      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 0.78/0.97      inference('sup-', [status(thm)], ['41', '42'])).
% 0.78/0.97  thf('44', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.78/0.97      inference('sup+', [status(thm)], ['40', '43'])).
% 0.78/0.97  thf('45', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.78/0.97      inference('demod', [status(thm)], ['23', '44'])).
% 0.78/0.97  thf('46', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.78/0.97      inference('demod', [status(thm)], ['20', '45'])).
% 0.78/0.97  thf(commutativity_k3_xboole_0, axiom,
% 0.78/0.97    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.78/0.97  thf('47', plain,
% 0.78/0.97      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.78/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.78/0.97  thf(t100_xboole_1, axiom,
% 0.78/0.97    (![A:$i,B:$i]:
% 0.78/0.97     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.78/0.97  thf('48', plain,
% 0.78/0.97      (![X7 : $i, X8 : $i]:
% 0.78/0.97         ((k4_xboole_0 @ X7 @ X8)
% 0.78/0.97           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.78/0.97      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.78/0.97  thf('49', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i]:
% 0.78/0.97         ((k4_xboole_0 @ X0 @ X1)
% 0.78/0.97           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.78/0.97      inference('sup+', [status(thm)], ['47', '48'])).
% 0.78/0.97  thf('50', plain,
% 0.78/0.97      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.78/0.97      inference('sup+', [status(thm)], ['46', '49'])).
% 0.78/0.97  thf('51', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.78/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.97  thf('52', plain,
% 0.78/0.97      (![X38 : $i, X39 : $i]:
% 0.78/0.97         (((k3_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))
% 0.78/0.97          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38)))),
% 0.78/0.97      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.78/0.97  thf('53', plain,
% 0.78/0.97      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.78/0.97      inference('sup-', [status(thm)], ['51', '52'])).
% 0.78/0.97  thf('54', plain,
% 0.78/0.97      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.78/0.97      inference('sup+', [status(thm)], ['50', '53'])).
% 0.78/0.97  thf('55', plain, (~ (r1_tarski @ sk_C_1 @ (k5_xboole_0 @ sk_A @ sk_B))),
% 0.78/0.97      inference('demod', [status(thm)], ['0', '54'])).
% 0.78/0.97  thf('56', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.78/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.97  thf('57', plain,
% 0.78/0.97      (![X35 : $i, X36 : $i]:
% 0.78/0.97         (~ (m1_subset_1 @ X35 @ X36)
% 0.78/0.97          | (r2_hidden @ X35 @ X36)
% 0.78/0.97          | (v1_xboole_0 @ X36))),
% 0.78/0.97      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.78/0.97  thf('58', plain,
% 0.78/0.97      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.78/0.97        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.78/0.97      inference('sup-', [status(thm)], ['56', '57'])).
% 0.78/0.97  thf('59', plain, (![X40 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X40))),
% 0.78/0.97      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.78/0.97  thf('60', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.78/0.97      inference('clc', [status(thm)], ['58', '59'])).
% 0.78/0.97  thf('61', plain,
% 0.78/0.97      (![X31 : $i, X33 : $i]:
% 0.78/0.97         ((r1_tarski @ X33 @ X31) | ~ (r2_hidden @ X33 @ (k1_zfmisc_1 @ X31)))),
% 0.78/0.97      inference('simplify', [status(thm)], ['7'])).
% 0.78/0.97  thf('62', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 0.78/0.97      inference('sup-', [status(thm)], ['60', '61'])).
% 0.78/0.97  thf('63', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.78/0.97      inference('simplify', [status(thm)], ['29'])).
% 0.78/0.97  thf('64', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))),
% 0.78/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.97  thf('65', plain,
% 0.78/0.97      (![X25 : $i, X26 : $i]: (r1_tarski @ X25 @ (k2_xboole_0 @ X25 @ X26))),
% 0.78/0.97      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.78/0.97  thf('66', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 0.78/0.97      inference('sup-', [status(thm)], ['60', '61'])).
% 0.78/0.97  thf('67', plain,
% 0.78/0.97      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.78/0.97         (~ (r1_tarski @ X14 @ X15)
% 0.78/0.97          | ~ (r1_tarski @ X15 @ X16)
% 0.78/0.97          | (r1_tarski @ X14 @ X16))),
% 0.78/0.97      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.78/0.97  thf('68', plain,
% 0.78/0.97      (![X0 : $i]: ((r1_tarski @ sk_C_1 @ X0) | ~ (r1_tarski @ sk_A @ X0))),
% 0.78/0.97      inference('sup-', [status(thm)], ['66', '67'])).
% 0.78/0.97  thf('69', plain,
% 0.78/0.97      (![X0 : $i]: (r1_tarski @ sk_C_1 @ (k2_xboole_0 @ sk_A @ X0))),
% 0.78/0.97      inference('sup-', [status(thm)], ['65', '68'])).
% 0.78/0.97  thf('70', plain,
% 0.78/0.97      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.78/0.97         ((r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X22)
% 0.78/0.97          | ~ (r1_tarski @ X20 @ (k2_xboole_0 @ X21 @ X22)))),
% 0.78/0.97      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.78/0.97  thf('71', plain,
% 0.78/0.97      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_C_1 @ sk_A) @ X0)),
% 0.78/0.97      inference('sup-', [status(thm)], ['69', '70'])).
% 0.78/0.97  thf('72', plain,
% 0.78/0.97      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.78/0.97      inference('sup-', [status(thm)], ['15', '16'])).
% 0.78/0.97  thf('73', plain, (((k4_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 0.78/0.97      inference('sup-', [status(thm)], ['71', '72'])).
% 0.78/0.97  thf('74', plain,
% 0.78/0.97      (![X23 : $i, X24 : $i]:
% 0.78/0.97         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 0.78/0.97           = (k3_xboole_0 @ X23 @ X24))),
% 0.78/0.97      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.78/0.97  thf('75', plain,
% 0.78/0.97      (((k4_xboole_0 @ sk_C_1 @ k1_xboole_0) = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 0.78/0.97      inference('sup+', [status(thm)], ['73', '74'])).
% 0.78/0.97  thf('76', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.78/0.97      inference('demod', [status(thm)], ['23', '44'])).
% 0.78/0.97  thf('77', plain, (((sk_C_1) = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 0.78/0.97      inference('demod', [status(thm)], ['75', '76'])).
% 0.78/0.97  thf('78', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i]:
% 0.78/0.97         ((k4_xboole_0 @ X0 @ X1)
% 0.78/0.97           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.78/0.97      inference('sup+', [status(thm)], ['47', '48'])).
% 0.78/0.97  thf('79', plain,
% 0.78/0.97      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 0.78/0.97      inference('sup+', [status(thm)], ['77', '78'])).
% 0.78/0.97  thf('80', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.78/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.97  thf('81', plain,
% 0.78/0.97      (![X38 : $i, X39 : $i]:
% 0.78/0.97         (((k3_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))
% 0.78/0.97          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38)))),
% 0.78/0.97      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.78/0.97  thf('82', plain,
% 0.78/0.97      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.78/0.97      inference('sup-', [status(thm)], ['80', '81'])).
% 0.78/0.97  thf('83', plain,
% 0.78/0.97      (((k3_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 0.78/0.97      inference('sup+', [status(thm)], ['79', '82'])).
% 0.78/0.97  thf('84', plain, ((r1_tarski @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C_1))),
% 0.78/0.97      inference('demod', [status(thm)], ['64', '83'])).
% 0.78/0.97  thf('85', plain,
% 0.78/0.97      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 0.78/0.97      inference('sup+', [status(thm)], ['77', '78'])).
% 0.78/0.97  thf(t106_xboole_1, axiom,
% 0.78/0.97    (![A:$i,B:$i,C:$i]:
% 0.78/0.97     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.78/0.97       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.78/0.97  thf('86', plain,
% 0.78/0.97      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.78/0.97         ((r1_xboole_0 @ X9 @ X11)
% 0.78/0.97          | ~ (r1_tarski @ X9 @ (k4_xboole_0 @ X10 @ X11)))),
% 0.78/0.97      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.78/0.97  thf('87', plain,
% 0.78/0.97      (![X0 : $i]:
% 0.78/0.97         (~ (r1_tarski @ X0 @ (k5_xboole_0 @ sk_A @ sk_C_1))
% 0.78/0.97          | (r1_xboole_0 @ X0 @ sk_C_1))),
% 0.78/0.97      inference('sup-', [status(thm)], ['85', '86'])).
% 0.78/0.97  thf('88', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 0.78/0.97      inference('sup-', [status(thm)], ['84', '87'])).
% 0.78/0.97  thf(t86_xboole_1, axiom,
% 0.78/0.97    (![A:$i,B:$i,C:$i]:
% 0.78/0.97     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.78/0.97       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.78/0.97  thf('89', plain,
% 0.78/0.97      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.78/0.97         (~ (r1_tarski @ X27 @ X28)
% 0.78/0.97          | ~ (r1_xboole_0 @ X27 @ X29)
% 0.78/0.97          | (r1_tarski @ X27 @ (k4_xboole_0 @ X28 @ X29)))),
% 0.78/0.97      inference('cnf', [status(esa)], [t86_xboole_1])).
% 0.78/0.97  thf('90', plain,
% 0.78/0.97      (![X0 : $i]:
% 0.78/0.97         ((r1_tarski @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_1))
% 0.78/0.97          | ~ (r1_tarski @ sk_B @ X0))),
% 0.78/0.97      inference('sup-', [status(thm)], ['88', '89'])).
% 0.78/0.97  thf('91', plain, ((r1_tarski @ sk_B @ (k4_xboole_0 @ sk_B @ sk_C_1))),
% 0.78/0.97      inference('sup-', [status(thm)], ['63', '90'])).
% 0.78/0.97  thf(t36_xboole_1, axiom,
% 0.78/0.97    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.78/0.97  thf('92', plain,
% 0.78/0.97      (![X18 : $i, X19 : $i]: (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X18)),
% 0.78/0.97      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.78/0.97  thf('93', plain,
% 0.78/0.97      (![X4 : $i, X6 : $i]:
% 0.78/0.97         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.78/0.97      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.78/0.97  thf('94', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i]:
% 0.78/0.97         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.78/0.97          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.78/0.97      inference('sup-', [status(thm)], ['92', '93'])).
% 0.78/0.97  thf('95', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_C_1))),
% 0.78/0.97      inference('sup-', [status(thm)], ['91', '94'])).
% 0.78/0.97  thf('96', plain,
% 0.78/0.97      (![X23 : $i, X24 : $i]:
% 0.78/0.97         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 0.78/0.97           = (k3_xboole_0 @ X23 @ X24))),
% 0.78/0.97      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.78/0.97  thf('97', plain,
% 0.78/0.97      (((k4_xboole_0 @ sk_B @ sk_B) = (k3_xboole_0 @ sk_B @ sk_C_1))),
% 0.78/0.97      inference('sup+', [status(thm)], ['95', '96'])).
% 0.78/0.97  thf('98', plain,
% 0.78/0.97      (![X23 : $i, X24 : $i]:
% 0.78/0.97         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 0.78/0.97           = (k3_xboole_0 @ X23 @ X24))),
% 0.78/0.97      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.78/0.97  thf('99', plain,
% 0.78/0.97      (![X18 : $i, X19 : $i]: (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X18)),
% 0.78/0.97      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.78/0.97  thf('100', plain,
% 0.78/0.97      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.78/0.97      inference('sup-', [status(thm)], ['15', '16'])).
% 0.78/0.97  thf('101', plain,
% 0.78/0.97      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.78/0.97      inference('sup-', [status(thm)], ['99', '100'])).
% 0.78/0.97  thf('102', plain,
% 0.78/0.97      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.78/0.97      inference('sup+', [status(thm)], ['98', '101'])).
% 0.78/0.97  thf('103', plain,
% 0.78/0.97      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.78/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.78/0.97  thf('104', plain,
% 0.78/0.97      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.78/0.97      inference('sup+', [status(thm)], ['102', '103'])).
% 0.78/0.97  thf('105', plain,
% 0.78/0.97      (![X23 : $i, X24 : $i]:
% 0.78/0.97         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 0.78/0.97           = (k3_xboole_0 @ X23 @ X24))),
% 0.78/0.97      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.78/0.97  thf('106', plain,
% 0.78/0.97      (![X23 : $i, X24 : $i]:
% 0.78/0.97         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 0.78/0.97           = (k3_xboole_0 @ X23 @ X24))),
% 0.78/0.97      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.78/0.97  thf('107', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i]:
% 0.78/0.97         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.78/0.97           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.78/0.97      inference('sup+', [status(thm)], ['105', '106'])).
% 0.78/0.97  thf('108', plain,
% 0.78/0.97      (![X0 : $i]:
% 0.78/0.97         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.78/0.97           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.78/0.97      inference('sup+', [status(thm)], ['104', '107'])).
% 0.78/0.97  thf('109', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.78/0.97      inference('demod', [status(thm)], ['23', '44'])).
% 0.78/0.97  thf('110', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.78/0.97      inference('demod', [status(thm)], ['23', '44'])).
% 0.78/0.97  thf('111', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.78/0.97      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.78/0.97  thf('112', plain,
% 0.78/0.97      (![X7 : $i, X8 : $i]:
% 0.78/0.97         ((k4_xboole_0 @ X7 @ X8)
% 0.78/0.97           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.78/0.97      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.78/0.97  thf('113', plain,
% 0.78/0.97      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.78/0.97      inference('sup+', [status(thm)], ['111', '112'])).
% 0.78/0.97  thf('114', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.78/0.97      inference('demod', [status(thm)], ['28', '39'])).
% 0.78/0.97  thf('115', plain,
% 0.78/0.97      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.78/0.97      inference('sup+', [status(thm)], ['111', '112'])).
% 0.78/0.97  thf('116', plain,
% 0.78/0.97      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.78/0.97      inference('sup-', [status(thm)], ['37', '38'])).
% 0.78/0.97  thf('117', plain,
% 0.78/0.97      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.78/0.97      inference('sup+', [status(thm)], ['115', '116'])).
% 0.78/0.97  thf('118', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.78/0.97      inference('demod', [status(thm)], ['114', '117'])).
% 0.78/0.97  thf('119', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_C_1))),
% 0.78/0.97      inference('demod', [status(thm)], ['97', '113', '118'])).
% 0.78/0.97  thf('120', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i]:
% 0.78/0.97         ((k4_xboole_0 @ X0 @ X1)
% 0.78/0.97           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.78/0.97      inference('sup+', [status(thm)], ['47', '48'])).
% 0.78/0.97  thf('121', plain,
% 0.78/0.97      (((k4_xboole_0 @ sk_C_1 @ sk_B) = (k5_xboole_0 @ sk_C_1 @ k1_xboole_0))),
% 0.78/0.97      inference('sup+', [status(thm)], ['119', '120'])).
% 0.78/0.97  thf('122', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.78/0.97      inference('demod', [status(thm)], ['23', '44'])).
% 0.78/0.97  thf('123', plain,
% 0.78/0.97      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.78/0.97      inference('sup+', [status(thm)], ['102', '103'])).
% 0.78/0.97  thf('124', plain,
% 0.78/0.97      (![X7 : $i, X8 : $i]:
% 0.78/0.97         ((k4_xboole_0 @ X7 @ X8)
% 0.78/0.97           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.78/0.97      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.78/0.97  thf('125', plain,
% 0.78/0.97      (![X0 : $i]:
% 0.78/0.97         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.78/0.97      inference('sup+', [status(thm)], ['123', '124'])).
% 0.78/0.97  thf('126', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.78/0.97      inference('sup+', [status(thm)], ['122', '125'])).
% 0.78/0.97  thf('127', plain, (((k4_xboole_0 @ sk_C_1 @ sk_B) = (sk_C_1))),
% 0.78/0.97      inference('demod', [status(thm)], ['121', '126'])).
% 0.78/0.97  thf('128', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.78/0.97      inference('simplify', [status(thm)], ['29'])).
% 0.78/0.97  thf('129', plain,
% 0.78/0.97      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.78/0.97         ((r1_xboole_0 @ X9 @ X11)
% 0.78/0.97          | ~ (r1_tarski @ X9 @ (k4_xboole_0 @ X10 @ X11)))),
% 0.78/0.97      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.78/0.97  thf('130', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.78/0.97      inference('sup-', [status(thm)], ['128', '129'])).
% 0.78/0.97  thf('131', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 0.78/0.97      inference('sup+', [status(thm)], ['127', '130'])).
% 0.78/0.97  thf('132', plain,
% 0.78/0.97      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.78/0.97         (~ (r1_tarski @ X27 @ X28)
% 0.78/0.97          | ~ (r1_xboole_0 @ X27 @ X29)
% 0.78/0.97          | (r1_tarski @ X27 @ (k4_xboole_0 @ X28 @ X29)))),
% 0.78/0.97      inference('cnf', [status(esa)], [t86_xboole_1])).
% 0.78/0.97  thf('133', plain,
% 0.78/0.97      (![X0 : $i]:
% 0.78/0.97         ((r1_tarski @ sk_C_1 @ (k4_xboole_0 @ X0 @ sk_B))
% 0.78/0.97          | ~ (r1_tarski @ sk_C_1 @ X0))),
% 0.78/0.97      inference('sup-', [status(thm)], ['131', '132'])).
% 0.78/0.97  thf('134', plain, ((r1_tarski @ sk_C_1 @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.78/0.97      inference('sup-', [status(thm)], ['62', '133'])).
% 0.78/0.97  thf('135', plain,
% 0.78/0.97      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.78/0.97      inference('sup+', [status(thm)], ['46', '49'])).
% 0.78/0.97  thf('136', plain, ((r1_tarski @ sk_C_1 @ (k5_xboole_0 @ sk_A @ sk_B))),
% 0.78/0.97      inference('demod', [status(thm)], ['134', '135'])).
% 0.78/0.97  thf('137', plain, ($false), inference('demod', [status(thm)], ['55', '136'])).
% 0.78/0.97  
% 0.78/0.97  % SZS output end Refutation
% 0.78/0.97  
% 0.78/0.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
