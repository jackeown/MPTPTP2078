%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IlcO8L2NYS

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:49 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 246 expanded)
%              Number of leaves         :   25 (  87 expanded)
%              Depth                    :   15
%              Number of atoms          :  679 (1876 expanded)
%              Number of equality atoms :   72 ( 190 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X20 @ ( k3_subset_1 @ X20 @ X19 ) )
        = X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('3',plain,(
    ! [X12: $i] :
      ( ( k1_subset_1 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X24: $i] :
      ( ( k2_subset_1 @ X24 )
      = ( k3_subset_1 @ X24 @ ( k1_subset_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('5',plain,(
    ! [X13: $i] :
      ( ( k2_subset_1 @ X13 )
      = X13 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('6',plain,(
    ! [X24: $i] :
      ( X24
      = ( k3_subset_1 @ X24 @ ( k1_subset_1 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','7'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('9',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X16 ) @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('10',plain,(
    ! [X13: $i] :
      ( ( k2_subset_1 @ X13 )
      = X13 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('11',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X14 @ X15 )
        = ( k4_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','13'])).

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

thf('16',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X20 @ ( k3_subset_1 @ X20 @ X19 ) )
        = X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('17',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X14 @ X15 )
        = ( k4_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('20',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('23',plain,(
    ! [X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('24',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('26',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X14 @ X15 )
        = ( k4_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('28',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['21','28'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) )
      = ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('31',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B )
    = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('33',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) )
      = ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('35',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('36',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_A ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_A ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['14','39'])).

thf('41',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) )
      = ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('42',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('44',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('46',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('47',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf('53',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) )
      = ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['44','51','56'])).

thf('58',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X13: $i] :
      ( ( k2_subset_1 @ X13 )
      = X13 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('60',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('62',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('65',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) )
      | ( ( k4_subset_1 @ X22 @ X21 @ X23 )
        = ( k2_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) )
      = ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('69',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ( k2_xboole_0 @ sk_B @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['62','69'])).

thf('71',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['57','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IlcO8L2NYS
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:23:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.36/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.54  % Solved by: fo/fo7.sh
% 0.36/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.54  % done 183 iterations in 0.082s
% 0.36/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.54  % SZS output start Refutation
% 0.36/0.54  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.36/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.54  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.36/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.54  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.36/0.54  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.36/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.54  thf(t4_subset_1, axiom,
% 0.36/0.54    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.36/0.54  thf('0', plain,
% 0.36/0.54      (![X25 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X25))),
% 0.36/0.54      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.36/0.54  thf(involutiveness_k3_subset_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.54       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.36/0.54  thf('1', plain,
% 0.36/0.54      (![X19 : $i, X20 : $i]:
% 0.36/0.54         (((k3_subset_1 @ X20 @ (k3_subset_1 @ X20 @ X19)) = (X19))
% 0.36/0.54          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.36/0.54      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.36/0.54  thf('2', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.36/0.54  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.36/0.54  thf('3', plain, (![X12 : $i]: ((k1_subset_1 @ X12) = (k1_xboole_0))),
% 0.36/0.54      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.36/0.54  thf(t22_subset_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.36/0.54  thf('4', plain,
% 0.36/0.54      (![X24 : $i]:
% 0.36/0.54         ((k2_subset_1 @ X24) = (k3_subset_1 @ X24 @ (k1_subset_1 @ X24)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.36/0.54  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.36/0.54  thf('5', plain, (![X13 : $i]: ((k2_subset_1 @ X13) = (X13))),
% 0.36/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.36/0.54  thf('6', plain,
% 0.36/0.54      (![X24 : $i]: ((X24) = (k3_subset_1 @ X24 @ (k1_subset_1 @ X24)))),
% 0.36/0.54      inference('demod', [status(thm)], ['4', '5'])).
% 0.36/0.54  thf('7', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.36/0.54      inference('sup+', [status(thm)], ['3', '6'])).
% 0.36/0.54  thf('8', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.36/0.54      inference('demod', [status(thm)], ['2', '7'])).
% 0.36/0.54  thf(dt_k2_subset_1, axiom,
% 0.36/0.54    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.36/0.54  thf('9', plain,
% 0.36/0.54      (![X16 : $i]: (m1_subset_1 @ (k2_subset_1 @ X16) @ (k1_zfmisc_1 @ X16))),
% 0.36/0.54      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.36/0.54  thf('10', plain, (![X13 : $i]: ((k2_subset_1 @ X13) = (X13))),
% 0.36/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.36/0.54  thf('11', plain, (![X16 : $i]: (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X16))),
% 0.36/0.54      inference('demod', [status(thm)], ['9', '10'])).
% 0.36/0.54  thf(d5_subset_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.54       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.36/0.54  thf('12', plain,
% 0.36/0.54      (![X14 : $i, X15 : $i]:
% 0.36/0.54         (((k3_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))
% 0.36/0.54          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.36/0.54      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.36/0.54  thf('13', plain,
% 0.36/0.54      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.54  thf('14', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.36/0.54      inference('sup+', [status(thm)], ['8', '13'])).
% 0.36/0.54  thf(t25_subset_1, conjecture,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.54       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.36/0.54         ( k2_subset_1 @ A ) ) ))).
% 0.36/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.54    (~( ![A:$i,B:$i]:
% 0.36/0.54        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.54          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.36/0.54            ( k2_subset_1 @ A ) ) ) )),
% 0.36/0.54    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 0.36/0.54  thf('15', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('16', plain,
% 0.36/0.54      (![X19 : $i, X20 : $i]:
% 0.36/0.54         (((k3_subset_1 @ X20 @ (k3_subset_1 @ X20 @ X19)) = (X19))
% 0.36/0.54          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.36/0.54      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.36/0.54  thf('17', plain,
% 0.36/0.54      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.36/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.36/0.54  thf('18', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('19', plain,
% 0.36/0.54      (![X14 : $i, X15 : $i]:
% 0.36/0.54         (((k3_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))
% 0.36/0.54          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.36/0.54      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.36/0.54  thf('20', plain,
% 0.36/0.54      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.36/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.36/0.54  thf('21', plain,
% 0.36/0.54      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.36/0.54      inference('demod', [status(thm)], ['17', '20'])).
% 0.36/0.54  thf('22', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(dt_k3_subset_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.54       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.36/0.54  thf('23', plain,
% 0.36/0.54      (![X17 : $i, X18 : $i]:
% 0.36/0.54         ((m1_subset_1 @ (k3_subset_1 @ X17 @ X18) @ (k1_zfmisc_1 @ X17))
% 0.36/0.54          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.36/0.54      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.36/0.54  thf('24', plain,
% 0.36/0.54      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['22', '23'])).
% 0.36/0.54  thf('25', plain,
% 0.36/0.54      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.36/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.36/0.54  thf('26', plain,
% 0.36/0.54      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['24', '25'])).
% 0.36/0.54  thf('27', plain,
% 0.36/0.54      (![X14 : $i, X15 : $i]:
% 0.36/0.54         (((k3_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))
% 0.36/0.54          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.36/0.54      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.36/0.54  thf('28', plain,
% 0.36/0.54      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.36/0.54         = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['26', '27'])).
% 0.36/0.54  thf('29', plain,
% 0.36/0.54      (((sk_B) = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.36/0.54      inference('sup+', [status(thm)], ['21', '28'])).
% 0.36/0.54  thf(t39_xboole_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.36/0.54  thf('30', plain,
% 0.36/0.54      (![X3 : $i, X4 : $i]:
% 0.36/0.54         ((k2_xboole_0 @ X3 @ (k4_xboole_0 @ X4 @ X3))
% 0.36/0.54           = (k2_xboole_0 @ X3 @ X4))),
% 0.36/0.54      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.36/0.54  thf('31', plain,
% 0.36/0.54      (((k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B)
% 0.36/0.54         = (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A))),
% 0.36/0.54      inference('sup+', [status(thm)], ['29', '30'])).
% 0.36/0.54  thf(commutativity_k2_xboole_0, axiom,
% 0.36/0.54    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.36/0.54  thf('32', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.36/0.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.36/0.54  thf('33', plain,
% 0.36/0.54      (![X3 : $i, X4 : $i]:
% 0.36/0.54         ((k2_xboole_0 @ X3 @ (k4_xboole_0 @ X4 @ X3))
% 0.36/0.54           = (k2_xboole_0 @ X3 @ X4))),
% 0.36/0.54      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.36/0.54  thf('34', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.36/0.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.36/0.54  thf('35', plain,
% 0.36/0.54      (((k2_xboole_0 @ sk_B @ sk_A)
% 0.36/0.54         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.36/0.54      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.36/0.54  thf(t41_xboole_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.36/0.54       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.36/0.54  thf('36', plain,
% 0.36/0.54      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.36/0.54         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 0.36/0.54           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.36/0.54  thf('37', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_A) @ 
% 0.36/0.54           (k4_xboole_0 @ sk_A @ sk_B))
% 0.36/0.54           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.36/0.54      inference('sup+', [status(thm)], ['35', '36'])).
% 0.36/0.54  thf('38', plain,
% 0.36/0.54      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.36/0.54         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 0.36/0.54           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.36/0.54  thf('39', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_A) @ 
% 0.36/0.54           (k4_xboole_0 @ sk_A @ sk_B))
% 0.36/0.54           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['37', '38'])).
% 0.36/0.54  thf('40', plain,
% 0.36/0.54      (((k4_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.36/0.54         = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A))),
% 0.36/0.54      inference('sup+', [status(thm)], ['14', '39'])).
% 0.36/0.54  thf('41', plain,
% 0.36/0.54      (![X3 : $i, X4 : $i]:
% 0.36/0.54         ((k2_xboole_0 @ X3 @ (k4_xboole_0 @ X4 @ X3))
% 0.36/0.54           = (k2_xboole_0 @ X3 @ X4))),
% 0.36/0.54      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.36/0.54  thf('42', plain,
% 0.36/0.54      (((k2_xboole_0 @ sk_A @ 
% 0.36/0.54         (k4_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B)))
% 0.36/0.54         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.36/0.54      inference('sup+', [status(thm)], ['40', '41'])).
% 0.36/0.54  thf('43', plain,
% 0.36/0.54      (((k2_xboole_0 @ sk_B @ sk_A)
% 0.36/0.54         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.36/0.54      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.36/0.54  thf('44', plain,
% 0.36/0.54      (((k2_xboole_0 @ sk_A @ 
% 0.36/0.54         (k4_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B)))
% 0.36/0.54         = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['42', '43'])).
% 0.36/0.54  thf('45', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.36/0.54      inference('sup+', [status(thm)], ['8', '13'])).
% 0.36/0.54  thf(idempotence_k2_xboole_0, axiom,
% 0.36/0.54    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.36/0.54  thf('46', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.36/0.54      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.36/0.54  thf('47', plain,
% 0.36/0.54      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.36/0.54         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 0.36/0.54           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.36/0.54  thf('48', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.36/0.54           = (k4_xboole_0 @ X1 @ X0))),
% 0.36/0.54      inference('sup+', [status(thm)], ['46', '47'])).
% 0.36/0.54  thf('49', plain,
% 0.36/0.54      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.36/0.54      inference('sup+', [status(thm)], ['45', '48'])).
% 0.36/0.54  thf('50', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.36/0.54      inference('sup+', [status(thm)], ['8', '13'])).
% 0.36/0.54  thf('51', plain,
% 0.36/0.54      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.36/0.54      inference('demod', [status(thm)], ['49', '50'])).
% 0.36/0.54  thf('52', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.36/0.54      inference('sup+', [status(thm)], ['8', '13'])).
% 0.36/0.54  thf('53', plain,
% 0.36/0.54      (![X3 : $i, X4 : $i]:
% 0.36/0.54         ((k2_xboole_0 @ X3 @ (k4_xboole_0 @ X4 @ X3))
% 0.36/0.54           = (k2_xboole_0 @ X3 @ X4))),
% 0.36/0.54      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.36/0.54  thf('54', plain,
% 0.36/0.54      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 0.36/0.54      inference('sup+', [status(thm)], ['52', '53'])).
% 0.36/0.54  thf('55', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.36/0.54      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.36/0.54  thf('56', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.36/0.54      inference('demod', [status(thm)], ['54', '55'])).
% 0.36/0.54  thf('57', plain, (((sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['44', '51', '56'])).
% 0.36/0.54  thf('58', plain,
% 0.36/0.54      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.36/0.54         != (k2_subset_1 @ sk_A))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('59', plain, (![X13 : $i]: ((k2_subset_1 @ X13) = (X13))),
% 0.36/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.36/0.54  thf('60', plain,
% 0.36/0.54      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['58', '59'])).
% 0.36/0.54  thf('61', plain,
% 0.36/0.54      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.36/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.36/0.54  thf('62', plain,
% 0.36/0.54      (((k4_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)) != (sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['60', '61'])).
% 0.36/0.54  thf('63', plain,
% 0.36/0.54      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['24', '25'])).
% 0.36/0.54  thf('64', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(redefinition_k4_subset_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.36/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.36/0.54       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.36/0.54  thf('65', plain,
% 0.36/0.54      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.36/0.54          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22))
% 0.36/0.54          | ((k4_subset_1 @ X22 @ X21 @ X23) = (k2_xboole_0 @ X21 @ X23)))),
% 0.36/0.54      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.36/0.54  thf('66', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.36/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['64', '65'])).
% 0.36/0.54  thf('67', plain,
% 0.36/0.54      (((k4_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.36/0.54         = (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['63', '66'])).
% 0.36/0.54  thf('68', plain,
% 0.36/0.54      (![X3 : $i, X4 : $i]:
% 0.36/0.54         ((k2_xboole_0 @ X3 @ (k4_xboole_0 @ X4 @ X3))
% 0.36/0.54           = (k2_xboole_0 @ X3 @ X4))),
% 0.36/0.54      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.36/0.54  thf('69', plain,
% 0.36/0.54      (((k4_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.36/0.54         = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['67', '68'])).
% 0.36/0.54  thf('70', plain, (((k2_xboole_0 @ sk_B @ sk_A) != (sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['62', '69'])).
% 0.36/0.54  thf('71', plain, ($false),
% 0.36/0.54      inference('simplify_reflect-', [status(thm)], ['57', '70'])).
% 0.36/0.54  
% 0.36/0.54  % SZS output end Refutation
% 0.36/0.54  
% 0.40/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
