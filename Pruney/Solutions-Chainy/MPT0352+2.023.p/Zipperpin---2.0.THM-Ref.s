%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5DuoiReOj4

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 437 expanded)
%              Number of leaves         :   22 ( 148 expanded)
%              Depth                    :   17
%              Number of atoms          :  796 (4143 expanded)
%              Number of equality atoms :   46 ( 267 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k4_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k6_subset_1 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k6_subset_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k6_subset_1 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('9',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X17 @ ( k3_subset_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('12',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('15',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k6_subset_1 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('18',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('19',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('20',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k6_subset_1 @ X10 @ ( k6_subset_1 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','20'])).

thf('22',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['12','13','21'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('24',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k6_subset_1 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k6_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,
    ( ~ ( r1_tarski @ ( k6_subset_1 @ sk_A @ sk_C ) @ ( k5_xboole_0 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['1','6','9','26'])).

thf('28',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['12','13','21'])).

thf('30',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('31',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k6_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['30','32'])).

thf('34',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k6_subset_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('35',plain,
    ( ( r1_tarski @ ( k6_subset_1 @ sk_A @ sk_C ) @ ( k6_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('36',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('37',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('38',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) )
      | ~ ( r1_tarski @ ( k6_subset_1 @ X7 @ X8 ) @ X9 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('41',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X6 )
      | ~ ( r1_tarski @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('42',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('43',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X4 @ X5 ) @ X6 )
      | ~ ( r1_tarski @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k6_subset_1 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,
    ( ( r1_tarski @ ( k6_subset_1 @ sk_A @ ( k6_subset_1 @ sk_A @ sk_B ) ) @ sk_C )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k6_subset_1 @ X10 @ ( k6_subset_1 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('47',plain,
    ( ( r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_C )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['29','47'])).

thf('49',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C )
   <= ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('50',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['28','50'])).

thf('52',plain,(
    ~ ( r1_tarski @ ( k6_subset_1 @ sk_A @ sk_C ) @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['27','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X17 @ ( k3_subset_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('55',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k6_subset_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','20'])).

thf('58',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k6_subset_1 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('60',plain,
    ( ( k6_subset_1 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C ) @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','60'])).

thf('62',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['31'])).

thf('63',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['31'])).

thf('64',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference('sat_resolution*',[status(thm)],['28','50','63'])).

thf('65',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(simpl_trail,[status(thm)],['62','64'])).

thf('66',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['12','13','21'])).

thf('67',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k6_subset_1 @ X10 @ ( k6_subset_1 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('68',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) )
      | ~ ( r1_tarski @ ( k6_subset_1 @ X7 @ X8 ) @ X9 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ ( k6_subset_1 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ ( k2_xboole_0 @ ( k6_subset_1 @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,
    ( ( k6_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ ( k2_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['65','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('75',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_C @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X4 @ X5 ) @ X6 )
      | ~ ( r1_tarski @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('77',plain,(
    r1_tarski @ ( k6_subset_1 @ sk_A @ sk_C ) @ ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k6_subset_1 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('79',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C ) @ ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    $false ),
    inference(demod,[status(thm)],['61','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5DuoiReOj4
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:44:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 100 iterations in 0.042s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(t31_subset_1, conjecture,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.51       ( ![C:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.51           ( ( r1_tarski @ B @ C ) <=>
% 0.21/0.51             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i]:
% 0.21/0.51        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.51          ( ![C:$i]:
% 0.21/0.51            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.51              ( ( r1_tarski @ B @ C ) <=>
% 0.21/0.51                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t31_subset_1])).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.21/0.51           (k3_subset_1 @ sk_A @ sk_B))
% 0.21/0.51        | ~ (r1_tarski @ sk_B @ sk_C))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.21/0.51           (k3_subset_1 @ sk_A @ sk_B)))
% 0.21/0.51         <= (~
% 0.21/0.51             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.21/0.51               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('2', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(d5_subset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.51       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i]:
% 0.21/0.51         (((k3_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))
% 0.21/0.51          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.51  thf(redefinition_k6_subset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X18 : $i, X19 : $i]:
% 0.21/0.51         ((k6_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i]:
% 0.21/0.51         (((k3_subset_1 @ X12 @ X13) = (k6_subset_1 @ X12 @ X13))
% 0.21/0.51          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.21/0.51      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (((k3_subset_1 @ sk_A @ sk_C) = (k6_subset_1 @ sk_A @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '5'])).
% 0.21/0.51  thf('7', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i]:
% 0.21/0.51         (((k3_subset_1 @ X12 @ X13) = (k6_subset_1 @ X12 @ X13))
% 0.21/0.51          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.21/0.51      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (((k3_subset_1 @ sk_A @ sk_B) = (k6_subset_1 @ sk_A @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf('10', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(involutiveness_k3_subset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.51       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X16 : $i, X17 : $i]:
% 0.21/0.51         (((k3_subset_1 @ X17 @ (k3_subset_1 @ X17 @ X16)) = (X16))
% 0.21/0.51          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.21/0.51      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (((k3_subset_1 @ sk_A @ sk_B) = (k6_subset_1 @ sk_A @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf(dt_k6_subset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X14 : $i, X15 : $i]:
% 0.21/0.51         (m1_subset_1 @ (k6_subset_1 @ X14 @ X15) @ (k1_zfmisc_1 @ X14))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i]:
% 0.21/0.51         (((k3_subset_1 @ X12 @ X13) = (k6_subset_1 @ X12 @ X13))
% 0.21/0.51          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.21/0.51      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 0.21/0.51           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.51  thf(t48_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i]:
% 0.21/0.51         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.21/0.51           = (k3_xboole_0 @ X10 @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X18 : $i, X19 : $i]:
% 0.21/0.51         ((k6_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (![X18 : $i, X19 : $i]:
% 0.21/0.51         ((k6_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i]:
% 0.21/0.51         ((k6_subset_1 @ X10 @ (k6_subset_1 @ X10 @ X11))
% 0.21/0.51           = (k3_xboole_0 @ X10 @ X11))),
% 0.21/0.51      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 0.21/0.51           = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('demod', [status(thm)], ['16', '20'])).
% 0.21/0.51  thf('22', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['12', '13', '21'])).
% 0.21/0.51  thf(t100_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      (![X2 : $i, X3 : $i]:
% 0.21/0.51         ((k4_xboole_0 @ X2 @ X3)
% 0.21/0.51           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (![X18 : $i, X19 : $i]:
% 0.21/0.51         ((k6_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (![X2 : $i, X3 : $i]:
% 0.21/0.51         ((k6_subset_1 @ X2 @ X3)
% 0.21/0.51           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.21/0.51      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (((k6_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.51      inference('sup+', [status(thm)], ['22', '25'])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      ((~ (r1_tarski @ (k6_subset_1 @ sk_A @ sk_C) @ 
% 0.21/0.51           (k5_xboole_0 @ sk_A @ sk_B)))
% 0.21/0.51         <= (~
% 0.21/0.51             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.21/0.51               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.21/0.51      inference('demod', [status(thm)], ['1', '6', '9', '26'])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (~
% 0.21/0.51       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.21/0.51       ~ ((r1_tarski @ sk_B @ sk_C))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('29', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['12', '13', '21'])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      (((k3_subset_1 @ sk_A @ sk_B) = (k6_subset_1 @ sk_A @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B))
% 0.21/0.51        | (r1_tarski @ sk_B @ sk_C))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.21/0.51         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.21/0.51               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.21/0.51      inference('split', [status(esa)], ['31'])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k6_subset_1 @ sk_A @ sk_B)))
% 0.21/0.51         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.21/0.51               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.21/0.51      inference('sup+', [status(thm)], ['30', '32'])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      (((k3_subset_1 @ sk_A @ sk_C) = (k6_subset_1 @ sk_A @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '5'])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      (((r1_tarski @ (k6_subset_1 @ sk_A @ sk_C) @ (k6_subset_1 @ sk_A @ sk_B)))
% 0.21/0.51         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.21/0.51               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.21/0.51      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.51  thf(t44_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.21/0.51       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.51         ((r1_tarski @ X7 @ (k2_xboole_0 @ X8 @ X9))
% 0.21/0.51          | ~ (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      (![X18 : $i, X19 : $i]:
% 0.21/0.51         ((k6_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.51         ((r1_tarski @ X7 @ (k2_xboole_0 @ X8 @ X9))
% 0.21/0.51          | ~ (r1_tarski @ (k6_subset_1 @ X7 @ X8) @ X9))),
% 0.21/0.51      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B))))
% 0.21/0.51         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.21/0.51               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['35', '38'])).
% 0.21/0.51  thf(commutativity_k2_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.21/0.51  thf('40', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.51  thf(t43_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.21/0.51       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.21/0.51  thf('41', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.51         ((r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X6)
% 0.21/0.51          | ~ (r1_tarski @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      (![X18 : $i, X19 : $i]:
% 0.21/0.51         ((k6_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.51         ((r1_tarski @ (k6_subset_1 @ X4 @ X5) @ X6)
% 0.21/0.51          | ~ (r1_tarski @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.21/0.51      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.51  thf('44', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.21/0.51          | (r1_tarski @ (k6_subset_1 @ X2 @ X0) @ X1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['40', '43'])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      (((r1_tarski @ (k6_subset_1 @ sk_A @ (k6_subset_1 @ sk_A @ sk_B)) @ sk_C))
% 0.21/0.51         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.21/0.51               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['39', '44'])).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i]:
% 0.21/0.51         ((k6_subset_1 @ X10 @ (k6_subset_1 @ X10 @ X11))
% 0.21/0.51           = (k3_xboole_0 @ X10 @ X11))),
% 0.21/0.51      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      (((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_C))
% 0.21/0.51         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.21/0.51               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.21/0.51      inference('demod', [status(thm)], ['45', '46'])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      (((r1_tarski @ sk_B @ sk_C))
% 0.21/0.51         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.21/0.51               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.21/0.51      inference('sup+', [status(thm)], ['29', '47'])).
% 0.21/0.51  thf('49', plain,
% 0.21/0.51      ((~ (r1_tarski @ sk_B @ sk_C)) <= (~ ((r1_tarski @ sk_B @ sk_C)))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('50', plain,
% 0.21/0.51      (((r1_tarski @ sk_B @ sk_C)) | 
% 0.21/0.51       ~
% 0.21/0.51       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.51  thf('51', plain,
% 0.21/0.51      (~
% 0.21/0.51       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['28', '50'])).
% 0.21/0.51  thf('52', plain,
% 0.21/0.51      (~ (r1_tarski @ (k6_subset_1 @ sk_A @ sk_C) @ (k5_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['27', '51'])).
% 0.21/0.51  thf('53', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('54', plain,
% 0.21/0.51      (![X16 : $i, X17 : $i]:
% 0.21/0.51         (((k3_subset_1 @ X17 @ (k3_subset_1 @ X17 @ X16)) = (X16))
% 0.21/0.51          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.21/0.51      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.21/0.51  thf('55', plain,
% 0.21/0.51      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)) = (sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.51  thf('56', plain,
% 0.21/0.51      (((k3_subset_1 @ sk_A @ sk_C) = (k6_subset_1 @ sk_A @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '5'])).
% 0.21/0.51  thf('57', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 0.21/0.51           = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('demod', [status(thm)], ['16', '20'])).
% 0.21/0.51  thf('58', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (sk_C))),
% 0.21/0.51      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.21/0.51  thf('59', plain,
% 0.21/0.51      (![X2 : $i, X3 : $i]:
% 0.21/0.51         ((k6_subset_1 @ X2 @ X3)
% 0.21/0.51           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.21/0.51      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.51  thf('60', plain,
% 0.21/0.51      (((k6_subset_1 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 0.21/0.51      inference('sup+', [status(thm)], ['58', '59'])).
% 0.21/0.51  thf('61', plain,
% 0.21/0.51      (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C) @ (k5_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['52', '60'])).
% 0.21/0.51  thf('62', plain,
% 0.21/0.51      (((r1_tarski @ sk_B @ sk_C)) <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.21/0.51      inference('split', [status(esa)], ['31'])).
% 0.21/0.51  thf('63', plain,
% 0.21/0.51      (((r1_tarski @ sk_B @ sk_C)) | 
% 0.21/0.51       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.21/0.51      inference('split', [status(esa)], ['31'])).
% 0.21/0.51  thf('64', plain, (((r1_tarski @ sk_B @ sk_C))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['28', '50', '63'])).
% 0.21/0.51  thf('65', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['62', '64'])).
% 0.21/0.51  thf('66', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['12', '13', '21'])).
% 0.21/0.51  thf('67', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i]:
% 0.21/0.51         ((k6_subset_1 @ X10 @ (k6_subset_1 @ X10 @ X11))
% 0.21/0.51           = (k3_xboole_0 @ X10 @ X11))),
% 0.21/0.51      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.21/0.51  thf('68', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.51         ((r1_tarski @ X7 @ (k2_xboole_0 @ X8 @ X9))
% 0.21/0.51          | ~ (r1_tarski @ (k6_subset_1 @ X7 @ X8) @ X9))),
% 0.21/0.51      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.51  thf('69', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.21/0.51          | (r1_tarski @ X1 @ (k2_xboole_0 @ (k6_subset_1 @ X1 @ X0) @ X2)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.51  thf('70', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (r1_tarski @ sk_B @ X0)
% 0.21/0.51          | (r1_tarski @ sk_A @ 
% 0.21/0.51             (k2_xboole_0 @ (k6_subset_1 @ sk_A @ sk_B) @ X0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['66', '69'])).
% 0.21/0.51  thf('71', plain,
% 0.21/0.51      (((k6_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.51      inference('sup+', [status(thm)], ['22', '25'])).
% 0.21/0.51  thf('72', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (r1_tarski @ sk_B @ X0)
% 0.21/0.51          | (r1_tarski @ sk_A @ 
% 0.21/0.51             (k2_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ X0)))),
% 0.21/0.51      inference('demod', [status(thm)], ['70', '71'])).
% 0.21/0.51  thf('73', plain,
% 0.21/0.51      ((r1_tarski @ sk_A @ (k2_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['65', '72'])).
% 0.21/0.51  thf('74', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.51  thf('75', plain,
% 0.21/0.51      ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_C @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.51      inference('demod', [status(thm)], ['73', '74'])).
% 0.21/0.51  thf('76', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.51         ((r1_tarski @ (k6_subset_1 @ X4 @ X5) @ X6)
% 0.21/0.51          | ~ (r1_tarski @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.21/0.51      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.51  thf('77', plain,
% 0.21/0.51      ((r1_tarski @ (k6_subset_1 @ sk_A @ sk_C) @ (k5_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['75', '76'])).
% 0.21/0.51  thf('78', plain,
% 0.21/0.51      (((k6_subset_1 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 0.21/0.51      inference('sup+', [status(thm)], ['58', '59'])).
% 0.21/0.51  thf('79', plain,
% 0.21/0.51      ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C) @ (k5_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['77', '78'])).
% 0.21/0.51  thf('80', plain, ($false), inference('demod', [status(thm)], ['61', '79'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
