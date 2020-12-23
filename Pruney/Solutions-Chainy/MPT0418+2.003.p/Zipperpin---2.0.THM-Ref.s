%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EA8z4NhhqA

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 208 expanded)
%              Number of leaves         :   18 (  70 expanded)
%              Depth                    :   12
%              Number of atoms          :  871 (2227 expanded)
%              Number of equality atoms :   24 (  56 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t49_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r2_hidden @ ( k3_subset_1 @ A @ C ) @ ( k7_setfam_1 @ A @ B ) )
          <=> ( r2_hidden @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r2_hidden @ ( k3_subset_1 @ A @ C ) @ ( k7_setfam_1 @ A @ B ) )
            <=> ( r2_hidden @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_setfam_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_B )
    | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_B )
    | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
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
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k4_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('4',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_C @ sk_B )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ ( k4_xboole_0 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X5 @ ( k3_subset_1 @ X5 @ X4 ) )
        = X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('10',plain,
    ( ( k3_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ ( k3_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k4_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('13',plain,
    ( ( k3_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k4_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k4_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['10','13','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('21',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k7_setfam_1 @ X0 @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ X1 ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(d8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( C
              = ( k7_setfam_1 @ A @ B ) )
          <=> ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
               => ( ( r2_hidden @ D @ C )
                <=> ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) )).

thf('23',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X7 ) ) )
      | ( X6
       != ( k7_setfam_1 @ X7 @ X8 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X7 @ X9 ) @ X8 )
      | ~ ( r2_hidden @ X9 @ X6 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('24',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r2_hidden @ X9 @ ( k7_setfam_1 @ X7 @ X8 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X7 @ X9 ) @ X8 )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ X0 @ X2 ) @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ X1 ) )
      | ~ ( r2_hidden @ X2 @ ( k7_setfam_1 @ X0 @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ X1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ X0 @ X2 ) @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ X1 ) )
      | ~ ( r2_hidden @ X2 @ ( k7_setfam_1 @ X0 @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k7_setfam_1 @ X0 @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ X1 ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('29',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( m1_subset_1 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k7_setfam_1 @ X0 @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k7_setfam_1 @ X0 @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ X1 ) ) )
      | ( r2_hidden @ ( k3_subset_1 @ X0 @ X2 ) @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ X1 ) ) ) ),
    inference(clc,[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['19','31'])).

thf('33',plain,
    ( ( k4_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['10','13','18'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C ) ) @ sk_B )
   <= ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X5 @ ( k3_subset_1 @ X5 @ X4 ) )
        = X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('39',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('42',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( r2_hidden @ sk_C @ sk_B )
   <= ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','36','42'])).

thf('44',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_B )
   <= ~ ( r2_hidden @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,
    ( ( r2_hidden @ sk_C @ sk_B )
    | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( r2_hidden @ sk_C @ sk_B )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('47',plain,
    ( ( r2_hidden @ sk_C @ sk_B )
   <= ( r2_hidden @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('48',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('52',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X7 ) ) )
      | ( X6
       != ( k7_setfam_1 @ X7 @ X8 ) )
      | ( r2_hidden @ X9 @ X6 )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X7 @ X9 ) @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('54',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X7 @ X9 ) @ X8 )
      | ( r2_hidden @ X9 @ ( k7_setfam_1 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ X0 ) ) @ sk_B )
      | ~ ( m1_subset_1 @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r2_hidden @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['49','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ X0 ) ) @ sk_B )
      | ( r2_hidden @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_B )
    | ( r2_hidden @ ( k4_xboole_0 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','60'])).

thf('62',plain,
    ( ( r2_hidden @ ( k4_xboole_0 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['47','61'])).

thf('63',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('64',plain,
    ( ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) )
   <= ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('65',plain,
    ( ~ ( r2_hidden @ ( k4_xboole_0 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) )
   <= ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_B )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','45','46','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EA8z4NhhqA
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:12:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 177 iterations in 0.079s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(t49_setfam_1, conjecture,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.53       ( ![C:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53           ( ( r2_hidden @ ( k3_subset_1 @ A @ C ) @ ( k7_setfam_1 @ A @ B ) ) <=>
% 0.20/0.53             ( r2_hidden @ C @ B ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i]:
% 0.20/0.53        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.53          ( ![C:$i]:
% 0.20/0.53            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53              ( ( r2_hidden @ ( k3_subset_1 @ A @ C ) @ ( k7_setfam_1 @ A @ B ) ) <=>
% 0.20/0.53                ( r2_hidden @ C @ B ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t49_setfam_1])).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      ((~ (r2_hidden @ sk_C @ sk_B)
% 0.20/0.53        | ~ (r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.20/0.53             (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (~ ((r2_hidden @ sk_C @ sk_B)) | 
% 0.20/0.53       ~
% 0.20/0.53       ((r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('2', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(d5_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X2 : $i, X3 : $i]:
% 0.20/0.53         (((k3_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))
% 0.20/0.53          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (((r2_hidden @ sk_C @ sk_B)
% 0.20/0.53        | (r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.20/0.53           (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (((r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ (k7_setfam_1 @ sk_A @ sk_B)))
% 0.20/0.53         <= (((r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.20/0.53               (k7_setfam_1 @ sk_A @ sk_B))))),
% 0.20/0.53      inference('split', [status(esa)], ['5'])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (((r2_hidden @ (k4_xboole_0 @ sk_A @ sk_C) @ (k7_setfam_1 @ sk_A @ sk_B)))
% 0.20/0.53         <= (((r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.20/0.53               (k7_setfam_1 @ sk_A @ sk_B))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['4', '6'])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(involutiveness_k3_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (![X4 : $i, X5 : $i]:
% 0.20/0.53         (((k3_subset_1 @ X5 @ (k3_subset_1 @ X5 @ X4)) = (X4))
% 0.20/0.53          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.20/0.53      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (((k3_subset_1 @ (k1_zfmisc_1 @ sk_A) @ 
% 0.20/0.53         (k3_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B)) = (sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (![X2 : $i, X3 : $i]:
% 0.20/0.53         (((k3_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))
% 0.20/0.53          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (((k3_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B)
% 0.20/0.53         = (k4_xboole_0 @ (k1_zfmisc_1 @ sk_A) @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.53  thf(t36_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.20/0.53      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.20/0.53  thf(t3_subset, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X12 : $i, X14 : $i]:
% 0.20/0.53         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (![X2 : $i, X3 : $i]:
% 0.20/0.53         (((k3_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))
% 0.20/0.53          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.20/0.53           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (((k4_xboole_0 @ (k1_zfmisc_1 @ sk_A) @ 
% 0.20/0.53         (k4_xboole_0 @ (k1_zfmisc_1 @ sk_A) @ sk_B)) = (sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['10', '13', '18'])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.53  thf(dt_k7_setfam_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.53       ( m1_subset_1 @
% 0.20/0.53         ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (![X10 : $i, X11 : $i]:
% 0.20/0.53         ((m1_subset_1 @ (k7_setfam_1 @ X10 @ X11) @ 
% 0.20/0.53           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10)))
% 0.20/0.53          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10))))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (m1_subset_1 @ 
% 0.20/0.53          (k7_setfam_1 @ X0 @ (k4_xboole_0 @ (k1_zfmisc_1 @ X0) @ X1)) @ 
% 0.20/0.53          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf(d8_setfam_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.53       ( ![C:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.53           ( ( ( C ) = ( k7_setfam_1 @ A @ B ) ) <=>
% 0.20/0.53             ( ![D:$i]:
% 0.20/0.53               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53                 ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.53                   ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X7)))
% 0.20/0.53          | ((X6) != (k7_setfam_1 @ X7 @ X8))
% 0.20/0.53          | (r2_hidden @ (k3_subset_1 @ X7 @ X9) @ X8)
% 0.20/0.53          | ~ (r2_hidden @ X9 @ X6)
% 0.20/0.53          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X7))
% 0.20/0.53          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X7))))),
% 0.20/0.53      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X7)))
% 0.20/0.53          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X7))
% 0.20/0.53          | ~ (r2_hidden @ X9 @ (k7_setfam_1 @ X7 @ X8))
% 0.20/0.53          | (r2_hidden @ (k3_subset_1 @ X7 @ X9) @ X8)
% 0.20/0.53          | ~ (m1_subset_1 @ (k7_setfam_1 @ X7 @ X8) @ 
% 0.20/0.53               (k1_zfmisc_1 @ (k1_zfmisc_1 @ X7))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((r2_hidden @ (k3_subset_1 @ X0 @ X2) @ 
% 0.20/0.53           (k4_xboole_0 @ (k1_zfmisc_1 @ X0) @ X1))
% 0.20/0.53          | ~ (r2_hidden @ X2 @ 
% 0.20/0.53               (k7_setfam_1 @ X0 @ (k4_xboole_0 @ (k1_zfmisc_1 @ X0) @ X1)))
% 0.20/0.53          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0))
% 0.20/0.53          | ~ (m1_subset_1 @ (k4_xboole_0 @ (k1_zfmisc_1 @ X0) @ X1) @ 
% 0.20/0.53               (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['22', '24'])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((r2_hidden @ (k3_subset_1 @ X0 @ X2) @ 
% 0.20/0.53           (k4_xboole_0 @ (k1_zfmisc_1 @ X0) @ X1))
% 0.20/0.53          | ~ (r2_hidden @ X2 @ 
% 0.20/0.53               (k7_setfam_1 @ X0 @ (k4_xboole_0 @ (k1_zfmisc_1 @ X0) @ X1)))
% 0.20/0.53          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (m1_subset_1 @ 
% 0.20/0.53          (k7_setfam_1 @ X0 @ (k4_xboole_0 @ (k1_zfmisc_1 @ X0) @ X1)) @ 
% 0.20/0.53          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf(t4_subset, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.20/0.53       ( m1_subset_1 @ A @ C ) ))).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X15 @ X16)
% 0.20/0.53          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.20/0.53          | (m1_subset_1 @ X15 @ X17))),
% 0.20/0.53      inference('cnf', [status(esa)], [t4_subset])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0))
% 0.20/0.53          | ~ (r2_hidden @ X2 @ 
% 0.20/0.53               (k7_setfam_1 @ X0 @ (k4_xboole_0 @ (k1_zfmisc_1 @ X0) @ X1))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X2 @ 
% 0.20/0.53             (k7_setfam_1 @ X0 @ (k4_xboole_0 @ (k1_zfmisc_1 @ X0) @ X1)))
% 0.20/0.53          | (r2_hidden @ (k3_subset_1 @ X0 @ X2) @ 
% 0.20/0.53             (k4_xboole_0 @ (k1_zfmisc_1 @ X0) @ X1)))),
% 0.20/0.53      inference('clc', [status(thm)], ['27', '30'])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X0 @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.20/0.53          | (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ 
% 0.20/0.53             (k4_xboole_0 @ (k1_zfmisc_1 @ sk_A) @ 
% 0.20/0.53              (k4_xboole_0 @ (k1_zfmisc_1 @ sk_A) @ sk_B))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['19', '31'])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      (((k4_xboole_0 @ (k1_zfmisc_1 @ sk_A) @ 
% 0.20/0.53         (k4_xboole_0 @ (k1_zfmisc_1 @ sk_A) @ sk_B)) = (sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['10', '13', '18'])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X0 @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.20/0.53          | (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      (((r2_hidden @ (k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C)) @ sk_B))
% 0.20/0.53         <= (((r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.20/0.53               (k7_setfam_1 @ sk_A @ sk_B))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['7', '34'])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.20/0.53           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.53  thf('37', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      (![X4 : $i, X5 : $i]:
% 0.20/0.53         (((k3_subset_1 @ X5 @ (k3_subset_1 @ X5 @ X4)) = (X4))
% 0.20/0.53          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.20/0.53      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)) = (sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.20/0.53           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C)) = (sk_C))),
% 0.20/0.53      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      (((r2_hidden @ sk_C @ sk_B))
% 0.20/0.53         <= (((r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.20/0.53               (k7_setfam_1 @ sk_A @ sk_B))))),
% 0.20/0.53      inference('demod', [status(thm)], ['35', '36', '42'])).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      ((~ (r2_hidden @ sk_C @ sk_B)) <= (~ ((r2_hidden @ sk_C @ sk_B)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      (((r2_hidden @ sk_C @ sk_B)) | 
% 0.20/0.53       ~
% 0.20/0.53       ((r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      (((r2_hidden @ sk_C @ sk_B)) | 
% 0.20/0.53       ((r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('split', [status(esa)], ['5'])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      (((r2_hidden @ sk_C @ sk_B)) <= (((r2_hidden @ sk_C @ sk_B)))),
% 0.20/0.53      inference('split', [status(esa)], ['5'])).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C)) = (sk_C))),
% 0.20/0.53      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.20/0.53  thf('49', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.20/0.53           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('51', plain,
% 0.20/0.53      (![X10 : $i, X11 : $i]:
% 0.20/0.53         ((m1_subset_1 @ (k7_setfam_1 @ X10 @ X11) @ 
% 0.20/0.53           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10)))
% 0.20/0.53          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10))))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.20/0.53  thf('52', plain,
% 0.20/0.53      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B) @ 
% 0.20/0.53        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.53  thf('53', plain,
% 0.20/0.53      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X7)))
% 0.20/0.53          | ((X6) != (k7_setfam_1 @ X7 @ X8))
% 0.20/0.53          | (r2_hidden @ X9 @ X6)
% 0.20/0.53          | ~ (r2_hidden @ (k3_subset_1 @ X7 @ X9) @ X8)
% 0.20/0.53          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X7))
% 0.20/0.53          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X7))))),
% 0.20/0.53      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.20/0.53  thf('54', plain,
% 0.20/0.53      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X7)))
% 0.20/0.53          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X7))
% 0.20/0.53          | ~ (r2_hidden @ (k3_subset_1 @ X7 @ X9) @ X8)
% 0.20/0.53          | (r2_hidden @ X9 @ (k7_setfam_1 @ X7 @ X8))
% 0.20/0.53          | ~ (m1_subset_1 @ (k7_setfam_1 @ X7 @ X8) @ 
% 0.20/0.53               (k1_zfmisc_1 @ (k1_zfmisc_1 @ X7))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['53'])).
% 0.20/0.53  thf('55', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r2_hidden @ X0 @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.20/0.53          | ~ (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ sk_B)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.53          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['52', '54'])).
% 0.20/0.53  thf('56', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('57', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r2_hidden @ X0 @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.20/0.53          | ~ (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ sk_B)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['55', '56'])).
% 0.20/0.53  thf('58', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r2_hidden @ (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ X0)) @ 
% 0.20/0.53             sk_B)
% 0.20/0.53          | ~ (m1_subset_1 @ (k4_xboole_0 @ sk_A @ X0) @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.53          | (r2_hidden @ (k4_xboole_0 @ sk_A @ X0) @ 
% 0.20/0.53             (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['49', '57'])).
% 0.20/0.53  thf('59', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.53  thf('60', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r2_hidden @ (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ X0)) @ 
% 0.20/0.53             sk_B)
% 0.20/0.53          | (r2_hidden @ (k4_xboole_0 @ sk_A @ X0) @ 
% 0.20/0.53             (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['58', '59'])).
% 0.20/0.53  thf('61', plain,
% 0.20/0.53      ((~ (r2_hidden @ sk_C @ sk_B)
% 0.20/0.53        | (r2_hidden @ (k4_xboole_0 @ sk_A @ sk_C) @ 
% 0.20/0.53           (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['48', '60'])).
% 0.20/0.53  thf('62', plain,
% 0.20/0.53      (((r2_hidden @ (k4_xboole_0 @ sk_A @ sk_C) @ (k7_setfam_1 @ sk_A @ sk_B)))
% 0.20/0.53         <= (((r2_hidden @ sk_C @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['47', '61'])).
% 0.20/0.53  thf('63', plain,
% 0.20/0.53      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf('64', plain,
% 0.20/0.53      ((~ (r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.20/0.53           (k7_setfam_1 @ sk_A @ sk_B)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.20/0.53               (k7_setfam_1 @ sk_A @ sk_B))))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('65', plain,
% 0.20/0.53      ((~ (r2_hidden @ (k4_xboole_0 @ sk_A @ sk_C) @ 
% 0.20/0.53           (k7_setfam_1 @ sk_A @ sk_B)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.20/0.53               (k7_setfam_1 @ sk_A @ sk_B))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.53  thf('66', plain,
% 0.20/0.53      (~ ((r2_hidden @ sk_C @ sk_B)) | 
% 0.20/0.53       ((r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['62', '65'])).
% 0.20/0.53  thf('67', plain, ($false),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['1', '45', '46', '66'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
