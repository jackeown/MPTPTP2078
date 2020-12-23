%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JZKIBT5SbH

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:52 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  158 (4413 expanded)
%              Number of leaves         :   27 (1313 expanded)
%              Depth                    :   19
%              Number of atoms          : 1285 (34931 expanded)
%              Number of equality atoms :  130 (2681 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t23_pre_topc,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ~ ( ( B
                 != ( k2_struct_0 @ A ) )
                & ( ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B )
                  = k1_xboole_0 ) )
            & ~ ( ( ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B )
                 != k1_xboole_0 )
                & ( B
                  = ( k2_struct_0 @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ~ ( ( B
                   != ( k2_struct_0 @ A ) )
                  & ( ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B )
                    = k1_xboole_0 ) )
              & ~ ( ( ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B )
                   != k1_xboole_0 )
                  & ( B
                    = ( k2_struct_0 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_pre_topc])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('2',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf(t18_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) )
            = ( k2_struct_0 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( ( k4_subset_1 @ ( u1_struct_0 @ X30 ) @ X29 @ ( k3_subset_1 @ ( u1_struct_0 @ X30 ) @ X29 ) )
        = ( k2_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t18_pre_topc])).

thf('8',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X16 @ ( k3_subset_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('12',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('14',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_B )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9','14'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X26: $i,X28: $i] :
      ( ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( r1_tarski @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( ( k4_subset_1 @ ( u1_struct_0 @ X30 ) @ X29 @ ( k3_subset_1 @ ( u1_struct_0 @ X30 ) @ X29 ) )
        = ( k2_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t18_pre_topc])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k4_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('23',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('26',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('27',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) )
      | ( ( k4_subset_1 @ X18 @ X17 @ X19 )
        = ( k2_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ X0 @ X0 @ X1 )
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ X0 @ X0 @ X0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(idempotence_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ B )
        = B ) ) )).

thf('31',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k4_subset_1 @ X13 @ X12 @ X12 )
        = X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[idempotence_k4_subset_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ X1 @ X0 @ X0 )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(condensation,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ X0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['29','33'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('35',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X3 @ X4 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('39',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('42',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('44',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ X0 @ X0 @ X1 )
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ X0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('48',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(commutativity_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k4_subset_1 @ A @ C @ B ) ) ) )).

thf('49',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) )
      | ( ( k4_subset_1 @ X6 @ X5 @ X7 )
        = ( k4_subset_1 @ X6 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k4_subset_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ X0 @ k1_xboole_0 @ X1 )
        = ( k4_subset_1 @ X0 @ X1 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ X0 @ k1_xboole_0 @ X0 )
      = ( k4_subset_1 @ X0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ X0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ X0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('55',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('56',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) )
      | ( ( k4_subset_1 @ X18 @ X17 @ X19 )
        = ( k2_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ X0 @ k1_xboole_0 @ X1 )
        = ( k2_xboole_0 @ k1_xboole_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ X0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_xboole_0 @ k1_xboole_0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','37','46','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','58'])).

thf('62',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('63',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(t33_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) )
            = ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) )).

thf('64',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( ( k3_subset_1 @ X24 @ ( k7_subset_1 @ X24 @ X25 @ X23 ) )
        = ( k4_subset_1 @ X24 @ ( k3_subset_1 @ X24 @ X25 ) @ X23 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t33_subset_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k3_subset_1 @ X0 @ ( k7_subset_1 @ X0 @ X1 @ k1_xboole_0 ) )
        = ( k4_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X1 ) @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k7_subset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) )
      = ( k4_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('68',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k7_subset_1 @ X21 @ X20 @ X22 )
        = ( k4_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ k1_xboole_0 @ X1 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('71',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X16 @ ( k3_subset_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('76',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['74','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('80',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ X0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['66','69','80','83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['61','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','88'])).

thf('90',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['12','13'])).

thf('91',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = sk_B )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','88'])).

thf('95',plain,
    ( ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = k1_xboole_0 )
    | ( sk_B
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['95'])).

thf('97',plain,
    ( ( sk_B
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( sk_B
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['97'])).

thf('99',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k7_subset_1 @ X21 @ X20 @ X22 )
        = ( k4_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( sk_B
      = ( k2_struct_0 @ sk_A ) )
   <= ( sk_B
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['95'])).

thf('103',plain,
    ( ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B )
     != k1_xboole_0 )
   <= ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['97'])).

thf('104',plain,
    ( ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_B )
     != k1_xboole_0 )
   <= ( ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B )
       != k1_xboole_0 )
      & ( sk_B
        = ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_B )
     != k1_xboole_0 )
   <= ( ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B )
       != k1_xboole_0 )
      & ( sk_B
        = ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['101','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('107',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B )
       != k1_xboole_0 )
      & ( sk_B
        = ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = k1_xboole_0 )
    | ( sk_B
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,
    ( ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = k1_xboole_0 )
    | ( sk_B
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['95'])).

thf('110',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['98','108','109'])).

thf('111',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['96','110'])).

thf('112',plain,
    ( ( ( k7_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['94','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('114',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k7_subset_1 @ X21 @ X20 @ X22 )
        = ( k4_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['112','115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('119',plain,
    ( ( u1_struct_0 @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['93','117','118'])).

thf('120',plain,
    ( ( u1_struct_0 @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['93','117','118'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ X0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ X0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
    ( sk_B
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','119','120','121','124'])).

thf('126',plain,
    ( ( sk_B
     != ( k2_struct_0 @ sk_A ) )
   <= ( sk_B
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['97'])).

thf('127',plain,(
    sk_B
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['98','108'])).

thf('128',plain,(
    sk_B
 != ( k2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['126','127'])).

thf('129',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['125','128'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JZKIBT5SbH
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:06:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 212 iterations in 0.073s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.52  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.22/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.52  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.52  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.22/0.52  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.22/0.52  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.22/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(t23_pre_topc, conjecture,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( l1_struct_0 @ A ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52           ( ( ~( ( ( B ) != ( k2_struct_0 @ A ) ) & 
% 0.22/0.52                  ( ( k7_subset_1 @
% 0.22/0.52                      ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) =
% 0.22/0.52                    ( k1_xboole_0 ) ) ) ) & 
% 0.22/0.52             ( ~( ( ( k7_subset_1 @
% 0.22/0.52                      ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) !=
% 0.22/0.52                    ( k1_xboole_0 ) ) & 
% 0.22/0.52                  ( ( B ) = ( k2_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i]:
% 0.22/0.52        ( ( l1_struct_0 @ A ) =>
% 0.22/0.52          ( ![B:$i]:
% 0.22/0.52            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52              ( ( ~( ( ( B ) != ( k2_struct_0 @ A ) ) & 
% 0.22/0.52                     ( ( k7_subset_1 @
% 0.22/0.52                         ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) =
% 0.22/0.52                       ( k1_xboole_0 ) ) ) ) & 
% 0.22/0.52                ( ~( ( ( k7_subset_1 @
% 0.22/0.52                         ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) !=
% 0.22/0.52                       ( k1_xboole_0 ) ) & 
% 0.22/0.52                     ( ( B ) = ( k2_struct_0 @ A ) ) ) ) ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t23_pre_topc])).
% 0.22/0.52  thf('0', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(dt_k3_subset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.52       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      (![X10 : $i, X11 : $i]:
% 0.22/0.52         ((m1_subset_1 @ (k3_subset_1 @ X10 @ X11) @ (k1_zfmisc_1 @ X10))
% 0.22/0.52          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(d5_subset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.52       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      (![X8 : $i, X9 : $i]:
% 0.22/0.52         (((k3_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))
% 0.22/0.52          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.22/0.52      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.22/0.52         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.52  thf('6', plain,
% 0.22/0.52      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('demod', [status(thm)], ['2', '5'])).
% 0.22/0.52  thf(t18_pre_topc, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( l1_struct_0 @ A ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52           ( ( k4_subset_1 @
% 0.22/0.52               ( u1_struct_0 @ A ) @ B @ 
% 0.22/0.52               ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.22/0.52             ( k2_struct_0 @ A ) ) ) ) ))).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      (![X29 : $i, X30 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.22/0.52          | ((k4_subset_1 @ (u1_struct_0 @ X30) @ X29 @ 
% 0.22/0.52              (k3_subset_1 @ (u1_struct_0 @ X30) @ X29)) = (k2_struct_0 @ X30))
% 0.22/0.52          | ~ (l1_struct_0 @ X30))),
% 0.22/0.52      inference('cnf', [status(esa)], [t18_pre_topc])).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      ((~ (l1_struct_0 @ sk_A)
% 0.22/0.52        | ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52            (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.52            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.22/0.52            = (k2_struct_0 @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.52  thf('9', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(involutiveness_k3_subset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.52       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      (![X15 : $i, X16 : $i]:
% 0.22/0.52         (((k3_subset_1 @ X16 @ (k3_subset_1 @ X16 @ X15)) = (X15))
% 0.22/0.52          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.22/0.52      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.22/0.52         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_B)
% 0.22/0.52         = (k2_struct_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['8', '9', '14'])).
% 0.22/0.52  thf(d10_xboole_0, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.22/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.52  thf('17', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.52      inference('simplify', [status(thm)], ['16'])).
% 0.22/0.52  thf(t3_subset, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (![X26 : $i, X28 : $i]:
% 0.22/0.52         ((m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X28)) | ~ (r1_tarski @ X26 @ X28))),
% 0.22/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.52  thf('19', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      (![X29 : $i, X30 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.22/0.52          | ((k4_subset_1 @ (u1_struct_0 @ X30) @ X29 @ 
% 0.22/0.52              (k3_subset_1 @ (u1_struct_0 @ X30) @ X29)) = (k2_struct_0 @ X30))
% 0.22/0.52          | ~ (l1_struct_0 @ X30))),
% 0.22/0.52      inference('cnf', [status(esa)], [t18_pre_topc])).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (l1_struct_0 @ X0)
% 0.22/0.52          | ((k4_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 0.22/0.52              (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 0.22/0.52              = (k2_struct_0 @ X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.52  thf('22', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      (![X8 : $i, X9 : $i]:
% 0.22/0.52         (((k3_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))
% 0.22/0.52          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.22/0.52      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.52  thf('25', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.52  thf('26', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.52  thf(redefinition_k4_subset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.22/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.52       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.22/0.52  thf('27', plain,
% 0.22/0.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.22/0.52          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18))
% 0.22/0.52          | ((k4_subset_1 @ X18 @ X17 @ X19) = (k2_xboole_0 @ X17 @ X19)))),
% 0.22/0.52      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.22/0.52  thf('28', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (((k4_subset_1 @ X0 @ X0 @ X1) = (k2_xboole_0 @ X0 @ X1))
% 0.22/0.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      (![X0 : $i]: ((k4_subset_1 @ X0 @ X0 @ X0) = (k2_xboole_0 @ X0 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['25', '28'])).
% 0.22/0.52  thf('30', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.52  thf(idempotence_k4_subset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.22/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.52       ( ( k4_subset_1 @ A @ B @ B ) = ( B ) ) ))).
% 0.22/0.52  thf('31', plain,
% 0.22/0.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.52         (((k4_subset_1 @ X13 @ X12 @ X12) = (X12))
% 0.22/0.52          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.22/0.52          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.22/0.52      inference('cnf', [status(esa)], [idempotence_k4_subset_1])).
% 0.22/0.52  thf('32', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (((k4_subset_1 @ X1 @ X0 @ X0) = (X0))
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.22/0.52      inference('condensation', [status(thm)], ['31'])).
% 0.22/0.52  thf('33', plain, (![X0 : $i]: ((k4_subset_1 @ X0 @ X0 @ X0) = (X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['30', '32'])).
% 0.22/0.52  thf('34', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['29', '33'])).
% 0.22/0.52  thf(t46_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.22/0.52  thf('35', plain,
% 0.22/0.52      (![X3 : $i, X4 : $i]:
% 0.22/0.52         ((k4_xboole_0 @ X3 @ (k2_xboole_0 @ X3 @ X4)) = (k1_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.22/0.52  thf('36', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['34', '35'])).
% 0.22/0.52  thf('37', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.52      inference('demod', [status(thm)], ['24', '36'])).
% 0.22/0.52  thf('38', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.52  thf('39', plain,
% 0.22/0.52      (![X10 : $i, X11 : $i]:
% 0.22/0.52         ((m1_subset_1 @ (k3_subset_1 @ X10 @ X11) @ (k1_zfmisc_1 @ X10))
% 0.22/0.52          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.22/0.52  thf('40', plain,
% 0.22/0.52      (![X0 : $i]: (m1_subset_1 @ (k3_subset_1 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['38', '39'])).
% 0.22/0.52  thf('41', plain,
% 0.22/0.52      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.52  thf('42', plain,
% 0.22/0.52      (![X0 : $i]: (m1_subset_1 @ (k4_xboole_0 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.22/0.52      inference('demod', [status(thm)], ['40', '41'])).
% 0.22/0.52  thf('43', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['34', '35'])).
% 0.22/0.52  thf('44', plain,
% 0.22/0.52      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.52      inference('demod', [status(thm)], ['42', '43'])).
% 0.22/0.52  thf('45', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (((k4_subset_1 @ X0 @ X0 @ X1) = (k2_xboole_0 @ X0 @ X1))
% 0.22/0.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.22/0.52  thf('46', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((k4_subset_1 @ X0 @ X0 @ k1_xboole_0)
% 0.22/0.52           = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['44', '45'])).
% 0.22/0.53  thf('47', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.53  thf('48', plain,
% 0.22/0.53      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.53      inference('demod', [status(thm)], ['42', '43'])).
% 0.22/0.53  thf(commutativity_k4_subset_1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.22/0.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.53       ( ( k4_subset_1 @ A @ B @ C ) = ( k4_subset_1 @ A @ C @ B ) ) ))).
% 0.22/0.53  thf('49', plain,
% 0.22/0.53      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.22/0.53          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6))
% 0.22/0.53          | ((k4_subset_1 @ X6 @ X5 @ X7) = (k4_subset_1 @ X6 @ X7 @ X5)))),
% 0.22/0.53      inference('cnf', [status(esa)], [commutativity_k4_subset_1])).
% 0.22/0.53  thf('50', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         (((k4_subset_1 @ X0 @ k1_xboole_0 @ X1)
% 0.22/0.53            = (k4_subset_1 @ X0 @ X1 @ k1_xboole_0))
% 0.22/0.53          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['48', '49'])).
% 0.22/0.53  thf('51', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((k4_subset_1 @ X0 @ k1_xboole_0 @ X0)
% 0.22/0.53           = (k4_subset_1 @ X0 @ X0 @ k1_xboole_0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['47', '50'])).
% 0.22/0.53  thf('52', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((k4_subset_1 @ X0 @ X0 @ k1_xboole_0)
% 0.22/0.53           = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['44', '45'])).
% 0.22/0.53  thf('53', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((k4_subset_1 @ X0 @ k1_xboole_0 @ X0)
% 0.22/0.53           = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.53      inference('demod', [status(thm)], ['51', '52'])).
% 0.22/0.53  thf('54', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.53  thf('55', plain,
% 0.22/0.53      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.53      inference('demod', [status(thm)], ['42', '43'])).
% 0.22/0.53  thf('56', plain,
% 0.22/0.53      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.22/0.53          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18))
% 0.22/0.53          | ((k4_subset_1 @ X18 @ X17 @ X19) = (k2_xboole_0 @ X17 @ X19)))),
% 0.22/0.53      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.22/0.53  thf('57', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         (((k4_subset_1 @ X0 @ k1_xboole_0 @ X1)
% 0.22/0.53            = (k2_xboole_0 @ k1_xboole_0 @ X1))
% 0.22/0.53          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['55', '56'])).
% 0.22/0.53  thf('58', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((k4_subset_1 @ X0 @ k1_xboole_0 @ X0)
% 0.22/0.53           = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['54', '57'])).
% 0.22/0.53  thf('59', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.22/0.53      inference('sup+', [status(thm)], ['53', '58'])).
% 0.22/0.53  thf('60', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (l1_struct_0 @ X0)
% 0.22/0.53          | ((k2_xboole_0 @ k1_xboole_0 @ (u1_struct_0 @ X0))
% 0.22/0.53              = (k2_struct_0 @ X0)))),
% 0.22/0.53      inference('demod', [status(thm)], ['21', '37', '46', '59'])).
% 0.22/0.53  thf('61', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.22/0.53      inference('sup+', [status(thm)], ['53', '58'])).
% 0.22/0.53  thf('62', plain,
% 0.22/0.53      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.53      inference('demod', [status(thm)], ['42', '43'])).
% 0.22/0.53  thf('63', plain,
% 0.22/0.53      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.53      inference('demod', [status(thm)], ['42', '43'])).
% 0.22/0.53  thf(t33_subset_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.53       ( ![C:$i]:
% 0.22/0.53         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.53           ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) ) =
% 0.22/0.53             ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.22/0.53  thf('64', plain,
% 0.22/0.53      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 0.22/0.53          | ((k3_subset_1 @ X24 @ (k7_subset_1 @ X24 @ X25 @ X23))
% 0.22/0.53              = (k4_subset_1 @ X24 @ (k3_subset_1 @ X24 @ X25) @ X23))
% 0.22/0.53          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 0.22/0.53      inference('cnf', [status(esa)], [t33_subset_1])).
% 0.22/0.53  thf('65', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.22/0.53          | ((k3_subset_1 @ X0 @ (k7_subset_1 @ X0 @ X1 @ k1_xboole_0))
% 0.22/0.53              = (k4_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X1) @ k1_xboole_0)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['63', '64'])).
% 0.22/0.53  thf('66', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((k3_subset_1 @ X0 @ (k7_subset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0))
% 0.22/0.53           = (k4_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['62', '65'])).
% 0.22/0.53  thf('67', plain,
% 0.22/0.53      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.53      inference('demod', [status(thm)], ['42', '43'])).
% 0.22/0.53  thf(redefinition_k7_subset_1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.53       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.22/0.53  thf('68', plain,
% 0.22/0.53      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.22/0.53          | ((k7_subset_1 @ X21 @ X20 @ X22) = (k4_xboole_0 @ X20 @ X22)))),
% 0.22/0.53      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.22/0.53  thf('69', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((k7_subset_1 @ X0 @ k1_xboole_0 @ X1)
% 0.22/0.53           = (k4_xboole_0 @ k1_xboole_0 @ X1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['67', '68'])).
% 0.22/0.53  thf('70', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.53  thf('71', plain,
% 0.22/0.53      (![X15 : $i, X16 : $i]:
% 0.22/0.53         (((k3_subset_1 @ X16 @ (k3_subset_1 @ X16 @ X15)) = (X15))
% 0.22/0.53          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.22/0.53      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.22/0.53  thf('72', plain,
% 0.22/0.53      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['70', '71'])).
% 0.22/0.53  thf('73', plain,
% 0.22/0.53      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.53  thf('74', plain,
% 0.22/0.53      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X0)) = (X0))),
% 0.22/0.53      inference('demod', [status(thm)], ['72', '73'])).
% 0.22/0.53  thf('75', plain,
% 0.22/0.53      (![X0 : $i]: (m1_subset_1 @ (k4_xboole_0 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.22/0.53      inference('demod', [status(thm)], ['40', '41'])).
% 0.22/0.53  thf('76', plain,
% 0.22/0.53      (![X8 : $i, X9 : $i]:
% 0.22/0.53         (((k3_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))
% 0.22/0.53          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.22/0.53      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.53  thf('77', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X0))
% 0.22/0.53           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['75', '76'])).
% 0.22/0.53  thf('78', plain,
% 0.22/0.53      (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.22/0.53      inference('sup+', [status(thm)], ['74', '77'])).
% 0.22/0.53  thf('79', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.53      inference('sup+', [status(thm)], ['34', '35'])).
% 0.22/0.53  thf('80', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.53      inference('demod', [status(thm)], ['78', '79'])).
% 0.22/0.53  thf('81', plain,
% 0.22/0.53      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X0)) = (X0))),
% 0.22/0.53      inference('demod', [status(thm)], ['72', '73'])).
% 0.22/0.53  thf('82', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.53      inference('sup+', [status(thm)], ['34', '35'])).
% 0.22/0.53  thf('83', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.53      inference('demod', [status(thm)], ['81', '82'])).
% 0.22/0.53  thf('84', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((k4_subset_1 @ X0 @ X0 @ k1_xboole_0)
% 0.22/0.53           = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['44', '45'])).
% 0.22/0.53  thf('85', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.53      inference('demod', [status(thm)], ['66', '69', '80', '83', '84'])).
% 0.22/0.53  thf('86', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.53      inference('demod', [status(thm)], ['81', '82'])).
% 0.22/0.53  thf('87', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.53      inference('sup+', [status(thm)], ['85', '86'])).
% 0.22/0.53  thf('88', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.22/0.53      inference('demod', [status(thm)], ['61', '87'])).
% 0.22/0.53  thf('89', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (l1_struct_0 @ X0) | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0)))),
% 0.22/0.53      inference('demod', [status(thm)], ['60', '88'])).
% 0.22/0.53  thf('90', plain,
% 0.22/0.53      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.53         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.22/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.53  thf('91', plain,
% 0.22/0.53      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.53          (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) = (sk_B))
% 0.22/0.53        | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.53      inference('sup+', [status(thm)], ['89', '90'])).
% 0.22/0.53  thf('92', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('93', plain,
% 0.22/0.53      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.53         (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.22/0.53      inference('demod', [status(thm)], ['91', '92'])).
% 0.22/0.53  thf('94', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (l1_struct_0 @ X0) | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0)))),
% 0.22/0.53      inference('demod', [status(thm)], ['60', '88'])).
% 0.22/0.53  thf('95', plain,
% 0.22/0.53      ((((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.22/0.53          = (k1_xboole_0))
% 0.22/0.53        | ((sk_B) = (k2_struct_0 @ sk_A)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('96', plain,
% 0.22/0.53      ((((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.22/0.53          = (k1_xboole_0)))
% 0.22/0.53         <= ((((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 0.22/0.53                sk_B) = (k1_xboole_0))))),
% 0.22/0.53      inference('split', [status(esa)], ['95'])).
% 0.22/0.53  thf('97', plain,
% 0.22/0.53      ((((sk_B) != (k2_struct_0 @ sk_A))
% 0.22/0.53        | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.22/0.53            != (k1_xboole_0)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('98', plain,
% 0.22/0.53      (~ (((sk_B) = (k2_struct_0 @ sk_A))) | 
% 0.22/0.53       ~
% 0.22/0.53       (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.22/0.53          = (k1_xboole_0)))),
% 0.22/0.53      inference('split', [status(esa)], ['97'])).
% 0.22/0.53  thf('99', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('100', plain,
% 0.22/0.53      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.22/0.53          | ((k7_subset_1 @ X21 @ X20 @ X22) = (k4_xboole_0 @ X20 @ X22)))),
% 0.22/0.53      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.22/0.53  thf('101', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.22/0.53           = (k4_xboole_0 @ sk_B @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['99', '100'])).
% 0.22/0.53  thf('102', plain,
% 0.22/0.53      ((((sk_B) = (k2_struct_0 @ sk_A))) <= ((((sk_B) = (k2_struct_0 @ sk_A))))),
% 0.22/0.53      inference('split', [status(esa)], ['95'])).
% 0.22/0.53  thf('103', plain,
% 0.22/0.53      ((((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.22/0.53          != (k1_xboole_0)))
% 0.22/0.53         <= (~
% 0.22/0.53             (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 0.22/0.53                sk_B) = (k1_xboole_0))))),
% 0.22/0.53      inference('split', [status(esa)], ['97'])).
% 0.22/0.53  thf('104', plain,
% 0.22/0.53      ((((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_B) != (k1_xboole_0)))
% 0.22/0.53         <= (~
% 0.22/0.53             (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 0.22/0.53                sk_B) = (k1_xboole_0))) & 
% 0.22/0.53             (((sk_B) = (k2_struct_0 @ sk_A))))),
% 0.22/0.53      inference('sup-', [status(thm)], ['102', '103'])).
% 0.22/0.53  thf('105', plain,
% 0.22/0.53      ((((k4_xboole_0 @ sk_B @ sk_B) != (k1_xboole_0)))
% 0.22/0.53         <= (~
% 0.22/0.53             (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 0.22/0.53                sk_B) = (k1_xboole_0))) & 
% 0.22/0.53             (((sk_B) = (k2_struct_0 @ sk_A))))),
% 0.22/0.53      inference('sup-', [status(thm)], ['101', '104'])).
% 0.22/0.53  thf('106', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.53      inference('sup+', [status(thm)], ['34', '35'])).
% 0.22/0.53  thf('107', plain,
% 0.22/0.53      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.22/0.53         <= (~
% 0.22/0.53             (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 0.22/0.53                sk_B) = (k1_xboole_0))) & 
% 0.22/0.53             (((sk_B) = (k2_struct_0 @ sk_A))))),
% 0.22/0.53      inference('demod', [status(thm)], ['105', '106'])).
% 0.22/0.53  thf('108', plain,
% 0.22/0.53      ((((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.22/0.53          = (k1_xboole_0))) | 
% 0.22/0.53       ~ (((sk_B) = (k2_struct_0 @ sk_A)))),
% 0.22/0.53      inference('simplify', [status(thm)], ['107'])).
% 0.22/0.53  thf('109', plain,
% 0.22/0.53      ((((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.22/0.53          = (k1_xboole_0))) | 
% 0.22/0.53       (((sk_B) = (k2_struct_0 @ sk_A)))),
% 0.22/0.53      inference('split', [status(esa)], ['95'])).
% 0.22/0.53  thf('110', plain,
% 0.22/0.53      ((((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.22/0.53          = (k1_xboole_0)))),
% 0.22/0.53      inference('sat_resolution*', [status(thm)], ['98', '108', '109'])).
% 0.22/0.53  thf('111', plain,
% 0.22/0.53      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.22/0.53         = (k1_xboole_0))),
% 0.22/0.53      inference('simpl_trail', [status(thm)], ['96', '110'])).
% 0.22/0.53  thf('112', plain,
% 0.22/0.53      ((((k7_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.22/0.53          = (k1_xboole_0))
% 0.22/0.53        | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.53      inference('sup+', [status(thm)], ['94', '111'])).
% 0.22/0.53  thf('113', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.53  thf('114', plain,
% 0.22/0.53      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.22/0.53          | ((k7_subset_1 @ X21 @ X20 @ X22) = (k4_xboole_0 @ X20 @ X22)))),
% 0.22/0.53      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.22/0.53  thf('115', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['113', '114'])).
% 0.22/0.53  thf('116', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('117', plain,
% 0.22/0.53      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.22/0.53      inference('demod', [status(thm)], ['112', '115', '116'])).
% 0.22/0.53  thf('118', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.53      inference('demod', [status(thm)], ['81', '82'])).
% 0.22/0.53  thf('119', plain, (((u1_struct_0 @ sk_A) = (sk_B))),
% 0.22/0.53      inference('demod', [status(thm)], ['93', '117', '118'])).
% 0.22/0.53  thf('120', plain, (((u1_struct_0 @ sk_A) = (sk_B))),
% 0.22/0.53      inference('demod', [status(thm)], ['93', '117', '118'])).
% 0.22/0.53  thf('121', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.53      inference('sup+', [status(thm)], ['34', '35'])).
% 0.22/0.53  thf('122', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((k4_subset_1 @ X0 @ k1_xboole_0 @ X0)
% 0.22/0.53           = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.53      inference('demod', [status(thm)], ['51', '52'])).
% 0.22/0.53  thf('123', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.53      inference('sup+', [status(thm)], ['85', '86'])).
% 0.22/0.53  thf('124', plain,
% 0.22/0.53      (![X0 : $i]: ((k4_subset_1 @ X0 @ k1_xboole_0 @ X0) = (X0))),
% 0.22/0.53      inference('demod', [status(thm)], ['122', '123'])).
% 0.22/0.53  thf('125', plain, (((sk_B) = (k2_struct_0 @ sk_A))),
% 0.22/0.53      inference('demod', [status(thm)], ['15', '119', '120', '121', '124'])).
% 0.22/0.53  thf('126', plain,
% 0.22/0.53      ((((sk_B) != (k2_struct_0 @ sk_A)))
% 0.22/0.53         <= (~ (((sk_B) = (k2_struct_0 @ sk_A))))),
% 0.22/0.53      inference('split', [status(esa)], ['97'])).
% 0.22/0.53  thf('127', plain, (~ (((sk_B) = (k2_struct_0 @ sk_A)))),
% 0.22/0.53      inference('sat_resolution*', [status(thm)], ['98', '108'])).
% 0.22/0.53  thf('128', plain, (((sk_B) != (k2_struct_0 @ sk_A))),
% 0.22/0.53      inference('simpl_trail', [status(thm)], ['126', '127'])).
% 0.22/0.53  thf('129', plain, ($false),
% 0.22/0.53      inference('simplify_reflect-', [status(thm)], ['125', '128'])).
% 0.22/0.53  
% 0.22/0.53  % SZS output end Refutation
% 0.22/0.53  
% 0.22/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
