%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.C2jZCOXXNp

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:14 EST 2020

% Result     : Theorem 0.56s
% Output     : Refutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 451 expanded)
%              Number of leaves         :   25 ( 150 expanded)
%              Depth                    :   15
%              Number of atoms          :  885 (4176 expanded)
%              Number of equality atoms :   41 ( 234 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

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
    ( ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) )
   <= ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k6_subset_1 @ X12 @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k6_subset_1 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k6_subset_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('9',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference('sup-',[status(thm)],['9','10'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k6_subset_1 @ X12 @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k6_subset_1 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,
    ( ( k6_subset_1 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['11','16'])).

thf('18',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['6','17'])).

thf('19',plain,
    ( ~ ( r2_hidden @ ( k5_xboole_0 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) )
   <= ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['1','18'])).

thf('20',plain,
    ( ( r2_hidden @ sk_C @ sk_B )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['6','17'])).

thf('22',plain,
    ( ( r2_hidden @ sk_C @ sk_B )
    | ( r2_hidden @ ( k5_xboole_0 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('24',plain,(
    ! [X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('25',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

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

thf('26',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) )
      | ( X14
       != ( k7_setfam_1 @ X15 @ X16 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X15 @ X17 ) @ X16 )
      | ~ ( r2_hidden @ X17 @ X14 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('27',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r2_hidden @ X17 @ ( k7_setfam_1 @ X15 @ X16 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X15 @ X17 ) @ X16 )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('33',plain,(
    r1_tarski @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('35',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('37',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('38',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k6_subset_1 @ X12 @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('39',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k6_subset_1 @ X12 @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('40',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k6_subset_1 @ X6 @ ( k6_subset_1 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('41',plain,(
    ! [X10: $i,X11: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','42'])).

thf('44',plain,(
    ! [X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k7_setfam_1 @ X0 @ ( k3_xboole_0 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('46',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ( m1_subset_1 @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k7_setfam_1 @ X0 @ ( k3_xboole_0 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['30','48'])).

thf('50',plain,
    ( ( r2_hidden @ sk_C @ sk_B )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['22','49'])).

thf('51',plain,
    ( ( k6_subset_1 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['11','16'])).

thf('52',plain,(
    ! [X10: $i,X11: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('53',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k6_subset_1 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('55',plain,
    ( ( k3_subset_1 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C ) )
    = ( k6_subset_1 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k6_subset_1 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['11','16'])).

thf('57',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k6_subset_1 @ X6 @ ( k6_subset_1 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('58',plain,
    ( ( k6_subset_1 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C ) )
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('60',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference('sup-',[status(thm)],['9','10'])).

thf('61',plain,
    ( ( k6_subset_1 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ( k3_subset_1 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['55','61'])).

thf('63',plain,
    ( ( r2_hidden @ sk_C @ sk_B )
    | ( r2_hidden @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['50','62'])).

thf('64',plain,(
    r2_hidden @ sk_C @ sk_B ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_B )
   <= ~ ( r2_hidden @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('66',plain,(
    r2_hidden @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('68',plain,(
    ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( r2_hidden @ ( k5_xboole_0 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['19','68'])).

thf('70',plain,
    ( ( k3_subset_1 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['55','61'])).

thf('71',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('72',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) )
      | ( X14
       != ( k7_setfam_1 @ X15 @ X16 ) )
      | ( r2_hidden @ X17 @ X14 )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X15 @ X17 ) @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('73',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X15 @ X17 ) @ X16 )
      | ( r2_hidden @ X17 @ ( k7_setfam_1 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['71','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k5_xboole_0 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ ( k5_xboole_0 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['70','76'])).

thf('78',plain,(
    r2_hidden @ sk_C @ sk_B ),
    inference(simplify,[status(thm)],['63'])).

thf('79',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('80',plain,(
    r2_hidden @ ( k5_xboole_0 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    $false ),
    inference(demod,[status(thm)],['69','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.C2jZCOXXNp
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:57:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.56/0.75  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.56/0.75  % Solved by: fo/fo7.sh
% 0.56/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.56/0.75  % done 1084 iterations in 0.300s
% 0.56/0.75  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.56/0.75  % SZS output start Refutation
% 0.56/0.75  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.56/0.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.56/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.56/0.75  thf(sk_C_type, type, sk_C: $i).
% 0.56/0.75  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.56/0.75  thf(sk_B_type, type, sk_B: $i).
% 0.56/0.75  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.56/0.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.56/0.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.56/0.75  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.56/0.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.56/0.75  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.56/0.75  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.56/0.75  thf(t49_setfam_1, conjecture,
% 0.56/0.75    (![A:$i,B:$i]:
% 0.56/0.75     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.56/0.75       ( ![C:$i]:
% 0.56/0.75         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.56/0.75           ( ( r2_hidden @ ( k3_subset_1 @ A @ C ) @ ( k7_setfam_1 @ A @ B ) ) <=>
% 0.56/0.75             ( r2_hidden @ C @ B ) ) ) ) ))).
% 0.56/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.56/0.75    (~( ![A:$i,B:$i]:
% 0.56/0.75        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.56/0.75          ( ![C:$i]:
% 0.56/0.75            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.56/0.75              ( ( r2_hidden @ ( k3_subset_1 @ A @ C ) @ ( k7_setfam_1 @ A @ B ) ) <=>
% 0.56/0.75                ( r2_hidden @ C @ B ) ) ) ) ) )),
% 0.56/0.75    inference('cnf.neg', [status(esa)], [t49_setfam_1])).
% 0.56/0.75  thf('0', plain,
% 0.56/0.75      ((~ (r2_hidden @ sk_C @ sk_B)
% 0.56/0.75        | ~ (r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.56/0.75             (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.75  thf('1', plain,
% 0.56/0.75      ((~ (r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.56/0.75           (k7_setfam_1 @ sk_A @ sk_B)))
% 0.56/0.75         <= (~
% 0.56/0.75             ((r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.56/0.75               (k7_setfam_1 @ sk_A @ sk_B))))),
% 0.56/0.75      inference('split', [status(esa)], ['0'])).
% 0.56/0.75  thf('2', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.75  thf(d5_subset_1, axiom,
% 0.56/0.75    (![A:$i,B:$i]:
% 0.56/0.75     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.56/0.75       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.56/0.75  thf('3', plain,
% 0.56/0.75      (![X8 : $i, X9 : $i]:
% 0.56/0.75         (((k3_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))
% 0.56/0.75          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.56/0.75      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.56/0.75  thf(redefinition_k6_subset_1, axiom,
% 0.56/0.75    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.56/0.75  thf('4', plain,
% 0.56/0.75      (![X12 : $i, X13 : $i]:
% 0.56/0.75         ((k6_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))),
% 0.56/0.75      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.56/0.75  thf('5', plain,
% 0.56/0.75      (![X8 : $i, X9 : $i]:
% 0.56/0.75         (((k3_subset_1 @ X8 @ X9) = (k6_subset_1 @ X8 @ X9))
% 0.56/0.75          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.56/0.75      inference('demod', [status(thm)], ['3', '4'])).
% 0.56/0.75  thf('6', plain,
% 0.56/0.75      (((k3_subset_1 @ sk_A @ sk_C) = (k6_subset_1 @ sk_A @ sk_C))),
% 0.56/0.75      inference('sup-', [status(thm)], ['2', '5'])).
% 0.56/0.75  thf('7', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.75  thf(t3_subset, axiom,
% 0.56/0.75    (![A:$i,B:$i]:
% 0.56/0.75     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.56/0.75  thf('8', plain,
% 0.56/0.75      (![X20 : $i, X21 : $i]:
% 0.56/0.75         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.56/0.75      inference('cnf', [status(esa)], [t3_subset])).
% 0.56/0.75  thf('9', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.56/0.75      inference('sup-', [status(thm)], ['7', '8'])).
% 0.56/0.75  thf(t28_xboole_1, axiom,
% 0.56/0.75    (![A:$i,B:$i]:
% 0.56/0.75     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.56/0.75  thf('10', plain,
% 0.56/0.75      (![X4 : $i, X5 : $i]:
% 0.56/0.75         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.56/0.75      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.56/0.75  thf('11', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 0.56/0.75      inference('sup-', [status(thm)], ['9', '10'])).
% 0.56/0.75  thf(commutativity_k3_xboole_0, axiom,
% 0.56/0.75    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.56/0.75  thf('12', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.56/0.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.56/0.75  thf(t100_xboole_1, axiom,
% 0.56/0.75    (![A:$i,B:$i]:
% 0.56/0.75     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.56/0.75  thf('13', plain,
% 0.56/0.75      (![X2 : $i, X3 : $i]:
% 0.56/0.75         ((k4_xboole_0 @ X2 @ X3)
% 0.56/0.75           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.56/0.75      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.56/0.75  thf('14', plain,
% 0.56/0.75      (![X12 : $i, X13 : $i]:
% 0.56/0.75         ((k6_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))),
% 0.56/0.75      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.56/0.75  thf('15', plain,
% 0.56/0.75      (![X2 : $i, X3 : $i]:
% 0.56/0.75         ((k6_subset_1 @ X2 @ X3)
% 0.56/0.75           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.56/0.75      inference('demod', [status(thm)], ['13', '14'])).
% 0.56/0.75  thf('16', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]:
% 0.56/0.75         ((k6_subset_1 @ X0 @ X1)
% 0.56/0.75           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.56/0.75      inference('sup+', [status(thm)], ['12', '15'])).
% 0.56/0.75  thf('17', plain,
% 0.56/0.75      (((k6_subset_1 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 0.56/0.75      inference('sup+', [status(thm)], ['11', '16'])).
% 0.56/0.75  thf('18', plain,
% 0.56/0.75      (((k3_subset_1 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 0.56/0.75      inference('demod', [status(thm)], ['6', '17'])).
% 0.56/0.75  thf('19', plain,
% 0.56/0.75      ((~ (r2_hidden @ (k5_xboole_0 @ sk_A @ sk_C) @ 
% 0.56/0.75           (k7_setfam_1 @ sk_A @ sk_B)))
% 0.56/0.75         <= (~
% 0.56/0.75             ((r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.56/0.75               (k7_setfam_1 @ sk_A @ sk_B))))),
% 0.56/0.75      inference('demod', [status(thm)], ['1', '18'])).
% 0.56/0.75  thf('20', plain,
% 0.56/0.75      (((r2_hidden @ sk_C @ sk_B)
% 0.56/0.75        | (r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.56/0.75           (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.75  thf('21', plain,
% 0.56/0.75      (((k3_subset_1 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 0.56/0.75      inference('demod', [status(thm)], ['6', '17'])).
% 0.56/0.75  thf('22', plain,
% 0.56/0.75      (((r2_hidden @ sk_C @ sk_B)
% 0.56/0.75        | (r2_hidden @ (k5_xboole_0 @ sk_A @ sk_C) @ 
% 0.56/0.75           (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.56/0.75      inference('demod', [status(thm)], ['20', '21'])).
% 0.56/0.75  thf('23', plain,
% 0.56/0.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.75  thf(dt_k7_setfam_1, axiom,
% 0.56/0.75    (![A:$i,B:$i]:
% 0.56/0.75     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.56/0.75       ( m1_subset_1 @
% 0.56/0.75         ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.56/0.75  thf('24', plain,
% 0.56/0.75      (![X18 : $i, X19 : $i]:
% 0.56/0.75         ((m1_subset_1 @ (k7_setfam_1 @ X18 @ X19) @ 
% 0.56/0.75           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18)))
% 0.56/0.75          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18))))),
% 0.56/0.75      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.56/0.75  thf('25', plain,
% 0.56/0.75      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B) @ 
% 0.56/0.75        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.56/0.75      inference('sup-', [status(thm)], ['23', '24'])).
% 0.56/0.75  thf(d8_setfam_1, axiom,
% 0.56/0.75    (![A:$i,B:$i]:
% 0.56/0.75     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.56/0.75       ( ![C:$i]:
% 0.56/0.75         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.56/0.75           ( ( ( C ) = ( k7_setfam_1 @ A @ B ) ) <=>
% 0.56/0.75             ( ![D:$i]:
% 0.56/0.75               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.56/0.75                 ( ( r2_hidden @ D @ C ) <=>
% 0.56/0.75                   ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) ) ))).
% 0.56/0.75  thf('26', plain,
% 0.56/0.75      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.56/0.75         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15)))
% 0.56/0.75          | ((X14) != (k7_setfam_1 @ X15 @ X16))
% 0.56/0.75          | (r2_hidden @ (k3_subset_1 @ X15 @ X17) @ X16)
% 0.56/0.75          | ~ (r2_hidden @ X17 @ X14)
% 0.56/0.75          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X15))
% 0.56/0.75          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.56/0.75      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.56/0.75  thf('27', plain,
% 0.56/0.75      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.56/0.75         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15)))
% 0.56/0.75          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X15))
% 0.56/0.75          | ~ (r2_hidden @ X17 @ (k7_setfam_1 @ X15 @ X16))
% 0.56/0.75          | (r2_hidden @ (k3_subset_1 @ X15 @ X17) @ X16)
% 0.56/0.75          | ~ (m1_subset_1 @ (k7_setfam_1 @ X15 @ X16) @ 
% 0.56/0.75               (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.56/0.75      inference('simplify', [status(thm)], ['26'])).
% 0.56/0.75  thf('28', plain,
% 0.56/0.75      (![X0 : $i]:
% 0.56/0.75         ((r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ sk_B)
% 0.56/0.75          | ~ (r2_hidden @ X0 @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.56/0.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.56/0.75          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.56/0.75      inference('sup-', [status(thm)], ['25', '27'])).
% 0.56/0.75  thf('29', plain,
% 0.56/0.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.75  thf('30', plain,
% 0.56/0.75      (![X0 : $i]:
% 0.56/0.75         ((r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ sk_B)
% 0.56/0.75          | ~ (r2_hidden @ X0 @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.56/0.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.56/0.75      inference('demod', [status(thm)], ['28', '29'])).
% 0.56/0.75  thf('31', plain,
% 0.56/0.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.75  thf('32', plain,
% 0.56/0.75      (![X20 : $i, X21 : $i]:
% 0.56/0.75         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.56/0.75      inference('cnf', [status(esa)], [t3_subset])).
% 0.56/0.75  thf('33', plain, ((r1_tarski @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.56/0.75      inference('sup-', [status(thm)], ['31', '32'])).
% 0.56/0.75  thf('34', plain,
% 0.56/0.75      (![X4 : $i, X5 : $i]:
% 0.56/0.75         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.56/0.75      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.56/0.75  thf('35', plain, (((k3_xboole_0 @ sk_B @ (k1_zfmisc_1 @ sk_A)) = (sk_B))),
% 0.56/0.75      inference('sup-', [status(thm)], ['33', '34'])).
% 0.56/0.75  thf('36', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.56/0.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.56/0.75  thf(t48_xboole_1, axiom,
% 0.56/0.75    (![A:$i,B:$i]:
% 0.56/0.75     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.56/0.75  thf('37', plain,
% 0.56/0.75      (![X6 : $i, X7 : $i]:
% 0.56/0.75         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.56/0.75           = (k3_xboole_0 @ X6 @ X7))),
% 0.56/0.75      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.56/0.75  thf('38', plain,
% 0.56/0.75      (![X12 : $i, X13 : $i]:
% 0.56/0.75         ((k6_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))),
% 0.56/0.75      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.56/0.75  thf('39', plain,
% 0.56/0.75      (![X12 : $i, X13 : $i]:
% 0.56/0.75         ((k6_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))),
% 0.56/0.75      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.56/0.75  thf('40', plain,
% 0.56/0.75      (![X6 : $i, X7 : $i]:
% 0.56/0.75         ((k6_subset_1 @ X6 @ (k6_subset_1 @ X6 @ X7))
% 0.56/0.75           = (k3_xboole_0 @ X6 @ X7))),
% 0.56/0.75      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.56/0.75  thf(dt_k6_subset_1, axiom,
% 0.56/0.75    (![A:$i,B:$i]:
% 0.56/0.75     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.56/0.75  thf('41', plain,
% 0.56/0.75      (![X10 : $i, X11 : $i]:
% 0.56/0.75         (m1_subset_1 @ (k6_subset_1 @ X10 @ X11) @ (k1_zfmisc_1 @ X10))),
% 0.56/0.75      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.56/0.75  thf('42', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]:
% 0.56/0.75         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 0.56/0.75      inference('sup+', [status(thm)], ['40', '41'])).
% 0.56/0.75  thf('43', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]:
% 0.56/0.75         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.56/0.75      inference('sup+', [status(thm)], ['36', '42'])).
% 0.56/0.75  thf('44', plain,
% 0.56/0.75      (![X18 : $i, X19 : $i]:
% 0.56/0.75         ((m1_subset_1 @ (k7_setfam_1 @ X18 @ X19) @ 
% 0.56/0.75           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18)))
% 0.56/0.75          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18))))),
% 0.56/0.75      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.56/0.75  thf('45', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]:
% 0.56/0.75         (m1_subset_1 @ 
% 0.56/0.75          (k7_setfam_1 @ X0 @ (k3_xboole_0 @ X1 @ (k1_zfmisc_1 @ X0))) @ 
% 0.56/0.75          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 0.56/0.75      inference('sup-', [status(thm)], ['43', '44'])).
% 0.56/0.75  thf(t4_subset, axiom,
% 0.56/0.75    (![A:$i,B:$i,C:$i]:
% 0.56/0.75     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.56/0.75       ( m1_subset_1 @ A @ C ) ))).
% 0.56/0.75  thf('46', plain,
% 0.56/0.75      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.56/0.75         (~ (r2_hidden @ X23 @ X24)
% 0.56/0.75          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25))
% 0.56/0.75          | (m1_subset_1 @ X23 @ X25))),
% 0.56/0.75      inference('cnf', [status(esa)], [t4_subset])).
% 0.56/0.75  thf('47', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.75         ((m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0))
% 0.56/0.75          | ~ (r2_hidden @ X2 @ 
% 0.56/0.75               (k7_setfam_1 @ X0 @ (k3_xboole_0 @ X1 @ (k1_zfmisc_1 @ X0)))))),
% 0.56/0.75      inference('sup-', [status(thm)], ['45', '46'])).
% 0.56/0.75  thf('48', plain,
% 0.56/0.75      (![X0 : $i]:
% 0.56/0.75         (~ (r2_hidden @ X0 @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.56/0.75          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.56/0.75      inference('sup-', [status(thm)], ['35', '47'])).
% 0.56/0.75  thf('49', plain,
% 0.56/0.75      (![X0 : $i]:
% 0.56/0.75         (~ (r2_hidden @ X0 @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.56/0.75          | (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ sk_B))),
% 0.56/0.75      inference('clc', [status(thm)], ['30', '48'])).
% 0.56/0.75  thf('50', plain,
% 0.56/0.75      (((r2_hidden @ sk_C @ sk_B)
% 0.56/0.75        | (r2_hidden @ (k3_subset_1 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C)) @ 
% 0.56/0.75           sk_B))),
% 0.56/0.75      inference('sup-', [status(thm)], ['22', '49'])).
% 0.56/0.75  thf('51', plain,
% 0.56/0.75      (((k6_subset_1 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 0.56/0.75      inference('sup+', [status(thm)], ['11', '16'])).
% 0.56/0.75  thf('52', plain,
% 0.56/0.75      (![X10 : $i, X11 : $i]:
% 0.56/0.75         (m1_subset_1 @ (k6_subset_1 @ X10 @ X11) @ (k1_zfmisc_1 @ X10))),
% 0.56/0.75      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.56/0.75  thf('53', plain,
% 0.56/0.75      ((m1_subset_1 @ (k5_xboole_0 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.56/0.75      inference('sup+', [status(thm)], ['51', '52'])).
% 0.56/0.75  thf('54', plain,
% 0.56/0.75      (![X8 : $i, X9 : $i]:
% 0.56/0.75         (((k3_subset_1 @ X8 @ X9) = (k6_subset_1 @ X8 @ X9))
% 0.56/0.75          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.56/0.75      inference('demod', [status(thm)], ['3', '4'])).
% 0.56/0.75  thf('55', plain,
% 0.56/0.75      (((k3_subset_1 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C))
% 0.56/0.75         = (k6_subset_1 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C)))),
% 0.56/0.75      inference('sup-', [status(thm)], ['53', '54'])).
% 0.56/0.75  thf('56', plain,
% 0.56/0.75      (((k6_subset_1 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 0.56/0.75      inference('sup+', [status(thm)], ['11', '16'])).
% 0.56/0.75  thf('57', plain,
% 0.56/0.75      (![X6 : $i, X7 : $i]:
% 0.56/0.75         ((k6_subset_1 @ X6 @ (k6_subset_1 @ X6 @ X7))
% 0.56/0.75           = (k3_xboole_0 @ X6 @ X7))),
% 0.56/0.75      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.56/0.75  thf('58', plain,
% 0.56/0.75      (((k6_subset_1 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C))
% 0.56/0.75         = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.56/0.75      inference('sup+', [status(thm)], ['56', '57'])).
% 0.56/0.75  thf('59', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.56/0.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.56/0.75  thf('60', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 0.56/0.75      inference('sup-', [status(thm)], ['9', '10'])).
% 0.56/0.75  thf('61', plain,
% 0.56/0.75      (((k6_subset_1 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C)) = (sk_C))),
% 0.56/0.75      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.56/0.75  thf('62', plain,
% 0.56/0.75      (((k3_subset_1 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C)) = (sk_C))),
% 0.56/0.75      inference('demod', [status(thm)], ['55', '61'])).
% 0.56/0.75  thf('63', plain, (((r2_hidden @ sk_C @ sk_B) | (r2_hidden @ sk_C @ sk_B))),
% 0.56/0.75      inference('demod', [status(thm)], ['50', '62'])).
% 0.56/0.75  thf('64', plain, ((r2_hidden @ sk_C @ sk_B)),
% 0.56/0.75      inference('simplify', [status(thm)], ['63'])).
% 0.56/0.75  thf('65', plain,
% 0.56/0.75      ((~ (r2_hidden @ sk_C @ sk_B)) <= (~ ((r2_hidden @ sk_C @ sk_B)))),
% 0.56/0.75      inference('split', [status(esa)], ['0'])).
% 0.56/0.75  thf('66', plain, (((r2_hidden @ sk_C @ sk_B))),
% 0.56/0.75      inference('sup-', [status(thm)], ['64', '65'])).
% 0.56/0.75  thf('67', plain,
% 0.56/0.75      (~
% 0.56/0.75       ((r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ (k7_setfam_1 @ sk_A @ sk_B))) | 
% 0.56/0.75       ~ ((r2_hidden @ sk_C @ sk_B))),
% 0.56/0.75      inference('split', [status(esa)], ['0'])).
% 0.56/0.75  thf('68', plain,
% 0.56/0.75      (~
% 0.56/0.75       ((r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.56/0.75      inference('sat_resolution*', [status(thm)], ['66', '67'])).
% 0.56/0.75  thf('69', plain,
% 0.56/0.75      (~ (r2_hidden @ (k5_xboole_0 @ sk_A @ sk_C) @ (k7_setfam_1 @ sk_A @ sk_B))),
% 0.56/0.75      inference('simpl_trail', [status(thm)], ['19', '68'])).
% 0.56/0.75  thf('70', plain,
% 0.56/0.75      (((k3_subset_1 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C)) = (sk_C))),
% 0.56/0.75      inference('demod', [status(thm)], ['55', '61'])).
% 0.56/0.75  thf('71', plain,
% 0.56/0.75      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B) @ 
% 0.56/0.75        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.56/0.75      inference('sup-', [status(thm)], ['23', '24'])).
% 0.56/0.75  thf('72', plain,
% 0.56/0.75      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.56/0.75         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15)))
% 0.56/0.75          | ((X14) != (k7_setfam_1 @ X15 @ X16))
% 0.56/0.75          | (r2_hidden @ X17 @ X14)
% 0.56/0.75          | ~ (r2_hidden @ (k3_subset_1 @ X15 @ X17) @ X16)
% 0.56/0.75          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X15))
% 0.56/0.75          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.56/0.75      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.56/0.75  thf('73', plain,
% 0.56/0.75      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.56/0.75         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15)))
% 0.56/0.75          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X15))
% 0.56/0.75          | ~ (r2_hidden @ (k3_subset_1 @ X15 @ X17) @ X16)
% 0.56/0.75          | (r2_hidden @ X17 @ (k7_setfam_1 @ X15 @ X16))
% 0.56/0.75          | ~ (m1_subset_1 @ (k7_setfam_1 @ X15 @ X16) @ 
% 0.56/0.75               (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.56/0.75      inference('simplify', [status(thm)], ['72'])).
% 0.56/0.75  thf('74', plain,
% 0.56/0.75      (![X0 : $i]:
% 0.56/0.75         ((r2_hidden @ X0 @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.56/0.75          | ~ (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ sk_B)
% 0.56/0.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.56/0.75          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.56/0.75      inference('sup-', [status(thm)], ['71', '73'])).
% 0.56/0.75  thf('75', plain,
% 0.56/0.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.75  thf('76', plain,
% 0.56/0.75      (![X0 : $i]:
% 0.56/0.75         ((r2_hidden @ X0 @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.56/0.75          | ~ (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ sk_B)
% 0.56/0.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.56/0.75      inference('demod', [status(thm)], ['74', '75'])).
% 0.56/0.75  thf('77', plain,
% 0.56/0.75      ((~ (r2_hidden @ sk_C @ sk_B)
% 0.56/0.75        | ~ (m1_subset_1 @ (k5_xboole_0 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))
% 0.56/0.75        | (r2_hidden @ (k5_xboole_0 @ sk_A @ sk_C) @ 
% 0.56/0.75           (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.56/0.75      inference('sup-', [status(thm)], ['70', '76'])).
% 0.56/0.75  thf('78', plain, ((r2_hidden @ sk_C @ sk_B)),
% 0.56/0.75      inference('simplify', [status(thm)], ['63'])).
% 0.56/0.75  thf('79', plain,
% 0.56/0.75      ((m1_subset_1 @ (k5_xboole_0 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.56/0.75      inference('sup+', [status(thm)], ['51', '52'])).
% 0.56/0.75  thf('80', plain,
% 0.56/0.75      ((r2_hidden @ (k5_xboole_0 @ sk_A @ sk_C) @ (k7_setfam_1 @ sk_A @ sk_B))),
% 0.56/0.75      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.56/0.75  thf('81', plain, ($false), inference('demod', [status(thm)], ['69', '80'])).
% 0.56/0.75  
% 0.56/0.75  % SZS output end Refutation
% 0.56/0.75  
% 0.61/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
