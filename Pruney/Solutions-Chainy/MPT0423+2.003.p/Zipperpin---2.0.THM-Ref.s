%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ls1Gjeix8H

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:16 EST 2020

% Result     : Theorem 1.96s
% Output     : Refutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 320 expanded)
%              Number of leaves         :   41 ( 110 expanded)
%              Depth                    :   17
%              Number of atoms          : 1105 (2638 expanded)
%              Number of equality atoms :   88 ( 272 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X56: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X73: $i,X74: $i] :
      ( ( r1_tarski @ X73 @ X74 )
      | ~ ( m1_subset_1 @ X73 @ ( k1_zfmisc_1 @ X74 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('2',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('3',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( r1_tarski @ X38 @ X39 )
      | ( r2_hidden @ X38 @ X40 )
      | ( X40
       != ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('4',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r2_hidden @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ~ ( r1_tarski @ X38 @ X39 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X59: $i,X60: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X59 ) @ ( k1_zfmisc_1 @ X60 ) )
      | ~ ( r2_hidden @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(involutiveness_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
        = B ) ) )).

thf('8',plain,(
    ! [X67: $i,X68: $i] :
      ( ( ( k7_setfam_1 @ X68 @ ( k7_setfam_1 @ X68 @ X67 ) )
        = X67 )
      | ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X68 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k7_setfam_1 @ X0 @ ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) ) )
      = ( k1_tarski @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t55_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( B
          = ( k1_tarski @ A ) )
       => ( ( k7_setfam_1 @ A @ B )
          = ( k1_tarski @ k1_xboole_0 ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ( ( B
            = ( k1_tarski @ A ) )
         => ( ( k7_setfam_1 @ A @ B )
            = ( k1_tarski @ k1_xboole_0 ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t55_setfam_1])).

thf('10',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('12',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X69: $i,X70: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X69 @ X70 ) )
      = ( k3_xboole_0 @ X69 @ X70 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k1_setfam_1 @ sk_B_1 )
    = sk_A ),
    inference('sup+',[status(thm)],['11','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['10','17'])).

thf(t51_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ ( k7_setfam_1 @ A @ C ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf('19',plain,(
    ! [X81: $i,X82: $i,X83: $i] :
      ( ~ ( m1_subset_1 @ X81 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X82 ) ) )
      | ( r1_tarski @ X83 @ X81 )
      | ~ ( r1_tarski @ ( k7_setfam_1 @ X82 @ X83 ) @ ( k7_setfam_1 @ X82 @ X81 ) )
      | ~ ( m1_subset_1 @ X83 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X82 ) ) ) ) ),
    inference(cnf,[status(esa)],[t51_setfam_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B_1 ) ) ) )
      | ~ ( r1_tarski @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ X0 ) @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 ) )
      | ( r1_tarski @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ k1_xboole_0 ) @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 ) )
    | ( r1_tarski @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ ( k1_tarski @ k1_xboole_0 ) ) @ sk_B_1 )
    | ~ ( m1_subset_1 @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ ( k1_tarski @ k1_xboole_0 ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','20'])).

thf('22',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('23',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( X6 != X5 )
      | ( r2_hidden @ X6 @ X7 )
      | ( X7
       != ( k1_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('24',plain,(
    ! [X5: $i] :
      ( r2_hidden @ X5 @ ( k1_tarski @ X5 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference('sup+',[status(thm)],['22','24'])).

thf('26',plain,
    ( ( k1_setfam_1 @ sk_B_1 )
    = sk_A ),
    inference('sup+',[status(thm)],['11','16'])).

thf('27',plain,(
    r2_hidden @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['10','17'])).

thf('29',plain,(
    ! [X67: $i,X68: $i] :
      ( ( ( k7_setfam_1 @ X68 @ ( k7_setfam_1 @ X68 @ X67 ) )
        = X67 )
      | ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X68 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('30',plain,
    ( ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['28','29'])).

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

thf('31',plain,(
    ! [X61: $i,X62: $i,X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X62 ) ) )
      | ( X61
       != ( k7_setfam_1 @ X62 @ X63 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X62 @ X64 ) @ X63 )
      | ~ ( r2_hidden @ X64 @ X61 )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ X62 ) )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X62 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('32',plain,(
    ! [X62: $i,X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X62 ) ) )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ X62 ) )
      | ~ ( r2_hidden @ X64 @ ( k7_setfam_1 @ X62 @ X63 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X62 @ X64 ) @ X63 )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X62 @ X63 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X62 ) ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B_1 ) ) ) )
      | ( r2_hidden @ ( k3_subset_1 @ ( k1_setfam_1 @ sk_B_1 ) @ X0 ) @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['10','17'])).

thf('35',plain,
    ( ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['28','29'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ ( k1_setfam_1 @ sk_B_1 ) @ X0 ) @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['10','17'])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('38',plain,(
    ! [X65: $i,X66: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X65 @ X66 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X65 ) ) )
      | ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X65 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('39',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ ( k1_setfam_1 @ sk_B_1 ) @ X0 ) @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['10','17'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('42',plain,(
    ! [X78: $i,X79: $i,X80: $i] :
      ( ~ ( r2_hidden @ X78 @ X79 )
      | ~ ( m1_subset_1 @ X79 @ ( k1_zfmisc_1 @ X80 ) )
      | ( m1_subset_1 @ X78 @ X80 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B_1 ) ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( k3_subset_1 @ ( k1_setfam_1 @ sk_B_1 ) @ X0 ) @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['40','43'])).

thf('45',plain,(
    r2_hidden @ ( k3_subset_1 @ ( k1_setfam_1 @ sk_B_1 ) @ ( k1_setfam_1 @ sk_B_1 ) ) @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['27','44'])).

thf('46',plain,(
    ! [X56: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('47',plain,(
    ! [X51: $i,X52: $i] :
      ( ( ( k3_subset_1 @ X52 @ ( k3_subset_1 @ X52 @ X51 ) )
        = X51 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('49',plain,(
    ! [X49: $i] :
      ( ( k1_subset_1 @ X49 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('50',plain,(
    ! [X53: $i] :
      ( ( k2_subset_1 @ X53 )
      = ( k3_subset_1 @ X53 @ ( k1_subset_1 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('51',plain,(
    ! [X50: $i] :
      ( ( k2_subset_1 @ X50 )
      = X50 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('52',plain,(
    ! [X53: $i] :
      ( X53
      = ( k3_subset_1 @ X53 @ ( k1_subset_1 @ X53 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','53'])).

thf('55',plain,(
    r2_hidden @ k1_xboole_0 @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['45','54'])).

thf('56',plain,(
    ! [X59: $i,X60: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X59 ) @ ( k1_zfmisc_1 @ X60 ) )
      | ~ ( r2_hidden @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('57',plain,(
    m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X73: $i,X74: $i] :
      ( ( r1_tarski @ X73 @ X74 )
      | ~ ( m1_subset_1 @ X73 @ ( k1_zfmisc_1 @ X74 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('59',plain,(
    r1_tarski @ ( k1_tarski @ k1_xboole_0 ) @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('61',plain,(
    ! [X65: $i,X66: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X65 @ X66 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X65 ) ) )
      | ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X65 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    r1_tarski @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ ( k1_tarski @ k1_xboole_0 ) ) @ sk_B_1 ),
    inference(demod,[status(thm)],['21','59','62'])).

thf('64',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t39_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('65',plain,(
    ! [X46: $i,X47: $i] :
      ( ( X47
        = ( k1_tarski @ X46 ) )
      | ( X47 = k1_xboole_0 )
      | ~ ( r1_tarski @ X47 @ ( k1_tarski @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t39_zfmisc_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = sk_B_1 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ ( k1_tarski @ k1_xboole_0 ) )
      = sk_B_1 )
    | ( ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ ( k1_tarski @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t46_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ~ ( ( B != k1_xboole_0 )
          & ( ( k7_setfam_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf('71',plain,(
    ! [X76: $i,X77: $i] :
      ( ( ( k7_setfam_1 @ X76 @ X77 )
       != k1_xboole_0 )
      | ( X77 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X77 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X76 ) ) ) ) ),
    inference(cnf,[status(esa)],[t46_setfam_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('73',plain,(
    ! [X43: $i,X44: $i] :
      ( ( X44 != X43 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X44 ) @ ( k1_tarski @ X43 ) )
       != ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('74',plain,(
    ! [X43: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X43 ) @ ( k1_tarski @ X43 ) )
     != ( k1_tarski @ X43 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('76',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('78',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('79',plain,(
    ! [X43: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X43 ) ) ),
    inference(demod,[status(thm)],['74','77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) )
     != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['72','79'])).

thf('81',plain,
    ( ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['28','29'])).

thf('82',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t53_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( ( k7_setfam_1 @ A @ B )
              = ( k7_setfam_1 @ A @ C ) )
           => ( B = C ) ) ) ) )).

thf('83',plain,(
    ! [X84: $i,X85: $i,X86: $i] :
      ( ~ ( m1_subset_1 @ X84 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X85 ) ) )
      | ( X86 = X84 )
      | ( ( k7_setfam_1 @ X85 @ X86 )
       != ( k7_setfam_1 @ X85 @ X84 ) )
      | ~ ( m1_subset_1 @ X86 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X85 ) ) ) ) ),
    inference(cnf,[status(esa)],[t53_setfam_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( ( k7_setfam_1 @ X0 @ X1 )
       != ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) ) )
      | ( X1
        = ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( sk_B_1
     != ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ ( k1_tarski @ k1_xboole_0 ) ) )
    | ( ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 )
      = ( k1_tarski @ k1_xboole_0 ) )
    | ~ ( m1_subset_1 @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('87',plain,
    ( ( sk_B_1
     != ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ ( k1_tarski @ k1_xboole_0 ) ) )
    | ( ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 )
      = ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ( k7_setfam_1 @ sk_A @ sk_B_1 )
 != ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( k1_setfam_1 @ sk_B_1 )
    = sk_A ),
    inference('sup+',[status(thm)],['11','16'])).

thf('90',plain,(
    ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 )
 != ( k1_tarski @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    sk_B_1
 != ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['87','90'])).

thf('92',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['69','80','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ls1Gjeix8H
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:10:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.96/2.17  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.96/2.17  % Solved by: fo/fo7.sh
% 1.96/2.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.96/2.17  % done 4409 iterations in 1.715s
% 1.96/2.17  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.96/2.17  % SZS output start Refutation
% 1.96/2.17  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.96/2.17  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.96/2.17  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.96/2.17  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.96/2.17  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.96/2.17  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.96/2.17  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.96/2.17  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.96/2.17  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.96/2.17  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.96/2.17  thf(sk_A_type, type, sk_A: $i).
% 1.96/2.17  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.96/2.17  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.96/2.17  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 1.96/2.17  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.96/2.17  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.96/2.17  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 1.96/2.17  thf(t4_subset_1, axiom,
% 1.96/2.17    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.96/2.17  thf('0', plain,
% 1.96/2.17      (![X56 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X56))),
% 1.96/2.17      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.96/2.17  thf(t3_subset, axiom,
% 1.96/2.17    (![A:$i,B:$i]:
% 1.96/2.17     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.96/2.17  thf('1', plain,
% 1.96/2.17      (![X73 : $i, X74 : $i]:
% 1.96/2.17         ((r1_tarski @ X73 @ X74) | ~ (m1_subset_1 @ X73 @ (k1_zfmisc_1 @ X74)))),
% 1.96/2.17      inference('cnf', [status(esa)], [t3_subset])).
% 1.96/2.17  thf('2', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.96/2.17      inference('sup-', [status(thm)], ['0', '1'])).
% 1.96/2.17  thf(d1_zfmisc_1, axiom,
% 1.96/2.17    (![A:$i,B:$i]:
% 1.96/2.17     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 1.96/2.17       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 1.96/2.17  thf('3', plain,
% 1.96/2.17      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.96/2.17         (~ (r1_tarski @ X38 @ X39)
% 1.96/2.17          | (r2_hidden @ X38 @ X40)
% 1.96/2.17          | ((X40) != (k1_zfmisc_1 @ X39)))),
% 1.96/2.17      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.96/2.17  thf('4', plain,
% 1.96/2.17      (![X38 : $i, X39 : $i]:
% 1.96/2.17         ((r2_hidden @ X38 @ (k1_zfmisc_1 @ X39)) | ~ (r1_tarski @ X38 @ X39))),
% 1.96/2.17      inference('simplify', [status(thm)], ['3'])).
% 1.96/2.17  thf('5', plain, (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.96/2.17      inference('sup-', [status(thm)], ['2', '4'])).
% 1.96/2.17  thf(t63_subset_1, axiom,
% 1.96/2.17    (![A:$i,B:$i]:
% 1.96/2.17     ( ( r2_hidden @ A @ B ) =>
% 1.96/2.17       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 1.96/2.17  thf('6', plain,
% 1.96/2.17      (![X59 : $i, X60 : $i]:
% 1.96/2.17         ((m1_subset_1 @ (k1_tarski @ X59) @ (k1_zfmisc_1 @ X60))
% 1.96/2.17          | ~ (r2_hidden @ X59 @ X60))),
% 1.96/2.17      inference('cnf', [status(esa)], [t63_subset_1])).
% 1.96/2.17  thf('7', plain,
% 1.96/2.17      (![X0 : $i]:
% 1.96/2.17         (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 1.96/2.17          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 1.96/2.17      inference('sup-', [status(thm)], ['5', '6'])).
% 1.96/2.17  thf(involutiveness_k7_setfam_1, axiom,
% 1.96/2.17    (![A:$i,B:$i]:
% 1.96/2.17     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.96/2.17       ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) = ( B ) ) ))).
% 1.96/2.17  thf('8', plain,
% 1.96/2.17      (![X67 : $i, X68 : $i]:
% 1.96/2.17         (((k7_setfam_1 @ X68 @ (k7_setfam_1 @ X68 @ X67)) = (X67))
% 1.96/2.17          | ~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X68))))),
% 1.96/2.17      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 1.96/2.17  thf('9', plain,
% 1.96/2.17      (![X0 : $i]:
% 1.96/2.17         ((k7_setfam_1 @ X0 @ (k7_setfam_1 @ X0 @ (k1_tarski @ k1_xboole_0)))
% 1.96/2.17           = (k1_tarski @ k1_xboole_0))),
% 1.96/2.17      inference('sup-', [status(thm)], ['7', '8'])).
% 1.96/2.17  thf(t55_setfam_1, conjecture,
% 1.96/2.17    (![A:$i,B:$i]:
% 1.96/2.17     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.96/2.17       ( ( ( B ) = ( k1_tarski @ A ) ) =>
% 1.96/2.17         ( ( k7_setfam_1 @ A @ B ) = ( k1_tarski @ k1_xboole_0 ) ) ) ))).
% 1.96/2.17  thf(zf_stmt_0, negated_conjecture,
% 1.96/2.17    (~( ![A:$i,B:$i]:
% 1.96/2.17        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.96/2.17          ( ( ( B ) = ( k1_tarski @ A ) ) =>
% 1.96/2.17            ( ( k7_setfam_1 @ A @ B ) = ( k1_tarski @ k1_xboole_0 ) ) ) ) )),
% 1.96/2.17    inference('cnf.neg', [status(esa)], [t55_setfam_1])).
% 1.96/2.17  thf('10', plain,
% 1.96/2.17      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 1.96/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.17  thf('11', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 1.96/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.17  thf(t69_enumset1, axiom,
% 1.96/2.17    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.96/2.17  thf('12', plain,
% 1.96/2.17      (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 1.96/2.17      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.96/2.17  thf(t12_setfam_1, axiom,
% 1.96/2.17    (![A:$i,B:$i]:
% 1.96/2.17     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.96/2.17  thf('13', plain,
% 1.96/2.17      (![X69 : $i, X70 : $i]:
% 1.96/2.17         ((k1_setfam_1 @ (k2_tarski @ X69 @ X70)) = (k3_xboole_0 @ X69 @ X70))),
% 1.96/2.17      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.96/2.17  thf('14', plain,
% 1.96/2.17      (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 1.96/2.17      inference('sup+', [status(thm)], ['12', '13'])).
% 1.96/2.17  thf(idempotence_k3_xboole_0, axiom,
% 1.96/2.17    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.96/2.17  thf('15', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.96/2.17      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.96/2.17  thf('16', plain, (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (X0))),
% 1.96/2.17      inference('demod', [status(thm)], ['14', '15'])).
% 1.96/2.17  thf('17', plain, (((k1_setfam_1 @ sk_B_1) = (sk_A))),
% 1.96/2.17      inference('sup+', [status(thm)], ['11', '16'])).
% 1.96/2.17  thf('18', plain,
% 1.96/2.17      ((m1_subset_1 @ sk_B_1 @ 
% 1.96/2.17        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B_1))))),
% 1.96/2.17      inference('demod', [status(thm)], ['10', '17'])).
% 1.96/2.17  thf(t51_setfam_1, axiom,
% 1.96/2.17    (![A:$i,B:$i]:
% 1.96/2.17     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.96/2.17       ( ![C:$i]:
% 1.96/2.17         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.96/2.17           ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ ( k7_setfam_1 @ A @ C ) ) =>
% 1.96/2.17             ( r1_tarski @ B @ C ) ) ) ) ))).
% 1.96/2.17  thf('19', plain,
% 1.96/2.17      (![X81 : $i, X82 : $i, X83 : $i]:
% 1.96/2.17         (~ (m1_subset_1 @ X81 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X82)))
% 1.96/2.17          | (r1_tarski @ X83 @ X81)
% 1.96/2.17          | ~ (r1_tarski @ (k7_setfam_1 @ X82 @ X83) @ 
% 1.96/2.17               (k7_setfam_1 @ X82 @ X81))
% 1.96/2.17          | ~ (m1_subset_1 @ X83 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X82))))),
% 1.96/2.17      inference('cnf', [status(esa)], [t51_setfam_1])).
% 1.96/2.17  thf('20', plain,
% 1.96/2.17      (![X0 : $i]:
% 1.96/2.17         (~ (m1_subset_1 @ X0 @ 
% 1.96/2.17             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B_1))))
% 1.96/2.17          | ~ (r1_tarski @ (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ X0) @ 
% 1.96/2.17               (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1))
% 1.96/2.17          | (r1_tarski @ X0 @ sk_B_1))),
% 1.96/2.17      inference('sup-', [status(thm)], ['18', '19'])).
% 1.96/2.17  thf('21', plain,
% 1.96/2.17      ((~ (r1_tarski @ (k1_tarski @ k1_xboole_0) @ 
% 1.96/2.17           (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1))
% 1.96/2.17        | (r1_tarski @ 
% 1.96/2.17           (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ (k1_tarski @ k1_xboole_0)) @ 
% 1.96/2.17           sk_B_1)
% 1.96/2.17        | ~ (m1_subset_1 @ 
% 1.96/2.17             (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ (k1_tarski @ k1_xboole_0)) @ 
% 1.96/2.17             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B_1)))))),
% 1.96/2.17      inference('sup-', [status(thm)], ['9', '20'])).
% 1.96/2.17  thf('22', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 1.96/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.17  thf(d1_tarski, axiom,
% 1.96/2.17    (![A:$i,B:$i]:
% 1.96/2.17     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.96/2.17       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.96/2.17  thf('23', plain,
% 1.96/2.17      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.96/2.17         (((X6) != (X5)) | (r2_hidden @ X6 @ X7) | ((X7) != (k1_tarski @ X5)))),
% 1.96/2.17      inference('cnf', [status(esa)], [d1_tarski])).
% 1.96/2.17  thf('24', plain, (![X5 : $i]: (r2_hidden @ X5 @ (k1_tarski @ X5))),
% 1.96/2.17      inference('simplify', [status(thm)], ['23'])).
% 1.96/2.17  thf('25', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 1.96/2.17      inference('sup+', [status(thm)], ['22', '24'])).
% 1.96/2.17  thf('26', plain, (((k1_setfam_1 @ sk_B_1) = (sk_A))),
% 1.96/2.17      inference('sup+', [status(thm)], ['11', '16'])).
% 1.96/2.17  thf('27', plain, ((r2_hidden @ (k1_setfam_1 @ sk_B_1) @ sk_B_1)),
% 1.96/2.17      inference('demod', [status(thm)], ['25', '26'])).
% 1.96/2.17  thf('28', plain,
% 1.96/2.17      ((m1_subset_1 @ sk_B_1 @ 
% 1.96/2.17        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B_1))))),
% 1.96/2.17      inference('demod', [status(thm)], ['10', '17'])).
% 1.96/2.17  thf('29', plain,
% 1.96/2.17      (![X67 : $i, X68 : $i]:
% 1.96/2.17         (((k7_setfam_1 @ X68 @ (k7_setfam_1 @ X68 @ X67)) = (X67))
% 1.96/2.17          | ~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X68))))),
% 1.96/2.17      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 1.96/2.17  thf('30', plain,
% 1.96/2.17      (((k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ 
% 1.96/2.17         (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1)) = (sk_B_1))),
% 1.96/2.17      inference('sup-', [status(thm)], ['28', '29'])).
% 1.96/2.17  thf(d8_setfam_1, axiom,
% 1.96/2.17    (![A:$i,B:$i]:
% 1.96/2.17     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.96/2.17       ( ![C:$i]:
% 1.96/2.17         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.96/2.17           ( ( ( C ) = ( k7_setfam_1 @ A @ B ) ) <=>
% 1.96/2.17             ( ![D:$i]:
% 1.96/2.17               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 1.96/2.17                 ( ( r2_hidden @ D @ C ) <=>
% 1.96/2.17                   ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) ) ))).
% 1.96/2.17  thf('31', plain,
% 1.96/2.17      (![X61 : $i, X62 : $i, X63 : $i, X64 : $i]:
% 1.96/2.17         (~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X62)))
% 1.96/2.17          | ((X61) != (k7_setfam_1 @ X62 @ X63))
% 1.96/2.17          | (r2_hidden @ (k3_subset_1 @ X62 @ X64) @ X63)
% 1.96/2.17          | ~ (r2_hidden @ X64 @ X61)
% 1.96/2.17          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ X62))
% 1.96/2.17          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X62))))),
% 1.96/2.17      inference('cnf', [status(esa)], [d8_setfam_1])).
% 1.96/2.17  thf('32', plain,
% 1.96/2.17      (![X62 : $i, X63 : $i, X64 : $i]:
% 1.96/2.17         (~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X62)))
% 1.96/2.17          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ X62))
% 1.96/2.17          | ~ (r2_hidden @ X64 @ (k7_setfam_1 @ X62 @ X63))
% 1.96/2.17          | (r2_hidden @ (k3_subset_1 @ X62 @ X64) @ X63)
% 1.96/2.17          | ~ (m1_subset_1 @ (k7_setfam_1 @ X62 @ X63) @ 
% 1.96/2.17               (k1_zfmisc_1 @ (k1_zfmisc_1 @ X62))))),
% 1.96/2.17      inference('simplify', [status(thm)], ['31'])).
% 1.96/2.17  thf('33', plain,
% 1.96/2.17      (![X0 : $i]:
% 1.96/2.17         (~ (m1_subset_1 @ sk_B_1 @ 
% 1.96/2.17             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B_1))))
% 1.96/2.17          | (r2_hidden @ (k3_subset_1 @ (k1_setfam_1 @ sk_B_1) @ X0) @ 
% 1.96/2.17             (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1))
% 1.96/2.17          | ~ (r2_hidden @ X0 @ 
% 1.96/2.17               (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ 
% 1.96/2.17                (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1)))
% 1.96/2.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B_1)))
% 1.96/2.17          | ~ (m1_subset_1 @ (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1) @ 
% 1.96/2.17               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B_1)))))),
% 1.96/2.17      inference('sup-', [status(thm)], ['30', '32'])).
% 1.96/2.17  thf('34', plain,
% 1.96/2.17      ((m1_subset_1 @ sk_B_1 @ 
% 1.96/2.17        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B_1))))),
% 1.96/2.17      inference('demod', [status(thm)], ['10', '17'])).
% 1.96/2.17  thf('35', plain,
% 1.96/2.17      (((k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ 
% 1.96/2.17         (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1)) = (sk_B_1))),
% 1.96/2.17      inference('sup-', [status(thm)], ['28', '29'])).
% 1.96/2.17  thf('36', plain,
% 1.96/2.17      (![X0 : $i]:
% 1.96/2.17         ((r2_hidden @ (k3_subset_1 @ (k1_setfam_1 @ sk_B_1) @ X0) @ 
% 1.96/2.17           (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1))
% 1.96/2.17          | ~ (r2_hidden @ X0 @ sk_B_1)
% 1.96/2.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B_1)))
% 1.96/2.17          | ~ (m1_subset_1 @ (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1) @ 
% 1.96/2.17               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B_1)))))),
% 1.96/2.17      inference('demod', [status(thm)], ['33', '34', '35'])).
% 1.96/2.17  thf('37', plain,
% 1.96/2.17      ((m1_subset_1 @ sk_B_1 @ 
% 1.96/2.17        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B_1))))),
% 1.96/2.17      inference('demod', [status(thm)], ['10', '17'])).
% 1.96/2.17  thf(dt_k7_setfam_1, axiom,
% 1.96/2.17    (![A:$i,B:$i]:
% 1.96/2.17     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.96/2.17       ( m1_subset_1 @
% 1.96/2.17         ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 1.96/2.17  thf('38', plain,
% 1.96/2.17      (![X65 : $i, X66 : $i]:
% 1.96/2.17         ((m1_subset_1 @ (k7_setfam_1 @ X65 @ X66) @ 
% 1.96/2.17           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X65)))
% 1.96/2.17          | ~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X65))))),
% 1.96/2.17      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 1.96/2.17  thf('39', plain,
% 1.96/2.17      ((m1_subset_1 @ (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1) @ 
% 1.96/2.17        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B_1))))),
% 1.96/2.17      inference('sup-', [status(thm)], ['37', '38'])).
% 1.96/2.17  thf('40', plain,
% 1.96/2.17      (![X0 : $i]:
% 1.96/2.17         ((r2_hidden @ (k3_subset_1 @ (k1_setfam_1 @ sk_B_1) @ X0) @ 
% 1.96/2.17           (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1))
% 1.96/2.17          | ~ (r2_hidden @ X0 @ sk_B_1)
% 1.96/2.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B_1))))),
% 1.96/2.17      inference('demod', [status(thm)], ['36', '39'])).
% 1.96/2.17  thf('41', plain,
% 1.96/2.17      ((m1_subset_1 @ sk_B_1 @ 
% 1.96/2.17        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B_1))))),
% 1.96/2.17      inference('demod', [status(thm)], ['10', '17'])).
% 1.96/2.17  thf(t4_subset, axiom,
% 1.96/2.17    (![A:$i,B:$i,C:$i]:
% 1.96/2.17     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 1.96/2.17       ( m1_subset_1 @ A @ C ) ))).
% 1.96/2.17  thf('42', plain,
% 1.96/2.17      (![X78 : $i, X79 : $i, X80 : $i]:
% 1.96/2.17         (~ (r2_hidden @ X78 @ X79)
% 1.96/2.17          | ~ (m1_subset_1 @ X79 @ (k1_zfmisc_1 @ X80))
% 1.96/2.17          | (m1_subset_1 @ X78 @ X80))),
% 1.96/2.17      inference('cnf', [status(esa)], [t4_subset])).
% 1.96/2.17  thf('43', plain,
% 1.96/2.17      (![X0 : $i]:
% 1.96/2.17         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B_1)))
% 1.96/2.17          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 1.96/2.17      inference('sup-', [status(thm)], ['41', '42'])).
% 1.96/2.17  thf('44', plain,
% 1.96/2.17      (![X0 : $i]:
% 1.96/2.17         (~ (r2_hidden @ X0 @ sk_B_1)
% 1.96/2.17          | (r2_hidden @ (k3_subset_1 @ (k1_setfam_1 @ sk_B_1) @ X0) @ 
% 1.96/2.17             (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1)))),
% 1.96/2.17      inference('clc', [status(thm)], ['40', '43'])).
% 1.96/2.17  thf('45', plain,
% 1.96/2.17      ((r2_hidden @ 
% 1.96/2.17        (k3_subset_1 @ (k1_setfam_1 @ sk_B_1) @ (k1_setfam_1 @ sk_B_1)) @ 
% 1.96/2.17        (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1))),
% 1.96/2.17      inference('sup-', [status(thm)], ['27', '44'])).
% 1.96/2.17  thf('46', plain,
% 1.96/2.17      (![X56 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X56))),
% 1.96/2.17      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.96/2.17  thf(involutiveness_k3_subset_1, axiom,
% 1.96/2.17    (![A:$i,B:$i]:
% 1.96/2.17     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.96/2.17       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.96/2.17  thf('47', plain,
% 1.96/2.17      (![X51 : $i, X52 : $i]:
% 1.96/2.17         (((k3_subset_1 @ X52 @ (k3_subset_1 @ X52 @ X51)) = (X51))
% 1.96/2.17          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ X52)))),
% 1.96/2.17      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.96/2.17  thf('48', plain,
% 1.96/2.17      (![X0 : $i]:
% 1.96/2.17         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 1.96/2.17      inference('sup-', [status(thm)], ['46', '47'])).
% 1.96/2.17  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 1.96/2.17  thf('49', plain, (![X49 : $i]: ((k1_subset_1 @ X49) = (k1_xboole_0))),
% 1.96/2.17      inference('cnf', [status(esa)], [d3_subset_1])).
% 1.96/2.17  thf(t22_subset_1, axiom,
% 1.96/2.17    (![A:$i]:
% 1.96/2.17     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 1.96/2.17  thf('50', plain,
% 1.96/2.17      (![X53 : $i]:
% 1.96/2.17         ((k2_subset_1 @ X53) = (k3_subset_1 @ X53 @ (k1_subset_1 @ X53)))),
% 1.96/2.17      inference('cnf', [status(esa)], [t22_subset_1])).
% 1.96/2.17  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.96/2.17  thf('51', plain, (![X50 : $i]: ((k2_subset_1 @ X50) = (X50))),
% 1.96/2.17      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.96/2.17  thf('52', plain,
% 1.96/2.17      (![X53 : $i]: ((X53) = (k3_subset_1 @ X53 @ (k1_subset_1 @ X53)))),
% 1.96/2.17      inference('demod', [status(thm)], ['50', '51'])).
% 1.96/2.17  thf('53', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 1.96/2.17      inference('sup+', [status(thm)], ['49', '52'])).
% 1.96/2.17  thf('54', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 1.96/2.17      inference('demod', [status(thm)], ['48', '53'])).
% 1.96/2.17  thf('55', plain,
% 1.96/2.17      ((r2_hidden @ k1_xboole_0 @ 
% 1.96/2.17        (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1))),
% 1.96/2.17      inference('demod', [status(thm)], ['45', '54'])).
% 1.96/2.17  thf('56', plain,
% 1.96/2.17      (![X59 : $i, X60 : $i]:
% 1.96/2.17         ((m1_subset_1 @ (k1_tarski @ X59) @ (k1_zfmisc_1 @ X60))
% 1.96/2.17          | ~ (r2_hidden @ X59 @ X60))),
% 1.96/2.17      inference('cnf', [status(esa)], [t63_subset_1])).
% 1.96/2.17  thf('57', plain,
% 1.96/2.17      ((m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 1.96/2.17        (k1_zfmisc_1 @ (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1)))),
% 1.96/2.17      inference('sup-', [status(thm)], ['55', '56'])).
% 1.96/2.17  thf('58', plain,
% 1.96/2.17      (![X73 : $i, X74 : $i]:
% 1.96/2.17         ((r1_tarski @ X73 @ X74) | ~ (m1_subset_1 @ X73 @ (k1_zfmisc_1 @ X74)))),
% 1.96/2.17      inference('cnf', [status(esa)], [t3_subset])).
% 1.96/2.17  thf('59', plain,
% 1.96/2.17      ((r1_tarski @ (k1_tarski @ k1_xboole_0) @ 
% 1.96/2.17        (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1))),
% 1.96/2.17      inference('sup-', [status(thm)], ['57', '58'])).
% 1.96/2.17  thf('60', plain,
% 1.96/2.17      (![X0 : $i]:
% 1.96/2.17         (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 1.96/2.17          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 1.96/2.17      inference('sup-', [status(thm)], ['5', '6'])).
% 1.96/2.17  thf('61', plain,
% 1.96/2.17      (![X65 : $i, X66 : $i]:
% 1.96/2.17         ((m1_subset_1 @ (k7_setfam_1 @ X65 @ X66) @ 
% 1.96/2.17           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X65)))
% 1.96/2.17          | ~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X65))))),
% 1.96/2.17      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 1.96/2.17  thf('62', plain,
% 1.96/2.17      (![X0 : $i]:
% 1.96/2.17         (m1_subset_1 @ (k7_setfam_1 @ X0 @ (k1_tarski @ k1_xboole_0)) @ 
% 1.96/2.17          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 1.96/2.17      inference('sup-', [status(thm)], ['60', '61'])).
% 1.96/2.17  thf('63', plain,
% 1.96/2.17      ((r1_tarski @ 
% 1.96/2.17        (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ (k1_tarski @ k1_xboole_0)) @ 
% 1.96/2.17        sk_B_1)),
% 1.96/2.17      inference('demod', [status(thm)], ['21', '59', '62'])).
% 1.96/2.17  thf('64', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 1.96/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.17  thf(t39_zfmisc_1, axiom,
% 1.96/2.17    (![A:$i,B:$i]:
% 1.96/2.17     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 1.96/2.17       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 1.96/2.17  thf('65', plain,
% 1.96/2.17      (![X46 : $i, X47 : $i]:
% 1.96/2.17         (((X47) = (k1_tarski @ X46))
% 1.96/2.17          | ((X47) = (k1_xboole_0))
% 1.96/2.17          | ~ (r1_tarski @ X47 @ (k1_tarski @ X46)))),
% 1.96/2.17      inference('cnf', [status(esa)], [t39_zfmisc_1])).
% 1.96/2.17  thf('66', plain,
% 1.96/2.17      (![X0 : $i]:
% 1.96/2.17         (~ (r1_tarski @ X0 @ sk_B_1)
% 1.96/2.17          | ((X0) = (k1_xboole_0))
% 1.96/2.17          | ((X0) = (k1_tarski @ sk_A)))),
% 1.96/2.17      inference('sup-', [status(thm)], ['64', '65'])).
% 1.96/2.17  thf('67', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 1.96/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.17  thf('68', plain,
% 1.96/2.17      (![X0 : $i]:
% 1.96/2.17         (~ (r1_tarski @ X0 @ sk_B_1)
% 1.96/2.17          | ((X0) = (k1_xboole_0))
% 1.96/2.17          | ((X0) = (sk_B_1)))),
% 1.96/2.17      inference('demod', [status(thm)], ['66', '67'])).
% 1.96/2.17  thf('69', plain,
% 1.96/2.17      ((((k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ (k1_tarski @ k1_xboole_0))
% 1.96/2.17          = (sk_B_1))
% 1.96/2.17        | ((k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ (k1_tarski @ k1_xboole_0))
% 1.96/2.17            = (k1_xboole_0)))),
% 1.96/2.17      inference('sup-', [status(thm)], ['63', '68'])).
% 1.96/2.17  thf('70', plain,
% 1.96/2.17      (![X0 : $i]:
% 1.96/2.17         (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 1.96/2.17          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 1.96/2.17      inference('sup-', [status(thm)], ['5', '6'])).
% 1.96/2.17  thf(t46_setfam_1, axiom,
% 1.96/2.17    (![A:$i,B:$i]:
% 1.96/2.17     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.96/2.17       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.96/2.17            ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 1.96/2.17  thf('71', plain,
% 1.96/2.17      (![X76 : $i, X77 : $i]:
% 1.96/2.17         (((k7_setfam_1 @ X76 @ X77) != (k1_xboole_0))
% 1.96/2.17          | ((X77) = (k1_xboole_0))
% 1.96/2.17          | ~ (m1_subset_1 @ X77 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X76))))),
% 1.96/2.17      inference('cnf', [status(esa)], [t46_setfam_1])).
% 1.96/2.17  thf('72', plain,
% 1.96/2.17      (![X0 : $i]:
% 1.96/2.17         (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))
% 1.96/2.17          | ((k7_setfam_1 @ X0 @ (k1_tarski @ k1_xboole_0)) != (k1_xboole_0)))),
% 1.96/2.17      inference('sup-', [status(thm)], ['70', '71'])).
% 1.96/2.17  thf(t20_zfmisc_1, axiom,
% 1.96/2.17    (![A:$i,B:$i]:
% 1.96/2.17     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.96/2.17         ( k1_tarski @ A ) ) <=>
% 1.96/2.17       ( ( A ) != ( B ) ) ))).
% 1.96/2.17  thf('73', plain,
% 1.96/2.17      (![X43 : $i, X44 : $i]:
% 1.96/2.17         (((X44) != (X43))
% 1.96/2.17          | ((k4_xboole_0 @ (k1_tarski @ X44) @ (k1_tarski @ X43))
% 1.96/2.17              != (k1_tarski @ X44)))),
% 1.96/2.17      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 1.96/2.17  thf('74', plain,
% 1.96/2.17      (![X43 : $i]:
% 1.96/2.17         ((k4_xboole_0 @ (k1_tarski @ X43) @ (k1_tarski @ X43))
% 1.96/2.17           != (k1_tarski @ X43))),
% 1.96/2.17      inference('simplify', [status(thm)], ['73'])).
% 1.96/2.17  thf('75', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.96/2.17      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.96/2.17  thf(t100_xboole_1, axiom,
% 1.96/2.17    (![A:$i,B:$i]:
% 1.96/2.17     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.96/2.17  thf('76', plain,
% 1.96/2.17      (![X2 : $i, X3 : $i]:
% 1.96/2.17         ((k4_xboole_0 @ X2 @ X3)
% 1.96/2.17           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 1.96/2.17      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.96/2.17  thf('77', plain,
% 1.96/2.17      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.96/2.17      inference('sup+', [status(thm)], ['75', '76'])).
% 1.96/2.17  thf(t92_xboole_1, axiom,
% 1.96/2.17    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.96/2.17  thf('78', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ X4) = (k1_xboole_0))),
% 1.96/2.17      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.96/2.17  thf('79', plain, (![X43 : $i]: ((k1_xboole_0) != (k1_tarski @ X43))),
% 1.96/2.17      inference('demod', [status(thm)], ['74', '77', '78'])).
% 1.96/2.17  thf('80', plain,
% 1.96/2.17      (![X0 : $i]:
% 1.96/2.17         ((k7_setfam_1 @ X0 @ (k1_tarski @ k1_xboole_0)) != (k1_xboole_0))),
% 1.96/2.17      inference('clc', [status(thm)], ['72', '79'])).
% 1.96/2.17  thf('81', plain,
% 1.96/2.17      (((k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ 
% 1.96/2.17         (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1)) = (sk_B_1))),
% 1.96/2.17      inference('sup-', [status(thm)], ['28', '29'])).
% 1.96/2.17  thf('82', plain,
% 1.96/2.17      (![X0 : $i]:
% 1.96/2.17         (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 1.96/2.17          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 1.96/2.17      inference('sup-', [status(thm)], ['5', '6'])).
% 1.96/2.17  thf(t53_setfam_1, axiom,
% 1.96/2.17    (![A:$i,B:$i]:
% 1.96/2.17     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.96/2.17       ( ![C:$i]:
% 1.96/2.17         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.96/2.17           ( ( ( k7_setfam_1 @ A @ B ) = ( k7_setfam_1 @ A @ C ) ) =>
% 1.96/2.17             ( ( B ) = ( C ) ) ) ) ) ))).
% 1.96/2.17  thf('83', plain,
% 1.96/2.17      (![X84 : $i, X85 : $i, X86 : $i]:
% 1.96/2.17         (~ (m1_subset_1 @ X84 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X85)))
% 1.96/2.17          | ((X86) = (X84))
% 1.96/2.17          | ((k7_setfam_1 @ X85 @ X86) != (k7_setfam_1 @ X85 @ X84))
% 1.96/2.17          | ~ (m1_subset_1 @ X86 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X85))))),
% 1.96/2.17      inference('cnf', [status(esa)], [t53_setfam_1])).
% 1.96/2.17  thf('84', plain,
% 1.96/2.17      (![X0 : $i, X1 : $i]:
% 1.96/2.17         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))
% 1.96/2.17          | ((k7_setfam_1 @ X0 @ X1)
% 1.96/2.17              != (k7_setfam_1 @ X0 @ (k1_tarski @ k1_xboole_0)))
% 1.96/2.17          | ((X1) = (k1_tarski @ k1_xboole_0)))),
% 1.96/2.17      inference('sup-', [status(thm)], ['82', '83'])).
% 1.96/2.17  thf('85', plain,
% 1.96/2.17      ((((sk_B_1)
% 1.96/2.17          != (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ (k1_tarski @ k1_xboole_0)))
% 1.96/2.17        | ((k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1)
% 1.96/2.17            = (k1_tarski @ k1_xboole_0))
% 1.96/2.17        | ~ (m1_subset_1 @ (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1) @ 
% 1.96/2.17             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B_1)))))),
% 1.96/2.17      inference('sup-', [status(thm)], ['81', '84'])).
% 1.96/2.17  thf('86', plain,
% 1.96/2.17      ((m1_subset_1 @ (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1) @ 
% 1.96/2.17        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B_1))))),
% 1.96/2.17      inference('sup-', [status(thm)], ['37', '38'])).
% 1.96/2.17  thf('87', plain,
% 1.96/2.17      ((((sk_B_1)
% 1.96/2.17          != (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ (k1_tarski @ k1_xboole_0)))
% 1.96/2.17        | ((k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1)
% 1.96/2.17            = (k1_tarski @ k1_xboole_0)))),
% 1.96/2.17      inference('demod', [status(thm)], ['85', '86'])).
% 1.96/2.17  thf('88', plain,
% 1.96/2.17      (((k7_setfam_1 @ sk_A @ sk_B_1) != (k1_tarski @ k1_xboole_0))),
% 1.96/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.17  thf('89', plain, (((k1_setfam_1 @ sk_B_1) = (sk_A))),
% 1.96/2.17      inference('sup+', [status(thm)], ['11', '16'])).
% 1.96/2.17  thf('90', plain,
% 1.96/2.17      (((k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1)
% 1.96/2.17         != (k1_tarski @ k1_xboole_0))),
% 1.96/2.17      inference('demod', [status(thm)], ['88', '89'])).
% 1.96/2.17  thf('91', plain,
% 1.96/2.17      (((sk_B_1)
% 1.96/2.17         != (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ (k1_tarski @ k1_xboole_0)))),
% 1.96/2.17      inference('simplify_reflect-', [status(thm)], ['87', '90'])).
% 1.96/2.17  thf('92', plain, ($false),
% 1.96/2.17      inference('simplify_reflect-', [status(thm)], ['69', '80', '91'])).
% 1.96/2.17  
% 1.96/2.17  % SZS output end Refutation
% 1.96/2.17  
% 1.96/2.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
