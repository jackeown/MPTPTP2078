%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0420+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kIGwKqWF2D

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:53 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 113 expanded)
%              Number of leaves         :   11 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :  442 (1445 expanded)
%              Number of equality atoms :    5 (   9 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(t52_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ C )
          <=> ( r1_tarski @ B @ ( k7_setfam_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
           => ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ C )
            <=> ( r1_tarski @ B @ ( k7_setfam_1 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_setfam_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k7_setfam_1 @ sk_A @ sk_C ) )
    | ~ ( r1_tarski @ ( k7_setfam_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k7_setfam_1 @ sk_A @ sk_C ) )
   <= ~ ( r1_tarski @ sk_B @ ( k7_setfam_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k7_setfam_1 @ sk_A @ sk_C ) )
    | ~ ( r1_tarski @ ( k7_setfam_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r1_tarski @ sk_B @ ( k7_setfam_1 @ sk_A @ sk_C ) )
    | ( r1_tarski @ ( k7_setfam_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_tarski @ sk_B @ ( k7_setfam_1 @ sk_A @ sk_C ) )
   <= ( r1_tarski @ sk_B @ ( k7_setfam_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
        = B ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k7_setfam_1 @ X3 @ ( k7_setfam_1 @ X3 @ X2 ) )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('7',plain,
    ( ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t51_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ ( k7_setfam_1 @ A @ C ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) )
      | ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ ( k7_setfam_1 @ X5 @ X6 ) @ ( k7_setfam_1 @ X5 @ X4 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[t51_setfam_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ~ ( r1_tarski @ ( k7_setfam_1 @ sk_A @ X0 ) @ ( k7_setfam_1 @ sk_A @ sk_C ) )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k7_setfam_1 @ sk_A @ sk_C ) )
    | ( r1_tarski @ ( k7_setfam_1 @ sk_A @ sk_B ) @ sk_C )
    | ~ ( m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('14',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k7_setfam_1 @ sk_A @ sk_C ) )
    | ( r1_tarski @ ( k7_setfam_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,
    ( ( r1_tarski @ ( k7_setfam_1 @ sk_A @ sk_B ) @ sk_C )
   <= ( r1_tarski @ sk_B @ ( k7_setfam_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','15'])).

thf('17',plain,
    ( ~ ( r1_tarski @ ( k7_setfam_1 @ sk_A @ sk_B ) @ sk_C )
   <= ~ ( r1_tarski @ ( k7_setfam_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,
    ( ( r1_tarski @ ( k7_setfam_1 @ sk_A @ sk_B ) @ sk_C )
    | ~ ( r1_tarski @ sk_B @ ( k7_setfam_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( r1_tarski @ sk_B @ ( k7_setfam_1 @ sk_A @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['2','18'])).

thf('20',plain,(
    ~ ( r1_tarski @ sk_B @ ( k7_setfam_1 @ sk_A @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['1','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('24',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) )
      | ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ ( k7_setfam_1 @ X5 @ X6 ) @ ( k7_setfam_1 @ X5 @ X4 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[t51_setfam_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ~ ( r1_tarski @ ( k7_setfam_1 @ sk_A @ X0 ) @ ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_C ) ) )
      | ( r1_tarski @ X0 @ ( k7_setfam_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k7_setfam_1 @ X3 @ ( k7_setfam_1 @ X3 @ X2 ) )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('29',plain,
    ( ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ~ ( r1_tarski @ ( k7_setfam_1 @ sk_A @ X0 ) @ sk_C )
      | ( r1_tarski @ X0 @ ( k7_setfam_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('31',plain,
    ( ( r1_tarski @ sk_B @ ( k7_setfam_1 @ sk_A @ sk_C ) )
    | ~ ( r1_tarski @ ( k7_setfam_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['21','30'])).

thf('32',plain,
    ( ( r1_tarski @ ( k7_setfam_1 @ sk_A @ sk_B ) @ sk_C )
   <= ( r1_tarski @ ( k7_setfam_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('33',plain,
    ( ( r1_tarski @ ( k7_setfam_1 @ sk_A @ sk_B ) @ sk_C )
    | ( r1_tarski @ sk_B @ ( k7_setfam_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('34',plain,(
    r1_tarski @ ( k7_setfam_1 @ sk_A @ sk_B ) @ sk_C ),
    inference('sat_resolution*',[status(thm)],['2','18','33'])).

thf('35',plain,(
    r1_tarski @ ( k7_setfam_1 @ sk_A @ sk_B ) @ sk_C ),
    inference(simpl_trail,[status(thm)],['32','34'])).

thf('36',plain,(
    r1_tarski @ sk_B @ ( k7_setfam_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['31','35'])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['20','36'])).


%------------------------------------------------------------------------------
