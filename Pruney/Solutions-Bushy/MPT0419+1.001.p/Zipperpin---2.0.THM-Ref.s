%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0419+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Oz9X72XhNC

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:52 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   61 (  98 expanded)
%              Number of leaves         :   16 (  36 expanded)
%              Depth                    :   13
%              Number of atoms          :  581 (1182 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t51_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ ( k7_setfam_1 @ A @ C ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
           => ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ ( k7_setfam_1 @ A @ C ) )
             => ( r1_tarski @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t51_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
        = B ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k7_setfam_1 @ X11 @ ( k7_setfam_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('4',plain,
    ( ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['2','3'])).

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

thf('5',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) )
      | ( X4
       != ( k7_setfam_1 @ X5 @ X6 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X5 @ X7 ) @ X6 )
      | ~ ( r2_hidden @ X7 @ X4 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('6',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r2_hidden @ X7 @ ( k7_setfam_1 @ X5 @ X6 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X5 @ X7 ) @ X6 )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X5 @ X6 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['2','3'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('12',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['7','8','9','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('15',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( m1_subset_1 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_C @ X0 @ sk_B ) ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['1','17'])).

thf('19',plain,(
    r1_tarski @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k7_setfam_1 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_C @ X0 @ sk_B ) ) @ ( k7_setfam_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k7_setfam_1 @ X11 @ ( k7_setfam_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('25',plain,
    ( ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_C_1 ) )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) )
      | ( X4
       != ( k7_setfam_1 @ X5 @ X6 ) )
      | ( r2_hidden @ X7 @ X4 )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X5 @ X7 ) @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('27',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X5 @ X7 ) @ X6 )
      | ( r2_hidden @ X7 @ ( k7_setfam_1 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X5 @ X6 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_C_1 ) ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ ( k7_setfam_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_C_1 ) )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['23','24'])).

thf('31',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('33',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ ( k7_setfam_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['28','29','30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['22','34'])).

thf('36',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_C_1 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('41',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    $false ),
    inference(demod,[status(thm)],['0','42'])).


%------------------------------------------------------------------------------
