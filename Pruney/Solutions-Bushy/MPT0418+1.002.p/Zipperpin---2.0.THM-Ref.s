%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0418+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bs2ixLO2yW

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:52 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   53 (  93 expanded)
%              Number of leaves         :   13 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :  547 (1187 expanded)
%              Number of equality atoms :    7 (  10 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

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

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X9 @ ( k3_subset_1 @ X9 @ X8 ) )
        = X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('4',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_C @ sk_B )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('9',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

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

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) )
      | ( X0
       != ( k7_setfam_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X1 @ X3 ) @ X2 )
      | ~ ( r2_hidden @ X3 @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('11',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ ( k7_setfam_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X1 @ X3 ) @ X2 )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X1 @ X2 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ~ ( m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) ) @ sk_B ) )
   <= ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('18',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) ) @ sk_B )
   <= ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,
    ( ( r2_hidden @ sk_C @ sk_B )
   <= ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['4','19'])).

thf('21',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_B )
   <= ~ ( r2_hidden @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ( r2_hidden @ sk_C @ sk_B )
    | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r2_hidden @ sk_C @ sk_B )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('24',plain,
    ( ( r2_hidden @ sk_C @ sk_B )
   <= ( r2_hidden @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('25',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('26',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) )
      | ( X0
       != ( k7_setfam_1 @ X1 @ X2 ) )
      | ( r2_hidden @ X3 @ X0 )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X1 @ X3 ) @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('28',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X1 @ X3 ) @ X2 )
      | ( r2_hidden @ X3 @ ( k7_setfam_1 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X1 @ X2 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('34',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_B )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['24','34'])).

thf('36',plain,
    ( ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) )
   <= ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_B )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','22','23','37'])).


%------------------------------------------------------------------------------
