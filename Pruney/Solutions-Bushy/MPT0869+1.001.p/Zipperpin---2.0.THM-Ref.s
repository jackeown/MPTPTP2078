%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0869+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bOJuhzSAHP

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:37 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 136 expanded)
%              Number of leaves         :   13 (  43 expanded)
%              Depth                    :   15
%              Number of atoms          :  309 (1239 expanded)
%              Number of equality atoms :   61 ( 236 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf('#_fresh_sk1_type',type,(
    '#_fresh_sk1': $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf('#_fresh_sk2_type',type,(
    '#_fresh_sk2': $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t28_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( k3_mcart_1 @ A @ B @ C )
        = ( k3_mcart_1 @ D @ E @ F ) )
     => ( ( A = D )
        & ( B = E )
        & ( C = F ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( ( k3_mcart_1 @ A @ B @ C )
          = ( k3_mcart_1 @ D @ E @ F ) )
       => ( ( A = D )
          & ( B = E )
          & ( C = F ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_mcart_1])).

thf('0',plain,
    ( ( k3_mcart_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_mcart_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k3_mcart_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_mcart_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(t33_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( k4_tarski @ A @ B )
        = ( k4_tarski @ C @ D ) )
     => ( ( A = C )
        & ( B = D ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X6 = X5 )
      | ( ( k4_tarski @ X4 @ X6 )
       != ( k4_tarski @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t33_zfmisc_1])).

thf('4',plain,(
    ! [X4: $i,X6: $i] :
      ( ( '#_fresh_sk2' @ ( k4_tarski @ X4 @ X6 ) )
      = X6 ) ),
    inference(inj_rec,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( '#_fresh_sk2' @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,
    ( ( '#_fresh_sk2' @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) )
    = sk_F ),
    inference('sup+',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( '#_fresh_sk2' @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('8',plain,(
    sk_C = sk_F ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k3_mcart_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_mcart_1 @ sk_D @ sk_E @ sk_C ) ),
    inference(demod,[status(thm)],['0','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('11',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X4 = X3 )
      | ( ( k4_tarski @ X4 @ X6 )
       != ( k4_tarski @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t33_zfmisc_1])).

thf('12',plain,(
    ! [X4: $i,X6: $i] :
      ( ( '#_fresh_sk1' @ ( k4_tarski @ X4 @ X6 ) )
      = X4 ) ),
    inference(inj_rec,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( '#_fresh_sk1' @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','12'])).

thf('14',plain,
    ( ( '#_fresh_sk1' @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) )
    = ( k4_tarski @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['9','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( '#_fresh_sk1' @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','12'])).

thf('16',plain,
    ( ( k4_tarski @ sk_A @ sk_B )
    = ( k4_tarski @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X4: $i,X6: $i] :
      ( ( '#_fresh_sk2' @ ( k4_tarski @ X4 @ X6 ) )
      = X6 ) ),
    inference(inj_rec,[status(thm)],['3'])).

thf('18',plain,
    ( ( '#_fresh_sk2' @ ( k4_tarski @ sk_A @ sk_B ) )
    = sk_E ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X4: $i,X6: $i] :
      ( ( '#_fresh_sk2' @ ( k4_tarski @ X4 @ X6 ) )
      = X6 ) ),
    inference(inj_rec,[status(thm)],['3'])).

thf('20',plain,(
    sk_B = sk_E ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_A != sk_D )
    | ( sk_B != sk_E )
    | ( sk_C != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( sk_B != sk_E )
   <= ( sk_B != sk_E ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,(
    sk_C = sk_F ),
    inference(demod,[status(thm)],['6','7'])).

thf('24',plain,
    ( ( sk_C != sk_F )
   <= ( sk_C != sk_F ) ),
    inference(split,[status(esa)],['21'])).

thf('25',plain,
    ( ( sk_C != sk_C )
   <= ( sk_C != sk_F ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    sk_C = sk_F ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( k4_tarski @ sk_A @ sk_B )
    = ( k4_tarski @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('28',plain,(
    ! [X4: $i,X6: $i] :
      ( ( '#_fresh_sk1' @ ( k4_tarski @ X4 @ X6 ) )
      = X4 ) ),
    inference(inj_rec,[status(thm)],['11'])).

thf('29',plain,
    ( ( '#_fresh_sk1' @ ( k4_tarski @ sk_A @ sk_B ) )
    = sk_D ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X4: $i,X6: $i] :
      ( ( '#_fresh_sk1' @ ( k4_tarski @ X4 @ X6 ) )
      = X4 ) ),
    inference(inj_rec,[status(thm)],['11'])).

thf('31',plain,(
    sk_A = sk_D ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_A != sk_D )
   <= ( sk_A != sk_D ) ),
    inference(split,[status(esa)],['21'])).

thf('33',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A != sk_D ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    sk_A = sk_D ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( sk_B != sk_E )
    | ( sk_A != sk_D )
    | ( sk_C != sk_F ) ),
    inference(split,[status(esa)],['21'])).

thf('36',plain,(
    sk_B != sk_E ),
    inference('sat_resolution*',[status(thm)],['26','34','35'])).

thf('37',plain,(
    sk_B != sk_E ),
    inference(simpl_trail,[status(thm)],['22','36'])).

thf('38',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['20','37'])).


%------------------------------------------------------------------------------
