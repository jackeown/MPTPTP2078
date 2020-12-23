%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1091+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TyboBo2Jan

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 253 expanded)
%              Number of leaves         :   18 (  77 expanded)
%              Depth                    :   12
%              Number of atoms          :  395 (1722 expanded)
%              Number of equality atoms :    5 (  36 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t25_finset_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_finset_1 @ A )
        & ! [B: $i] :
            ( ( r2_hidden @ B @ A )
           => ( v1_finset_1 @ B ) ) )
    <=> ( v1_finset_1 @ ( k3_tarski @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_finset_1 @ A )
          & ! [B: $i] :
              ( ( r2_hidden @ B @ A )
             => ( v1_finset_1 @ B ) ) )
      <=> ( v1_finset_1 @ ( k3_tarski @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_finset_1])).

thf('0',plain,
    ( ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ sk_A )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
   <= ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
    | ( v1_finset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v1_finset_1 @ sk_A )
   <= ( v1_finset_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(l22_finset_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_finset_1 @ A )
        & ! [B: $i] :
            ( ( r2_hidden @ B @ A )
           => ( v1_finset_1 @ B ) ) )
     => ( v1_finset_1 @ ( k3_tarski @ A ) ) ) )).

thf('4',plain,(
    ! [X3: $i] :
      ( ( v1_finset_1 @ ( k3_tarski @ X3 ) )
      | ( r2_hidden @ ( sk_B @ X3 ) @ X3 )
      | ~ ( v1_finset_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l22_finset_1])).

thf('5',plain,(
    ! [X11: $i] :
      ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
      | ( v1_finset_1 @ X11 )
      | ~ ( r2_hidden @ X11 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ! [X11: $i] :
        ( ( v1_finset_1 @ X11 )
        | ~ ( r2_hidden @ X11 @ sk_A ) )
   <= ! [X11: $i] :
        ( ( v1_finset_1 @ X11 )
        | ~ ( r2_hidden @ X11 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( ~ ( v1_finset_1 @ sk_A )
      | ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
      | ( v1_finset_1 @ ( sk_B @ sk_A ) ) )
   <= ! [X11: $i] :
        ( ( v1_finset_1 @ X11 )
        | ~ ( r2_hidden @ X11 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X3: $i] :
      ( ( v1_finset_1 @ ( k3_tarski @ X3 ) )
      | ~ ( v1_finset_1 @ ( sk_B @ X3 ) )
      | ~ ( v1_finset_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l22_finset_1])).

thf('9',plain,
    ( ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
      | ~ ( v1_finset_1 @ sk_A ) )
   <= ! [X11: $i] :
        ( ( v1_finset_1 @ X11 )
        | ~ ( r2_hidden @ X11 @ sk_A ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
   <= ( ( v1_finset_1 @ sk_A )
      & ! [X11: $i] :
          ( ( v1_finset_1 @ X11 )
          | ~ ( r2_hidden @ X11 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
    | ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,
    ( ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
    | ~ ( v1_finset_1 @ sk_B_1 )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
    | ~ ( v1_finset_1 @ sk_B_1 )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
   <= ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('15',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
   <= ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t92_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ ( k3_tarski @ X10 ) )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t92_zfmisc_1])).

thf('17',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('19',plain,(
    ! [X4: $i] :
      ( ( k9_setfam_1 @ X4 )
      = ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('20',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k9_setfam_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k3_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf(cc2_finset_1,axiom,(
    ! [A: $i] :
      ( ( v1_finset_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_finset_1 @ B ) ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_finset_1 @ X0 )
      | ~ ( v1_finset_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_finset_1])).

thf('23',plain,(
    ! [X4: $i] :
      ( ( k9_setfam_1 @ X4 )
      = ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ X1 ) )
      | ( v1_finset_1 @ X0 )
      | ~ ( v1_finset_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
      | ( v1_finset_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,
    ( ( v1_finset_1 @ sk_B_1 )
   <= ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
      & ( r2_hidden @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','25'])).

thf('27',plain,
    ( ~ ( v1_finset_1 @ sk_B_1 )
   <= ~ ( v1_finset_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['12'])).

thf('28',plain,
    ( ( v1_finset_1 @ sk_B_1 )
    | ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
   <= ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf(fc17_finset_1,axiom,(
    ! [A: $i] :
      ( ( v1_finset_1 @ A )
     => ( v1_finset_1 @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('30',plain,(
    ! [X2: $i] :
      ( ( v1_finset_1 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( v1_finset_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc17_finset_1])).

thf('31',plain,(
    ! [X4: $i] :
      ( ( k9_setfam_1 @ X4 )
      = ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('32',plain,(
    ! [X2: $i] :
      ( ( v1_finset_1 @ ( k9_setfam_1 @ X2 ) )
      | ~ ( v1_finset_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t100_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ) )).

thf('33',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ ( k1_zfmisc_1 @ ( k3_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_zfmisc_1])).

thf('34',plain,(
    ! [X4: $i] :
      ( ( k9_setfam_1 @ X4 )
      = ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('35',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ ( k9_setfam_1 @ ( k3_tarski @ X5 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k9_setfam_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('37',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( k3_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ X1 ) )
      | ( v1_finset_1 @ X0 )
      | ~ ( v1_finset_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_finset_1 @ ( k9_setfam_1 @ ( k3_tarski @ X0 ) ) )
      | ( v1_finset_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_finset_1 @ ( k3_tarski @ X0 ) )
      | ( v1_finset_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','39'])).

thf('41',plain,
    ( ( v1_finset_1 @ sk_A )
   <= ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','40'])).

thf('42',plain,
    ( ~ ( v1_finset_1 @ sk_A )
   <= ~ ( v1_finset_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('43',plain,
    ( ( v1_finset_1 @ sk_A )
    | ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( v1_finset_1 @ sk_A )
    | ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('45',plain,(
    v1_finset_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['11','13','28','43','44'])).

thf('46',plain,
    ( ! [X11: $i] :
        ( ( v1_finset_1 @ X11 )
        | ~ ( r2_hidden @ X11 @ sk_A ) )
    | ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('47',plain,(
    ! [X11: $i] :
      ( ( v1_finset_1 @ X11 )
      | ~ ( r2_hidden @ X11 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['11','13','28','43','46'])).

thf('48',plain,(
    v1_finset_1 @ ( k3_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['10','45','47'])).

thf('49',plain,
    ( $false
   <= ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','48'])).

thf('50',plain,(
    ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['11','13','28','43'])).

thf('51',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['49','50'])).


%------------------------------------------------------------------------------
