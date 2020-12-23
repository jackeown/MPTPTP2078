%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Jztksl1xWK

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:57 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 170 expanded)
%              Number of leaves         :   29 (  61 expanded)
%              Depth                    :   10
%              Number of atoms          :  713 (2126 expanded)
%              Number of equality atoms :    9 (  24 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(t48_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
             => ! [D: $i] :
                  ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) )
                <=> ? [E: $i] :
                      ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C )
                      & ( m1_subset_1 @ E @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
               => ! [D: $i] :
                    ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) )
                  <=> ? [E: $i] :
                        ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C )
                        & ( m1_subset_1 @ E @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_relset_1])).

thf('0',plain,
    ( ( m1_subset_1 @ sk_E @ sk_B )
    | ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( m1_subset_1 @ sk_E @ sk_B )
    | ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X22: $i] :
      ( ~ ( m1_subset_1 @ X22 @ sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ X22 @ sk_D_1 ) @ sk_C )
      | ~ ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X22: $i] :
        ( ~ ( m1_subset_1 @ X22 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X22 @ sk_D_1 ) @ sk_C ) )
    | ~ ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k7_relset_1 @ X19 @ X20 @ X21 @ X19 )
        = ( k2_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('6',plain,
    ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B )
    = ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( ( k7_relset_1 @ X16 @ X17 @ X15 @ X18 )
        = ( k9_relat_1 @ X15 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k9_relat_1 @ sk_C @ sk_B )
    = ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k9_relat_1 @ sk_C @ sk_B ) )
   <= ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['10','12'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k9_relat_1 @ X11 @ X9 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X11 @ X9 @ X10 ) @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('15',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_C @ sk_B @ sk_D_1 ) @ sk_D_1 ) @ sk_C ) )
   <= ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('19',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('20',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_C @ sk_B @ sk_D_1 ) @ sk_D_1 ) @ sk_C )
   <= ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('22',plain,
    ( ! [X22: $i] :
        ( ~ ( m1_subset_1 @ X22 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X22 @ sk_D_1 ) @ sk_C ) )
   <= ! [X22: $i] :
        ( ~ ( m1_subset_1 @ X22 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X22 @ sk_D_1 ) @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf('23',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_D_1 ) @ sk_B )
   <= ( ! [X22: $i] :
          ( ~ ( m1_subset_1 @ X22 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X22 @ sk_D_1 ) @ sk_C ) )
      & ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k9_relat_1 @ sk_C @ sk_B ) )
   <= ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['10','12'])).

thf('25',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k9_relat_1 @ X11 @ X9 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X9 @ X10 ) @ X9 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('26',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_D_1 ) @ sk_B ) )
   <= ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('28',plain,
    ( ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_D_1 ) @ sk_B )
   <= ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('30',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_D_1 ) @ sk_B )
   <= ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ! [X22: $i] :
          ( ~ ( m1_subset_1 @ X22 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X22 @ sk_D_1 ) @ sk_C ) )
    | ~ ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['23','30'])).

thf('32',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['11'])).

thf('33',plain,
    ( ( m1_subset_1 @ sk_E @ sk_B )
   <= ( m1_subset_1 @ sk_E @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('35',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( r2_hidden @ sk_E @ sk_B ) )
   <= ( m1_subset_1 @ sk_E @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( r2_hidden @ sk_E @ sk_B )
   <= ( m1_subset_1 @ sk_E @ sk_B ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ),
    inference(split,[status(esa)],['11'])).

thf('39',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X10 ) @ X11 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X11 ) )
      | ( r2_hidden @ X10 @ ( k9_relat_1 @ X11 @ X9 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_C )
        | ( r2_hidden @ sk_D_1 @ ( k9_relat_1 @ sk_C @ X0 ) )
        | ~ ( r2_hidden @ sk_E @ ( k1_relat_1 @ sk_C ) )
        | ~ ( r2_hidden @ sk_E @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_D_1 @ ( k9_relat_1 @ sk_C @ X0 ) )
        | ~ ( r2_hidden @ sk_E @ ( k1_relat_1 @ sk_C ) )
        | ~ ( r2_hidden @ sk_E @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ),
    inference(split,[status(esa)],['11'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('44',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X12 @ X13 ) @ X14 )
      | ( r2_hidden @ X12 @ ( k1_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('45',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ sk_E @ ( k1_relat_1 @ sk_C ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('47',plain,
    ( ( r2_hidden @ sk_E @ ( k1_relat_1 @ sk_C ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_D_1 @ ( k9_relat_1 @ sk_C @ X0 ) )
        | ~ ( r2_hidden @ sk_E @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['42','47'])).

thf('49',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k9_relat_1 @ sk_C @ sk_B ) )
   <= ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C )
      & ( m1_subset_1 @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','48'])).

thf('50',plain,
    ( ( k9_relat_1 @ sk_C @ sk_B )
    = ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('51',plain,
    ( ~ ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ~ ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf('52',plain,
    ( ~ ( r2_hidden @ sk_D_1 @ ( k9_relat_1 @ sk_C @ sk_B ) )
   <= ~ ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_E @ sk_B ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','31','32','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Jztksl1xWK
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:17:33 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 86 iterations in 0.028s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.47  thf(sk_E_type, type, sk_E: $i).
% 0.19/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.47  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.19/0.47  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.19/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.47  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.19/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.19/0.47  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.19/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.47  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.19/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.47  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.19/0.47  thf(t48_relset_1, conjecture,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.47       ( ![B:$i]:
% 0.19/0.47         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.19/0.47           ( ![C:$i]:
% 0.19/0.47             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.19/0.47               ( ![D:$i]:
% 0.19/0.47                 ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) ) <=>
% 0.19/0.47                   ( ?[E:$i]:
% 0.19/0.47                     ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) & 
% 0.19/0.47                       ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i]:
% 0.19/0.47        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.47          ( ![B:$i]:
% 0.19/0.47            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.19/0.47              ( ![C:$i]:
% 0.19/0.47                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.19/0.47                  ( ![D:$i]:
% 0.19/0.47                    ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) ) <=>
% 0.19/0.47                      ( ?[E:$i]:
% 0.19/0.47                        ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) & 
% 0.19/0.47                          ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t48_relset_1])).
% 0.19/0.47  thf('0', plain,
% 0.19/0.47      (((m1_subset_1 @ sk_E @ sk_B)
% 0.19/0.47        | (r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('1', plain,
% 0.19/0.47      (((m1_subset_1 @ sk_E @ sk_B)) | 
% 0.19/0.47       ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.19/0.47      inference('split', [status(esa)], ['0'])).
% 0.19/0.47  thf('2', plain,
% 0.19/0.47      (![X22 : $i]:
% 0.19/0.47         (~ (m1_subset_1 @ X22 @ sk_B)
% 0.19/0.47          | ~ (r2_hidden @ (k4_tarski @ X22 @ sk_D_1) @ sk_C)
% 0.19/0.47          | ~ (r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('3', plain,
% 0.19/0.47      ((![X22 : $i]:
% 0.19/0.47          (~ (m1_subset_1 @ X22 @ sk_B)
% 0.19/0.47           | ~ (r2_hidden @ (k4_tarski @ X22 @ sk_D_1) @ sk_C))) | 
% 0.19/0.47       ~ ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.19/0.47      inference('split', [status(esa)], ['2'])).
% 0.19/0.47  thf('4', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(t38_relset_1, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.47       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.19/0.47         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.19/0.47  thf('5', plain,
% 0.19/0.47      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.19/0.47         (((k7_relset_1 @ X19 @ X20 @ X21 @ X19)
% 0.19/0.47            = (k2_relset_1 @ X19 @ X20 @ X21))
% 0.19/0.47          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.19/0.47      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.19/0.47  thf('6', plain,
% 0.19/0.47      (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B)
% 0.19/0.47         = (k2_relset_1 @ sk_B @ sk_A @ sk_C))),
% 0.19/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.47  thf('7', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(redefinition_k7_relset_1, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.47       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.19/0.47  thf('8', plain,
% 0.19/0.47      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.47         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.19/0.47          | ((k7_relset_1 @ X16 @ X17 @ X15 @ X18) = (k9_relat_1 @ X15 @ X18)))),
% 0.19/0.47      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.19/0.47  thf('9', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.47  thf('10', plain,
% 0.19/0.47      (((k9_relat_1 @ sk_C @ sk_B) = (k2_relset_1 @ sk_B @ sk_A @ sk_C))),
% 0.19/0.47      inference('demod', [status(thm)], ['6', '9'])).
% 0.19/0.47  thf('11', plain,
% 0.19/0.47      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)
% 0.19/0.47        | (r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('12', plain,
% 0.19/0.47      (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.19/0.47         <= (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.19/0.47      inference('split', [status(esa)], ['11'])).
% 0.19/0.47  thf('13', plain,
% 0.19/0.47      (((r2_hidden @ sk_D_1 @ (k9_relat_1 @ sk_C @ sk_B)))
% 0.19/0.47         <= (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.19/0.47      inference('sup+', [status(thm)], ['10', '12'])).
% 0.19/0.47  thf(t143_relat_1, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( v1_relat_1 @ C ) =>
% 0.19/0.47       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.19/0.47         ( ?[D:$i]:
% 0.19/0.47           ( ( r2_hidden @ D @ B ) & 
% 0.19/0.47             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.19/0.47             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.19/0.47  thf('14', plain,
% 0.19/0.47      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X10 @ (k9_relat_1 @ X11 @ X9))
% 0.19/0.47          | (r2_hidden @ (k4_tarski @ (sk_D @ X11 @ X9 @ X10) @ X10) @ X11)
% 0.19/0.47          | ~ (v1_relat_1 @ X11))),
% 0.19/0.47      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.19/0.47  thf('15', plain,
% 0.19/0.47      (((~ (v1_relat_1 @ sk_C)
% 0.19/0.47         | (r2_hidden @ (k4_tarski @ (sk_D @ sk_C @ sk_B @ sk_D_1) @ sk_D_1) @ 
% 0.19/0.47            sk_C)))
% 0.19/0.47         <= (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.47  thf('16', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(cc2_relat_1, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( v1_relat_1 @ A ) =>
% 0.19/0.47       ( ![B:$i]:
% 0.19/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.19/0.47  thf('17', plain,
% 0.19/0.47      (![X4 : $i, X5 : $i]:
% 0.19/0.47         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.19/0.47          | (v1_relat_1 @ X4)
% 0.19/0.47          | ~ (v1_relat_1 @ X5))),
% 0.19/0.47      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.19/0.47  thf('18', plain,
% 0.19/0.47      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_C))),
% 0.19/0.47      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.47  thf(fc6_relat_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.19/0.47  thf('19', plain,
% 0.19/0.47      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 0.19/0.47      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.19/0.47  thf('20', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.47      inference('demod', [status(thm)], ['18', '19'])).
% 0.19/0.47  thf('21', plain,
% 0.19/0.47      (((r2_hidden @ (k4_tarski @ (sk_D @ sk_C @ sk_B @ sk_D_1) @ sk_D_1) @ 
% 0.19/0.47         sk_C))
% 0.19/0.47         <= (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.19/0.47      inference('demod', [status(thm)], ['15', '20'])).
% 0.19/0.47  thf('22', plain,
% 0.19/0.47      ((![X22 : $i]:
% 0.19/0.47          (~ (m1_subset_1 @ X22 @ sk_B)
% 0.19/0.47           | ~ (r2_hidden @ (k4_tarski @ X22 @ sk_D_1) @ sk_C)))
% 0.19/0.47         <= ((![X22 : $i]:
% 0.19/0.47                (~ (m1_subset_1 @ X22 @ sk_B)
% 0.19/0.47                 | ~ (r2_hidden @ (k4_tarski @ X22 @ sk_D_1) @ sk_C))))),
% 0.19/0.47      inference('split', [status(esa)], ['2'])).
% 0.19/0.47  thf('23', plain,
% 0.19/0.47      ((~ (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_D_1) @ sk_B))
% 0.19/0.47         <= ((![X22 : $i]:
% 0.19/0.47                (~ (m1_subset_1 @ X22 @ sk_B)
% 0.19/0.47                 | ~ (r2_hidden @ (k4_tarski @ X22 @ sk_D_1) @ sk_C))) & 
% 0.19/0.47             ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.47  thf('24', plain,
% 0.19/0.47      (((r2_hidden @ sk_D_1 @ (k9_relat_1 @ sk_C @ sk_B)))
% 0.19/0.47         <= (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.19/0.47      inference('sup+', [status(thm)], ['10', '12'])).
% 0.19/0.47  thf('25', plain,
% 0.19/0.47      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X10 @ (k9_relat_1 @ X11 @ X9))
% 0.19/0.47          | (r2_hidden @ (sk_D @ X11 @ X9 @ X10) @ X9)
% 0.19/0.47          | ~ (v1_relat_1 @ X11))),
% 0.19/0.47      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.19/0.47  thf('26', plain,
% 0.19/0.47      (((~ (v1_relat_1 @ sk_C)
% 0.19/0.47         | (r2_hidden @ (sk_D @ sk_C @ sk_B @ sk_D_1) @ sk_B)))
% 0.19/0.47         <= (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['24', '25'])).
% 0.19/0.47  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.47      inference('demod', [status(thm)], ['18', '19'])).
% 0.19/0.47  thf('28', plain,
% 0.19/0.47      (((r2_hidden @ (sk_D @ sk_C @ sk_B @ sk_D_1) @ sk_B))
% 0.19/0.47         <= (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.19/0.47      inference('demod', [status(thm)], ['26', '27'])).
% 0.19/0.47  thf(t1_subset, axiom,
% 0.19/0.47    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.19/0.47  thf('29', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X0 @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.19/0.47      inference('cnf', [status(esa)], [t1_subset])).
% 0.19/0.47  thf('30', plain,
% 0.19/0.47      (((m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_D_1) @ sk_B))
% 0.19/0.47         <= (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['28', '29'])).
% 0.19/0.47  thf('31', plain,
% 0.19/0.47      (~
% 0.19/0.47       (![X22 : $i]:
% 0.19/0.47          (~ (m1_subset_1 @ X22 @ sk_B)
% 0.19/0.47           | ~ (r2_hidden @ (k4_tarski @ X22 @ sk_D_1) @ sk_C))) | 
% 0.19/0.47       ~ ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.19/0.47      inference('demod', [status(thm)], ['23', '30'])).
% 0.19/0.47  thf('32', plain,
% 0.19/0.47      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)) | 
% 0.19/0.47       ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.19/0.47      inference('split', [status(esa)], ['11'])).
% 0.19/0.47  thf('33', plain,
% 0.19/0.47      (((m1_subset_1 @ sk_E @ sk_B)) <= (((m1_subset_1 @ sk_E @ sk_B)))),
% 0.19/0.47      inference('split', [status(esa)], ['0'])).
% 0.19/0.47  thf(t2_subset, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( m1_subset_1 @ A @ B ) =>
% 0.19/0.47       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.19/0.47  thf('34', plain,
% 0.19/0.47      (![X2 : $i, X3 : $i]:
% 0.19/0.47         ((r2_hidden @ X2 @ X3)
% 0.19/0.47          | (v1_xboole_0 @ X3)
% 0.19/0.47          | ~ (m1_subset_1 @ X2 @ X3))),
% 0.19/0.47      inference('cnf', [status(esa)], [t2_subset])).
% 0.19/0.47  thf('35', plain,
% 0.19/0.47      ((((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_E @ sk_B)))
% 0.19/0.47         <= (((m1_subset_1 @ sk_E @ sk_B)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['33', '34'])).
% 0.19/0.47  thf('36', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('37', plain,
% 0.19/0.47      (((r2_hidden @ sk_E @ sk_B)) <= (((m1_subset_1 @ sk_E @ sk_B)))),
% 0.19/0.47      inference('clc', [status(thm)], ['35', '36'])).
% 0.19/0.47  thf('38', plain,
% 0.19/0.47      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C))
% 0.19/0.47         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.19/0.47      inference('split', [status(esa)], ['11'])).
% 0.19/0.47  thf('39', plain,
% 0.19/0.47      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X8 @ X9)
% 0.19/0.47          | ~ (r2_hidden @ (k4_tarski @ X8 @ X10) @ X11)
% 0.19/0.47          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ X11))
% 0.19/0.47          | (r2_hidden @ X10 @ (k9_relat_1 @ X11 @ X9))
% 0.19/0.47          | ~ (v1_relat_1 @ X11))),
% 0.19/0.47      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.19/0.47  thf('40', plain,
% 0.19/0.47      ((![X0 : $i]:
% 0.19/0.47          (~ (v1_relat_1 @ sk_C)
% 0.19/0.47           | (r2_hidden @ sk_D_1 @ (k9_relat_1 @ sk_C @ X0))
% 0.19/0.47           | ~ (r2_hidden @ sk_E @ (k1_relat_1 @ sk_C))
% 0.19/0.47           | ~ (r2_hidden @ sk_E @ X0)))
% 0.19/0.47         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['38', '39'])).
% 0.19/0.47  thf('41', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.47      inference('demod', [status(thm)], ['18', '19'])).
% 0.19/0.47  thf('42', plain,
% 0.19/0.47      ((![X0 : $i]:
% 0.19/0.47          ((r2_hidden @ sk_D_1 @ (k9_relat_1 @ sk_C @ X0))
% 0.19/0.47           | ~ (r2_hidden @ sk_E @ (k1_relat_1 @ sk_C))
% 0.19/0.47           | ~ (r2_hidden @ sk_E @ X0)))
% 0.19/0.47         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.19/0.47      inference('demod', [status(thm)], ['40', '41'])).
% 0.19/0.47  thf('43', plain,
% 0.19/0.47      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C))
% 0.19/0.47         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.19/0.47      inference('split', [status(esa)], ['11'])).
% 0.19/0.47  thf(t20_relat_1, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( v1_relat_1 @ C ) =>
% 0.19/0.47       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.19/0.47         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.19/0.47           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.19/0.47  thf('44', plain,
% 0.19/0.47      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.47         (~ (r2_hidden @ (k4_tarski @ X12 @ X13) @ X14)
% 0.19/0.47          | (r2_hidden @ X12 @ (k1_relat_1 @ X14))
% 0.19/0.47          | ~ (v1_relat_1 @ X14))),
% 0.19/0.47      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.19/0.47  thf('45', plain,
% 0.19/0.47      (((~ (v1_relat_1 @ sk_C) | (r2_hidden @ sk_E @ (k1_relat_1 @ sk_C))))
% 0.19/0.47         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['43', '44'])).
% 0.19/0.47  thf('46', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.47      inference('demod', [status(thm)], ['18', '19'])).
% 0.19/0.47  thf('47', plain,
% 0.19/0.47      (((r2_hidden @ sk_E @ (k1_relat_1 @ sk_C)))
% 0.19/0.47         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.19/0.47      inference('demod', [status(thm)], ['45', '46'])).
% 0.19/0.47  thf('48', plain,
% 0.19/0.47      ((![X0 : $i]:
% 0.19/0.47          ((r2_hidden @ sk_D_1 @ (k9_relat_1 @ sk_C @ X0))
% 0.19/0.47           | ~ (r2_hidden @ sk_E @ X0)))
% 0.19/0.47         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.19/0.47      inference('demod', [status(thm)], ['42', '47'])).
% 0.19/0.47  thf('49', plain,
% 0.19/0.47      (((r2_hidden @ sk_D_1 @ (k9_relat_1 @ sk_C @ sk_B)))
% 0.19/0.47         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)) & 
% 0.19/0.47             ((m1_subset_1 @ sk_E @ sk_B)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['37', '48'])).
% 0.19/0.47  thf('50', plain,
% 0.19/0.47      (((k9_relat_1 @ sk_C @ sk_B) = (k2_relset_1 @ sk_B @ sk_A @ sk_C))),
% 0.19/0.47      inference('demod', [status(thm)], ['6', '9'])).
% 0.19/0.47  thf('51', plain,
% 0.19/0.47      ((~ (r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.19/0.47         <= (~ ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.19/0.47      inference('split', [status(esa)], ['2'])).
% 0.19/0.47  thf('52', plain,
% 0.19/0.47      ((~ (r2_hidden @ sk_D_1 @ (k9_relat_1 @ sk_C @ sk_B)))
% 0.19/0.47         <= (~ ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['50', '51'])).
% 0.19/0.47  thf('53', plain,
% 0.19/0.47      (~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)) | 
% 0.19/0.47       ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))) | 
% 0.19/0.47       ~ ((m1_subset_1 @ sk_E @ sk_B))),
% 0.19/0.47      inference('sup-', [status(thm)], ['49', '52'])).
% 0.19/0.47  thf('54', plain, ($false),
% 0.19/0.47      inference('sat_resolution*', [status(thm)], ['1', '3', '31', '32', '53'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
