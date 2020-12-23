%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oLyEmk8yCW

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 271 expanded)
%              Number of leaves         :   29 (  91 expanded)
%              Depth                    :   13
%              Number of atoms          :  724 (3213 expanded)
%              Number of equality atoms :   13 (  41 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

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
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X12 )
      | ( r2_hidden @ X11 @ ( k2_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('3',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ sk_D_1 @ ( k2_relat_1 @ sk_C ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('6',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k2_relat_1 @ sk_C ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('9',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('10',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X22: $i] :
      ( ~ ( m1_subset_1 @ X22 @ sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ X22 @ sk_D_1 ) @ sk_C )
      | ~ ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ~ ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ~ ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,
    ( ~ ( r2_hidden @ sk_D_1 @ ( k2_relat_1 @ sk_C ) )
   <= ~ ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k2_relat_1 @ sk_C ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('17',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v4_relat_1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('18',plain,(
    v4_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8
        = ( k7_relat_1 @ X8 @ X9 ) )
      | ~ ( v4_relat_1 @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['4','5'])).

thf('22',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X6 @ X7 ) )
        = ( k9_relat_1 @ X6 @ X7 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('24',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['4','5'])).

thf('26',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('27',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k9_relat_1 @ X5 @ X3 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X5 @ X3 @ X4 ) @ X4 ) @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_C @ sk_B @ X0 ) @ X0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['4','5'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_C @ sk_B @ X0 ) @ X0 ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_C @ sk_B @ sk_D_1 ) @ sk_D_1 ) @ sk_C )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['15','30'])).

thf('32',plain,
    ( ! [X22: $i] :
        ( ~ ( m1_subset_1 @ X22 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X22 @ sk_D_1 ) @ sk_C ) )
   <= ! [X22: $i] :
        ( ~ ( m1_subset_1 @ X22 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X22 @ sk_D_1 ) @ sk_C ) ) ),
    inference(split,[status(esa)],['11'])).

thf('33',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_D_1 ) @ sk_B )
   <= ( ! [X22: $i] :
          ( ~ ( m1_subset_1 @ X22 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X22 @ sk_D_1 ) @ sk_C ) )
      & ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k2_relat_1 @ sk_C ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('35',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('36',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k9_relat_1 @ X5 @ X3 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X3 @ X4 ) @ X3 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['4','5'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C ) )
      | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_D_1 ) @ sk_B )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('42',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_D_1 ) @ sk_B )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ! [X22: $i] :
          ( ~ ( m1_subset_1 @ X22 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X22 @ sk_D_1 ) @ sk_C ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['33','42'])).

thf('44',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,
    ( ! [X22: $i] :
        ( ~ ( m1_subset_1 @ X22 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X22 @ sk_D_1 ) @ sk_C ) )
    | ~ ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['11'])).

thf('46',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('47',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k2_relat_1 @ sk_C ) )
   <= ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_C @ sk_B @ X0 ) @ X0 ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('50',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_C @ sk_B @ sk_D_1 ) @ sk_D_1 ) @ sk_C )
   <= ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ! [X22: $i] :
        ( ~ ( m1_subset_1 @ X22 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X22 @ sk_D_1 ) @ sk_C ) )
   <= ! [X22: $i] :
        ( ~ ( m1_subset_1 @ X22 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X22 @ sk_D_1 ) @ sk_C ) ) ),
    inference(split,[status(esa)],['11'])).

thf('52',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_D_1 ) @ sk_B )
   <= ( ! [X22: $i] :
          ( ~ ( m1_subset_1 @ X22 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X22 @ sk_D_1 ) @ sk_C ) )
      & ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k2_relat_1 @ sk_C ) )
   <= ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C ) )
      | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('55',plain,
    ( ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_D_1 ) @ sk_B )
   <= ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('57',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_D_1 ) @ sk_B )
   <= ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ! [X22: $i] :
          ( ~ ( m1_subset_1 @ X22 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X22 @ sk_D_1 ) @ sk_C ) )
    | ~ ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['52','57'])).

thf('59',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['14','43','44','45','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oLyEmk8yCW
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:10:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 70 iterations in 0.028s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.48  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.48  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.48  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.48  thf(t48_relset_1, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.20/0.48               ( ![D:$i]:
% 0.20/0.48                 ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) ) <=>
% 0.20/0.48                   ( ?[E:$i]:
% 0.20/0.48                     ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) & 
% 0.20/0.48                       ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.48          ( ![B:$i]:
% 0.20/0.48            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.48              ( ![C:$i]:
% 0.20/0.48                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.20/0.48                  ( ![D:$i]:
% 0.20/0.48                    ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) ) <=>
% 0.20/0.48                      ( ?[E:$i]:
% 0.20/0.48                        ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) & 
% 0.20/0.48                          ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t48_relset_1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)
% 0.20/0.48        | (r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C))
% 0.20/0.48         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf(t20_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ C ) =>
% 0.20/0.48       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.20/0.48         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.48           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.48         (~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X12)
% 0.20/0.48          | (r2_hidden @ X11 @ (k2_relat_1 @ X12))
% 0.20/0.48          | ~ (v1_relat_1 @ X12))),
% 0.20/0.48      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (((~ (v1_relat_1 @ sk_C) | (r2_hidden @ sk_D_1 @ (k2_relat_1 @ sk_C))))
% 0.20/0.48         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(cc1_relset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.48       ( v1_relat_1 @ C ) ))).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.48         ((v1_relat_1 @ X13)
% 0.20/0.48          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.20/0.48      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.48  thf('6', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (((r2_hidden @ sk_D_1 @ (k2_relat_1 @ sk_C)))
% 0.20/0.48         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['3', '6'])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.49         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 0.20/0.49          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (((k2_relset_1 @ sk_B @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X22 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X22 @ sk_B)
% 0.20/0.49          | ~ (r2_hidden @ (k4_tarski @ X22 @ sk_D_1) @ sk_C)
% 0.20/0.49          | ~ (r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      ((~ (r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.20/0.49         <= (~ ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.49      inference('split', [status(esa)], ['11'])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      ((~ (r2_hidden @ sk_D_1 @ (k2_relat_1 @ sk_C)))
% 0.20/0.49         <= (~ ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['10', '12'])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))) | 
% 0.20/0.49       ~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['7', '13'])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (((r2_hidden @ sk_D_1 @ (k2_relat_1 @ sk_C)))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['3', '6'])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(cc2_relset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.49         ((v4_relat_1 @ X16 @ X17)
% 0.20/0.49          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.49  thf('18', plain, ((v4_relat_1 @ sk_C @ sk_B)),
% 0.20/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.49  thf(t209_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.20/0.49       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X8 : $i, X9 : $i]:
% 0.20/0.49         (((X8) = (k7_relat_1 @ X8 @ X9))
% 0.20/0.49          | ~ (v4_relat_1 @ X8 @ X9)
% 0.20/0.49          | ~ (v1_relat_1 @ X8))),
% 0.20/0.49      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.49  thf('21', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.49  thf('22', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.49  thf(t148_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) =>
% 0.20/0.49       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i]:
% 0.20/0.49         (((k2_relat_1 @ (k7_relat_1 @ X6 @ X7)) = (k9_relat_1 @ X6 @ X7))
% 0.20/0.49          | ~ (v1_relat_1 @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))
% 0.20/0.49        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.49      inference('sup+', [status(thm)], ['22', '23'])).
% 0.20/0.49  thf('25', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.49  thf('26', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.49  thf(t143_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ C ) =>
% 0.20/0.49       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.20/0.49         ( ?[D:$i]:
% 0.20/0.49           ( ( r2_hidden @ D @ B ) & 
% 0.20/0.49             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.20/0.49             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X4 @ (k9_relat_1 @ X5 @ X3))
% 0.20/0.49          | (r2_hidden @ (k4_tarski @ (sk_D @ X5 @ X3 @ X4) @ X4) @ X5)
% 0.20/0.49          | ~ (v1_relat_1 @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C))
% 0.20/0.49          | ~ (v1_relat_1 @ sk_C)
% 0.20/0.49          | (r2_hidden @ (k4_tarski @ (sk_D @ sk_C @ sk_B @ X0) @ X0) @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.49  thf('29', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C))
% 0.20/0.49          | (r2_hidden @ (k4_tarski @ (sk_D @ sk_C @ sk_B @ X0) @ X0) @ sk_C))),
% 0.20/0.49      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (((r2_hidden @ (k4_tarski @ (sk_D @ sk_C @ sk_B @ sk_D_1) @ sk_D_1) @ 
% 0.20/0.49         sk_C)) <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['15', '30'])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      ((![X22 : $i]:
% 0.20/0.49          (~ (m1_subset_1 @ X22 @ sk_B)
% 0.20/0.49           | ~ (r2_hidden @ (k4_tarski @ X22 @ sk_D_1) @ sk_C)))
% 0.20/0.49         <= ((![X22 : $i]:
% 0.20/0.49                (~ (m1_subset_1 @ X22 @ sk_B)
% 0.20/0.49                 | ~ (r2_hidden @ (k4_tarski @ X22 @ sk_D_1) @ sk_C))))),
% 0.20/0.49      inference('split', [status(esa)], ['11'])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      ((~ (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_D_1) @ sk_B))
% 0.20/0.49         <= ((![X22 : $i]:
% 0.20/0.49                (~ (m1_subset_1 @ X22 @ sk_B)
% 0.20/0.49                 | ~ (r2_hidden @ (k4_tarski @ X22 @ sk_D_1) @ sk_C))) & 
% 0.20/0.49             ((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (((r2_hidden @ sk_D_1 @ (k2_relat_1 @ sk_C)))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['3', '6'])).
% 0.20/0.49  thf('35', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X4 @ (k9_relat_1 @ X5 @ X3))
% 0.20/0.49          | (r2_hidden @ (sk_D @ X5 @ X3 @ X4) @ X3)
% 0.20/0.49          | ~ (v1_relat_1 @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C))
% 0.20/0.49          | ~ (v1_relat_1 @ sk_C)
% 0.20/0.49          | (r2_hidden @ (sk_D @ sk_C @ sk_B @ X0) @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.49  thf('38', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C))
% 0.20/0.49          | (r2_hidden @ (sk_D @ sk_C @ sk_B @ X0) @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      (((r2_hidden @ (sk_D @ sk_C @ sk_B @ sk_D_1) @ sk_B))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['34', '39'])).
% 0.20/0.49  thf(t1_subset, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X0 @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [t1_subset])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      (((m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_D_1) @ sk_B))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      (~
% 0.20/0.49       (![X22 : $i]:
% 0.20/0.49          (~ (m1_subset_1 @ X22 @ sk_B)
% 0.20/0.49           | ~ (r2_hidden @ (k4_tarski @ X22 @ sk_D_1) @ sk_C))) | 
% 0.20/0.49       ~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C))),
% 0.20/0.49      inference('demod', [status(thm)], ['33', '42'])).
% 0.20/0.49  thf('44', plain,
% 0.20/0.49      (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))) | 
% 0.20/0.49       ((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('45', plain,
% 0.20/0.49      ((![X22 : $i]:
% 0.20/0.49          (~ (m1_subset_1 @ X22 @ sk_B)
% 0.20/0.49           | ~ (r2_hidden @ (k4_tarski @ X22 @ sk_D_1) @ sk_C))) | 
% 0.20/0.49       ~ ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.20/0.49      inference('split', [status(esa)], ['11'])).
% 0.20/0.49  thf('46', plain,
% 0.20/0.49      (((k2_relset_1 @ sk_B @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.49  thf('47', plain,
% 0.20/0.49      (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.20/0.49         <= (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('48', plain,
% 0.20/0.49      (((r2_hidden @ sk_D_1 @ (k2_relat_1 @ sk_C)))
% 0.20/0.49         <= (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.49      inference('sup+', [status(thm)], ['46', '47'])).
% 0.20/0.49  thf('49', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C))
% 0.20/0.49          | (r2_hidden @ (k4_tarski @ (sk_D @ sk_C @ sk_B @ X0) @ X0) @ sk_C))),
% 0.20/0.49      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.49  thf('50', plain,
% 0.20/0.49      (((r2_hidden @ (k4_tarski @ (sk_D @ sk_C @ sk_B @ sk_D_1) @ sk_D_1) @ 
% 0.20/0.49         sk_C))
% 0.20/0.49         <= (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.49  thf('51', plain,
% 0.20/0.49      ((![X22 : $i]:
% 0.20/0.49          (~ (m1_subset_1 @ X22 @ sk_B)
% 0.20/0.49           | ~ (r2_hidden @ (k4_tarski @ X22 @ sk_D_1) @ sk_C)))
% 0.20/0.49         <= ((![X22 : $i]:
% 0.20/0.49                (~ (m1_subset_1 @ X22 @ sk_B)
% 0.20/0.49                 | ~ (r2_hidden @ (k4_tarski @ X22 @ sk_D_1) @ sk_C))))),
% 0.20/0.49      inference('split', [status(esa)], ['11'])).
% 0.20/0.49  thf('52', plain,
% 0.20/0.49      ((~ (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_D_1) @ sk_B))
% 0.20/0.49         <= ((![X22 : $i]:
% 0.20/0.49                (~ (m1_subset_1 @ X22 @ sk_B)
% 0.20/0.49                 | ~ (r2_hidden @ (k4_tarski @ X22 @ sk_D_1) @ sk_C))) & 
% 0.20/0.49             ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.49  thf('53', plain,
% 0.20/0.49      (((r2_hidden @ sk_D_1 @ (k2_relat_1 @ sk_C)))
% 0.20/0.49         <= (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.49      inference('sup+', [status(thm)], ['46', '47'])).
% 0.20/0.49  thf('54', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C))
% 0.20/0.49          | (r2_hidden @ (sk_D @ sk_C @ sk_B @ X0) @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.49  thf('55', plain,
% 0.20/0.49      (((r2_hidden @ (sk_D @ sk_C @ sk_B @ sk_D_1) @ sk_B))
% 0.20/0.49         <= (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.49  thf('56', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X0 @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [t1_subset])).
% 0.20/0.49  thf('57', plain,
% 0.20/0.49      (((m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_D_1) @ sk_B))
% 0.20/0.49         <= (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.49  thf('58', plain,
% 0.20/0.49      (~
% 0.20/0.49       (![X22 : $i]:
% 0.20/0.49          (~ (m1_subset_1 @ X22 @ sk_B)
% 0.20/0.49           | ~ (r2_hidden @ (k4_tarski @ X22 @ sk_D_1) @ sk_C))) | 
% 0.20/0.49       ~ ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['52', '57'])).
% 0.20/0.49  thf('59', plain, ($false),
% 0.20/0.49      inference('sat_resolution*', [status(thm)],
% 0.20/0.49                ['14', '43', '44', '45', '58'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
