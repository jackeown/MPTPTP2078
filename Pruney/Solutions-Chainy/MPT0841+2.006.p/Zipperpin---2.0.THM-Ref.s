%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1Rr1RNNl43

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:22 EST 2020

% Result     : Theorem 0.71s
% Output     : Refutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 175 expanded)
%              Number of leaves         :   25 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :  898 (2955 expanded)
%              Number of equality atoms :    6 (  14 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t52_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ~ ( v1_xboole_0 @ C )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ A )
                     => ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) )
                      <=> ? [F: $i] :
                            ( ( r2_hidden @ F @ B )
                            & ( r2_hidden @ ( k4_tarski @ F @ E ) @ D )
                            & ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ~ ( v1_xboole_0 @ C )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ A )
                       => ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) )
                        <=> ? [F: $i] :
                              ( ( r2_hidden @ F @ B )
                              & ( r2_hidden @ ( k4_tarski @ F @ E ) @ D )
                              & ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_relset_1])).

thf('0',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 )
    | ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 )
    | ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( m1_subset_1 @ sk_F @ sk_C_1 )
    | ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( m1_subset_1 @ sk_F @ sk_C_1 )
    | ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('5',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k7_relset_1 @ X25 @ X26 @ X24 @ X27 )
        = ( k9_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ X0 )
      = ( k9_relat_1 @ sk_D_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_3 @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('10',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ ( k9_relat_1 @ X20 @ X18 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X20 @ X18 @ X19 ) @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('11',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_E ) @ sk_D_3 ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('13',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('14',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_E ) @ sk_D_3 )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('17',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_E ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('21',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_C_1 )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('23',plain,
    ( ( m1_subset_1 @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_C_1 )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_E ) @ sk_D_3 )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('25',plain,(
    ! [X28: $i] :
      ( ~ ( m1_subset_1 @ X28 @ sk_C_1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_E ) @ sk_D_3 )
      | ~ ( r2_hidden @ X28 @ sk_B )
      | ~ ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_E ) @ sk_D_3 )
        | ~ ( r2_hidden @ X28 @ sk_B ) )
   <= ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_E ) @ sk_D_3 )
        | ~ ( r2_hidden @ X28 @ sk_B ) ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,
    ( ( ~ ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_C_1 ) )
   <= ( ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_E ) @ sk_D_3 )
          | ~ ( r2_hidden @ X28 @ sk_B ) )
      & ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,
    ( ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_3 @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf('29',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ ( k9_relat_1 @ X20 @ X18 ) )
      | ( r2_hidden @ ( sk_D_2 @ X20 @ X18 @ X19 ) @ X18 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('30',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_3 )
      | ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('32',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_B )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_C_1 )
   <= ( ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_E ) @ sk_D_3 )
          | ~ ( r2_hidden @ X28 @ sk_B ) )
      & ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('34',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) )
    | ~ ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_E ) @ sk_D_3 )
          | ~ ( r2_hidden @ X28 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','33'])).

thf('35',plain,
    ( ( m1_subset_1 @ sk_F @ sk_C_1 )
   <= ( m1_subset_1 @ sk_F @ sk_C_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('36',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
   <= ( r2_hidden @ sk_F @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('37',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,
    ( ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_E ) @ sk_D_3 )
        | ~ ( r2_hidden @ X28 @ sk_B ) )
   <= ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_E ) @ sk_D_3 )
        | ~ ( r2_hidden @ X28 @ sk_B ) ) ),
    inference(split,[status(esa)],['25'])).

thf('39',plain,
    ( ( ~ ( r2_hidden @ sk_F @ sk_B )
      | ~ ( m1_subset_1 @ sk_F @ sk_C_1 ) )
   <= ( ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_E ) @ sk_D_3 )
          | ~ ( r2_hidden @ X28 @ sk_B ) )
      & ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( m1_subset_1 @ sk_F @ sk_C_1 )
   <= ( ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_E ) @ sk_D_3 )
          | ~ ( r2_hidden @ X28 @ sk_B ) )
      & ( r2_hidden @ sk_F @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 )
    | ~ ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_E ) @ sk_D_3 )
          | ~ ( r2_hidden @ X28 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_F @ sk_C_1 )
    | ~ ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) )
    | ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_E ) @ sk_D_3 )
        | ~ ( r2_hidden @ X28 @ sk_B ) ) ),
    inference(split,[status(esa)],['25'])).

thf('43',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('44',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
   <= ( r2_hidden @ sk_F @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('45',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 ) ),
    inference(split,[status(esa)],['0'])).

thf('46',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X19 ) @ X20 )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X20 ) )
      | ( r2_hidden @ X19 @ ( k9_relat_1 @ X20 @ X18 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('47',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_D_3 )
        | ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_3 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ ( k1_relat_1 @ sk_D_3 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('49',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 ) ),
    inference(split,[status(esa)],['0'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('50',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X12 )
      | ( r2_hidden @ X10 @ X13 )
      | ( X13
       != ( k1_relat_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('51',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X10 @ ( k1_relat_1 @ X12 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X12 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( r2_hidden @ sk_F @ ( k1_relat_1 @ sk_D_3 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_3 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 ) ),
    inference(demod,[status(thm)],['47','48','52'])).

thf('54',plain,
    ( ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_3 @ sk_B ) )
   <= ( ( r2_hidden @ sk_F @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['44','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ X0 )
      = ( k9_relat_1 @ sk_D_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('56',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference(split,[status(esa)],['25'])).

thf('57',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_3 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( r2_hidden @ sk_F @ sk_B )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 )
    | ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','34','41','42','43','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1Rr1RNNl43
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:13:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.71/0.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.71/0.89  % Solved by: fo/fo7.sh
% 0.71/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.71/0.89  % done 350 iterations in 0.440s
% 0.71/0.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.71/0.89  % SZS output start Refutation
% 0.71/0.89  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.71/0.89  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.71/0.89  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.71/0.89  thf(sk_B_type, type, sk_B: $i).
% 0.71/0.89  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.71/0.89  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 0.71/0.89  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.71/0.89  thf(sk_F_type, type, sk_F: $i).
% 0.71/0.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.71/0.89  thf(sk_E_type, type, sk_E: $i).
% 0.71/0.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.71/0.89  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.71/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.71/0.89  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.71/0.89  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.71/0.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.71/0.89  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.71/0.89  thf(t52_relset_1, conjecture,
% 0.71/0.89    (![A:$i]:
% 0.71/0.89     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.71/0.89       ( ![B:$i]:
% 0.71/0.89         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.71/0.89           ( ![C:$i]:
% 0.71/0.89             ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.71/0.89               ( ![D:$i]:
% 0.71/0.89                 ( ( m1_subset_1 @
% 0.71/0.89                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.71/0.89                   ( ![E:$i]:
% 0.71/0.89                     ( ( m1_subset_1 @ E @ A ) =>
% 0.71/0.89                       ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) ) <=>
% 0.71/0.89                         ( ?[F:$i]:
% 0.71/0.89                           ( ( r2_hidden @ F @ B ) & 
% 0.71/0.89                             ( r2_hidden @ ( k4_tarski @ F @ E ) @ D ) & 
% 0.71/0.89                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.71/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.71/0.89    (~( ![A:$i]:
% 0.71/0.89        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.71/0.89          ( ![B:$i]:
% 0.71/0.89            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.71/0.89              ( ![C:$i]:
% 0.71/0.89                ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.71/0.89                  ( ![D:$i]:
% 0.71/0.89                    ( ( m1_subset_1 @
% 0.71/0.89                        D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.71/0.89                      ( ![E:$i]:
% 0.71/0.89                        ( ( m1_subset_1 @ E @ A ) =>
% 0.71/0.89                          ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) ) <=>
% 0.71/0.89                            ( ?[F:$i]:
% 0.71/0.89                              ( ( r2_hidden @ F @ B ) & 
% 0.71/0.89                                ( r2_hidden @ ( k4_tarski @ F @ E ) @ D ) & 
% 0.71/0.89                                ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.71/0.89    inference('cnf.neg', [status(esa)], [t52_relset_1])).
% 0.71/0.89  thf('0', plain,
% 0.71/0.89      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3)
% 0.71/0.89        | (r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B)))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('1', plain,
% 0.71/0.89      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3)) | 
% 0.71/0.89       ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B)))),
% 0.71/0.89      inference('split', [status(esa)], ['0'])).
% 0.71/0.89  thf('2', plain,
% 0.71/0.89      (((m1_subset_1 @ sk_F @ sk_C_1)
% 0.71/0.89        | (r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B)))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('3', plain,
% 0.71/0.89      (((m1_subset_1 @ sk_F @ sk_C_1)) | 
% 0.71/0.89       ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B)))),
% 0.71/0.89      inference('split', [status(esa)], ['2'])).
% 0.71/0.89  thf('4', plain,
% 0.71/0.89      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf(redefinition_k7_relset_1, axiom,
% 0.71/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.71/0.89       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.71/0.89  thf('5', plain,
% 0.71/0.89      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.71/0.89         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.71/0.89          | ((k7_relset_1 @ X25 @ X26 @ X24 @ X27) = (k9_relat_1 @ X24 @ X27)))),
% 0.71/0.89      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.71/0.89  thf('6', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         ((k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ X0)
% 0.71/0.89           = (k9_relat_1 @ sk_D_3 @ X0))),
% 0.71/0.89      inference('sup-', [status(thm)], ['4', '5'])).
% 0.71/0.89  thf('7', plain,
% 0.71/0.89      (((r2_hidden @ sk_F @ sk_B)
% 0.71/0.89        | (r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B)))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('8', plain,
% 0.71/0.89      (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B)))
% 0.71/0.89         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.71/0.89      inference('split', [status(esa)], ['7'])).
% 0.71/0.89  thf('9', plain,
% 0.71/0.89      (((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_3 @ sk_B)))
% 0.71/0.89         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.71/0.89      inference('sup+', [status(thm)], ['6', '8'])).
% 0.71/0.89  thf(t143_relat_1, axiom,
% 0.71/0.89    (![A:$i,B:$i,C:$i]:
% 0.71/0.89     ( ( v1_relat_1 @ C ) =>
% 0.71/0.89       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.71/0.89         ( ?[D:$i]:
% 0.71/0.89           ( ( r2_hidden @ D @ B ) & 
% 0.71/0.89             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.71/0.89             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.71/0.89  thf('10', plain,
% 0.71/0.89      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.71/0.89         (~ (r2_hidden @ X19 @ (k9_relat_1 @ X20 @ X18))
% 0.71/0.89          | (r2_hidden @ (k4_tarski @ (sk_D_2 @ X20 @ X18 @ X19) @ X19) @ X20)
% 0.71/0.89          | ~ (v1_relat_1 @ X20))),
% 0.71/0.89      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.71/0.89  thf('11', plain,
% 0.71/0.89      (((~ (v1_relat_1 @ sk_D_3)
% 0.71/0.89         | (r2_hidden @ (k4_tarski @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_E) @ 
% 0.71/0.89            sk_D_3)))
% 0.71/0.89         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.71/0.89      inference('sup-', [status(thm)], ['9', '10'])).
% 0.71/0.89  thf('12', plain,
% 0.71/0.89      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf(cc1_relset_1, axiom,
% 0.71/0.89    (![A:$i,B:$i,C:$i]:
% 0.71/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.71/0.89       ( v1_relat_1 @ C ) ))).
% 0.71/0.89  thf('13', plain,
% 0.71/0.89      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.71/0.89         ((v1_relat_1 @ X21)
% 0.71/0.89          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.71/0.89      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.71/0.89  thf('14', plain, ((v1_relat_1 @ sk_D_3)),
% 0.71/0.89      inference('sup-', [status(thm)], ['12', '13'])).
% 0.71/0.89  thf('15', plain,
% 0.71/0.89      (((r2_hidden @ (k4_tarski @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_E) @ 
% 0.71/0.89         sk_D_3))
% 0.71/0.89         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.71/0.89      inference('demod', [status(thm)], ['11', '14'])).
% 0.71/0.89  thf('16', plain,
% 0.71/0.89      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf(l3_subset_1, axiom,
% 0.71/0.89    (![A:$i,B:$i]:
% 0.71/0.89     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.71/0.89       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.71/0.89  thf('17', plain,
% 0.71/0.89      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.71/0.89         (~ (r2_hidden @ X5 @ X6)
% 0.71/0.89          | (r2_hidden @ X5 @ X7)
% 0.71/0.89          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.71/0.89      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.71/0.89  thf('18', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A))
% 0.71/0.89          | ~ (r2_hidden @ X0 @ sk_D_3))),
% 0.71/0.89      inference('sup-', [status(thm)], ['16', '17'])).
% 0.71/0.89  thf('19', plain,
% 0.71/0.89      (((r2_hidden @ (k4_tarski @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_E) @ 
% 0.71/0.89         (k2_zfmisc_1 @ sk_C_1 @ sk_A)))
% 0.71/0.89         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.71/0.89      inference('sup-', [status(thm)], ['15', '18'])).
% 0.71/0.89  thf(l54_zfmisc_1, axiom,
% 0.71/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.89     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.71/0.89       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.71/0.89  thf('20', plain,
% 0.71/0.89      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.71/0.89         ((r2_hidden @ X0 @ X1)
% 0.71/0.89          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 0.71/0.89      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.71/0.89  thf('21', plain,
% 0.71/0.89      (((r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_C_1))
% 0.71/0.89         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.71/0.89      inference('sup-', [status(thm)], ['19', '20'])).
% 0.71/0.89  thf(t1_subset, axiom,
% 0.71/0.89    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.71/0.89  thf('22', plain,
% 0.71/0.89      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 0.71/0.89      inference('cnf', [status(esa)], [t1_subset])).
% 0.71/0.89  thf('23', plain,
% 0.71/0.89      (((m1_subset_1 @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_C_1))
% 0.71/0.89         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.71/0.89      inference('sup-', [status(thm)], ['21', '22'])).
% 0.71/0.89  thf('24', plain,
% 0.71/0.89      (((r2_hidden @ (k4_tarski @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_E) @ 
% 0.71/0.89         sk_D_3))
% 0.71/0.89         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.71/0.89      inference('demod', [status(thm)], ['11', '14'])).
% 0.71/0.89  thf('25', plain,
% 0.71/0.89      (![X28 : $i]:
% 0.71/0.89         (~ (m1_subset_1 @ X28 @ sk_C_1)
% 0.71/0.89          | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_E) @ sk_D_3)
% 0.71/0.89          | ~ (r2_hidden @ X28 @ sk_B)
% 0.71/0.89          | ~ (r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B)))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('26', plain,
% 0.71/0.89      ((![X28 : $i]:
% 0.71/0.89          (~ (m1_subset_1 @ X28 @ sk_C_1)
% 0.71/0.89           | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_E) @ sk_D_3)
% 0.71/0.89           | ~ (r2_hidden @ X28 @ sk_B)))
% 0.71/0.89         <= ((![X28 : $i]:
% 0.71/0.89                (~ (m1_subset_1 @ X28 @ sk_C_1)
% 0.71/0.89                 | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_E) @ sk_D_3)
% 0.71/0.89                 | ~ (r2_hidden @ X28 @ sk_B))))),
% 0.71/0.89      inference('split', [status(esa)], ['25'])).
% 0.71/0.89  thf('27', plain,
% 0.71/0.89      (((~ (r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_B)
% 0.71/0.89         | ~ (m1_subset_1 @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_C_1)))
% 0.71/0.89         <= ((![X28 : $i]:
% 0.71/0.89                (~ (m1_subset_1 @ X28 @ sk_C_1)
% 0.71/0.89                 | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_E) @ sk_D_3)
% 0.71/0.89                 | ~ (r2_hidden @ X28 @ sk_B))) & 
% 0.71/0.89             ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.71/0.89      inference('sup-', [status(thm)], ['24', '26'])).
% 0.71/0.89  thf('28', plain,
% 0.71/0.89      (((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_3 @ sk_B)))
% 0.71/0.89         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.71/0.89      inference('sup+', [status(thm)], ['6', '8'])).
% 0.71/0.89  thf('29', plain,
% 0.71/0.89      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.71/0.89         (~ (r2_hidden @ X19 @ (k9_relat_1 @ X20 @ X18))
% 0.71/0.89          | (r2_hidden @ (sk_D_2 @ X20 @ X18 @ X19) @ X18)
% 0.71/0.89          | ~ (v1_relat_1 @ X20))),
% 0.71/0.89      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.71/0.89  thf('30', plain,
% 0.71/0.89      (((~ (v1_relat_1 @ sk_D_3)
% 0.71/0.89         | (r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_B)))
% 0.71/0.89         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.71/0.89      inference('sup-', [status(thm)], ['28', '29'])).
% 0.71/0.89  thf('31', plain, ((v1_relat_1 @ sk_D_3)),
% 0.71/0.89      inference('sup-', [status(thm)], ['12', '13'])).
% 0.71/0.89  thf('32', plain,
% 0.71/0.89      (((r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_B))
% 0.71/0.89         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.71/0.89      inference('demod', [status(thm)], ['30', '31'])).
% 0.71/0.89  thf('33', plain,
% 0.71/0.89      ((~ (m1_subset_1 @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_C_1))
% 0.71/0.89         <= ((![X28 : $i]:
% 0.71/0.89                (~ (m1_subset_1 @ X28 @ sk_C_1)
% 0.71/0.89                 | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_E) @ sk_D_3)
% 0.71/0.89                 | ~ (r2_hidden @ X28 @ sk_B))) & 
% 0.71/0.89             ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.71/0.89      inference('demod', [status(thm)], ['27', '32'])).
% 0.71/0.89  thf('34', plain,
% 0.71/0.89      (~ ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))) | 
% 0.71/0.89       ~
% 0.71/0.89       (![X28 : $i]:
% 0.71/0.89          (~ (m1_subset_1 @ X28 @ sk_C_1)
% 0.71/0.89           | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_E) @ sk_D_3)
% 0.71/0.89           | ~ (r2_hidden @ X28 @ sk_B)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['23', '33'])).
% 0.71/0.89  thf('35', plain,
% 0.71/0.89      (((m1_subset_1 @ sk_F @ sk_C_1)) <= (((m1_subset_1 @ sk_F @ sk_C_1)))),
% 0.71/0.89      inference('split', [status(esa)], ['2'])).
% 0.71/0.89  thf('36', plain,
% 0.71/0.89      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 0.71/0.89      inference('split', [status(esa)], ['7'])).
% 0.71/0.89  thf('37', plain,
% 0.71/0.89      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3))
% 0.71/0.89         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3)))),
% 0.71/0.89      inference('split', [status(esa)], ['0'])).
% 0.71/0.89  thf('38', plain,
% 0.71/0.89      ((![X28 : $i]:
% 0.71/0.89          (~ (m1_subset_1 @ X28 @ sk_C_1)
% 0.71/0.89           | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_E) @ sk_D_3)
% 0.71/0.89           | ~ (r2_hidden @ X28 @ sk_B)))
% 0.71/0.89         <= ((![X28 : $i]:
% 0.71/0.89                (~ (m1_subset_1 @ X28 @ sk_C_1)
% 0.71/0.89                 | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_E) @ sk_D_3)
% 0.71/0.89                 | ~ (r2_hidden @ X28 @ sk_B))))),
% 0.71/0.89      inference('split', [status(esa)], ['25'])).
% 0.71/0.89  thf('39', plain,
% 0.71/0.89      (((~ (r2_hidden @ sk_F @ sk_B) | ~ (m1_subset_1 @ sk_F @ sk_C_1)))
% 0.71/0.89         <= ((![X28 : $i]:
% 0.71/0.89                (~ (m1_subset_1 @ X28 @ sk_C_1)
% 0.71/0.89                 | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_E) @ sk_D_3)
% 0.71/0.89                 | ~ (r2_hidden @ X28 @ sk_B))) & 
% 0.71/0.89             ((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['37', '38'])).
% 0.71/0.89  thf('40', plain,
% 0.71/0.89      ((~ (m1_subset_1 @ sk_F @ sk_C_1))
% 0.71/0.89         <= ((![X28 : $i]:
% 0.71/0.89                (~ (m1_subset_1 @ X28 @ sk_C_1)
% 0.71/0.89                 | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_E) @ sk_D_3)
% 0.71/0.89                 | ~ (r2_hidden @ X28 @ sk_B))) & 
% 0.71/0.89             ((r2_hidden @ sk_F @ sk_B)) & 
% 0.71/0.89             ((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['36', '39'])).
% 0.71/0.89  thf('41', plain,
% 0.71/0.89      (~ ((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3)) | 
% 0.71/0.89       ~
% 0.71/0.89       (![X28 : $i]:
% 0.71/0.89          (~ (m1_subset_1 @ X28 @ sk_C_1)
% 0.71/0.89           | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_E) @ sk_D_3)
% 0.71/0.89           | ~ (r2_hidden @ X28 @ sk_B))) | 
% 0.71/0.89       ~ ((m1_subset_1 @ sk_F @ sk_C_1)) | ~ ((r2_hidden @ sk_F @ sk_B))),
% 0.71/0.89      inference('sup-', [status(thm)], ['35', '40'])).
% 0.71/0.89  thf('42', plain,
% 0.71/0.89      (~ ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))) | 
% 0.71/0.89       (![X28 : $i]:
% 0.71/0.89          (~ (m1_subset_1 @ X28 @ sk_C_1)
% 0.71/0.89           | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_E) @ sk_D_3)
% 0.71/0.89           | ~ (r2_hidden @ X28 @ sk_B)))),
% 0.71/0.89      inference('split', [status(esa)], ['25'])).
% 0.71/0.89  thf('43', plain,
% 0.71/0.89      (((r2_hidden @ sk_F @ sk_B)) | 
% 0.71/0.89       ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B)))),
% 0.71/0.89      inference('split', [status(esa)], ['7'])).
% 0.71/0.89  thf('44', plain,
% 0.71/0.89      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 0.71/0.89      inference('split', [status(esa)], ['7'])).
% 0.71/0.89  thf('45', plain,
% 0.71/0.89      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3))
% 0.71/0.89         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3)))),
% 0.71/0.89      inference('split', [status(esa)], ['0'])).
% 0.71/0.89  thf('46', plain,
% 0.71/0.89      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.71/0.89         (~ (r2_hidden @ X17 @ X18)
% 0.71/0.89          | ~ (r2_hidden @ (k4_tarski @ X17 @ X19) @ X20)
% 0.71/0.89          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ X20))
% 0.71/0.89          | (r2_hidden @ X19 @ (k9_relat_1 @ X20 @ X18))
% 0.71/0.89          | ~ (v1_relat_1 @ X20))),
% 0.71/0.89      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.71/0.89  thf('47', plain,
% 0.71/0.89      ((![X0 : $i]:
% 0.71/0.89          (~ (v1_relat_1 @ sk_D_3)
% 0.71/0.89           | (r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_3 @ X0))
% 0.71/0.89           | ~ (r2_hidden @ sk_F @ (k1_relat_1 @ sk_D_3))
% 0.71/0.89           | ~ (r2_hidden @ sk_F @ X0)))
% 0.71/0.89         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['45', '46'])).
% 0.71/0.89  thf('48', plain, ((v1_relat_1 @ sk_D_3)),
% 0.71/0.89      inference('sup-', [status(thm)], ['12', '13'])).
% 0.71/0.89  thf('49', plain,
% 0.71/0.89      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3))
% 0.71/0.89         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3)))),
% 0.71/0.89      inference('split', [status(esa)], ['0'])).
% 0.71/0.89  thf(d4_relat_1, axiom,
% 0.71/0.89    (![A:$i,B:$i]:
% 0.71/0.89     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.71/0.89       ( ![C:$i]:
% 0.71/0.89         ( ( r2_hidden @ C @ B ) <=>
% 0.71/0.89           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.71/0.89  thf('50', plain,
% 0.71/0.89      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.71/0.89         (~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X12)
% 0.71/0.89          | (r2_hidden @ X10 @ X13)
% 0.71/0.89          | ((X13) != (k1_relat_1 @ X12)))),
% 0.71/0.89      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.71/0.89  thf('51', plain,
% 0.71/0.89      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.71/0.89         ((r2_hidden @ X10 @ (k1_relat_1 @ X12))
% 0.71/0.89          | ~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X12))),
% 0.71/0.89      inference('simplify', [status(thm)], ['50'])).
% 0.71/0.89  thf('52', plain,
% 0.71/0.89      (((r2_hidden @ sk_F @ (k1_relat_1 @ sk_D_3)))
% 0.71/0.89         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['49', '51'])).
% 0.71/0.89  thf('53', plain,
% 0.71/0.89      ((![X0 : $i]:
% 0.71/0.89          ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_3 @ X0))
% 0.71/0.89           | ~ (r2_hidden @ sk_F @ X0)))
% 0.71/0.89         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3)))),
% 0.71/0.89      inference('demod', [status(thm)], ['47', '48', '52'])).
% 0.71/0.89  thf('54', plain,
% 0.71/0.89      (((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_3 @ sk_B)))
% 0.71/0.89         <= (((r2_hidden @ sk_F @ sk_B)) & 
% 0.71/0.89             ((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['44', '53'])).
% 0.71/0.89  thf('55', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         ((k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ X0)
% 0.71/0.89           = (k9_relat_1 @ sk_D_3 @ X0))),
% 0.71/0.89      inference('sup-', [status(thm)], ['4', '5'])).
% 0.71/0.89  thf('56', plain,
% 0.71/0.89      ((~ (r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B)))
% 0.71/0.89         <= (~
% 0.71/0.89             ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.71/0.89      inference('split', [status(esa)], ['25'])).
% 0.71/0.89  thf('57', plain,
% 0.71/0.89      ((~ (r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_3 @ sk_B)))
% 0.71/0.89         <= (~
% 0.71/0.89             ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.71/0.90      inference('sup-', [status(thm)], ['55', '56'])).
% 0.71/0.90  thf('58', plain,
% 0.71/0.90      (~ ((r2_hidden @ sk_F @ sk_B)) | 
% 0.71/0.90       ~ ((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3)) | 
% 0.71/0.90       ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['54', '57'])).
% 0.71/0.90  thf('59', plain, ($false),
% 0.71/0.90      inference('sat_resolution*', [status(thm)],
% 0.71/0.90                ['1', '3', '34', '41', '42', '43', '58'])).
% 0.71/0.90  
% 0.71/0.90  % SZS output end Refutation
% 0.71/0.90  
% 0.71/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
