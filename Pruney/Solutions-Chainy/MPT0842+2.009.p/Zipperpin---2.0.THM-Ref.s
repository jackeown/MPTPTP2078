%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2VbSMReXak

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 339 expanded)
%              Number of leaves         :   26 ( 105 expanded)
%              Depth                    :   12
%              Number of atoms          :  799 (5714 expanded)
%              Number of equality atoms :    9 (  41 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t53_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ~ ( v1_xboole_0 @ C )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ A )
                     => ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ C @ D @ B ) )
                      <=> ? [F: $i] :
                            ( ( r2_hidden @ F @ B )
                            & ( r2_hidden @ ( k4_tarski @ E @ F ) @ D )
                            & ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ~ ( v1_xboole_0 @ C )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ A )
                       => ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ C @ D @ B ) )
                        <=> ? [F: $i] :
                              ( ( r2_hidden @ F @ B )
                              & ( r2_hidden @ ( k4_tarski @ E @ F ) @ D )
                              & ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t53_relset_1])).

thf('0',plain,(
    ! [X27: $i] :
      ( ~ ( m1_subset_1 @ X27 @ sk_C_1 )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X27 ) @ sk_D_3 )
      | ~ ( r2_hidden @ X27 @ sk_B )
      | ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( ( k8_relset_1 @ X24 @ X25 @ X23 @ X26 )
        = ( k10_relat_1 @ X23 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ X0 )
      = ( k10_relat_1 @ sk_D_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
   <= ( r2_hidden @ sk_F @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_3 )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_3 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_3 ) ),
    inference(split,[status(esa)],['7'])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X10 ) @ X13 )
      | ~ ( r2_hidden @ X10 @ ( k2_relat_1 @ X13 ) )
      | ( r2_hidden @ X12 @ ( k10_relat_1 @ X13 @ X11 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_D_3 )
        | ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_3 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ ( k2_relat_1 @ sk_D_3 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('12',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('13',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_3 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_3 ) ),
    inference(split,[status(esa)],['7'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( X6
       != ( k2_relat_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('16',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ ( k2_relat_1 @ X5 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X5 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( r2_hidden @ sk_F @ ( k2_relat_1 @ sk_D_3 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_3 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_3 ) ),
    inference(demod,[status(thm)],['10','13','17'])).

thf('19',plain,
    ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_3 @ sk_B ) )
   <= ( ( r2_hidden @ sk_F @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['6','18'])).

thf('20',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) )
    | ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X27 ) @ sk_D_3 )
        | ~ ( r2_hidden @ X27 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ X0 )
      = ( k10_relat_1 @ sk_D_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('22',plain,
    ( ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('23',plain,
    ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_3 @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k10_relat_1 @ X13 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ X12 @ ( sk_D_2 @ X13 @ X11 @ X12 ) ) @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('25',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_3 )
      | ( r2_hidden @ ( k4_tarski @ sk_E @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) ) @ sk_D_3 ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('27',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) ) @ sk_D_3 )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X27 ) @ sk_D_3 )
        | ~ ( r2_hidden @ X27 @ sk_B ) )
   <= ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X27 ) @ sk_D_3 )
        | ~ ( r2_hidden @ X27 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,
    ( ( ~ ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_C_1 ) )
   <= ( ! [X27: $i] :
          ( ~ ( m1_subset_1 @ X27 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X27 ) @ sk_D_3 )
          | ~ ( r2_hidden @ X27 @ sk_B ) )
      & ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_3 @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('31',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k10_relat_1 @ X13 @ X11 ) )
      | ( r2_hidden @ ( sk_D_2 @ X13 @ X11 @ X12 ) @ X11 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('32',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_3 )
      | ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('34',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_B )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_3 @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('36',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k10_relat_1 @ X13 @ X11 ) )
      | ( r2_hidden @ ( sk_D_2 @ X13 @ X11 @ X12 ) @ ( k2_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('37',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_3 )
      | ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ ( k2_relat_1 @ sk_D_3 ) ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('39',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ ( k2_relat_1 @ sk_D_3 ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('41',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X17 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('42',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 ) @ ( k1_zfmisc_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('44',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_relset_1 @ X21 @ X22 @ X20 )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('45',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 )
    = ( k2_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_3 ) @ ( k1_zfmisc_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['42','45'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( m1_subset_1 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_3 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( m1_subset_1 @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_C_1 )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','48'])).

thf('50',plain,
    ( ~ ! [X27: $i] :
          ( ~ ( m1_subset_1 @ X27 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X27 ) @ sk_D_3 )
          | ~ ( r2_hidden @ X27 @ sk_B ) )
    | ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','34','49'])).

thf('51',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('52',plain,(
    r2_hidden @ sk_F @ sk_B ),
    inference('sat_resolution*',[status(thm)],['20','50','51'])).

thf('53',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_3 )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('54',plain,(
    r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_3 ),
    inference('sat_resolution*',[status(thm)],['20','50','53'])).

thf('55',plain,(
    r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_3 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['19','52','54'])).

thf('56',plain,
    ( $false
   <= ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference(demod,[status(thm)],['1','4','55'])).

thf('57',plain,(
    ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['20','50'])).

thf('58',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['56','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2VbSMReXak
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:16:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 77 iterations in 0.061s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.52  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.21/0.52  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.52  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 0.21/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.52  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(t53_relset_1, conjecture,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.21/0.52               ( ![D:$i]:
% 0.21/0.52                 ( ( m1_subset_1 @
% 0.21/0.52                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.21/0.52                   ( ![E:$i]:
% 0.21/0.52                     ( ( m1_subset_1 @ E @ A ) =>
% 0.21/0.52                       ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ C @ D @ B ) ) <=>
% 0.21/0.52                         ( ?[F:$i]:
% 0.21/0.52                           ( ( r2_hidden @ F @ B ) & 
% 0.21/0.52                             ( r2_hidden @ ( k4_tarski @ E @ F ) @ D ) & 
% 0.21/0.52                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i]:
% 0.21/0.52        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.52          ( ![B:$i]:
% 0.21/0.52            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.52              ( ![C:$i]:
% 0.21/0.52                ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.21/0.52                  ( ![D:$i]:
% 0.21/0.52                    ( ( m1_subset_1 @
% 0.21/0.52                        D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.21/0.52                      ( ![E:$i]:
% 0.21/0.52                        ( ( m1_subset_1 @ E @ A ) =>
% 0.21/0.52                          ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ C @ D @ B ) ) <=>
% 0.21/0.52                            ( ?[F:$i]:
% 0.21/0.52                              ( ( r2_hidden @ F @ B ) & 
% 0.21/0.52                                ( r2_hidden @ ( k4_tarski @ E @ F ) @ D ) & 
% 0.21/0.52                                ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t53_relset_1])).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (![X27 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X27 @ sk_C_1)
% 0.21/0.52          | ~ (r2_hidden @ (k4_tarski @ sk_E @ X27) @ sk_D_3)
% 0.21/0.52          | ~ (r2_hidden @ X27 @ sk_B)
% 0.21/0.52          | ~ (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      ((~ (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B)))
% 0.21/0.52         <= (~
% 0.21/0.52             ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(redefinition_k8_relset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.52       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.21/0.52          | ((k8_relset_1 @ X24 @ X25 @ X23 @ X26) = (k10_relat_1 @ X23 @ X26)))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ X0)
% 0.21/0.52           = (k10_relat_1 @ sk_D_3 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (((r2_hidden @ sk_F @ sk_B)
% 0.21/0.52        | (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 0.21/0.52      inference('split', [status(esa)], ['5'])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_3)
% 0.21/0.52        | (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_3))
% 0.21/0.52         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_3)))),
% 0.21/0.52      inference('split', [status(esa)], ['7'])).
% 0.21/0.52  thf(t166_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ C ) =>
% 0.21/0.52       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.21/0.52         ( ?[D:$i]:
% 0.21/0.52           ( ( r2_hidden @ D @ B ) & 
% 0.21/0.52             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.21/0.52             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X10 @ X11)
% 0.21/0.52          | ~ (r2_hidden @ (k4_tarski @ X12 @ X10) @ X13)
% 0.21/0.52          | ~ (r2_hidden @ X10 @ (k2_relat_1 @ X13))
% 0.21/0.52          | (r2_hidden @ X12 @ (k10_relat_1 @ X13 @ X11))
% 0.21/0.52          | ~ (v1_relat_1 @ X13))),
% 0.21/0.52      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      ((![X0 : $i]:
% 0.21/0.52          (~ (v1_relat_1 @ sk_D_3)
% 0.21/0.52           | (r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_3 @ X0))
% 0.21/0.52           | ~ (r2_hidden @ sk_F @ (k2_relat_1 @ sk_D_3))
% 0.21/0.52           | ~ (r2_hidden @ sk_F @ X0)))
% 0.21/0.52         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_3)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(cc1_relset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.52       ( v1_relat_1 @ C ) ))).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.52         ((v1_relat_1 @ X14)
% 0.21/0.52          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.21/0.52      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.52  thf('13', plain, ((v1_relat_1 @ sk_D_3)),
% 0.21/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_3))
% 0.21/0.52         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_3)))),
% 0.21/0.52      inference('split', [status(esa)], ['7'])).
% 0.21/0.52  thf(d5_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.21/0.52       ( ![C:$i]:
% 0.21/0.52         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.52           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.52         (~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X5)
% 0.21/0.52          | (r2_hidden @ X4 @ X6)
% 0.21/0.52          | ((X6) != (k2_relat_1 @ X5)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.52         ((r2_hidden @ X4 @ (k2_relat_1 @ X5))
% 0.21/0.52          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X5))),
% 0.21/0.52      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (((r2_hidden @ sk_F @ (k2_relat_1 @ sk_D_3)))
% 0.21/0.52         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_3)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['14', '16'])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      ((![X0 : $i]:
% 0.21/0.52          ((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_3 @ X0))
% 0.21/0.52           | ~ (r2_hidden @ sk_F @ X0)))
% 0.21/0.52         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_3)))),
% 0.21/0.52      inference('demod', [status(thm)], ['10', '13', '17'])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_3 @ sk_B)))
% 0.21/0.52         <= (((r2_hidden @ sk_F @ sk_B)) & 
% 0.21/0.52             ((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_3)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['6', '18'])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (~ ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))) | 
% 0.21/0.52       (![X27 : $i]:
% 0.21/0.52          (~ (m1_subset_1 @ X27 @ sk_C_1)
% 0.21/0.52           | ~ (r2_hidden @ (k4_tarski @ sk_E @ X27) @ sk_D_3)
% 0.21/0.52           | ~ (r2_hidden @ X27 @ sk_B)))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ X0)
% 0.21/0.52           = (k10_relat_1 @ sk_D_3 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B)))
% 0.21/0.52         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 0.21/0.52      inference('split', [status(esa)], ['5'])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      (((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_3 @ sk_B)))
% 0.21/0.52         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 0.21/0.52      inference('sup+', [status(thm)], ['21', '22'])).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X12 @ (k10_relat_1 @ X13 @ X11))
% 0.21/0.52          | (r2_hidden @ (k4_tarski @ X12 @ (sk_D_2 @ X13 @ X11 @ X12)) @ X13)
% 0.21/0.52          | ~ (v1_relat_1 @ X13))),
% 0.21/0.52      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      (((~ (v1_relat_1 @ sk_D_3)
% 0.21/0.52         | (r2_hidden @ (k4_tarski @ sk_E @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E)) @ 
% 0.21/0.52            sk_D_3)))
% 0.21/0.52         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.52  thf('26', plain, ((v1_relat_1 @ sk_D_3)),
% 0.21/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (((r2_hidden @ (k4_tarski @ sk_E @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E)) @ 
% 0.21/0.52         sk_D_3))
% 0.21/0.52         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 0.21/0.52      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      ((![X27 : $i]:
% 0.21/0.52          (~ (m1_subset_1 @ X27 @ sk_C_1)
% 0.21/0.52           | ~ (r2_hidden @ (k4_tarski @ sk_E @ X27) @ sk_D_3)
% 0.21/0.52           | ~ (r2_hidden @ X27 @ sk_B)))
% 0.21/0.52         <= ((![X27 : $i]:
% 0.21/0.52                (~ (m1_subset_1 @ X27 @ sk_C_1)
% 0.21/0.52                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X27) @ sk_D_3)
% 0.21/0.52                 | ~ (r2_hidden @ X27 @ sk_B))))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      (((~ (r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_B)
% 0.21/0.52         | ~ (m1_subset_1 @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_C_1)))
% 0.21/0.52         <= ((![X27 : $i]:
% 0.21/0.52                (~ (m1_subset_1 @ X27 @ sk_C_1)
% 0.21/0.52                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X27) @ sk_D_3)
% 0.21/0.52                 | ~ (r2_hidden @ X27 @ sk_B))) & 
% 0.21/0.52             ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      (((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_3 @ sk_B)))
% 0.21/0.52         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 0.21/0.52      inference('sup+', [status(thm)], ['21', '22'])).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X12 @ (k10_relat_1 @ X13 @ X11))
% 0.21/0.52          | (r2_hidden @ (sk_D_2 @ X13 @ X11 @ X12) @ X11)
% 0.21/0.52          | ~ (v1_relat_1 @ X13))),
% 0.21/0.52      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      (((~ (v1_relat_1 @ sk_D_3)
% 0.21/0.52         | (r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_B)))
% 0.21/0.52         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.52  thf('33', plain, ((v1_relat_1 @ sk_D_3)),
% 0.21/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.52  thf('34', plain,
% 0.21/0.52      (((r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_B))
% 0.21/0.52         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 0.21/0.52      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      (((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_3 @ sk_B)))
% 0.21/0.52         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 0.21/0.52      inference('sup+', [status(thm)], ['21', '22'])).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X12 @ (k10_relat_1 @ X13 @ X11))
% 0.21/0.52          | (r2_hidden @ (sk_D_2 @ X13 @ X11 @ X12) @ (k2_relat_1 @ X13))
% 0.21/0.52          | ~ (v1_relat_1 @ X13))),
% 0.21/0.52      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.21/0.52  thf('37', plain,
% 0.21/0.52      (((~ (v1_relat_1 @ sk_D_3)
% 0.21/0.52         | (r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ (k2_relat_1 @ sk_D_3))))
% 0.21/0.52         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.52  thf('38', plain, ((v1_relat_1 @ sk_D_3)),
% 0.21/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      (((r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ (k2_relat_1 @ sk_D_3)))
% 0.21/0.52         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 0.21/0.52      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.52  thf('40', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(dt_k2_relset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.52       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.21/0.52  thf('41', plain,
% 0.21/0.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.52         ((m1_subset_1 @ (k2_relset_1 @ X17 @ X18 @ X19) @ (k1_zfmisc_1 @ X18))
% 0.21/0.52          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.21/0.52  thf('42', plain,
% 0.21/0.52      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_C_1 @ sk_D_3) @ 
% 0.21/0.52        (k1_zfmisc_1 @ sk_C_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.52  thf('43', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.52       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.52  thf('44', plain,
% 0.21/0.52      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.52         (((k2_relset_1 @ X21 @ X22 @ X20) = (k2_relat_1 @ X20))
% 0.21/0.52          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.52  thf('45', plain,
% 0.21/0.52      (((k2_relset_1 @ sk_A @ sk_C_1 @ sk_D_3) = (k2_relat_1 @ sk_D_3))),
% 0.21/0.52      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.52  thf('46', plain,
% 0.21/0.52      ((m1_subset_1 @ (k2_relat_1 @ sk_D_3) @ (k1_zfmisc_1 @ sk_C_1))),
% 0.21/0.52      inference('demod', [status(thm)], ['42', '45'])).
% 0.21/0.52  thf(t4_subset, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.21/0.52       ( m1_subset_1 @ A @ C ) ))).
% 0.21/0.52  thf('47', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.21/0.52          | (m1_subset_1 @ X0 @ X2))),
% 0.21/0.52      inference('cnf', [status(esa)], [t4_subset])).
% 0.21/0.52  thf('48', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((m1_subset_1 @ X0 @ sk_C_1)
% 0.21/0.52          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_3)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.52  thf('49', plain,
% 0.21/0.52      (((m1_subset_1 @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_C_1))
% 0.21/0.52         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['39', '48'])).
% 0.21/0.52  thf('50', plain,
% 0.21/0.52      (~
% 0.21/0.52       (![X27 : $i]:
% 0.21/0.52          (~ (m1_subset_1 @ X27 @ sk_C_1)
% 0.21/0.52           | ~ (r2_hidden @ (k4_tarski @ sk_E @ X27) @ sk_D_3)
% 0.21/0.52           | ~ (r2_hidden @ X27 @ sk_B))) | 
% 0.21/0.52       ~ ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B)))),
% 0.21/0.52      inference('demod', [status(thm)], ['29', '34', '49'])).
% 0.21/0.52  thf('51', plain,
% 0.21/0.52      (((r2_hidden @ sk_F @ sk_B)) | 
% 0.21/0.52       ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B)))),
% 0.21/0.52      inference('split', [status(esa)], ['5'])).
% 0.21/0.52  thf('52', plain, (((r2_hidden @ sk_F @ sk_B))),
% 0.21/0.52      inference('sat_resolution*', [status(thm)], ['20', '50', '51'])).
% 0.21/0.52  thf('53', plain,
% 0.21/0.52      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_3)) | 
% 0.21/0.52       ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B)))),
% 0.21/0.52      inference('split', [status(esa)], ['7'])).
% 0.21/0.52  thf('54', plain, (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_3))),
% 0.21/0.52      inference('sat_resolution*', [status(thm)], ['20', '50', '53'])).
% 0.21/0.52  thf('55', plain, ((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_3 @ sk_B))),
% 0.21/0.52      inference('simpl_trail', [status(thm)], ['19', '52', '54'])).
% 0.21/0.52  thf('56', plain,
% 0.21/0.52      (($false)
% 0.21/0.52         <= (~
% 0.21/0.52             ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 0.21/0.52      inference('demod', [status(thm)], ['1', '4', '55'])).
% 0.21/0.52  thf('57', plain,
% 0.21/0.52      (~ ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B)))),
% 0.21/0.52      inference('sat_resolution*', [status(thm)], ['20', '50'])).
% 0.21/0.52  thf('58', plain, ($false),
% 0.21/0.52      inference('simpl_trail', [status(thm)], ['56', '57'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
