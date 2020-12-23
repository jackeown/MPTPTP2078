%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ArLkHl6Rpi

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:28 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 173 expanded)
%              Number of leaves         :   24 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :  773 (2630 expanded)
%              Number of equality atoms :    9 (  26 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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

thf('0',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_1 )
    | ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_1 )
    | ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( ( k8_relset_1 @ X23 @ X24 @ X22 @ X25 )
        = ( k10_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ X0 )
      = ( k10_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_1 @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf(d14_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k10_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ B )
                  & ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i,X16: $i,X17: $i] :
      ( ( X16
       != ( k10_relat_1 @ X14 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ X17 @ ( sk_E_1 @ X17 @ X13 @ X14 ) ) @ X14 )
      | ~ ( r2_hidden @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('9',plain,(
    ! [X13: $i,X14: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( r2_hidden @ X17 @ ( k10_relat_1 @ X14 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ X17 @ ( sk_E_1 @ X17 @ X13 @ X14 ) ) @ X14 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ ( sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1 ) ) @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X20: $i,X21: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ ( sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1 ) ) @ sk_D_1 )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_1 @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('18',plain,(
    ! [X26: $i] :
      ( ~ ( m1_subset_1 @ X26 @ sk_C )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X26 ) @ sk_D_1 )
      | ~ ( r2_hidden @ X26 @ sk_B )
      | ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ X0 )
      = ( k10_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('20',plain,(
    ! [X26: $i] :
      ( ~ ( m1_subset_1 @ X26 @ sk_C )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X26 ) @ sk_D_1 )
      | ~ ( r2_hidden @ X26 @ sk_B )
      | ~ ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X0 ) @ sk_D_1 )
        | ~ ( m1_subset_1 @ X0 @ sk_C ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1 ) @ sk_C )
      | ~ ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1 ) @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_1 @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('24',plain,(
    ! [X13: $i,X14: $i,X16: $i,X17: $i] :
      ( ( X16
       != ( k10_relat_1 @ X14 @ X13 ) )
      | ( r2_hidden @ ( sk_E_1 @ X17 @ X13 @ X14 ) @ X13 )
      | ~ ( r2_hidden @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('25',plain,(
    ! [X13: $i,X14: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( r2_hidden @ X17 @ ( k10_relat_1 @ X14 @ X13 ) )
      | ( r2_hidden @ ( sk_E_1 @ X17 @ X13 @ X14 ) @ X13 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1 ) @ sk_B )
      | ~ ( v1_relat_1 @ sk_D_1 ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('28',plain,
    ( ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1 ) @ sk_B )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1 ) @ sk_C )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','28'])).

thf('30',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ ( sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1 ) ) @ sk_D_1 )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('31',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('32',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ ( sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_C ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('36',plain,
    ( ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1 ) @ sk_C )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('37',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('38',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1 ) @ sk_C )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','38'])).

thf('40',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('41',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
   <= ( r2_hidden @ sk_F @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('42',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('43',plain,(
    ! [X13: $i,X14: $i,X16: $i,X18: $i,X19: $i] :
      ( ( X16
       != ( k10_relat_1 @ X14 @ X13 ) )
      | ( r2_hidden @ X18 @ X16 )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ X14 )
      | ~ ( r2_hidden @ X19 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('44',plain,(
    ! [X13: $i,X14: $i,X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( r2_hidden @ X19 @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ X14 )
      | ( r2_hidden @ X18 @ ( k10_relat_1 @ X14 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ X0 )
        | ~ ( v1_relat_1 @ sk_D_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('47',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_1 @ sk_B ) )
   <= ( ( r2_hidden @ sk_F @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['41','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ X0 )
      = ( k10_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('50',plain,(
    ! [X26: $i] :
      ( ~ ( m1_subset_1 @ X26 @ sk_C )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X26 ) @ sk_D_1 )
      | ~ ( r2_hidden @ X26 @ sk_B )
      | ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['50'])).

thf('52',plain,
    ( ~ ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,
    ( ~ ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['48','52'])).

thf('54',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','39','40','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ArLkHl6Rpi
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:46:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.77/0.95  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.77/0.95  % Solved by: fo/fo7.sh
% 0.77/0.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/0.95  % done 389 iterations in 0.495s
% 0.77/0.95  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.77/0.95  % SZS output start Refutation
% 0.77/0.95  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.77/0.95  thf(sk_C_type, type, sk_C: $i).
% 0.77/0.95  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.77/0.95  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.77/0.95  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.77/0.95  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.77/0.95  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.77/0.95  thf(sk_F_type, type, sk_F: $i).
% 0.77/0.95  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.77/0.95  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.77/0.95  thf(sk_A_type, type, sk_A: $i).
% 0.77/0.95  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.77/0.95  thf(sk_B_type, type, sk_B: $i).
% 0.77/0.95  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.77/0.95  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.77/0.95  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.77/0.95  thf(t53_relset_1, conjecture,
% 0.77/0.95    (![A:$i]:
% 0.77/0.95     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.77/0.95       ( ![B:$i]:
% 0.77/0.95         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.77/0.95           ( ![C:$i]:
% 0.77/0.95             ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.77/0.95               ( ![D:$i]:
% 0.77/0.95                 ( ( m1_subset_1 @
% 0.77/0.95                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.77/0.95                   ( ![E:$i]:
% 0.77/0.95                     ( ( m1_subset_1 @ E @ A ) =>
% 0.77/0.95                       ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ C @ D @ B ) ) <=>
% 0.77/0.95                         ( ?[F:$i]:
% 0.77/0.95                           ( ( r2_hidden @ F @ B ) & 
% 0.77/0.95                             ( r2_hidden @ ( k4_tarski @ E @ F ) @ D ) & 
% 0.77/0.95                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.77/0.95  thf(zf_stmt_0, negated_conjecture,
% 0.77/0.95    (~( ![A:$i]:
% 0.77/0.95        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.77/0.95          ( ![B:$i]:
% 0.77/0.95            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.77/0.95              ( ![C:$i]:
% 0.77/0.95                ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.77/0.95                  ( ![D:$i]:
% 0.77/0.95                    ( ( m1_subset_1 @
% 0.77/0.95                        D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.77/0.95                      ( ![E:$i]:
% 0.77/0.95                        ( ( m1_subset_1 @ E @ A ) =>
% 0.77/0.95                          ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ C @ D @ B ) ) <=>
% 0.77/0.95                            ( ?[F:$i]:
% 0.77/0.95                              ( ( r2_hidden @ F @ B ) & 
% 0.77/0.95                                ( r2_hidden @ ( k4_tarski @ E @ F ) @ D ) & 
% 0.77/0.95                                ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.77/0.95    inference('cnf.neg', [status(esa)], [t53_relset_1])).
% 0.77/0.95  thf('0', plain,
% 0.77/0.95      (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_1)
% 0.77/0.95        | (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('1', plain,
% 0.77/0.95      (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_1)) | 
% 0.77/0.95       ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.77/0.95      inference('split', [status(esa)], ['0'])).
% 0.77/0.95  thf('2', plain,
% 0.77/0.95      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf(redefinition_k8_relset_1, axiom,
% 0.77/0.95    (![A:$i,B:$i,C:$i,D:$i]:
% 0.77/0.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.77/0.95       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.77/0.95  thf('3', plain,
% 0.77/0.95      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.77/0.95         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.77/0.95          | ((k8_relset_1 @ X23 @ X24 @ X22 @ X25) = (k10_relat_1 @ X22 @ X25)))),
% 0.77/0.95      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.77/0.95  thf('4', plain,
% 0.77/0.95      (![X0 : $i]:
% 0.77/0.95         ((k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ X0)
% 0.77/0.95           = (k10_relat_1 @ sk_D_1 @ X0))),
% 0.77/0.95      inference('sup-', [status(thm)], ['2', '3'])).
% 0.77/0.95  thf('5', plain,
% 0.77/0.95      (((r2_hidden @ sk_F @ sk_B)
% 0.77/0.95        | (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('6', plain,
% 0.77/0.95      (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))
% 0.77/0.95         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.77/0.95      inference('split', [status(esa)], ['5'])).
% 0.77/0.95  thf('7', plain,
% 0.77/0.95      (((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_1 @ sk_B)))
% 0.77/0.95         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.77/0.95      inference('sup+', [status(thm)], ['4', '6'])).
% 0.77/0.95  thf(d14_relat_1, axiom,
% 0.77/0.95    (![A:$i]:
% 0.77/0.95     ( ( v1_relat_1 @ A ) =>
% 0.77/0.95       ( ![B:$i,C:$i]:
% 0.77/0.95         ( ( ( C ) = ( k10_relat_1 @ A @ B ) ) <=>
% 0.77/0.95           ( ![D:$i]:
% 0.77/0.95             ( ( r2_hidden @ D @ C ) <=>
% 0.77/0.95               ( ?[E:$i]:
% 0.77/0.95                 ( ( r2_hidden @ E @ B ) & 
% 0.77/0.95                   ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) ) ) ))).
% 0.77/0.95  thf('8', plain,
% 0.77/0.95      (![X13 : $i, X14 : $i, X16 : $i, X17 : $i]:
% 0.77/0.95         (((X16) != (k10_relat_1 @ X14 @ X13))
% 0.77/0.95          | (r2_hidden @ (k4_tarski @ X17 @ (sk_E_1 @ X17 @ X13 @ X14)) @ X14)
% 0.77/0.95          | ~ (r2_hidden @ X17 @ X16)
% 0.77/0.95          | ~ (v1_relat_1 @ X14))),
% 0.77/0.95      inference('cnf', [status(esa)], [d14_relat_1])).
% 0.77/0.95  thf('9', plain,
% 0.77/0.95      (![X13 : $i, X14 : $i, X17 : $i]:
% 0.77/0.95         (~ (v1_relat_1 @ X14)
% 0.77/0.95          | ~ (r2_hidden @ X17 @ (k10_relat_1 @ X14 @ X13))
% 0.77/0.95          | (r2_hidden @ (k4_tarski @ X17 @ (sk_E_1 @ X17 @ X13 @ X14)) @ X14))),
% 0.77/0.95      inference('simplify', [status(thm)], ['8'])).
% 0.77/0.95  thf('10', plain,
% 0.77/0.95      ((((r2_hidden @ 
% 0.77/0.95          (k4_tarski @ sk_E_2 @ (sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1)) @ sk_D_1)
% 0.77/0.95         | ~ (v1_relat_1 @ sk_D_1)))
% 0.77/0.95         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.77/0.95      inference('sup-', [status(thm)], ['7', '9'])).
% 0.77/0.95  thf('11', plain,
% 0.77/0.95      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf(cc2_relat_1, axiom,
% 0.77/0.95    (![A:$i]:
% 0.77/0.95     ( ( v1_relat_1 @ A ) =>
% 0.77/0.95       ( ![B:$i]:
% 0.77/0.95         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.77/0.95  thf('12', plain,
% 0.77/0.95      (![X10 : $i, X11 : $i]:
% 0.77/0.95         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.77/0.95          | (v1_relat_1 @ X10)
% 0.77/0.95          | ~ (v1_relat_1 @ X11))),
% 0.77/0.95      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.77/0.95  thf('13', plain,
% 0.77/0.95      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)) | (v1_relat_1 @ sk_D_1))),
% 0.77/0.95      inference('sup-', [status(thm)], ['11', '12'])).
% 0.77/0.95  thf(fc6_relat_1, axiom,
% 0.77/0.95    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.77/0.95  thf('14', plain,
% 0.77/0.95      (![X20 : $i, X21 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X20 @ X21))),
% 0.77/0.95      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.77/0.95  thf('15', plain, ((v1_relat_1 @ sk_D_1)),
% 0.77/0.95      inference('demod', [status(thm)], ['13', '14'])).
% 0.77/0.95  thf('16', plain,
% 0.77/0.95      (((r2_hidden @ 
% 0.77/0.95         (k4_tarski @ sk_E_2 @ (sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1)) @ sk_D_1))
% 0.77/0.95         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.77/0.95      inference('demod', [status(thm)], ['10', '15'])).
% 0.77/0.95  thf('17', plain,
% 0.77/0.95      (((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_1 @ sk_B)))
% 0.77/0.95         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.77/0.95      inference('sup+', [status(thm)], ['4', '6'])).
% 0.77/0.95  thf('18', plain,
% 0.77/0.95      (![X26 : $i]:
% 0.77/0.95         (~ (m1_subset_1 @ X26 @ sk_C)
% 0.77/0.95          | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X26) @ sk_D_1)
% 0.77/0.95          | ~ (r2_hidden @ X26 @ sk_B)
% 0.77/0.95          | ~ (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('19', plain,
% 0.77/0.95      (![X0 : $i]:
% 0.77/0.95         ((k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ X0)
% 0.77/0.95           = (k10_relat_1 @ sk_D_1 @ X0))),
% 0.77/0.95      inference('sup-', [status(thm)], ['2', '3'])).
% 0.77/0.95  thf('20', plain,
% 0.77/0.95      (![X26 : $i]:
% 0.77/0.95         (~ (m1_subset_1 @ X26 @ sk_C)
% 0.77/0.95          | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X26) @ sk_D_1)
% 0.77/0.95          | ~ (r2_hidden @ X26 @ sk_B)
% 0.77/0.95          | ~ (r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_1 @ sk_B)))),
% 0.77/0.95      inference('demod', [status(thm)], ['18', '19'])).
% 0.77/0.95  thf('21', plain,
% 0.77/0.95      ((![X0 : $i]:
% 0.77/0.95          (~ (r2_hidden @ X0 @ sk_B)
% 0.77/0.95           | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X0) @ sk_D_1)
% 0.77/0.95           | ~ (m1_subset_1 @ X0 @ sk_C)))
% 0.77/0.95         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.77/0.95      inference('sup-', [status(thm)], ['17', '20'])).
% 0.77/0.95  thf('22', plain,
% 0.77/0.95      (((~ (m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1) @ sk_C)
% 0.77/0.95         | ~ (r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1) @ sk_B)))
% 0.77/0.95         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.77/0.95      inference('sup-', [status(thm)], ['16', '21'])).
% 0.77/0.95  thf('23', plain,
% 0.77/0.95      (((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_1 @ sk_B)))
% 0.77/0.95         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.77/0.95      inference('sup+', [status(thm)], ['4', '6'])).
% 0.77/0.95  thf('24', plain,
% 0.77/0.95      (![X13 : $i, X14 : $i, X16 : $i, X17 : $i]:
% 0.77/0.95         (((X16) != (k10_relat_1 @ X14 @ X13))
% 0.77/0.95          | (r2_hidden @ (sk_E_1 @ X17 @ X13 @ X14) @ X13)
% 0.77/0.95          | ~ (r2_hidden @ X17 @ X16)
% 0.77/0.95          | ~ (v1_relat_1 @ X14))),
% 0.77/0.95      inference('cnf', [status(esa)], [d14_relat_1])).
% 0.77/0.95  thf('25', plain,
% 0.77/0.95      (![X13 : $i, X14 : $i, X17 : $i]:
% 0.77/0.95         (~ (v1_relat_1 @ X14)
% 0.77/0.95          | ~ (r2_hidden @ X17 @ (k10_relat_1 @ X14 @ X13))
% 0.77/0.95          | (r2_hidden @ (sk_E_1 @ X17 @ X13 @ X14) @ X13))),
% 0.77/0.95      inference('simplify', [status(thm)], ['24'])).
% 0.77/0.95  thf('26', plain,
% 0.77/0.95      ((((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1) @ sk_B)
% 0.77/0.95         | ~ (v1_relat_1 @ sk_D_1)))
% 0.77/0.95         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.77/0.95      inference('sup-', [status(thm)], ['23', '25'])).
% 0.77/0.95  thf('27', plain, ((v1_relat_1 @ sk_D_1)),
% 0.77/0.95      inference('demod', [status(thm)], ['13', '14'])).
% 0.77/0.95  thf('28', plain,
% 0.77/0.95      (((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1) @ sk_B))
% 0.77/0.95         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.77/0.95      inference('demod', [status(thm)], ['26', '27'])).
% 0.77/0.95  thf('29', plain,
% 0.77/0.95      ((~ (m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1) @ sk_C))
% 0.77/0.95         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.77/0.95      inference('demod', [status(thm)], ['22', '28'])).
% 0.77/0.95  thf('30', plain,
% 0.77/0.95      (((r2_hidden @ 
% 0.77/0.95         (k4_tarski @ sk_E_2 @ (sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1)) @ sk_D_1))
% 0.77/0.95         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.77/0.95      inference('demod', [status(thm)], ['10', '15'])).
% 0.77/0.95  thf('31', plain,
% 0.77/0.95      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf(l3_subset_1, axiom,
% 0.77/0.95    (![A:$i,B:$i]:
% 0.77/0.95     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.77/0.95       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.77/0.95  thf('32', plain,
% 0.77/0.95      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.77/0.95         (~ (r2_hidden @ X5 @ X6)
% 0.77/0.95          | (r2_hidden @ X5 @ X7)
% 0.77/0.95          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.77/0.95      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.77/0.95  thf('33', plain,
% 0.77/0.95      (![X0 : $i]:
% 0.77/0.95         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_C))
% 0.77/0.95          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.77/0.95      inference('sup-', [status(thm)], ['31', '32'])).
% 0.77/0.95  thf('34', plain,
% 0.77/0.95      (((r2_hidden @ 
% 0.77/0.95         (k4_tarski @ sk_E_2 @ (sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1)) @ 
% 0.77/0.95         (k2_zfmisc_1 @ sk_A @ sk_C)))
% 0.77/0.95         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.77/0.95      inference('sup-', [status(thm)], ['30', '33'])).
% 0.77/0.95  thf(l54_zfmisc_1, axiom,
% 0.77/0.95    (![A:$i,B:$i,C:$i,D:$i]:
% 0.77/0.95     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.77/0.95       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.77/0.95  thf('35', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.77/0.95         ((r2_hidden @ X2 @ X3)
% 0.77/0.95          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 0.77/0.95      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.77/0.95  thf('36', plain,
% 0.77/0.95      (((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1) @ sk_C))
% 0.77/0.95         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.77/0.95      inference('sup-', [status(thm)], ['34', '35'])).
% 0.77/0.95  thf(t1_subset, axiom,
% 0.77/0.95    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.77/0.95  thf('37', plain,
% 0.77/0.95      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 0.77/0.95      inference('cnf', [status(esa)], [t1_subset])).
% 0.77/0.95  thf('38', plain,
% 0.77/0.95      (((m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1) @ sk_C))
% 0.77/0.95         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.77/0.95      inference('sup-', [status(thm)], ['36', '37'])).
% 0.77/0.95  thf('39', plain,
% 0.77/0.95      (~ ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.77/0.95      inference('demod', [status(thm)], ['29', '38'])).
% 0.77/0.95  thf('40', plain,
% 0.77/0.95      (((r2_hidden @ sk_F @ sk_B)) | 
% 0.77/0.95       ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.77/0.95      inference('split', [status(esa)], ['5'])).
% 0.77/0.95  thf('41', plain,
% 0.77/0.95      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 0.77/0.95      inference('split', [status(esa)], ['5'])).
% 0.77/0.95  thf('42', plain,
% 0.77/0.95      (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_1))
% 0.77/0.95         <= (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_1)))),
% 0.77/0.95      inference('split', [status(esa)], ['0'])).
% 0.77/0.95  thf('43', plain,
% 0.77/0.95      (![X13 : $i, X14 : $i, X16 : $i, X18 : $i, X19 : $i]:
% 0.77/0.95         (((X16) != (k10_relat_1 @ X14 @ X13))
% 0.77/0.95          | (r2_hidden @ X18 @ X16)
% 0.77/0.95          | ~ (r2_hidden @ (k4_tarski @ X18 @ X19) @ X14)
% 0.77/0.95          | ~ (r2_hidden @ X19 @ X13)
% 0.77/0.95          | ~ (v1_relat_1 @ X14))),
% 0.77/0.95      inference('cnf', [status(esa)], [d14_relat_1])).
% 0.77/0.95  thf('44', plain,
% 0.77/0.95      (![X13 : $i, X14 : $i, X18 : $i, X19 : $i]:
% 0.77/0.95         (~ (v1_relat_1 @ X14)
% 0.77/0.95          | ~ (r2_hidden @ X19 @ X13)
% 0.77/0.95          | ~ (r2_hidden @ (k4_tarski @ X18 @ X19) @ X14)
% 0.77/0.95          | (r2_hidden @ X18 @ (k10_relat_1 @ X14 @ X13)))),
% 0.77/0.95      inference('simplify', [status(thm)], ['43'])).
% 0.77/0.95  thf('45', plain,
% 0.77/0.95      ((![X0 : $i]:
% 0.77/0.95          ((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_1 @ X0))
% 0.77/0.95           | ~ (r2_hidden @ sk_F @ X0)
% 0.77/0.95           | ~ (v1_relat_1 @ sk_D_1)))
% 0.77/0.95         <= (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_1)))),
% 0.77/0.95      inference('sup-', [status(thm)], ['42', '44'])).
% 0.77/0.95  thf('46', plain, ((v1_relat_1 @ sk_D_1)),
% 0.77/0.95      inference('demod', [status(thm)], ['13', '14'])).
% 0.77/0.95  thf('47', plain,
% 0.77/0.95      ((![X0 : $i]:
% 0.77/0.95          ((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_1 @ X0))
% 0.77/0.95           | ~ (r2_hidden @ sk_F @ X0)))
% 0.77/0.95         <= (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_1)))),
% 0.77/0.95      inference('demod', [status(thm)], ['45', '46'])).
% 0.77/0.95  thf('48', plain,
% 0.77/0.95      (((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_1 @ sk_B)))
% 0.77/0.95         <= (((r2_hidden @ sk_F @ sk_B)) & 
% 0.77/0.95             ((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_1)))),
% 0.77/0.95      inference('sup-', [status(thm)], ['41', '47'])).
% 0.77/0.95  thf('49', plain,
% 0.77/0.95      (![X0 : $i]:
% 0.77/0.95         ((k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ X0)
% 0.77/0.95           = (k10_relat_1 @ sk_D_1 @ X0))),
% 0.77/0.95      inference('sup-', [status(thm)], ['2', '3'])).
% 0.77/0.95  thf('50', plain,
% 0.77/0.95      (![X26 : $i]:
% 0.77/0.95         (~ (m1_subset_1 @ X26 @ sk_C)
% 0.77/0.95          | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X26) @ sk_D_1)
% 0.77/0.95          | ~ (r2_hidden @ X26 @ sk_B)
% 0.77/0.95          | ~ (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('51', plain,
% 0.77/0.95      ((~ (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))
% 0.77/0.95         <= (~
% 0.77/0.95             ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.77/0.95      inference('split', [status(esa)], ['50'])).
% 0.77/0.95  thf('52', plain,
% 0.77/0.95      ((~ (r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_1 @ sk_B)))
% 0.77/0.95         <= (~
% 0.77/0.95             ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.77/0.95      inference('sup-', [status(thm)], ['49', '51'])).
% 0.77/0.95  thf('53', plain,
% 0.77/0.95      (~ ((r2_hidden @ sk_F @ sk_B)) | 
% 0.77/0.95       ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))) | 
% 0.77/0.95       ~ ((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_1))),
% 0.77/0.95      inference('sup-', [status(thm)], ['48', '52'])).
% 0.77/0.95  thf('54', plain, ($false),
% 0.77/0.95      inference('sat_resolution*', [status(thm)], ['1', '39', '40', '53'])).
% 0.77/0.95  
% 0.77/0.95  % SZS output end Refutation
% 0.77/0.95  
% 0.77/0.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
