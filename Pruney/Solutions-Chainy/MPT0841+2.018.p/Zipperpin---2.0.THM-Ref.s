%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cvF74IV2J1

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 369 expanded)
%              Number of leaves         :   27 ( 115 expanded)
%              Depth                    :   12
%              Number of atoms          :  813 (5854 expanded)
%              Number of equality atoms :    9 (  41 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf('0',plain,(
    ! [X28: $i] :
      ( ~ ( m1_subset_1 @ X28 @ sk_C_1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_E ) @ sk_D_3 )
      | ~ ( r2_hidden @ X28 @ sk_B )
      | ~ ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k7_relset_1 @ X25 @ X26 @ X24 @ X27 )
        = ( k9_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ X0 )
      = ( k9_relat_1 @ sk_D_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
   <= ( r2_hidden @ sk_F @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 )
    | ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 ) ),
    inference(split,[status(esa)],['7'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ X17 )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X17 ) )
      | ( r2_hidden @ X16 @ ( k9_relat_1 @ X17 @ X15 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_D_3 )
        | ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_3 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ ( k1_relat_1 @ sk_D_3 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) )
    | ( v1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 ) ),
    inference(split,[status(esa)],['7'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('17',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X5 @ X6 ) @ X7 )
      | ( r2_hidden @ X5 @ X8 )
      | ( X8
       != ( k1_relat_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('18',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X5 @ ( k1_relat_1 @ X7 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X6 ) @ X7 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( r2_hidden @ sk_F @ ( k1_relat_1 @ sk_D_3 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_3 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 ) ),
    inference(demod,[status(thm)],['10','15','19'])).

thf('21',plain,
    ( ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_3 @ sk_B ) )
   <= ( ( r2_hidden @ sk_F @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['6','20'])).

thf('22',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) )
    | ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_E ) @ sk_D_3 )
        | ~ ( r2_hidden @ X28 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ X0 )
      = ( k9_relat_1 @ sk_D_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('24',plain,
    ( ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('25',plain,
    ( ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_3 @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k9_relat_1 @ X17 @ X15 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X17 @ X15 @ X16 ) @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('27',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_E ) @ sk_D_3 ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['13','14'])).

thf('29',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_E ) @ sk_D_3 )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_E ) @ sk_D_3 )
        | ~ ( r2_hidden @ X28 @ sk_B ) )
   <= ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_E ) @ sk_D_3 )
        | ~ ( r2_hidden @ X28 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,
    ( ( ~ ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_C_1 ) )
   <= ( ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_E ) @ sk_D_3 )
          | ~ ( r2_hidden @ X28 @ sk_B ) )
      & ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_3 @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('33',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k9_relat_1 @ X17 @ X15 ) )
      | ( r2_hidden @ ( sk_D_2 @ X17 @ X15 @ X16 ) @ X15 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('34',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_3 )
      | ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['13','14'])).

thf('36',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_B )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_3 @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('38',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k9_relat_1 @ X17 @ X15 ) )
      | ( r2_hidden @ ( sk_D_2 @ X17 @ X15 @ X16 ) @ ( k1_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('39',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_3 )
      | ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ ( k1_relat_1 @ sk_D_3 ) ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['13','14'])).

thf('41',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ ( k1_relat_1 @ sk_D_3 ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('43',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X18 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('44',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 ) @ ( k1_zfmisc_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('46',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('47',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 )
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_D_3 ) @ ( k1_zfmisc_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['44','47'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( m1_subset_1 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_3 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( m1_subset_1 @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_C_1 )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','50'])).

thf('52',plain,
    ( ~ ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_E ) @ sk_D_3 )
          | ~ ( r2_hidden @ X28 @ sk_B ) )
    | ~ ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','36','51'])).

thf('53',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('54',plain,(
    r2_hidden @ sk_F @ sk_B ),
    inference('sat_resolution*',[status(thm)],['22','52','53'])).

thf('55',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 )
    | ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('56',plain,(
    r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 ),
    inference('sat_resolution*',[status(thm)],['22','52','55'])).

thf('57',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_3 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['21','54','56'])).

thf('58',plain,
    ( $false
   <= ~ ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference(demod,[status(thm)],['1','4','57'])).

thf('59',plain,(
    ~ ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['22','52'])).

thf('60',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['58','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cvF74IV2J1
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:32:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 77 iterations in 0.066s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.51  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.51  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.51  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.20/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.51  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.51  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(t52_relset_1, conjecture,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.20/0.51               ( ![D:$i]:
% 0.20/0.51                 ( ( m1_subset_1 @
% 0.20/0.51                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.20/0.51                   ( ![E:$i]:
% 0.20/0.51                     ( ( m1_subset_1 @ E @ A ) =>
% 0.20/0.51                       ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) ) <=>
% 0.20/0.51                         ( ?[F:$i]:
% 0.20/0.51                           ( ( r2_hidden @ F @ B ) & 
% 0.20/0.51                             ( r2_hidden @ ( k4_tarski @ F @ E ) @ D ) & 
% 0.20/0.51                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i]:
% 0.20/0.51        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.51          ( ![B:$i]:
% 0.20/0.51            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.51              ( ![C:$i]:
% 0.20/0.51                ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.20/0.51                  ( ![D:$i]:
% 0.20/0.51                    ( ( m1_subset_1 @
% 0.20/0.51                        D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.20/0.51                      ( ![E:$i]:
% 0.20/0.51                        ( ( m1_subset_1 @ E @ A ) =>
% 0.20/0.51                          ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) ) <=>
% 0.20/0.51                            ( ?[F:$i]:
% 0.20/0.51                              ( ( r2_hidden @ F @ B ) & 
% 0.20/0.51                                ( r2_hidden @ ( k4_tarski @ F @ E ) @ D ) & 
% 0.20/0.51                                ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t52_relset_1])).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      (![X28 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X28 @ sk_C_1)
% 0.20/0.51          | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_E) @ sk_D_3)
% 0.20/0.51          | ~ (r2_hidden @ X28 @ sk_B)
% 0.20/0.51          | ~ (r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B)))
% 0.20/0.51         <= (~
% 0.20/0.51             ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(redefinition_k7_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.20/0.51          | ((k7_relset_1 @ X25 @ X26 @ X24 @ X27) = (k9_relat_1 @ X24 @ X27)))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ X0)
% 0.20/0.51           = (k9_relat_1 @ sk_D_3 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (((r2_hidden @ sk_F @ sk_B)
% 0.20/0.51        | (r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['5'])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3)
% 0.20/0.51        | (r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3))
% 0.20/0.51         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3)))),
% 0.20/0.51      inference('split', [status(esa)], ['7'])).
% 0.20/0.51  thf(t143_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ C ) =>
% 0.20/0.51       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.20/0.51         ( ?[D:$i]:
% 0.20/0.51           ( ( r2_hidden @ D @ B ) & 
% 0.20/0.51             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.20/0.51             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X14 @ X15)
% 0.20/0.51          | ~ (r2_hidden @ (k4_tarski @ X14 @ X16) @ X17)
% 0.20/0.51          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X17))
% 0.20/0.51          | (r2_hidden @ X16 @ (k9_relat_1 @ X17 @ X15))
% 0.20/0.51          | ~ (v1_relat_1 @ X17))),
% 0.20/0.51      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          (~ (v1_relat_1 @ sk_D_3)
% 0.20/0.51           | (r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_3 @ X0))
% 0.20/0.51           | ~ (r2_hidden @ sk_F @ (k1_relat_1 @ sk_D_3))
% 0.20/0.51           | ~ (r2_hidden @ sk_F @ X0)))
% 0.20/0.51         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(cc2_relat_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X3 : $i, X4 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.20/0.51          | (v1_relat_1 @ X3)
% 0.20/0.51          | ~ (v1_relat_1 @ X4))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)) | (v1_relat_1 @ sk_D_3))),
% 0.20/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.51  thf(fc6_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X12 @ X13))),
% 0.20/0.51      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.51  thf('15', plain, ((v1_relat_1 @ sk_D_3)),
% 0.20/0.51      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3))
% 0.20/0.51         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3)))),
% 0.20/0.51      inference('split', [status(esa)], ['7'])).
% 0.20/0.51  thf(d4_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.20/0.51       ( ![C:$i]:
% 0.20/0.51         ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.51           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.51         (~ (r2_hidden @ (k4_tarski @ X5 @ X6) @ X7)
% 0.20/0.52          | (r2_hidden @ X5 @ X8)
% 0.20/0.52          | ((X8) != (k1_relat_1 @ X7)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.52         ((r2_hidden @ X5 @ (k1_relat_1 @ X7))
% 0.20/0.52          | ~ (r2_hidden @ (k4_tarski @ X5 @ X6) @ X7))),
% 0.20/0.52      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (((r2_hidden @ sk_F @ (k1_relat_1 @ sk_D_3)))
% 0.20/0.52         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['16', '18'])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      ((![X0 : $i]:
% 0.20/0.52          ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_3 @ X0))
% 0.20/0.52           | ~ (r2_hidden @ sk_F @ X0)))
% 0.20/0.52         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3)))),
% 0.20/0.52      inference('demod', [status(thm)], ['10', '15', '19'])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_3 @ sk_B)))
% 0.20/0.52         <= (((r2_hidden @ sk_F @ sk_B)) & 
% 0.20/0.52             ((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['6', '20'])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (~ ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))) | 
% 0.20/0.52       (![X28 : $i]:
% 0.20/0.52          (~ (m1_subset_1 @ X28 @ sk_C_1)
% 0.20/0.52           | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_E) @ sk_D_3)
% 0.20/0.52           | ~ (r2_hidden @ X28 @ sk_B)))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ X0)
% 0.20/0.52           = (k9_relat_1 @ sk_D_3 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B)))
% 0.20/0.52         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.20/0.52      inference('split', [status(esa)], ['5'])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_3 @ sk_B)))
% 0.20/0.52         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['23', '24'])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X16 @ (k9_relat_1 @ X17 @ X15))
% 0.20/0.52          | (r2_hidden @ (k4_tarski @ (sk_D_2 @ X17 @ X15 @ X16) @ X16) @ X17)
% 0.20/0.52          | ~ (v1_relat_1 @ X17))),
% 0.20/0.52      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (((~ (v1_relat_1 @ sk_D_3)
% 0.20/0.52         | (r2_hidden @ (k4_tarski @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_E) @ 
% 0.20/0.52            sk_D_3)))
% 0.20/0.52         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.52  thf('28', plain, ((v1_relat_1 @ sk_D_3)),
% 0.20/0.52      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (((r2_hidden @ (k4_tarski @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_E) @ 
% 0.20/0.52         sk_D_3))
% 0.20/0.52         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.20/0.52      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      ((![X28 : $i]:
% 0.20/0.52          (~ (m1_subset_1 @ X28 @ sk_C_1)
% 0.20/0.52           | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_E) @ sk_D_3)
% 0.20/0.52           | ~ (r2_hidden @ X28 @ sk_B)))
% 0.20/0.52         <= ((![X28 : $i]:
% 0.20/0.52                (~ (m1_subset_1 @ X28 @ sk_C_1)
% 0.20/0.52                 | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_E) @ sk_D_3)
% 0.20/0.52                 | ~ (r2_hidden @ X28 @ sk_B))))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      (((~ (r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_B)
% 0.20/0.52         | ~ (m1_subset_1 @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_C_1)))
% 0.20/0.52         <= ((![X28 : $i]:
% 0.20/0.52                (~ (m1_subset_1 @ X28 @ sk_C_1)
% 0.20/0.52                 | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_E) @ sk_D_3)
% 0.20/0.52                 | ~ (r2_hidden @ X28 @ sk_B))) & 
% 0.20/0.52             ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      (((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_3 @ sk_B)))
% 0.20/0.52         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['23', '24'])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X16 @ (k9_relat_1 @ X17 @ X15))
% 0.20/0.52          | (r2_hidden @ (sk_D_2 @ X17 @ X15 @ X16) @ X15)
% 0.20/0.52          | ~ (v1_relat_1 @ X17))),
% 0.20/0.52      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      (((~ (v1_relat_1 @ sk_D_3)
% 0.20/0.52         | (r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_B)))
% 0.20/0.52         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.52  thf('35', plain, ((v1_relat_1 @ sk_D_3)),
% 0.20/0.52      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      (((r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_B))
% 0.20/0.52         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.20/0.52      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_3 @ sk_B)))
% 0.20/0.52         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['23', '24'])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X16 @ (k9_relat_1 @ X17 @ X15))
% 0.20/0.52          | (r2_hidden @ (sk_D_2 @ X17 @ X15 @ X16) @ (k1_relat_1 @ X17))
% 0.20/0.52          | ~ (v1_relat_1 @ X17))),
% 0.20/0.52      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (((~ (v1_relat_1 @ sk_D_3)
% 0.20/0.52         | (r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ (k1_relat_1 @ sk_D_3))))
% 0.20/0.52         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.52  thf('40', plain, ((v1_relat_1 @ sk_D_3)),
% 0.20/0.52      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      (((r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ (k1_relat_1 @ sk_D_3)))
% 0.20/0.52         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.20/0.52      inference('demod', [status(thm)], ['39', '40'])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(dt_k1_relset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (k1_relset_1 @ X18 @ X19 @ X20) @ (k1_zfmisc_1 @ X18))
% 0.20/0.52          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.20/0.52  thf('44', plain,
% 0.20/0.52      ((m1_subset_1 @ (k1_relset_1 @ sk_C_1 @ sk_A @ sk_D_3) @ 
% 0.20/0.52        (k1_zfmisc_1 @ sk_C_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.52  thf('45', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.52         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 0.20/0.52          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.52  thf('47', plain,
% 0.20/0.52      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_D_3) = (k1_relat_1 @ sk_D_3))),
% 0.20/0.52      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      ((m1_subset_1 @ (k1_relat_1 @ sk_D_3) @ (k1_zfmisc_1 @ sk_C_1))),
% 0.20/0.52      inference('demod', [status(thm)], ['44', '47'])).
% 0.20/0.52  thf(t4_subset, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.20/0.52       ( m1_subset_1 @ A @ C ) ))).
% 0.20/0.52  thf('49', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.20/0.52          | (m1_subset_1 @ X0 @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [t4_subset])).
% 0.20/0.52  thf('50', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((m1_subset_1 @ X0 @ sk_C_1)
% 0.20/0.52          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_3)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.52  thf('51', plain,
% 0.20/0.52      (((m1_subset_1 @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_C_1))
% 0.20/0.52         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['41', '50'])).
% 0.20/0.52  thf('52', plain,
% 0.20/0.52      (~
% 0.20/0.52       (![X28 : $i]:
% 0.20/0.52          (~ (m1_subset_1 @ X28 @ sk_C_1)
% 0.20/0.52           | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_E) @ sk_D_3)
% 0.20/0.52           | ~ (r2_hidden @ X28 @ sk_B))) | 
% 0.20/0.52       ~ ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B)))),
% 0.20/0.52      inference('demod', [status(thm)], ['31', '36', '51'])).
% 0.20/0.52  thf('53', plain,
% 0.20/0.52      (((r2_hidden @ sk_F @ sk_B)) | 
% 0.20/0.52       ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B)))),
% 0.20/0.52      inference('split', [status(esa)], ['5'])).
% 0.20/0.52  thf('54', plain, (((r2_hidden @ sk_F @ sk_B))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['22', '52', '53'])).
% 0.20/0.52  thf('55', plain,
% 0.20/0.52      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3)) | 
% 0.20/0.52       ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B)))),
% 0.20/0.52      inference('split', [status(esa)], ['7'])).
% 0.20/0.52  thf('56', plain, (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['22', '52', '55'])).
% 0.20/0.52  thf('57', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_3 @ sk_B))),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['21', '54', '56'])).
% 0.20/0.52  thf('58', plain,
% 0.20/0.52      (($false)
% 0.20/0.52         <= (~
% 0.20/0.52             ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.20/0.52      inference('demod', [status(thm)], ['1', '4', '57'])).
% 0.20/0.52  thf('59', plain,
% 0.20/0.52      (~ ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B)))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['22', '52'])).
% 0.20/0.52  thf('60', plain, ($false),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['58', '59'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
