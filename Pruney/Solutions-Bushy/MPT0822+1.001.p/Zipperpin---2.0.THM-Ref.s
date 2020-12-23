%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0822+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VEs3tUYXbA

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:32 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 493 expanded)
%              Number of leaves         :   23 ( 139 expanded)
%              Depth                    :   17
%              Number of atoms          : 1073 (7007 expanded)
%              Number of equality atoms :   58 ( 385 expanded)
%              Maximal formula depth    :   16 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('0',plain,(
    ! [X2: $i,X5: $i] :
      ( ( X5
        = ( k2_relat_1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X5 @ X2 ) @ ( sk_C @ X5 @ X2 ) ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X5 @ X2 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ X1 @ X3 )
      | ( X3
       != ( k2_relat_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ ( k2_relat_1 @ X2 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf(t23_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) )
      <=> ( ( k2_relset_1 @ A @ B @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
       => ( ! [D: $i] :
              ~ ( ( r2_hidden @ D @ B )
                & ! [E: $i] :
                    ~ ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) )
        <=> ( ( k2_relset_1 @ A @ B @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_relset_1])).

thf('4',plain,(
    ! [X22: $i] :
      ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
        = sk_B )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ X22 ) @ X22 ) @ sk_C_1 )
      | ~ ( r2_hidden @ X22 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ! [X22: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X22 ) @ X22 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X22 @ sk_B ) )
   <= ! [X22: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X22 ) @ X22 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X22 @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C @ sk_B @ X0 ) @ ( k2_relat_1 @ X0 ) )
        | ( sk_B
          = ( k2_relat_1 @ X0 ) )
        | ( r2_hidden @ ( k4_tarski @ ( sk_E @ ( sk_C @ sk_B @ X0 ) ) @ ( sk_C @ sk_B @ X0 ) ) @ sk_C_1 ) )
   <= ! [X22: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X22 ) @ X22 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X22 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X2: $i,X5: $i,X6: $i] :
      ( ( X5
        = ( k2_relat_1 @ X2 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ ( sk_C @ X5 @ X2 ) ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X2 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('8',plain,
    ( ( ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X22: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X22 ) @ X22 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X22 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X22: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X22 ) @ X22 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X22 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('11',plain,
    ( ( ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X22: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X22 ) @ X22 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X22 @ sk_B ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X22: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X22 ) @ X22 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X22 @ sk_B ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('13',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X7 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('15',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('18',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['15','18'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('20',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( m1_subset_1 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B ) )
   <= ! [X22: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X22 ) @ X22 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X22 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','21'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('23',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('24',plain,
    ( ( ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( v1_xboole_0 @ sk_B )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B ) )
   <= ! [X22: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X22 ) @ X22 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X22 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X22: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X22 ) @ X22 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X22 @ sk_B ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('26',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X4 @ X2 ) @ X4 ) @ X2 )
      | ( X3
       != ( k2_relat_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('27',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X4 @ X2 ) @ X4 ) @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k2_relat_1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_C_1 ) @ ( sk_C @ sk_B @ sk_C_1 ) ) @ sk_C_1 ) )
   <= ! [X22: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X22 ) @ X22 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X22 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X2: $i,X5: $i,X6: $i] :
      ( ( X5
        = ( k2_relat_1 @ X2 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ ( sk_C @ X5 @ X2 ) ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X2 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('30',plain,
    ( ( ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X22: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X22 ) @ X22 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X22 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X22: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X22 ) @ X22 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X22 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X22: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X22 ) @ X22 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X22 @ sk_B ) ) ),
    inference(clc,[status(thm)],['24','31'])).

thf('33',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('34',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B )
    | ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
     != sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,
    ( ( ( sk_B != sk_B )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
       != sk_B )
      & ! [X22: $i] :
          ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X22 ) @ X22 ) @ sk_C_1 )
          | ~ ( r2_hidden @ X22 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf('38',plain,
    ( ( v1_xboole_0 @ sk_B )
   <= ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
       != sk_B )
      & ! [X22: $i] :
          ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X22 ) @ X22 ) @ sk_C_1 )
          | ~ ( r2_hidden @ X22 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['15','18'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('40',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
       != sk_B )
      & ! [X22: $i] :
          ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X22 ) @ X22 ) @ sk_C_1 )
          | ~ ( r2_hidden @ X22 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,
    ( ( sk_B
      = ( k2_relat_1 @ sk_C_1 ) )
   <= ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
       != sk_B )
      & ! [X22: $i] :
          ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X22 ) @ X22 ) @ sk_C_1 )
          | ~ ( r2_hidden @ X22 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['11','42'])).

thf('44',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
     != sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('45',plain,
    ( $false
   <= ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
       != sk_B )
      & ! [X22: $i] :
          ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X22 ) @ X22 ) @ sk_C_1 )
          | ~ ( r2_hidden @ X22 @ sk_B ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X21: $i] :
      ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
       != sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ X21 @ sk_D_2 ) @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B )
    | ! [X21: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ X21 @ sk_D_2 ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_B )
   <= ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['34'])).

thf('49',plain,
    ( ! [X22: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X22 ) @ X22 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X22 @ sk_B ) )
   <= ! [X22: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X22 ) @ X22 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X22 @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf('50',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_D_2 ) @ sk_D_2 ) @ sk_C_1 )
   <= ( ( r2_hidden @ sk_D_2 @ sk_B )
      & ! [X22: $i] :
          ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X22 ) @ X22 ) @ sk_C_1 )
          | ~ ( r2_hidden @ X22 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ! [X21: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ X21 @ sk_D_2 ) @ sk_C_1 )
   <= ! [X21: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ X21 @ sk_D_2 ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['46'])).

thf('52',plain,
    ( ~ ( r2_hidden @ sk_D_2 @ sk_B )
    | ~ ! [X21: $i] :
          ~ ( r2_hidden @ ( k4_tarski @ X21 @ sk_D_2 ) @ sk_C_1 )
    | ~ ! [X22: $i] :
          ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X22 ) @ X22 ) @ sk_C_1 )
          | ~ ( r2_hidden @ X22 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_B )
   <= ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['34'])).

thf('54',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('55',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('56',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X4 @ X2 ) @ X4 ) @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k2_relat_1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X0 @ sk_C_1 ) @ X0 ) @ sk_C_1 ) )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_D_2 @ sk_C_1 ) @ sk_D_2 ) @ sk_C_1 )
   <= ( ( r2_hidden @ sk_D_2 @ sk_B )
      & ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['53','58'])).

thf('60',plain,
    ( ! [X21: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ X21 @ sk_D_2 ) @ sk_C_1 )
   <= ! [X21: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ X21 @ sk_D_2 ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['46'])).

thf('61',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B )
    | ~ ! [X21: $i] :
          ~ ( r2_hidden @ ( k4_tarski @ X21 @ sk_D_2 ) @ sk_C_1 )
    | ~ ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ! [X22: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X22 ) @ X22 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X22 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('63',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_D_2 ) @ sk_D_2 ) @ sk_C_1 )
   <= ( ( r2_hidden @ sk_D_2 @ sk_B )
      & ! [X22: $i] :
          ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X22 ) @ X22 ) @ sk_C_1 )
          | ~ ( r2_hidden @ X22 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ ( k2_relat_1 @ X2 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('65',plain,
    ( ( r2_hidden @ sk_D_2 @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_D_2 @ sk_B )
      & ! [X22: $i] :
          ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X22 ) @ X22 ) @ sk_C_1 )
          | ~ ( r2_hidden @ X22 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
       != sk_B )
      & ! [X22: $i] :
          ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X22 ) @ X22 ) @ sk_C_1 )
          | ~ ( r2_hidden @ X22 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('67',plain,
    ( ~ ( r2_hidden @ sk_D_2 @ sk_B )
    | ~ ! [X22: $i] :
          ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X22 ) @ X22 ) @ sk_C_1 )
          | ~ ( r2_hidden @ X22 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B )
    | ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['34'])).

thf('69',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['47','52','61','62','67','68'])).

thf('70',plain,(
    ! [X22: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X22 ) @ X22 ) @ sk_C_1 )
      | ~ ( r2_hidden @ X22 @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['47','52','61','67','68','62'])).

thf('71',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['45','69','70'])).


%------------------------------------------------------------------------------
